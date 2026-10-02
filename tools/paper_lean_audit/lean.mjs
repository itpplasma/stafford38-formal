// Lean source helpers: locate a declaration at a pinned revision, verify its
// fully qualified name against the enclosing namespaces, and extract the
// statement (docstring and signature, without the proof body).
import { escapeHtml } from './texhtml.mjs';

const DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|public|meta|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s:({\[]+)/;
const SCOPE_RE = /^\s*(?:@\[[^\]]*\]\s*)*((?:(?:public|noncomputable|meta)\s+)*)(namespace|section)(?:\s+(\S+))?\s*$/;

// The dot before an explicit universe binder (`name.{u}`) is syntax,
// rather than part of the declaration's exported name.
function declarationName(match) {
  return match[2].replace(/\.$/, '');
}

// Replace comments and string contents with spaces while preserving newlines
// and offsets. Lean block comments nest, and declaration-looking text in a
// comment must never affect namespace or declaration lookup.
function maskLeanCommentsAndStrings(text) {
  const out = text.split('');
  let blockDepth = 0;
  let inString = false;
  let escaped = false;
  const mask = (i) => { if (text[i] !== '\n') out[i] = ' '; };

  for (let i = 0; i < text.length; i++) {
    if (blockDepth > 0) {
      if (text.startsWith('/-', i)) {
        mask(i); mask(i + 1); blockDepth++; i++;
      } else if (text.startsWith('-/', i)) {
        mask(i); mask(i + 1); blockDepth--; i++;
      } else mask(i);
      continue;
    }
    if (inString) {
      mask(i);
      if (escaped) escaped = false;
      else if (text[i] === '\\') escaped = true;
      else if (text[i] === '"') inString = false;
      continue;
    }
    if (text.startsWith('/-', i)) {
      mask(i); mask(i + 1); blockDepth = 1; i++;
    } else if (text.startsWith('--', i)) {
      while (i < text.length && text[i] !== '\n') mask(i++);
      i--;
    } else if (text[i] === '"') {
      mask(i); inString = true;
    }
  }
  return out.join('');
}

function scopeAt(lines, index) {
  const stack = [];
  let defaultVisibility = 'public';
  const codeLines = maskLeanCommentsAndStrings(lines.join('\n')).split('\n');
  for (let i = 0; i < index; i++) {
    const line = codeLines[i];
    if (/^\s*module\s*$/.test(line)) { defaultVisibility = 'private'; continue; }
    let m = SCOPE_RE.exec(line);
    if (m) {
      const visibility = /\bpublic\b/.test(m[1]) ? 'public'
        : stack.at(-1)?.visibility ?? defaultVisibility;
      if (m[2] === 'namespace' && m[3]) {
        stack.push(...m[3].split('.').map((part) => ({ part, kind: 'ns', group: m[3], visibility })));
      } else if (m[2] === 'section') {
        stack.push({ part: null, kind: 'sec', group: m[3] ?? '', visibility });
      }
      continue;
    }
    m = /^\s*end(?:\s+(\S+))?\s*$/.exec(line);
    if (m) {
      const name = m[1] ?? '';
      // An unnamed `end` closes the innermost scope. A named end can close
      // a namespace opened with a dotted name, which occupies several frames.
      let k = -1;
      if (name) {
        for (let j = stack.length - 1; j >= 0; j--) {
          if (stack[j].group === name) { k = j; break; }
        }
      } else if (stack.length) k = stack.length - 1;
      if (k >= 0) {
        const { group, kind } = stack[k];
        while (stack.length > k) stack.pop();
        if (kind === 'ns') {
          while (stack.length && stack.at(-1).group === group && stack.at(-1).kind === 'ns') stack.pop();
        }
      }
    }
  }
  return {
    namespace: stack.filter((f) => f.kind === 'ns').map((f) => f.part),
    visibility: stack.at(-1)?.visibility ?? defaultVisibility,
  };
}

export function namespaceAt(lines, index) {
  return scopeAt(lines, index).namespace;
}

export function findDeclaration(text, fullName, hintLine) {
  const lines = text.split('\n');
  const codeLines = maskLeanCommentsAndStrings(text).split('\n');
  const short = fullName.split('.').pop();
  const candidates = [];
  codeLines.forEach((line, i) => {
    const m = DECL_RE.exec(line);
    if (!m) return;
    const declared = declarationName(m).replace(/^_root_\./, '');
    if (declared === short || fullName.endsWith('.' + declared) || declared === fullName) {
      const scope = scopeAt(lines, i);
      const ns = scope.namespace;
      const qualified = declarationName(m).startsWith('_root_.') ? declared : [...ns, declared].join('.');
      const modifierText = m[0].slice(0, m[0].indexOf(m[1]));
      const visibility = /\bprivate\b/.test(modifierText) ? 'private'
        : /\blocal\b/.test(modifierText) ? 'local'
        : /\bpublic\b/.test(modifierText) ? 'public' : scope.visibility;
      candidates.push({ line: i + 1, qualified, keyword: m[1], visibility, exported: visibility === 'public' });
    }
  });
  const exact = candidates.filter((c) => c.qualified === fullName);
  const pool = exact.length ? exact : candidates;
  if (!pool.length) return null;
  pool.sort((a, b) => Math.abs(a.line - (hintLine ?? 0)) - Math.abs(b.line - (hintLine ?? 0)));
  return { ...pool[0], exact: exact.length > 0, lines };
}

// Index of the first `:=` at bracket depth 0 (so named arguments such as
// `(k := k)` inside a signature do not end the statement), or -1.
function topLevelAssign(line, state) {
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c === '-' && line[i + 1] === '-') return -1; // line comment
    if ('([{⟨'.includes(c)) state.depth++;
    else if (')]}⟩'.includes(c)) state.depth = Math.max(0, state.depth - 1);
    else if (c === ':' && line[i + 1] === '=' && state.depth === 0) return i;
  }
  return -1;
}

export function extractStatement(lines, declLine, maxLines = 45, withBody = false) {
  const codeLines = maskLeanCommentsAndStrings(lines.join('\n')).split('\n');
  let start = declLine - 1;
  // Include a directly preceding docstring and attributes.
  let k = start - 1;
  while (k >= 0 && /^\s*(?:@\[[^\]]*\]\s*)+$/.test(lines[k])) k--;
  if (k >= 0 && /-\/\s*$/.test(lines[k])) {
    let d = k;
    while (d >= 0 && !/^\s*\/--/.test(lines[d])) d--;
    if (d >= 0 && k - d < 40) k = d - 1;
  }
  start = k + 1;
  const out = [];
  let end = declLine - 1;
  let truncated = false;
  const state = { depth: 0 };
  let inBody = false;
  const declarationIndent = /^\s*/.exec(lines[declLine - 1])[0].length;
  for (let i = declLine - 1; i < lines.length; i++) {
    const line = lines[i];
    const codeLine = codeLines[i];
    if (out.length >= maxLines) { truncated = true; break; }
    if (i > declLine - 1 && (DECL_RE.test(codeLine) || SCOPE_RE.test(codeLine) || /^\s*(?:end|variable|open|#check|#print)\b/.test(codeLine))) break;
    if (inBody) {
      // Blank lines inside a definition do not terminate it. Look past blank
      // lines/comments for the next command, rather than dropping later fields.
      if (/^\s*$/.test(codeLine)) {
        let next = i + 1;
        while (next < lines.length && /^\s*$/.test(codeLines[next])) next++;
        if (next === lines.length || DECL_RE.test(codeLines[next]) ||
            SCOPE_RE.test(codeLines[next]) || (/^\s*(?:end|variable|open|#\w+)\b/.test(codeLines[next])) ||
            (/^\s*/.exec(codeLines[next])[0].length <= declarationIndent && !/^\s*\|/.test(codeLines[next]))) break;
      }
      if (/:=\s*by\b/.test(codeLine)) { truncated = true; break; }
      out.push(line); end = i; continue;
    }
    const cut = topLevelAssign(codeLine, state);
    if (cut >= 0) {
      const remainingBody = [codeLine.slice(cut + 2), ...codeLines.slice(i + 1)].join('\n');
      if (withBody && !/^\s*by\b/.test(remainingBody)) { out.push(line); end = i; inBody = true; continue; }
      if (withBody) truncated = true;
      out.push(line.slice(0, cut + 2)); end = i; break;
    }
    if (withBody && /^\s*\|/.test(codeLine)) {
      inBody = true;
      out.push(line); end = i; continue;
    }
    if (/\bwhere\s*$/.test(codeLine)) {
      out.push(line); end = i;
      if (withBody) { inBody = true; continue; }
      break;
    }
    out.push(line); end = i;
  }
  const body = [...lines.slice(start, declLine - 1), ...out];
  return { text: body.join('\n').replace(/\s+$/, '') + (truncated ? '\n  …' : ''), startLine: start + 1, endLine: end + 1, truncated };
}

export function declarationContext(lines, declLine) {
  const code = maskLeanCommentsAndStrings(lines.join('\n')).split('\n');
  const scopes = [{ name: null, declarations: [] }];
  for (let i = 0; i < declLine - 1; i++) {
    const line = code[i];
    let m = SCOPE_RE.exec(line);
    if (m) { scopes.push({ name: m[3] ?? '', declarations: [] }); continue; }
    m = /^\s*end(?:\s+(\S+))?\s*$/.exec(line);
    if (m && scopes.length > 1) {
      let at = scopes.length - 1;
      if (m[1]) {
        while (at > 0 && scopes[at].name !== m[1]) at--;
      }
      if (at > 0) scopes.length = at;
      continue;
    }
    if (/^\s*local\s+(?:noncomputable\s+)?instance\b/.test(line)) {
      const signature = extractStatement(lines, i + 1, 160);
      scopes.at(-1).declarations.push({ text: signature.text, startLine: signature.startLine, endLine: signature.endLine });
      continue;
    }
    if (!/^\s*(?:variable|universe|include|omit|open|local\s+(?:notation|infix[lr]?|prefix|postfix))\b/.test(line)) continue;
    if (/\bin\s*$/.test(line) && i + 1 !== declLine - 1) continue;
    const start = i;
    let depth = 0;
    do {
      for (const c of code[i]) {
        if ('([{'.includes(c)) depth++;
        else if (')]}'.includes(c)) depth--;
      }
      if (i + 1 >= declLine - 1 || (depth === 0 && !/^\s+[([{]/.test(code[i + 1]))) break;
      i++;
    } while (true);
    scopes.at(-1).declarations.push({ text: lines.slice(start, i + 1).join('\n'), startLine: start + 1, endLine: i + 1 });
  }
  return scopes.flatMap((scope) => scope.declarations);
}

export function bindingNames(text) {
  const code = maskLeanCommentsAndStrings(text);
  const names = [];
  let depth = 0, start = 0, bracket = '', hasColon = false;
  const add = (s) => {
    for (const name of s.trim().split(/\s+/)) if (/^[\p{L}_][\p{L}\p{N}_']*$/u.test(name)) names.push(name);
  };
  for (let i = 0; i < code.length; i++) {
    const c = code[i];
    if ('([{'.includes(c)) {
      if (depth === 0) { start = i + 1; bracket = c; hasColon = false; }
      depth++;
    } else if (')]}'.includes(c)) {
      if (--depth === 0 && !hasColon && bracket !== '[') add(code.slice(start, i));
    } else if (c === ':' && code[i + 1] !== '=') {
      if (depth === 0) break; // result type, not a binder
      if (depth === 1 && !hasColon) { add(code.slice(start, i)); hasColon = true; }
    }
  }
  return [...new Set(names)];
}

export function declarationTrust(lines, declLine, keyword) {
  if (keyword === 'axiom') return 'axiom';
  const code = maskLeanCommentsAndStrings(lines.join('\n')).split('\n');
  let end = declLine;
  while (end < code.length && !DECL_RE.test(code[end]) && !SCOPE_RE.test(code[end]) && !/^\s*(?:end|#\w+)\b/.test(code[end])) end++;
  return /\b(?:sorry|admit)\b/.test(code.slice(declLine - 1, end).join('\n')) ? 'placeholder' : 'source declaration';
}

// A theorem whose result is a named predicate needs that predicate's source
// beside its signature. This is source navigation, not semantic unfolding.
export function namedResultType(lines, declLine) {
  const signature = maskLeanCommentsAndStrings(extractStatement(lines, declLine, 160).text);
  let depth = 0;
  for (let i = 0; i < signature.length; i++) {
    const c = signature[i];
    if ('([{⟨'.includes(c)) depth++;
    else if (')]}⟩'.includes(c)) depth--;
    else if (c === ':' && signature[i + 1] !== '=' && depth === 0) {
      const result = signature.slice(i + 1).replace(/:=\s*$/, '').trim();
      // An explicit equality/implication already states its conclusion; its
      // first term is not an opaque proposition alias.
      if (/[=<>↔→∧∨∀∃≤≥≠∈∉⊆⊂]/.test(result)) return null;
      return /^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)/.exec(result)?.[1] ?? null;
    }
  }
  return null;
}

export function definitionNames(text) {
  const lines = text.split('\n');
  return maskLeanCommentsAndStrings(text).split('\n').flatMap((line, i) => {
    const m = DECL_RE.exec(line);
    if (!m || !['def', 'abbrev'].includes(m[1]) || /\b(?:private|local)\b/.test(m[0])) return [];
    const scope = scopeAt(lines, i);
    if (scope.visibility !== 'public' && !/\bpublic\b/.test(m[0])) return [];
    const declared = declarationName(m);
    const name = declared.startsWith('_root_.') ? declared.slice(7) : [...scope.namespace, declared].join('.');
    return [{ name, line: i + 1 }];
  });
}

const KEYWORDS = new Set(['theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'instance', 'inductive', 'where',
  'fun', 'by', 'let', 'have', 'show', 'from', 'if', 'then', 'else', 'match', 'with', 'noncomputable', 'private',
  'protected', 'public', 'meta', 'module', 'variable', 'namespace', 'section', 'end', 'open', 'Type', 'Prop', 'Sort', 'extends', 'in', 'at']);

export function highlightLean(src, identifierLink = () => null) {
  let out = '';
  const re = /(\/--[\s\S]*?-\/|\/-[\s\S]*?-\/|--[^\n]*)|("(?:[^"\\]|\\.)*")|([A-Za-z_][A-Za-z0-9_'.!?]*)|([∀∃λ→↔∧∨¬≤≥≠∈∉⊆⊂∩∪×•∘⁻¹ᵐᵒᵖ]+)|([\s\S])/g;
  let m;
  while ((m = re.exec(src))) {
    if (m[1]) out += `<span class="lc">${escapeHtml(m[1])}</span>`;
    else if (m[2]) out += `<span class="ls">${escapeHtml(m[2])}</span>`;
    else if (m[3]) {
      const href = identifierLink(m[3]);
      const token = KEYWORDS.has(m[3]) ? `<span class="lk">${m[3]}</span>` : escapeHtml(m[3]);
      out += href && /^#[A-Za-z0-9_.:-]+$/.test(href) ? `<a class="definition-link" href="${href}">${token}</a>` : token;
    }
    else if (m[4]) out += `<span class="lo">${escapeHtml(m[4])}</span>`;
    else out += escapeHtml(m[5]);
  }
  return out;
}
