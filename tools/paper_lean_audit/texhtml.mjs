// Minimal LaTeX-to-HTML conversion for the manuscript excerpts shown in the
// review document. Mathematics is rendered by KaTeX; text-mode commands used
// by human_readable_main.tex (including the AI review markup) are translated.
// Unknown commands are kept visibly as \name so nothing is silently dropped.
import katex from 'katex';

const MATH_ENVS = new Set(['equation', 'equation*', 'align', 'align*', 'gather', 'gather*', 'multline', 'multline*']);
const DROP_CMDS = new Set(['noindent', 'smallskip', 'medskip', 'bigskip', 'clearpage', 'newpage', 'hfill',
  'par', 'maketitle', 'AIreviewlegend', 'centering', 'small', 'normalfont', 'nonumber']);

export function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

export function stripComments(tex) {
  return tex.split('\n').map((line) => {
    for (let i = 0; i < line.length; i++) {
      if (line[i] === '\\') { i++; continue; }
      if (line[i] === '%') return line.slice(0, i);
    }
    return line;
  }).join('\n');
}

// Reads a balanced {...} group starting at s[i] === '{'. Returns [content, nextIndex].
export function readGroup(s, i) {
  if (s[i] !== '{') return [null, i];
  let depth = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') { j++; continue; }
    if (s[j] === '{') depth++;
    else if (s[j] === '}') { depth--; if (depth === 0) return [s.slice(i + 1, j), j + 1]; }
  }
  return [s.slice(i + 1), s.length];
}

function skipSpaces(s, i) { while (i < s.length && /[ \t\n]/.test(s[i])) i++; return i; }

function isEscaped(s, i) {
  let slashes = 0;
  for (let j = i - 1; j >= 0 && s[j] === '\\'; j--) slashes++;
  return slashes % 2 === 1;
}

function findDelimiter(s, start, delimiter) {
  for (let i = start; i < s.length; i++) {
    if (isEscaped(s, i) || !s.startsWith(delimiter, i)) continue;
    // A single-dollar delimiter must not consume one half of a display pair.
    if (delimiter === '$' && (s[i - 1] === '$' || s[i + 1] === '$')) continue;
    return i;
  }
  return -1;
}

function isStringifiedCommand(s, i) {
  const match = /\\string\s*$/.exec(s.slice(0, i));
  return match !== null && !isEscaped(s, match.index);
}

function findToken(s, token, start) {
  let i = s.indexOf(token, start);
  while (i >= 0 && (isEscaped(s, i) || isStringifiedCommand(s, i))) i = s.indexOf(token, i + 1);
  return i;
}

function readOptional(s, i) {
  const j = skipSpaces(s, i);
  if (s[j] !== '[') return [null, i];
  let braces = 0, brackets = 0;
  for (let k = j; k < s.length; k++) {
    if (s[k] === '\\') { k++; continue; }
    if (s[k] === '{') braces++;
    else if (s[k] === '}') braces = Math.max(0, braces - 1);
    else if (braces === 0 && s[k] === '[') brackets++;
    else if (braces === 0 && s[k] === ']' && --brackets === 0) return [s.slice(j + 1, k), k + 1, j + 1];
  }
  return [null, i];
}

function findEnd(s, i, env) {
  const open = `\\begin{${env}}`, close = `\\end{${env}}`;
  let depth = 1, j = i;
  while (j < s.length) {
    const a = findToken(s, open, j), b = findToken(s, close, j);
    if (b < 0) return [-1, -1];
    if (a >= 0 && a < b) { depth++; j = a + open.length; continue; }
    depth--;
    if (depth === 0) return [b, b + close.length];
    j = b + close.length;
  }
  return [-1, -1];
}

function expandMathEdits(source, depth = 0) {
  if (depth > 100) return source;
  const re = /\\AI(add|remove|replace)\b/g;
  let command = null;
  for (let m; (m = re.exec(source));) {
    if (!isEscaped(source, m.index)) { command = m; break; }
  }
  if (!command) return source;
  let cursor = command.index + command[0].length;
  const [oldText, afterOld] = readGroup(source, cursor);
  if (oldText === null || afterOld <= cursor || source[afterOld - 1] !== '}') return source;
  cursor = afterOld;
  let newText = null;
  if (command[1] === 'replace') {
    const [value, afterNew] = readGroup(source, cursor);
    if (value === null || afterNew <= cursor || source[afterNew - 1] !== '}') return source;
    newText = value;
    cursor = afterNew;
  }
  const oldMath = `\\textcolor{blue}{\\cancel{${expandMathEdits(oldText, depth + 1)}}}`;
  const replacement = command[1] === 'add'
    ? `\\textcolor{red}{${expandMathEdits(oldText, depth + 1)}}`
    : command[1] === 'remove'
      ? oldMath
      : `${oldMath}\\,\\textcolor{red}{${expandMathEdits(newText, depth + 1)}}`;
  return expandMathEdits(source.slice(0, command.index) + replacement + source.slice(cursor), depth + 1);
}

export class TexRenderer {
  constructor({ macros, refs, cites, eqAuto, leanRefs = new Map() }) {
    this.macros = macros;      // KaTeX macros
    this.refs = refs;          // label -> {text, href}
    this.cites = cites;        // key -> short label
    this.eqAuto = eqAuto;      // display-math environment start offset -> rendered tag
    this.leanRefs = leanRefs;  // TeX macro key -> pinned source URL
    this.warnings = [];
  }

  math(src, display, tag) {
    let body = expandMathEdits(src).replace(/\\label\s*\{[^}]*\}/g, '').replace(/\\(?:nonumber|notag)\b/g, '');
    body = body.replace(/\\begin\{psmallmatrix\}/g, '\\left(\\begin{smallmatrix}')
      .replace(/\\end\{psmallmatrix\}/g, '\\end{smallmatrix}\\right)');
    let explicitTag = null;
    body = body.replace(/\\tag\{([^}]*)\}/g, (_, t) => { explicitTag = t; return ''; });
    const finalTag = explicitTag ?? tag;
    if (finalTag && display) body = `${body}\\tag{${finalTag}}`;
    try {
      return katex.renderToString(body, { displayMode: display, throwOnError: true, macros: { ...this.macros }, strict: 'ignore', trust: false });
    } catch (e) {
      this.warnings.push(`KaTeX: ${e.message.split('\n')[0]} in: ${src.slice(0, 80)}`);
      return `<code class="tex-error">${escapeHtml(src)}</code>`;
    }
  }

  ref(label, eq, displayHtml = null) {
    const r = this.refs[label];
    if (!r) {
      this.warnings.push(`unresolved \\ref{${label}}`);
      return displayHtml ?? `<span class="unresolved">??${escapeHtml(label)}</span>`;
    }
    const text = displayHtml ?? escapeHtml(eq ? `(${r.text})` : r.text);
    if (!r.href) return text;
    // References in this review document are local anchors. Do not let an
    // unexpected mapping value turn a TeX reference into an active URL.
    if (!/^#[A-Za-z0-9_.:-]+$/.test(r.href)) {
      this.warnings.push(`unsafe reference href omitted for \\ref{${label}}`);
      return text;
    }
    return `<a href="${escapeHtml(r.href)}">${text}</a>`;
  }

  // Converts text-mode LaTeX to HTML. `base` is the offset of s inside the document
  // (used to number equation environments consistently with the PDF).
  text(s, base = 0) {
    let out = '';
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (c === '$') {
        const dbl = s[i + 1] === '$';
        const delimiter = dbl ? '$$' : '$';
        const open = delimiter.length;
        const j = findDelimiter(s, i + open, delimiter);
        if (j < 0) {
          this.warnings.push(`unclosed math delimiter ${delimiter}`);
          out += `<code class="tex-error">${escapeHtml(s.slice(i))}</code>`;
          break;
        }
        const src = s.slice(i + open, j);
        out += this.math(src, dbl);
        i = j + open;
        continue;
      }
      if (c === '\\') {
        if (s[i + 1] === '[') {
          const j = findDelimiter(s, i + 2, '\\]');
          if (j < 0) {
            this.warnings.push('unclosed math delimiter \\[');
            out += `<code class="tex-error">${escapeHtml(s.slice(i))}</code>`;
            break;
          }
          out += `<div class="dmath">${this.math(s.slice(i + 2, j), true)}</div>`;
          i = j + 2;
          continue;
        }
        if (s[i + 1] === '(') {
          const j = findDelimiter(s, i + 2, '\\)');
          if (j < 0) {
            this.warnings.push('unclosed math delimiter \\(');
            out += `<code class="tex-error">${escapeHtml(s.slice(i))}</code>`;
            break;
          }
          out += this.math(s.slice(i + 2, j), false);
          i = j + 2;
          continue;
        }
        if (s[i + 1] === '\\') { out += '<br>'; i += 2; continue; }
        if ('%&_#{}$ ,;'.includes(s[i + 1])) { out += s[i + 1] === ',' || s[i + 1] === ';' ? '&thinsp;' : escapeHtml(s[i + 1]); i += 2; continue; }
        const m = /^\\([A-Za-z]+\*?)/.exec(s.slice(i));
        if (!m) { out += '\\'; i++; continue; }
        const name = m[1];
        let j = i + m[0].length;
        const readArg = () => {
          j = skipSpaces(s, j);
          const start = j;
          const [content, next] = readGroup(s, j);
          if (content === null) return { content: '', base: base + start };
          j = next;
          return { content, base: base + start + 1 };
        };
        const arg = () => readArg().content;
        switch (name) {
          case 'begin': {
            const env = arg();
            const [endStart, endAfter] = findEnd(s, j, env);
            if (endStart < 0) {
              this.warnings.push(`unclosed environment \\begin{${env}}`);
              out += `<code class="tex-error">${escapeHtml(s.slice(i))}</code>`;
              i = s.length;
              continue;
            }
            const inner = s.slice(j, endStart);
            if (MATH_ENVS.has(env)) {
              let tag = this.eqAuto.get(base + i) ?? null;
              let body = inner;
              if (env.startsWith('align') || env.startsWith('gather') || env.startsWith('multline')) {
                let t = null;
                body = body.replace(/\\tag\{([^}]*)\}/g, (_, x) => { t = x; return ''; });
                body = `\\begin{${env.startsWith('align') ? 'aligned' : 'gathered'}}${body}\\end{${env.startsWith('align') ? 'aligned' : 'gathered'}}`;
                tag = t ?? tag;
              }
              out += `<div class="dmath">${this.math(body, true, tag)}</div>`;
            } else if (env === 'itemize' || env === 'enumerate') {
              const tagName = env === 'itemize' ? 'ul' : 'ol';
              const prefix = /^\s*\[[^\]]*\]/.exec(inner)?.[0] ?? '';
              const innerBody = inner.slice(prefix.length);
              const items = [...innerBody.matchAll(/\\item\b/g)];
              out += `<${tagName}>` + items.map((item, index) => {
                const start = item.index + item[0].length;
                const end = items[index + 1]?.index ?? innerBody.length;
                return `<li>${this.text(innerBody.slice(start, end), base + j + prefix.length + start)}</li>`;
              }).join('') + `</${tagName}>`;
            } else if (env === 'proof') {
              const [opt, k, optStart] = readOptional(inner, 0);
              out += `<div class="proof"><span class="proof-head">${opt ? this.text(opt, base + j + optStart) : 'Proof.'}</span> ${this.text(inner.slice(k), base + j + k)}<span class="qed">∎</span></div>`;
            } else if (env === 'quote') {
              out += `<blockquote>${this.text(inner, base + j)}</blockquote>`;
            } else {
              const [opt, k, optStart] = readOptional(inner, 0);
              out += `<div class="env env-${escapeHtml(env)}"><span class="env-head">${escapeHtml(env[0].toUpperCase() + env.slice(1))}${opt ? ' (' + this.text(opt, base + j + optStart) + ')' : ''}.</span> ${this.text(inner.slice(k), base + j + k)}</div>`;
            }
            i = endAfter;
            continue;
          }
          case 'end': arg(); i = j; continue;
          case 'AIadd': { const a = readArg(); out += `<span class="ai-add">${this.text(a.content, a.base)}</span>`; i = j; continue; }
          case 'AIremove': { const a = readArg(); out += `<del class="ai-remove">${this.text(a.content, a.base)}</del>`; i = j; continue; }
          case 'AIreplace': { const a = readArg(), b = readArg(); out += `<del class="ai-remove">${this.text(a.content, a.base)}</del><span class="ai-add">${this.text(b.content, b.base)}</span>`; i = j; continue; }
          case 'AIcomment': { const id = arg(), body = readArg(); out += `<div class="ai-comment" id="aic-${escapeHtml(id)}"><b>AI comment ${escapeHtml(id)}.</b> ${this.text(body.content, body.base)}</div>`; i = j; continue; }
          case 'formalref': {
            const [relation, afterRelation, relationStart] = readOptional(s, j);
            if (relation !== null) j = afterRelation;
            const declarations = readArg();
            const relationHtml = relation === null ? '' : `<span class="formalref-relation"> (${this.text(relation, base + relationStart)})</span>`;
            out += `<span class="formalref"><b>Lean${relationHtml}:</b> ${this.text(declarations.content, declarations.base)}</span>`;
            i = j;
            continue;
          }
          case 'leandecl': case 'leanlib': {
            const fileArg = arg().trim(), lineArg = arg().trim(), declaration = arg().trim();
            // The lookup key is constructed by build.mjs from the command and
            // the exact file/line/name tuple validated against the pinned tree.
            const url = this.leanRefs.get([name, fileArg, lineArg, declaration].join('\0'));
            if (!url) {
              this.warnings.push(`unresolved \\${name}{${fileArg}}{${lineArg}}{${declaration}}`);
              out += `<code>${escapeHtml(declaration || `${fileArg}:${lineArg}`)}</code>`;
            } else if (!/^https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+\/blob\/[A-Fa-f0-9]{40}\/[^\s"<>]+#L\d+(?:-L\d+)?$/.test(url)) {
              this.warnings.push(`unsafe Lean source URL omitted for ${declaration}`);
              out += `<code>${escapeHtml(declaration)}</code>`;
            } else {
              out += `<a class="lean-source" href="${escapeHtml(url)}"><code>${escapeHtml(declaration)}</code></a>`;
            }
            i = j;
            continue;
          }
          case 'emph': case 'textit': { const a = readArg(); out += `<em>${this.text(a.content, a.base)}</em>`; i = j; continue; }
          case 'textbf': { const a = readArg(); out += `<b>${this.text(a.content, a.base)}</b>`; i = j; continue; }
          case 'texttt': { const a = readArg(); out += `<code>${this.text(a.content, a.base)}</code>`; i = j; continue; }
          case 'textsc': case 'textrm': case 'textsf': case 'mbox': case 'text': { const a = readArg(); out += this.text(a.content, a.base); i = j; continue; }
          case 'href': {
            const url = arg().trim().replace(/\\([#%_&])/g, '$1');
            const display = readArg();
            const label = this.text(display.content, display.base);
            if (!/^https?:\/\/[^\s"<>]+$/.test(url)) {
              this.warnings.push('unsafe external href omitted');
              out += label;
            } else out += `<a href="${escapeHtml(url)}">${label}</a>`;
            i = j; continue;
          }
          case 'nolinkurl': { const a = readArg(); out += `<code>${escapeHtml(a.content)}</code>`; i = j; continue; }
          case 'texorpdfstring': { const a = readArg(); readArg(); out += this.text(a.content, a.base); i = j; continue; }
          case 'string': {
            // \string\cmd prints the command name literally (used inside \texttt).
            const lit = /^\\([A-Za-z]+)/.exec(s.slice(j));
            if (lit) { out += escapeHtml('\\' + lit[1]); j += lit[0].length; }
            i = j; continue;
          }
          case 'cite': {
            const [opt, k, optStart] = readOptional(s, j); j = k;
            const keys = arg().split(',').map((x) => x.trim());
            const labels = keys.map((key) => escapeHtml(this.cites[key] ?? key)).join(', ');
            out += `<span class="cite">[${labels}${opt ? ', ' + this.text(opt, base + (optStart ?? 0)) : ''}]</span>`;
            i = j; continue;
          }
          case 'hyperref': {
            const [label, afterLabel] = readOptional(s, j);
            if (label === null) {
              const display = readArg();
              this.warnings.push('\\hyperref without an optional label kept as text');
              out += `<code>\\hyperref</code>${this.text(display.content, display.base)}`;
            } else {
              j = afterLabel;
              const display = readArg();
              out += this.ref(label, false, this.text(display.content, display.base));
            }
            i = j; continue;
          }
          case 'ref': out += this.ref(arg(), false); i = j; continue;
          case 'eqref': out += this.ref(arg(), true); i = j; continue;
          case 'label': arg(); i = j; continue;
          case 'section': case 'section*': case 'subsection': case 'subsection*':
            { const a = readArg(); out += `<h5 class="tex-sec">${this.text(a.content, a.base)}</h5>`; i = j; continue; }
          case 'item': out += '<br>• '; i = j; continue;
          case 'S': out += '§'; i = j; continue;
          case 'ldots': case 'dots': out += '…'; i = j; continue;
          case 'cdots': case 'cots': out += '⋯'; i = j; continue;
          case 'quad': case 'qquad': out += '&emsp;'; i = j; continue;
          case 'LaTeX': out += 'LaTeX'; i = j; continue;
          default:
            if (DROP_CMDS.has(name)) { i = j; continue; }
            this.warnings.push(`kept unknown text command \\${name}`);
            out += `<code>\\${escapeHtml(name)}</code>`;
            i = j;
            continue;
        }
      }
      if (c === '\n' && s[i + 1] === '\n') {
        out += '</p><p>';
        while (s[i] === '\n') i++;
        continue;
      }
      if (c === '~') { out += '&nbsp;'; i++; continue; }
      if (s.startsWith('---', i)) { out += '—'; i += 3; continue; }
      if (s.startsWith('--', i)) { out += '–'; i += 2; continue; }
      if (s.startsWith('``', i)) { out += '“'; i += 2; continue; }
      if (s.startsWith("''", i)) { out += '”'; i += 2; continue; }
      if (c === '{' || c === '}') { i++; continue; }
      out += escapeHtml(c);
      i++;
    }
    return out;
  }

  block(s, base) {
    const html = `<p>${this.text(s, base)}</p>`;
    return html.replace(/<p>\s*<\/p>/g, '');
  }
}
