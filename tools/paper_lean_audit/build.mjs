#!/usr/bin/env node
// Builds the Stafford 3.8 paper/Lean review document.
//
//   node build.mjs [--paper DIR] [--formal DIR] [--library DIR] [--out DIR] [--pdf] [--check]
//
// Rendered excerpts are read with `git show <pinned commit>:<path>`, so the
// document is reproducible from paper-lean-map.json and its pinned revisions.
// --check also audits the current paper checkout for theorem-like statement
// coverage and live \leandecl/\leanlib links against the pinned Lean trees.
import { execFileSync } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { TexRenderer, escapeHtml, stripComments, readGroup } from './texhtml.mjs';
import { findDeclaration, extractStatement, highlightLean, namedResultType, definitionNames, declarationContext, bindingNames, declarationTrust } from './lean.mjs';
import { reviewScopeOptions } from './review-scope.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const opt = (name, fallback) => { const i = argv.indexOf(name); return i >= 0 ? argv[i + 1] : fallback; };
const flag = (name) => argv.includes(name);
const home = path.resolve(here, '../../..');
const dirs = {
  paper: path.resolve(opt('--paper', path.join(home, 'stafford38-paper'))),
  formal: path.resolve(opt('--formal', path.join(home, 'stafford38-formal'))),
  library: path.resolve(opt('--library', path.join(home, 'algebraic-analysis'))),
  global: path.resolve(opt('--global', path.join(home, 'global-stafford-formal'))),
};
dirs.mathlib = path.resolve(opt('--mathlib', path.join(dirs.formal, '.lake/packages/mathlib')));
const outDir = path.resolve(opt('--out', path.join(here, 'build')));
const reviewsDir = path.resolve(opt('--reviews', path.join(here, '../../docs/paper-lean-audit/reviews')));
const mapPath = path.resolve(opt('--map', path.join(here, 'paper-lean-map.json')));
const map = JSON.parse(fs.readFileSync(mapPath, 'utf8'));
// Supply any pinned source repository, not just the legacy source roles.
for (let i = 0; i < argv.length; i++) {
  if (argv[i] !== '--source') continue;
  const entry = argv[++i] ?? '';
  const match = /^([A-Za-z][A-Za-z0-9_-]*)=(.+)$/.exec(entry);
  if (!match) throw new Error('--source requires NAME=PATH');
  dirs[match[1]] = path.resolve(match[2]);
}
const outputStem = map.output_stem ?? 'stafford38-paper-lean-audit';
if (!/^[A-Za-z0-9_-]+$/.test(outputStem)) throw new Error('output_stem must be a safe filename');
const liveUrl = map.live_url ?? '';
const errors = [];
const warnings = [];

function gitShow(repoKey, file) {
  const commit = map.sources[repoKey]?.commit;
  if (!commit || !dirs[repoKey]) {
    errors.push(`${repoKey}: no pinned source repository is configured for ${file}`);
    return null;
  }
  try {
    return execFileSync('git', ['-C', dirs[repoKey], 'show', `${commit}:${file}`], {
      encoding: 'utf8', maxBuffer: 64 << 20, stdio: ['ignore', 'pipe', 'ignore'],
    });
  } catch (e) {
    errors.push(`${repoKey}: cannot read ${file} at ${commit}`);
    return null;
  }
}
const ghBlob = (repoKey, file, a, b) => `https://github.com/${map.sources[repoKey].repo}/blob/${map.sources[repoKey].commit}/${file}#L${a}${b && b !== a ? '-L' + b : ''}`;
const slug = (s) => s.replace(/[^A-Za-z0-9_.:-]/g, '-');
const leanIndexKey = (info) => info.repo + ':' + (info.module_only ? 'file:' + info.file
  : info.exported === false ? 'private:' + info.file + ':' + info.name : 'decl:' + info.file + ':' + info.name);
const leanMacroKey = (command, file, line, name) => [command, file, line, name].join('\0');
const escapedCommand = (source, index) => {
  let slashes = 0;
  for (let i = index - 1; i >= 0 && source[i] === '\\'; i--) slashes++;
  return slashes % 2 === 1;
};

// ---------------------------------------------------------------- paper ----
const paperFile = map.sources.paper.file;
const texRaw = gitShow('paper', paperFile) ?? '';
let currentPaperRaw;
try { currentPaperRaw = fs.readFileSync(path.join(dirs.paper, paperFile), 'utf8'); }
catch { currentPaperRaw = texRaw; }
const texLines = texRaw.split('\n');
const cleanTexRaw = stripComments(texRaw);
const cleanTexLines = cleanTexRaw.split('\n');
const cleanLineOffsets = [0];
for (const l of cleanTexLines) cleanLineOffsets.push(cleanLineOffsets[cleanLineOffsets.length - 1] + l.length + 1);

const macros = { '\\cots': '\\cdots', '\\dd': '\\mathrm{d}', '\\sm': '\\mathrm{sm}', '\\Weyl': 'A_n', '\\Kbar': '\\overline{k}' };
for (const m of texRaw.matchAll(/\\newcommand\{(\\[A-Za-z]+)\}\{((?:[^{}]|\{[^{}]*\})*)\}/g)) if (!m[2].includes('#')) macros[m[1]] = m[2];
for (const m of texRaw.matchAll(/\\DeclareMathOperator\{(\\[A-Za-z]+)\}\{([^}]*)\}/g)) macros[m[1]] = `\\operatorname{${m[2]}}`;

function splitMathRows(body) {
  const rows = [];
  let start = 0, braces = 0, environments = 0;
  for (let i = 0; i < body.length; i++) {
    if (body[i] === '\\') {
      const env = /^\\(begin|end)\s*\{[^{}]+\}/.exec(body.slice(i));
      if (env) {
        environments += env[1] === 'begin' ? 1 : -1;
        i += env[0].length - 1;
      } else if (body[i + 1] === '\\') {
        if (braces === 0 && environments === 0) {
          rows.push(body.slice(start, i));
          i++;
          start = i + 1;
        } else i++;
      } else if (/[A-Za-z]/.test(body[i + 1] ?? '')) {
        while (/[A-Za-z]/.test(body[i + 1] ?? '')) i++;
      } else i++;
    } else if (body[i] === '{') braces++;
    else if (body[i] === '}') braces = Math.max(0, braces - 1);
  }
  rows.push(body.slice(start));
  return rows;
}

// Match the document's equation counter, including section resets and rows
// suppressed by \notag/\nonumber. Offsets are into the comment-stripped TeX,
// matching the renderer's absolute source offsets.
const eqAuto = new Map();
const refs = {};
const leanMacroRefs = new Map();
{
  const noComments = cleanTexRaw;
  const sectionNumbered = /\\numberwithin\s*\{\s*equation\s*\}\s*\{\s*section\s*\}/.test(noComments);
  const mathEnvs = new Set(['equation', 'align', 'gather', 'multline']);
  const envStack = [], mathRanges = [];
  for (const m of noComments.matchAll(/\\(begin|end)\s*\{([^{}]+)\}/g)) {
    if (escapedCommand(noComments, m.index)) continue;
    if (m[1] === 'begin') envStack.push({ name: m[2], start: m.index, bodyStart: m.index + m[0].length });
    else {
      let k = envStack.length - 1;
      while (k >= 0 && envStack[k].name !== m[2]) k--;
      if (k < 0) continue;
      const opened = envStack[k];
      envStack.length = k;
      const baseName = opened.name.replace(/\*$/, '');
      if (mathEnvs.has(baseName)) mathRanges.push({ ...opened, end: m.index, name: opened.name });
    }
  }
  const events = mathRanges.map((range) => ({ type: 'math', at: range.start, range }));
  for (const m of noComments.matchAll(/\\appendix\b|\\section(\*)?(?![A-Za-z])/g)) {
    if (escapedCommand(noComments, m.index)) continue;
    events.push({ type: m[0] === '\\appendix' ? 'appendix' : 'section', starred: Boolean(m[1]), at: m.index });
  }
  events.sort((a, b) => a.at - b.at);

  let counter = 0, section = 0, appendix = false;
  const currentSection = () => appendix
    ? String.fromCharCode(64 + section)
    : String(section);
  const nextEquationTag = () => {
    counter++;
    return sectionNumbered ? `${currentSection()}.${counter}` : String(counter);
  };

  for (const event of events) {
    if (event.type === 'appendix') { appendix = true; section = 0; counter = 0; continue; }
    if (event.type === 'section') {
      if (!event.starred) { section++; counter = 0; }
      continue;
    }
    const { range } = event;
    const body = noComments.slice(range.bodyStart, range.end);
    const starred = range.name.endsWith('*');
    const rows = splitMathRows(body);
    let renderedTag = null;
    for (const row of rows) {
      const explicitMatch = [...row.matchAll(/\\tag\*?\s*\{([^}]*)\}/g)].find((m) => !escapedCommand(row, m.index));
      const explicit = explicitMatch?.[1] ?? null;
      const suppressed = [...row.matchAll(/\\(?:notag|nonumber)\b/g)].some((m) => !escapedCommand(row, m.index));
      let tag = explicit;
      if (!starred && !suppressed) {
        const automatic = nextEquationTag();
        if (explicit === null) tag = automatic;
      }
      if (tag) renderedTag = tag;
      for (const label of row.matchAll(/\\label\s*\{([^}]*)\}/g)) {
        if (escapedCommand(row, label.index)) continue;
        const fallback = sectionNumbered && counter > 0 ? `${currentSection()}.${counter}` : String(counter);
        refs[label[1]] = { text: tag ?? fallback };
      }
    }
    if (renderedTag) eqAuto.set(range.start, renderedTag);
  }
}
const lineOfLabel = {};
texLines.forEach((line, i) => { for (const m of stripComments(line).matchAll(/\\label\{([^}]*)\}/g)) lineOfLabel[m[1]] = i + 1; });

const items = map.items;
// The rendered sequence follows the manuscript section order, then the order
// of entries within each section. Use the same order for guided navigation.
const guidedItems = map.sections.flatMap((sec) => items.filter((it) => it.section === sec.number));
const itemById = Object.fromEntries(items.map((it) => [it.id, it]));

// Require every theorem-like environment declared with \newtheorem to be
// represented in the correspondence map. Labels anchor labelled statements;
// for unlabelled ones, one item range must cover the whole environment.
function checkStatementCoverage(sourceText) {
  const source = stripComments(sourceText);
  const types = new Set([...source.matchAll(/\\newtheorem\s*\{([^{}]+)\}/g)].map((m) => m[1].trim()));
  if (!types.size) return;
  const stack = [], statements = [];
  const token = /\\(begin|end)\s*\{([^{}]+)\}|\\label\s*\{([^{}]+)\}/g;
  for (let m; (m = token.exec(source));) {
    if (escapedCommand(source, m.index)) continue;
    if (m[3] !== undefined) {
      const open = stack.at(-1);
      if (open && types.has(open.name)) open.labels.push(m[3].trim());
      continue;
    }
    if (m[1] === 'begin') stack.push({ name: m[2], start: m.index, labels: [] });
    else {
      let k = stack.length - 1;
      while (k >= 0 && stack[k].name !== m[2]) k--;
      if (k < 0) continue;
      const open = stack[k];
      stack.length = k;
      if (types.has(open.name)) {
        statements.push({ env: open.name, start: open.start, end: m.index + m[0].length, label: open.labels[0] ?? null });
      }
    }
  }
  const lineAt = (offset) => source.slice(0, offset).split('\n').length;
  const itemLabels = new Map(items.filter((it) => it.label).map((it) => [it.label, it]));
  for (const statement of statements) {
    const startLine = lineAt(statement.start), endLine = lineAt(statement.end);
    if (statement.label) {
      if (!itemLabels.has(statement.label)) {
        errors.push(`Statement coverage: labelled ${statement.env} ${statement.label} at ${paperFile}:${startLine}-${endLine} is absent from map.items`);
      }
    } else if (!items.some((it) => it.tex_lines && it.tex_lines[0] <= startLine && it.tex_lines[1] >= endLine)) {
      errors.push(`Statement coverage: unlabelled ${statement.env} at ${paperFile}:${startLine}-${endLine} is not covered by any item tex_lines range`);
    }
  }
}
checkStatementCoverage(currentPaperRaw);
function checkAnnotationIds(source, revision) {
  const clean = stripComments(source);
  const seen = new Map();
  for (const match of clean.matchAll(/\\AIcomment\s*\{/g)) {
    if (escapedCommand(clean, match.index)) continue;
    const [rawId] = readGroup(clean, match.index + match[0].length - 1);
    const id = rawId.trim();
    if (!id || /#\d/.test(id)) continue;
    const line = clean.slice(0, match.index).split('\n').length;
    if (seen.has(id)) {
      errors.push(`Duplicate AIcomment ID '${id}' in ${revision} manuscript at ${paperFile}:${line}; first at line ${seen.get(id)}`);
    } else seen.set(id, line);
  }
}
checkAnnotationIds(texRaw, 'pinned');
checkAnnotationIds(currentPaperRaw, 'current');

for (const it of items) {
  if (it.label) refs[it.label] = { text: it.number ?? it.label, href: `#item-${slug(it.id)}` };
}
for (const [label, text] of Object.entries(map.extra_refs ?? {})) refs[label] = { text };
for (const sec of map.sections) if (sec.label) refs[sec.label] = { text: sec.number, href: `#sec-${sec.number}` };
// Equation references link to the card whose excerpt contains the equation.
for (const [label, line] of Object.entries(lineOfLabel)) {
  if (!refs[label] || refs[label].href) continue;
  const owner = items.find((it) => it.tex_lines && line >= it.tex_lines[0] && line <= it.tex_lines[1]);
  if (owner) refs[label].href = `#item-${slug(owner.id)}`;
}

const cites = {};
const bibliographyFile = map.sources.paper.bib_file
  ?? path.posix.join(path.posix.dirname(paperFile), 'references.bib');
const bib = gitShow('paper', bibliographyFile) ?? '';
for (const m of bib.matchAll(/@\w+\{([^,]+),[\s\S]*?\n\}/g)) {
  const entry = m[0];
  const author = /author\s*=\s*[{"]([^}"]+)/i.exec(entry)?.[1] ?? m[1];
  const year = /year\s*=\s*[{"]?(\d{4})/i.exec(entry)?.[1] ?? '';
  const surname = author.split(/\s+and\s+/)[0].split(',')[0].trim().split(/\s+/).pop().replace(/[{}\\'"`^]/g, '');
  cites[m[1].trim()] = `${surname}${year ? ' ' + year : ''}`;
}

const tex = new TexRenderer({ macros, refs, cites, eqAuto, leanRefs: leanMacroRefs });
const markupSpans = [];
for (const match of cleanTexRaw.matchAll(/\\(AIadd|AIremove|AIreplace|AIcomment|formalref)\b/g)) {
  if (escapedCommand(cleanTexRaw, match.index)) continue;
  let end = match.index + match[0].length, complete = true;
  const arguments_ = [];
  const count = ['AIreplace', 'AIcomment'].includes(match[1]) ? 2 : 1;
  for (let n = 0; n < count; n++) {
    while (/\s/.test(cleanTexRaw[end] ?? '') && end < cleanTexRaw.length) end++;
    if (cleanTexRaw[end] !== '{') { complete = false; break; }
    const argumentStart = end + 1;
    [, end] = readGroup(cleanTexRaw, end);
    arguments_.push({ start: argumentStart, end: end - 1 });
  }
  if (complete) markupSpans.push({ start: match.index, end, command: match[1], arguments: arguments_ });
}
function excerpt(range) {
  const [a, b] = range;
  const start = cleanLineOffsets[a - 1], end = cleanLineOffsets[b];
  let prefix = '', suffix = '', contextNote = '';
  for (const span of markupSpans) {
    if ((span.start < start && start < span.end) || (span.start < end && end < span.end)) {
      const replacement = span.command === 'AIreplace' ? span.arguments[1] : null;
      if (replacement && replacement.start <= start && start < replacement.end && end > start && !prefix) {
        // Consequence cards deliberately quote part of a proposed replacement.
        // Inherit its addition style; keep the original on the parent card.
        prefix = '\\AIadd{';
        if (end <= replacement.end) suffix = '}';
        contextNote = '<p class="muted">Excerpt from a proposed replacement; the parent passage retains the original text.</p>';
        continue;
      }
      errors.push(`Excerpt ${a}-${b} cuts through \\${span.command}; include the complete markup command in tex_lines`);
    }
  }
  const src = cleanTexLines.slice(a - 1, b).join('\n');
  return contextNote + tex.block(prefix + src + suffix, cleanLineOffsets[a - 1] - prefix.length);
}

// ------------------------------------------------------------------ lean ----
const fileCache = new Map();
const leanIndex = new Map(); // repository-qualified declaration/file -> {source info, users}
function resolveLean(ref, userId) {
  const repoKey = ref.repo ?? 'formal';
  const key = `${repoKey}:${ref.file}`;
  if (!fileCache.has(key)) fileCache.set(key, gitShow(repoKey, ref.file));
  const text = fileCache.get(key);
  let info = { ...ref, repo: repoKey, ok: false };
  if (text == null) return info;
  if (ref.module_only) {
    info.ok = true;
    info.url = ghBlob(repoKey, ref.file, 1);
    info.statement = null;
  } else {
    const found = findDeclaration(text, ref.name, ref.line);
    if (!found) {
      errors.push(`Lean: ${ref.name} not found in ${repoKey}:${ref.file} (${userId})`);
      return info;
    }
    if (!found.exact) errors.push(`Lean: ${ref.name} resolves as ${found.qualified} in ${ref.file}:${found.line} (${userId})`);
    const explicitlyInternal = ref.visibility === 'module-private' && found.exported === false
      && ['main-proof', 'helper', 'verification provenance'].includes(ref.role);
    if (found.exported === false && !explicitlyInternal) {
      errors.push('Lean: ' + ref.name + ' is ' + found.visibility + '; add visibility:module-private only for a local proof/helper link, not a public FQN claim (' + userId + ')');
    }
    if (ref.line && ref.line !== found.line) warnings.push(`Lean: ${ref.name} is at line ${found.line}, map says ${ref.line}`);
    const st = extractStatement(found.lines, found.line, 160, ['def', 'abbrev', 'structure', 'class', 'inductive'].includes(found.keyword));
    const context = declarationContext(found.lines, found.line).map((entry) => ({ ...entry, url: ghBlob(repoKey, ref.file, entry.startLine, entry.endLine) }));
    info = { ...info, ok: found.exact && (found.exported !== false || explicitlyInternal), exported: found.exported,
      private: found.exported === false,
      visibility: found.visibility, line: found.line, qualified: found.qualified, keyword: found.keyword,
      statement: st.text, truncated: st.truncated,
      resultType: ['theorem', 'lemma'].includes(found.keyword) ? namedResultType(found.lines, found.line) : null,
      context,
      bindings: [...new Set([...bindingNames(st.text), ...context.filter((entry) => /^\s*variable\b/.test(entry.text)).flatMap((entry) => bindingNames(entry.text))])],
      trust: declarationTrust(found.lines, found.line, found.keyword),
      stLines: [st.startLine, st.endLine], url: ghBlob(repoKey, ref.file, st.startLine, st.endLine) };
  }
  info.sourceHash = crypto.createHash('sha256').update(text).digest('hex');
  info.sourceCommit = map.sources[repoKey].commit;
  const idx = leanIndexKey(info);
  if (!leanIndex.has(idx)) leanIndex.set(idx, { info, users: new Map() });
  leanIndex.get(idx).users.set(userId, ref.role ?? '');
  return info;
}

// Index definitions in the already mapped, pinned files. Never guess by a
// short-name match: resolve through enclosing namespaces, or explicit expands.
let definitionCatalog;
function statementDefinitions(info, userId) {
  if (info.resultType && info.bindings?.includes(info.resultType.split('.')[0])) return { definitions: [], unavailable: null };
  if (!definitionCatalog) {
    definitionCatalog = new Map();
    const indexedFiles = new Set();
    const refs = [...items.flatMap((it) => [...(it.lean ?? []), ...(it.steps ?? []).flatMap((st) => st.lean ?? [])]), ...(map.lean_only ?? []).flatMap((it) => it.lean ?? [])];
    for (const ref of refs.flatMap((ref) => [ref, ...(ref.expands ?? [])])) {
      const repo = ref.repo ?? 'formal', key = `${repo}:${ref.file}`;
      if (indexedFiles.has(key)) continue;
      indexedFiles.add(key);
      if (!fileCache.has(key)) fileCache.set(key, gitShow(repo, ref.file));
      const source = fileCache.get(key);
      if (source == null) continue;
      for (const decl of definitionNames(source)) {
        const name = `${repo}:${decl.name}`;
        if (!definitionCatalog.has(name)) definitionCatalog.set(name, []);
        definitionCatalog.get(name).push({ ...decl, repo, file: ref.file });
      }
    }
  }
  const explicit = (info.expands ?? []).map((ref) => resolveLean({ ...ref, repo: ref.repo ?? info.repo }, userId));
  if (!info.resultType || explicit.length) return { definitions: explicit, unavailable: null };
  const ns = info.name.split('.').slice(0, -1);
  const lookup = (name) => {
    const candidates = definitionCatalog.get(`${info.repo}:${name}`) ?? [];
    const local = candidates.filter((ref) => ref.file === info.file);
    return local.length === 1 ? local[0] : candidates.length === 1 ? candidates[0] : null;
  };
  for (let n = ns.length; n >= 0; n--) {
    const name = [...ns.slice(0, n), info.resultType].join('.');
    const ref = lookup(name);
    if (ref) return { definitions: [resolveLean(ref, userId)], unavailable: null };
    if (definitionCatalog.has(`${info.repo}:${name}`)) return { definitions: [], unavailable: info.resultType };
  }
  const opened = new Map();
  let ambiguousOpen = false;
  for (const entry of info.context ?? []) {
    const match = /^\s*open\s+([A-Za-z_][A-Za-z0-9_'.\s]*?)\s*$/.exec(entry.text);
    if (!match || match[1].startsWith('scoped ') || /\b(?:hiding|renaming|in)\b/.test(match[1])) continue;
    for (const name of match[1].trim().split(/\s+/)) {
      for (let n = ns.length; n >= 0; n--) {
        const qualified = [...ns.slice(0, n), name, info.resultType].join('.');
        const ref = lookup(qualified);
        if (ref) { opened.set(qualified, ref); break; }
        if (definitionCatalog.has(`${info.repo}:${qualified}`)) { ambiguousOpen = true; break; }
      }
    }
  }
  if (!ambiguousOpen && opened.size === 1) return { definitions: [resolveLean([...opened.values()][0], userId)], unavailable: null };
  // Built-in logical/type constructors are already legible in the signature.
  return { definitions: [], unavailable: /^[A-Z]/.test(info.resultType) && !['True', 'False', 'Nonempty', 'Exists', 'And', 'Or', 'Iff', 'Eq'].includes(info.resultType) ? info.resultType : null };
}

// The mapping intentionally pins an older, reviewable paper snapshot. Also
// audit links in the manuscript currently present in the paper checkout so a
// new or edited \leandecl/\leanlib cannot silently escape --check merely
// because it has not yet been added to the frozen item map.
function checkManuscriptLinks(rawSource, revisionLabel) {
  const source = stripComments(rawSource);
  const re = /\\(leandecl|leanlib)\b/g;
  const readCompleteGroup = (text, start) => {
    if (text[start] !== '{') return [null, start, false];
    let depth = 0;
    for (let i = start; i < text.length; i++) {
      if (text[i] === '\\') { i++; continue; }
      if (text[i] === '{') depth++;
      else if (text[i] === '}' && --depth === 0) return [text.slice(start + 1, i), i + 1, true];
    }
    return [text.slice(start + 1), text.length, false];
  };
  for (let m; (m = re.exec(source));) {
    if (escapedCommand(source, m.index)) continue;
    const line = source.slice(0, m.index).split('\n').length;
    let pos = m.index + m[0].length;
    const args = [];
    let malformed = false;
    for (let i = 0; i < 3; i++) {
      while (/[\t\n\r ]/.test(source[pos] ?? '')) pos++;
      if (source[pos] !== '{') break;
      const [arg, next, complete] = readCompleteGroup(source, pos);
      if (!complete) { malformed = true; break; }
      args.push(arg);
      pos = next;
    }
    if (malformed || args.length !== 3 || args.some((arg) => arg == null)) {
      errors.push(`Paper (${revisionLabel}): malformed \\${m[1]} reference at ${paperFile}:${line}`);
      continue;
    }
    const [file, lineText, name] = args.map((arg) => arg.trim());
    const sourceLine = Number(lineText);
    if (!file || !Number.isSafeInteger(sourceLine) || sourceLine < 1 || !name) {
      errors.push(`Paper (${revisionLabel}): invalid \\${m[1]} arguments at ${paperFile}:${line}`);
      continue;
    }
    const repoKey = m[1] === 'leanlib' ? 'library' : 'formal';
    const key = `${repoKey}:${file}`;
    if (!fileCache.has(key)) fileCache.set(key, gitShow(repoKey, file));
    const leanSource = fileCache.get(key);
    if (leanSource == null) continue; // gitShow already recorded the failure.
    const found = findDeclaration(leanSource, name, sourceLine);
    if (!found) {
      errors.push(`Paper (${revisionLabel}): \\${m[1]} ${name} not found in ${repoKey}:${file} (reference at ${paperFile}:${line})`);
    } else if (!found.exact) {
      errors.push(`Paper (${revisionLabel}): \\${m[1]} ${name} resolves as ${found.qualified} in ${file}:${found.line} (reference at ${paperFile}:${line})`);
    } else if (found.exported === false) {
      errors.push('Paper (' + revisionLabel + '): \\' + m[1] + ' ' + name + ' is ' + found.visibility + ' and is not exported from ' + file + ' (reference at ' + paperFile + ':' + line + ')');
    } else if (found.line !== sourceLine) {
      errors.push(`Paper (${revisionLabel}): \\${m[1]} ${name} points to ${file}:${sourceLine}, declaration is at line ${found.line} (reference at ${paperFile}:${line})`);
    } else {
      leanMacroRefs.set(leanMacroKey(m[1], file, sourceLine, name), ghBlob(repoKey, file, found.line));
    }
  }
}
checkManuscriptLinks(currentPaperRaw, 'current');
if (currentPaperRaw !== texRaw) checkManuscriptLinks(texRaw, 'pinned');

// ------------------------------------------------------------ validation ----
for (const it of items) {
  if (it.tex_lines) {
    const [a, b] = it.tex_lines;
    if (!(a >= 1 && b >= a && b <= texLines.length)) errors.push(`tex range ${a}-${b} invalid for ${it.id}`);
    if (it.label && !(lineOfLabel[it.label] >= a && lineOfLabel[it.label] <= b)) errors.push(`label ${it.label} is not inside ${it.id} range ${a}-${b} (found at ${lineOfLabel[it.label]})`);
    if (it.anchor_text && !texLines.slice(a - 1, b).join('\n').includes(it.anchor_text)) errors.push(`anchor text for ${it.id} not found in its range`);
  }
  for (const dep of it.depends_on ?? []) if (!itemById[dep]) errors.push(`${it.id} depends on unknown ${dep}`);
}

// ------------------------------------------------------------- rendering ----
const REL = map.vocab.statement_relation;
const ROUTE = map.vocab.route_relation;
const SEV = map.vocab.severity;
const badge = (vocab, key, prefix) => {
  const v = vocab[key];
  if (!v) { errors.push(`unknown ${prefix} value "${key}"`); return `<span class="badge">${escapeHtml(key ?? '?')}</span>`; }
  return `<span class="badge b-${v.color}" title="${escapeHtml(v.meaning)}">${escapeHtml(prefix)}: ${escapeHtml(v.label)}</span>`;
};

function mdInline(t) { return md(t).replace(/^<p>|<\/p>$/g, ''); }
function md(s) {
  // Tiny markdown: paragraphs, "- " bullets, **bold**, `code`, [text](url), $math$.
  const inline = (t) => {
    const parts = t.split(/(\$[^$]+\$)/g);
    return parts.map((p) => {
      if (/^\$[^$]+\$$/.test(p)) return tex.math(p.slice(1, -1), false);
      return escapeHtml(p)
        .replace(/`([^`]+)`/g, '<code>$1</code>')
        .replace(/\*\*([^*]+)\*\*/g, '<b>$1</b>')
        .replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2">$1</a>');
    }).join('');
  };
  const blocks = String(s ?? '').split(/\n\s*\n/);
  return blocks.map((blk) => {
    const lines = blk.split('\n');
    if (lines.every((l) => /^\s*- /.test(l) || /^\s{2,}\S/.test(l))) {
      const bullets = [];
      for (const l of lines) { if (/^\s*- /.test(l)) bullets.push(l.replace(/^\s*- /, '')); else bullets[bullets.length - 1] += ' ' + l.trim(); }
      return '<ul>' + bullets.map((b) => `<li>${inline(b)}</li>`).join('') + '</ul>';
    }
    return `<p>${inline(blk.replace(/\n/g, ' '))}</p>`;
  }).join('');
}

// Explicitly curated symbol links: no short-name guessing across namespaces.
const definitionRefs = map.challenge_definitions ?? [];
const definitionAnchor = (ref) => `definition-${slug((ref.repo ?? 'formal') + ':' + ref.name)}`;
function symbolLink(info, token) {
  // The lexer keeps the trailing dot in `name.{u}` as part of the identifier
  // token. It is universe-application syntax, so match the declaration name
  // without the dot while keeping the rendered token intact.
  const lookup = token.replace(/\.$/, '');
  const exactLink = (refs) => refs.length === 1 ? '#' + definitionAnchor(refs[0]) : null;

  // Lean resolves an unqualified identifier from the innermost namespace
  // outward before considering a root-level declaration. A short-name match
  // in some unrelated namespace is not enough evidence for a link.
  if (!lookup.includes('.')) {
    const parts = (info.name ?? '').split('.');
    parts.pop(); // The final component is the declaration being rendered.
    for (let n = parts.length; n > 0; n--) {
      const candidate = parts.slice(0, n).concat(lookup).join('.');
      const local = definitionRefs.filter((ref) => ref.name === candidate);
      if (local.length) return exactLink(local);
    }
  }

  // Explicitly qualified references, and unqualified root names such as
  // Mathlib's Field, resolve only when exactly one curated owner has that
  // exact name. Do not guess among namespaced suffix matches.
  return exactLink(definitionRefs.filter((ref) => ref.name === lookup));
}
function leanBlock(info, role) {
  if (!info.url) return `<div class="lean missing">✗ ${escapeHtml(info.name ?? info.file)} — not resolved</div>`;
  const repoTag = ({ library: 'AlgebraicAnalysis', global: 'GlobalStafford', mathlib: 'Mathlib' })[info.repo] ?? map.sources[info.repo]?.repo ?? info.repo;
  const anchor = `lean-${slug(leanIndexKey(info))}`;
  const head = info.module_only
    ? `<a class="lean-name" href="${info.url}">${escapeHtml(info.file)}</a> <span class="muted">(module)</span>`
    : `<a class="lean-name" href="${info.url}">${escapeHtml(info.name)}</a>`;
  return `<div class="lean">
    <div class="lean-head">${role ? `<span class="role">${escapeHtml(role)}</span>` : ''}${head}${info.private ? ' <span class="muted">(module-private; not an exported FQN)</span>' : ''}
      <span class="muted"> · ${repoTag} @ ${escapeHtml(info.sourceCommit?.slice(0, 7) ?? '')} · ${escapeHtml(info.file)}:${info.line ?? 1}</span>
      <a class="xref" href="#${anchor}" title="All paper items using this declaration">⇄</a></div>
    ${info.statement ? `<pre class="lean-src">${highlightLean(info.statement, (token) => symbolLink(info, token))}</pre>` : ''}
    ${info.trust === 'placeholder' ? '<p class="err">Unproved challenge/template: this declaration contains sorry/admit. Its signature specifies a target; it is not evidence of a proved theorem.</p>' : info.trust === 'axiom' ? '<p class="err">Axiom declaration: this is an assumption, not a proved theorem.</p>' : ''}
    ${info.context?.length ? `<details class="lean-context"><summary>Ambient source declarations</summary><p class="muted">Available local context, not a list of extra hypotheses. Lean determines parameters from the signature, proof and include/omit directives. Imports and other instances are in the linked full module.</p>${info.context.map((entry) => `<a href="${entry.url}" class="muted">${escapeHtml(info.file)}:${entry.startLine}–${entry.endLine}</a><pre class="lean-src">${highlightLean(entry.text)}</pre>`).join('')}</details>` : ''}
    ${info.truncated ? '<p class="lean-note">Excerpt truncated; follow the pinned source link for the complete declaration.</p>' : ''}
    ${info.note ? `<div class="lean-note">${md(info.note)}</div>` : ''}
  </div>`;
}

function issueBlock(iss, ownerId) {
  const sev = SEV[iss.severity] ?? { label: iss.severity, color: 'grey' };
  return `<li class="issue sev-${escapeHtml(iss.severity)}" id="issue-${slug(iss.id)}">
    <span class="badge b-${sev.color}">${escapeHtml(sev.label)}</span> <b>${escapeHtml(iss.id)}</b>
    ${iss.status ? `<span class="muted">${escapeHtml(iss.status)}</span> ` : ''}${iss.aicomment ? `<span class="aic">AIcomment ${escapeHtml(iss.aicomment)}${iss.aicomment_verdict ? ' — ' + escapeHtml(iss.aicomment_verdict) : ''}</span>` : '<span class="aic new">not covered by an AIcomment</span>'}
    <div>${md(iss.summary)}</div>
    ${iss.fix ? `<div class="fix"><b>Suggested fix.</b> ${md(iss.fix)}</div>` : ''}
    ${iss.lean_help ? `<div class="fix"><b>How Lean handles it.</b> ${md(iss.lean_help)}</div>` : ''}
  </li>`;
}

const reviewChecks = map.review_checks;
const sha = (s) => crypto.createHash('sha256').update(s).digest('hex').slice(0, 16);
const generatorHash = sha(['build.mjs', 'lean.mjs', 'texhtml.mjs', 'review.js', 'review-scope.mjs', 'style.css', 'package.json', 'package-lock.json']
  .map((file) => fs.readFileSync(path.join(here, file), 'utf8')).join('\0'));

// Committed review records (exported from the HTML, one file per reviewer and pass).
const recorded = {}; // item id -> [{reviewer, date, hash, notes, complete, file}]
if (fs.existsSync(reviewsDir)) {
  for (const f of fs.readdirSync(reviewsDir).filter((x) => x.endsWith('.json')).sort()) {
    let data;
    try { data = JSON.parse(fs.readFileSync(path.join(reviewsDir, f), 'utf8')); } catch (e) { errors.push(`review ${f}: invalid JSON`); continue; }
    if (data.format !== 'stafford38-paper-lean-review/1') { errors.push(`review ${f}: unknown format`); continue; }
    for (const [id, r] of Object.entries(data.items ?? {})) {
      if (!itemById[id]) { warnings.push(`review ${f}: unknown item ${id}`); continue; }
      if (!r || typeof r !== 'object' || Array.isArray(r)) { errors.push(`review ${f}: invalid item record ${id}`); continue; }
      const complete = reviewChecks.every((c) => r.checks?.[c.id] === true);
      (recorded[id] ??= []).push({ reviewer: r.reviewer || data.reviewer || 'anonymous', date: String(r.updated ?? data.exported ?? '').slice(0, 10), hash: r.hash, notes: r.notes, complete, file: f });
    }
  }
}
function recordedBlock(id, hash) {
  const recs = recorded[id] ?? [];
  if (!recs.length) return '';
  return `<div class="recorded"><b>Recorded reviews:</b> ${recs.map((r) => {
    const state = r.hash !== hash ? '<span class="stale-tag">stale</span>' : r.complete ? '<span class="ok-tag">signed off</span>' : '<span class="muted">partial</span>';
    return `${escapeHtml(r.reviewer)} (${escapeHtml(r.date)}, ${state})${r.notes ? ` — ${escapeHtml(r.notes)}` : ''}`;
  }).join('; ')}</div>`;
}
function reviewBlock(it, hash) {
  return `<div class="review" data-item="${escapeHtml(it.id)}" data-hash="${hash}">
    <div class="stale-note">Earlier sign-off was made against different paper text or Lean statements; re-check.</div>
    <div class="review-title">Human review</div>
    ${reviewChecks.map((c) => `<label><input type="checkbox" data-check="${c.id}"> ${escapeHtml(c.label)}</label>`).join('')}
    <textarea placeholder="Reviewer notes" data-notes></textarea>
    <div class="print-only signoff">Reviewer: ______________________ &nbsp; Date: ____________ &nbsp; Verdict: ☐ agree ☐ disagree ☐ needs change</div>
  </div>`;
}

function card(it) {
  const guidedIndex = guidedItems.findIndex((entry) => entry.id === it.id);
  const previous = guidedItems[guidedIndex - 1];
  const next = guidedItems[guidedIndex + 1];
  const leanInfos = (it.lean ?? []).map((ref) => [resolveLean(ref, it.id), ref.role]);
  const stepInfos = (it.steps ?? []).map((st) => (st.lean ?? []).map((ref) => [resolveLean(ref, it.id), ref.role]));
  const allLeanInfos = [...leanInfos, ...stepInfos.flat()];
  const expansions = allLeanInfos.map(([info]) => ({ info, ...statementDefinitions(info, it.id) }));
  const shownNames = new Set(leanInfos.map(([info]) => leanIndexKey(info)));
  const definitions = expansions.flatMap((entry) => entry.definitions).filter((info) => {
    const key = leanIndexKey(info);
    if (shownNames.has(key)) return false;
    shownNames.add(key); return true;
  });
  const theoremInfos = allLeanInfos.filter(([info]) => ['theorem', 'lemma'].includes(info.keyword));
  const primary = leanInfos.filter(([, role]) => role !== 'helper');
  const coverage = it.lean_explanation ?? (!allLeanInfos.length
    ? 'No Lean declaration is mapped to this passage; the paper text is not certified by this card.'
    : allLeanInfos.every(([info]) => info.module_only)
      ? 'Source/documentation links only: no theorem signature is mapped to this passage.'
    : primary.some(([info]) => ['placeholder', 'axiom'].includes(info.trust)) && !primary.some(([info]) => ['theorem', 'lemma'].includes(info.keyword) && info.trust === 'source declaration')
      ? 'Target specification or assumption only: the mapped declaration does not provide a proved theorem here.'
    : !theoremInfos.length
      ? 'Definitions and notation only: this card does not display a proved theorem for the passage.'
      : !primary.some(([info]) => ['theorem', 'lemma'].includes(info.keyword))
        ? 'The main display gives statement definitions; the proved results are shown under supporting declarations or proof steps below.'
        : 'The theorem signatures below state the mapped results. Named statement definitions are displayed separately when available; proof bodies are linked in the pinned source.');
  const stepRows = (it.steps ?? []).map((st, k) => {
    const infos = stepInfos[k];
    return `<tr><td class="step-n">${k + 1}</td><td><b>${escapeHtml(st.title)}</b>${st.tex_lines ? ` <span class="muted">tex ${st.tex_lines[0]}–${st.tex_lines[1]}</span>` : ''}
      ${st.relation ? badge(ROUTE, st.relation, 'route') : ''}<div>${md(st.note)}</div></td>
      <td>${infos.map(([info]) => info.url ? `<a href="${info.url}">${escapeHtml(info.module_only ? info.file : info.name)}</a>${info.private ? ' <span class="muted">(module-private; not an exported FQN)</span>' : ''}` : `<span class="err">${escapeHtml(info.name)}</span>`).join('<br>') || '<span class="muted">—</span>'}</td></tr>`;
  }).join('');
  const deps = (it.depends_on ?? []).map((d) => `<a href="#item-${slug(d)}">${escapeHtml(itemById[d]?.short ?? d)}</a>`).join(', ');
  const usedBy = items.filter((o) => (o.depends_on ?? []).includes(it.id)).map((o) => `<a href="#item-${slug(o.id)}">${escapeHtml(o.short ?? o.id)}</a>`).join(', ');
  const texLink = it.tex_lines ? `https://github.com/${map.sources.paper.repo}/blob/${map.sources.paper.commit}/${paperFile}#L${it.tex_lines[0]}-L${it.tex_lines[1]}` : null;
  const maxSev = (it.issues ?? []).reduce((acc, iss) => Math.max(acc, SEV[iss.severity]?.rank ?? 0), 0);
  const guidedNav = `<nav class="guided-claim-nav" aria-label="Paper-order claim navigation">
    ${previous ? `<a rel="prev" data-guided-visit="${escapeHtml(previous.id)}" href="#item-${slug(previous.id)}">← Previous claim</a>` : '<span class="guided-disabled" aria-disabled="true">First claim</span>'}
    <span class="guided-position">Paper-order claim ${guidedIndex + 1} of ${guidedItems.length}</span>
    ${next ? `<a rel="next" data-guided-visit="${escapeHtml(next.id)}" href="#item-${slug(next.id)}">Next claim →</a>` : '<span class="guided-disabled" aria-disabled="true">Last claim</span>'}
  </nav>`;
  return `<section class="card" id="item-${slug(it.id)}" data-rel="${escapeHtml(it.statement_relation)}" data-route="${escapeHtml(it.route_relation)}" data-sev="${maxSev}" data-review-scope="${escapeHtml(it.review_scope ?? 'publication')}">
  <header class="card-head">
    <h3>${escapeHtml(it.kind ?? '')} ${escapeHtml(it.number ?? '')}${it.title ? ' — ' + mdInline(it.title) : ''}</h3>
    <div class="meta">
      ${it.label ? `<code>${escapeHtml(it.label)}</code> · ` : ''}${it.pdf_page ? `PDF p.&nbsp;${it.pdf_page} · ` : ''}${texLink ? `<a href="${texLink}">tex ${it.tex_lines[0]}–${it.tex_lines[1]}</a>` : ''}
    </div>
    <div class="badges">${badge(REL, it.statement_relation, 'statement')} ${badge(ROUTE, it.route_relation, 'route')}
      ${(it.issues ?? []).length ? `<span class="badge b-${SEV[Object.keys(SEV).find((k) => SEV[k].rank === maxSev)]?.color ?? 'grey'}">${it.issues.length} issue${it.issues.length > 1 ? 's' : ''}</span>` : ''}</div>
  </header>
  ${it.publication_proof ? `<div class="publication-target"><b>Proof correspondence.</b> ${md(it.publication_proof)}<span class="muted">Compare the whole printed proof, including its intermediate claims. A different checked route is a comparison aid, not approval of the printed argument.</span></div>` : ''}
  <div class="cols">
    <div class="col paper">
      <div class="col-title">Paper <span class="muted">(${escapeHtml(paperFile)} @ ${map.sources.paper.commit.slice(0, 7)})</span></div>
      <div class="tex">${it.tex_lines ? excerpt(it.publication_tex_lines ?? it.tex_lines) : '<p class="muted">No manuscript text (Lean-only step).</p>'}${it.publication_tex_lines ? `<details><summary>Full printed proof — included in correspondence review</summary>${excerpt(it.tex_lines)}</details>` : ''}</div>
    </div>
    <div class="col formal">
      <div class="col-title">Lean <span class="muted">(repository and pinned revision on each declaration)</span></div>
      <p class="lean-coverage">${escapeHtml(coverage)}</p>
      ${leanInfos.length ? leanInfos.filter(([, role]) => role !== 'helper').map(([info, role]) => leanBlock(info, role)).join('') : `<p class="none">${stepInfos.flat().length ? 'See the Lean declarations for the proof steps below.' : 'No Lean counterpart is mapped.'}</p>`}
      ${leanInfos.some(([, role]) => role === 'helper') ? `<details class="helpers"><summary>Supporting declarations (full signatures)</summary>${leanInfos.filter(([, role]) => role === 'helper').map(([info, role]) => leanBlock(info, role)).join('')}</details>` : ''}
      ${definitions.length ? `<div class="statement-definitions"><div class="col-title">Definitions used in theorem statements</div>${definitions.map((info) => leanBlock(info, 'statement definition')).join('')}</div>` : ''}
      ${expansions.filter((entry) => entry.unavailable).map((entry) => `<p class="lean-note">Named result <code>${escapeHtml(entry.unavailable)}</code> is not expanded here: its definition could not be resolved in the mapped files. Follow ${entry.info.url ? `<a href="${entry.info.url}">${escapeHtml(entry.info.name)}</a>` : escapeHtml(entry.info.name)} for its source and imports.</p>`).join('')}
    </div>
  </div>
  <div class="assess">
    ${it.correspondence ? `<div class="corr"><b>Statement correspondence.</b> ${md(it.correspondence)}</div>` : ''}
    ${it.route ? `<div class="corr"><b>Proof route.</b> ${md(it.route)}</div>` : ''}
    ${stepRows ? `<table class="steps"><thead><tr><th>#</th><th>Proof step</th><th>Lean</th></tr></thead><tbody>${stepRows}</tbody></table>` : ''}
    ${stepInfos.flat().length ? `<details class="step-statements"><summary>Lean declarations for the proof steps</summary>${stepInfos.flat().map(([info, role]) => leanBlock(info, role)).join('')}</details>` : ''}
    ${(it.issues ?? []).length ? `<div class="issues-title">Issues</div><ul class="issues">${it.issues.map((iss) => issueBlock(iss, it.id)).join('')}</ul>` : ''}
    <div class="deps">${deps ? `Uses: ${deps}` : ''}${deps && usedBy ? ' · ' : ''}${usedBy ? `Used by: ${usedBy}` : ''}</div>
  </div>
  ${(() => {
    const paperText = it.tex_lines ? texLines.slice(it.tex_lines[0] - 1, it.tex_lines[1]).join('\n') : '';
    const reviewBasis = [Object.fromEntries(Object.entries(map.sources).map(([key, source]) => [key, source.commit])),
      generatorHash, map.review_checks, map.vocab, definitionRefs, map.challenge_endpoints, it, paperText, allLeanInfos.map(([info, role]) => ({ ...info, role })), expansions];
    const h = sha(JSON.stringify(reviewBasis));
    it._hash = h;
    return recordedBlock(it.id, h) + reviewBlock(it, h);
  })()}
  ${guidedNav}
</section>`;
}

function depGraph() {
  const nodes = items.filter((it) => it.in_graph);
  const ids = new Set(nodes.map((n) => n.id));
  const depth = {};
  const visit = (id, stack = new Set()) => {
    if (depth[id] != null) return depth[id];
    if (stack.has(id)) { errors.push(`dependency cycle at ${id}`); return 0; }
    stack.add(id);
    const deps = (itemById[id].depends_on ?? []).filter((d) => ids.has(d));
    depth[id] = deps.length ? 1 + Math.max(...deps.map((d) => visit(d, stack))) : 0;
    stack.delete(id);
    return depth[id];
  };
  nodes.forEach((n) => visit(n.id));
  const layers = [];
  nodes.forEach((n) => (layers[depth[n.id]] ??= []).push(n));
  const W = 1000, nodeW = 150, nodeH = 44, gapY = 78;
  const pos = {};
  layers.forEach((layer, d) => {
    layer.sort((a, b) => (a.graph_order ?? 0) - (b.graph_order ?? 0));
    const step = W / (layer.length + 1);
    layer.forEach((n, k) => { pos[n.id] = { x: step * (k + 1), y: 30 + d * gapY }; });
  });
  const H = 30 + layers.length * gapY;
  const colorOf = (it) => REL[it.statement_relation]?.color ?? 'grey';
  let svg = `<svg class="graph" viewBox="0 0 ${W} ${H}" role="img" aria-label="Dependency graph"><defs><marker id="arr" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 z" class="arrow"/></marker></defs>`;
  for (const n of nodes) for (const d of (n.depends_on ?? []).filter((x) => ids.has(x))) {
    const a = pos[d], b = pos[n.id];
    svg += `<line class="edge" x1="${a.x}" y1="${a.y + nodeH / 2}" x2="${b.x}" y2="${b.y - nodeH / 2}" marker-end="url(#arr)"/>`;
  }
  for (const n of nodes) {
    const p = pos[n.id];
    const issues = (n.issues ?? []).length;
    svg += `<a href="#item-${slug(n.id)}"><rect class="node n-${colorOf(n)}" x="${p.x - nodeW / 2}" y="${p.y - nodeH / 2}" width="${nodeW}" height="${nodeH}" rx="7"/>
      <text x="${p.x}" y="${p.y - 4}" class="nt">${escapeHtml(n.short ?? n.id)}</text>
      <text x="${p.x}" y="${p.y + 12}" class="ns">${escapeHtml(n.graph_sub ?? '')}${issues ? ` · ${issues}⚑` : ''}</text></a>`;
  }
  return svg + '</svg>';
}

const challengeDefinitions = definitionRefs.map((ref) => {
  const info = resolveLean(ref, 'challenge-definitions');
  return `<details id="${definitionAnchor(ref)}" class="challenge-definition"><summary>${escapeHtml(ref.name)}${ref.note ? ' — ' + escapeHtml(ref.note) : ''}</summary>${leanBlock(info, 'definition')}</details>`;
}).join('');
const challengeEndpoints = (map.challenge_endpoints ?? []).map((ref) => leanBlock(resolveLean(ref, 'challenge-definitions'), 'proved challenge endpoint')).join('');
// Render cards first so the Lean index is populated.
const sectionHtml = map.sections.map((sec) => {
  const secItems = items.filter((it) => it.section === sec.number);
  return `<div class="paper-section" id="sec-${escapeHtml(sec.number)}"><h2>${escapeHtml(sec.number)}. ${escapeHtml(sec.title)}</h2>
    ${sec.note ? `<div class="sec-note">${md(sec.note)}</div>` : ''}
    ${secItems.map(card).join('\n')}</div>`;
}).join('\n');
for (const it of items) if (!map.sections.some((s) => s.number === it.section)) errors.push(`item ${it.id} has unknown section ${it.section}`);

const leanOnly = (map.lean_only ?? []).map((lo) => {
  const info = resolveLean(lo, 'lean-only');
  return `<tr><td>${info.url ? `<a href="${info.url}">${escapeHtml(lo.name ?? lo.file)}</a>` : `<span class="err">${escapeHtml(lo.name)}</span>`}<div class="muted">${escapeHtml(lo.file)}:${info.line ?? ''}</div></td><td>${md(lo.note)}</td><td>${(lo.related ?? []).map((r) => `<a href="#item-${slug(r)}">${escapeHtml(itemById[r]?.short ?? r)}</a>`).join(', ')}</td></tr>`;
}).join('');

const allIssues = [];
for (const it of items) for (const iss of it.issues ?? []) allIssues.push({ ...iss, owner: it });
for (const iss of map.global_issues ?? []) allIssues.push({ ...iss, owner: null });
allIssues.sort((a, b) => (SEV[b.severity]?.rank ?? 0) - (SEV[a.severity]?.rank ?? 0));
const issueTable = allIssues.map((iss) => `<tr class="sev-${escapeHtml(iss.severity)}"><td><span class="badge b-${SEV[iss.severity]?.color ?? 'grey'}">${escapeHtml(SEV[iss.severity]?.label ?? iss.severity)}</span></td>
  <td>${iss.owner ? `<a href="#issue-${slug(iss.id)}">${escapeHtml(iss.id)}</a>` : `<span id="issue-${slug(iss.id)}">${escapeHtml(iss.id)}</span>`}</td>
  <td>${iss.owner ? `<a href="#item-${slug(iss.owner.id)}">${escapeHtml(iss.owner.short ?? iss.owner.id)}</a>` : 'global'}</td>
  <td>${md(iss.summary)}${!iss.owner && iss.fix ? `<div class="fix"><b>Fix.</b> ${md(iss.fix)}</div>` : ''}</td><td>${escapeHtml(iss.aicomment ?? '—')}</td></tr>`).join('');

const leanIndexRows = [...leanIndex.entries()].sort((a, b) => (a[1].info.file + a[0]).localeCompare(b[1].info.file + b[0])).map(([key, { info, users }]) => {
  const anchor = `lean-${slug(key)}`;
  const u = [...users.entries()].map(([id, role]) => id === 'challenge-definitions' ? '<a href="#challenge-definitions">Challenge definitions</a>' : id === 'lean-only' ? '<a href="#lean-only">Lean-only register</a>' : `<a href="#item-${slug(id)}">${escapeHtml(itemById[id]?.short ?? id)}</a>${role ? ` <span class="muted">(${escapeHtml(role)})</span>` : ''}`).join(', ');
  return `<tr id="${anchor}"><td>${info.url ? `<a href="${info.url}">${escapeHtml(info.module_only ? info.file : info.name)}</a>${info.private ? ' <span class="muted">(module-private; not an exported FQN)</span>' : ''}` : escapeHtml(info.name ?? info.file)}</td><td class="muted">${escapeHtml(({ library: 'AA', global: 'GlobalStafford' })[info.repo] ?? 'S38')} ${escapeHtml(info.file)}:${info.line ?? ''}</td><td>${u}</td></tr>`;
}).join('');

const aicRows = (map.aicomments ?? []).map((a) => `<tr><td><a href="#aic-${slug(a.id)}">${escapeHtml(a.id)}</a></td><td>${a.line}</td><td>${escapeHtml(a.verdict)}</td><td>${md(a.note)}</td></tr>`).join('');

const countBy = (key, vocab) => Object.entries(vocab).map(([k, v]) => {
  const n = items.filter((it) => it[key] === k && it.counted !== false).length;
  return n ? `<span class="badge b-${v.color}">${escapeHtml(v.label)}: ${n}</span>` : '';
}).join(' ');
const sevCount = Object.entries(SEV).sort((a, b) => b[1].rank - a[1].rank).map(([k, v]) => `<span class="badge b-${v.color}">${escapeHtml(v.label)}: ${allIssues.filter((i) => i.severity === k).length}</span>`).join(' ');

tex.warnings.forEach((w) => warnings.push(w));
const buildInfo = { generated: new Date().toISOString().slice(0, 10), errors: errors.length, warnings: warnings.length };

const css = fs.readFileSync(path.join(here, 'style.css'), 'utf8');
const js = fs.readFileSync(path.join(here, 'review.js'), 'utf8');
// Inline the KaTeX fonts (woff2 only) so the HTML is a single offline file.
const katexDir = path.join(here, 'node_modules/katex/dist');
const katexCss = fs.readFileSync(path.join(katexDir, 'katex.min.css'), 'utf8')
  .replace(/src:url\(fonts\/([^)]+\.woff2)\) format\("woff2"\)(?:,url\([^)]+\) format\("[a-z]+"\))*/g, (_, font) =>
    `src:url(data:font/woff2;base64,${fs.readFileSync(path.join(katexDir, 'fonts', font)).toString('base64')}) format("woff2")`);
const src = map.sources;
const html = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Stafford 3.8 paper–Lean audit</title>
<style>${katexCss}</style><style>${css}</style></head>
<body>
<nav class="side">
  <div class="brand">Stafford 3.8<br><span>paper ↔ Lean audit</span></div>
  <label for="review-scope">Review scope</label><select id="review-scope">${reviewScopeOptions(items)}</select>
  <input id="filter" type="search" placeholder="Filter cards…">
  <div class="filters">
    <label><input type="checkbox" id="only-issues"> with issues</label>
    <label><input type="checkbox" id="only-open"> not yet signed off</label>
    <label><input type="checkbox" id="clean-text"> hide AI markup</label>
  </div>
  <ol class="toc">
    <li><a href="#overview">Overview</a></li><li><a href="#graph">Dependency map</a></li>${challengeDefinitions ? '<li><a href="#challenge-definitions">Challenge definitions</a></li>' : ''}
    ${map.sections.map((sec) => `<li><a href="#sec-${escapeHtml(sec.number)}">${escapeHtml(sec.number)}. ${escapeHtml(sec.title)}</a><ol>${items.filter((it) => it.section === sec.number).map((it) => `<li><a href="#item-${slug(it.id)}" data-toc="${escapeHtml(it.id)}">${escapeHtml(it.short ?? it.id)}</a></li>`).join('')}</ol></li>`).join('')}
    <li><a href="#lean-only">Lean-only steps</a></li><li><a href="#issues">Issue register</a></li>
    <li><a href="#aicomments">AI comments</a></li><li><a href="#lean-index">Lean → paper index</a></li><li><a href="#provenance">Provenance</a></li>
  </ol>
  <div class="review-tools">
    <div id="progress"></div>
    <button id="export">Export review JSON</button>
    <label class="btn">Import review JSON<input type="file" id="import" accept="application/json" hidden></label>
    <input id="reviewer" placeholder="Reviewer name">
  </div>
</nav>
<main>
<header class="doc-head">
  <h1>${escapeHtml(map.title)}</h1>
  <p class="sub">${escapeHtml(map.subtitle)}</p>
  <table class="pins">
    <tr><th>Paper</th><td><a href="https://github.com/${src.paper.repo}/blob/${src.paper.commit}/${paperFile}">${escapeHtml(src.paper.repo)}/${escapeHtml(paperFile)}</a> @ <code>${src.paper.commit.slice(0, 12)}</code> ${escapeHtml(src.paper.note ?? '')}</td></tr>
    <tr><th>Lean</th><td><a href="https://github.com/${src.formal.repo}/tree/${src.formal.commit}">${escapeHtml(src.formal.repo)}</a> @ <code>${src.formal.commit.slice(0, 12)}</code> ${escapeHtml(src.formal.note ?? '')}</td></tr>
    ${src.library ? `<tr><th>Library</th><td><a href="https://github.com/${src.library.repo}/tree/${src.library.commit}">${escapeHtml(src.library.repo)}</a> @ <code>${src.library.commit.slice(0, 12)}</code> ${escapeHtml(src.library.note ?? '')}</td></tr>` : ''}
    ${src.global ? `<tr><th>GlobalStafford</th><td><a href="https://github.com/${src.global.repo}/tree/${src.global.commit}">${escapeHtml(src.global.repo)}</a> @ <code>${src.global.commit.slice(0, 12)}</code> ${escapeHtml(src.global.note ?? '')}</td></tr>` : ''}
    ${src.mathlib ? `<tr><th>Mathlib</th><td><a href="https://github.com/${src.mathlib.repo}/tree/${src.mathlib.commit}">${escapeHtml(src.mathlib.repo)}</a> @ <code>${src.mathlib.commit.slice(0, 12)}</code> ${escapeHtml(src.mathlib.note ?? '')}</td></tr>` : ''}
    <tr><th>Build</th><td>generated ${buildInfo.generated} by <code>paper-lean-audit</code> · mapping checks: ${errors.length ? `<b class="err">${errors.length} errors</b>` : 'all passed'} · ${warnings.length} warnings</td></tr>
  </table>
</header>
<section id="overview"><p class="publication-target"><b>Max: review the whole current paper–Lean correspondence.</b> Check every mathematical claim, its definitions, hypotheses, sidedness and proof steps, including exact matches. Keep valid paper arguments where checked variants or adapters can support them. Linked readable Lean proofs explain differences; they do not certify a different printed proof. Johanna reviews concrete text proposals. Human acceptance is still required.</p><div id="freshness" class="muted"></div><h2>Overview</h2>
  ${guidedItems.length ? `<p class="guided-start"><a data-guided-start href="#item-${slug(guidedItems[0].id)}">Start guided review at ${escapeHtml(guidedItems[0].short ?? guidedItems[0].title ?? guidedItems[0].id)}</a> <span class="muted">(${guidedItems.length} claims in paper order)</span> · <a id="guided-resume" data-guided-resume hidden>Resume last visited claim</a></p>` : ''}
  <div class="stats"><div>Statements: ${countBy('statement_relation', REL)}</div><div>Proof routes: ${countBy('route_relation', ROUTE)}</div><div>Issues: ${sevCount}</div><div>Recorded sign-offs (committed, current): ${items.filter((it) => (recorded[it.id] ?? []).some((r) => r.complete && r.hash === it._hash)).length} / ${items.length}</div></div>
  ${md(map.overview)}
  <h3>How to use this document</h3>${md(map.how_to_use)}
  <h3>Legend</h3>
  <table class="legend"><tr><th colspan="2">Statement relation (paper vs Lean)</th></tr>${Object.values(REL).map((v) => `<tr><td><span class="badge b-${v.color}">${escapeHtml(v.label)}</span></td><td>${escapeHtml(v.meaning)}</td></tr>`).join('')}
  <tr><th colspan="2">Proof-route relation</th></tr>${Object.values(ROUTE).map((v) => `<tr><td><span class="badge b-${v.color}">${escapeHtml(v.label)}</span></td><td>${escapeHtml(v.meaning)}</td></tr>`).join('')}
  <tr><th colspan="2">Issue severity</th></tr>${Object.values(SEV).map((v) => `<tr><td><span class="badge b-${v.color}">${escapeHtml(v.label)}</span></td><td>${escapeHtml(v.meaning)}</td></tr>`).join('')}</table>
</section>
<section id="graph" data-reference-material><h2>Dependency map</h2><p class="muted">Arrows point from an input to the item that uses it. Colour = statement relation. Click a node.</p>${depGraph()}</section>
${challengeDefinitions ? `<section id="challenge-definitions"><h2>Challenge: meaning and soundness</h2><p>Start here: check the quantified fields, characteristic, rank, nonzero input, Weyl relations and factor order against the paper. <code>Field</code> is a typeclass of commutative fields; <code>CharZero</code> requires injective natural-number casts. Definitions specify the proposition; only the proved solution endpoints supply evidence. The deliberate <code>sorry</code> in each challenge template is not a proof. Click linked identifiers in signatures to open their exact pinned definitions. Library parents and imports remain accessible in the pinned source.</p>${challengeEndpoints}<details><summary>Definitions entering the challenge and fixed-source strengthening</summary>${challengeDefinitions}</details></section>` : ''}
${sectionHtml}
<section id="lean-only" data-reference-material><h2>Lean-only steps</h2>${md(map.lean_only_intro)}<table class="reg fixed"><colgroup><col style="width:34%"><col style="width:48%"><col style="width:18%"></colgroup><thead><tr><th>Lean</th><th>What it does and why a reviewer should know</th><th>Nearest paper item</th></tr></thead><tbody>${leanOnly}</tbody></table></section>
<section id="issues" data-reference-material><h2>Issue register</h2><table class="reg fixed"><colgroup><col style="width:9%"><col style="width:7%"><col style="width:11%"><col style="width:61%"><col style="width:12%"></colgroup><thead><tr><th>Severity</th><th>ID</th><th>Item</th><th>Summary</th><th>AIcomment</th></tr></thead><tbody>${issueTable}</tbody></table></section>
<section id="aicomments" data-reference-material><h2>AI comments in the manuscript</h2><table class="reg"><thead><tr><th>ID</th><th>tex line</th><th>Audit verdict</th><th>Note</th></tr></thead><tbody>${aicRows}</tbody></table></section>
<section id="lean-index" data-reference-material><h2>Lean → paper index</h2><p class="muted">Every declaration or module cited in this document, with the paper items that use it. The ⇄ link on each Lean block lands here.</p><table class="reg fixed"><colgroup><col style="width:45%"><col style="width:25%"><col style="width:30%"></colgroup><thead><tr><th>Declaration</th><th>Location</th><th>Paper items</th></tr></thead><tbody>${leanIndexRows}</tbody></table></section>
<section id="provenance"><h2>Provenance and mapping checks</h2>${md(map.provenance)}
  <h3>Automatic checks</h3>${errors.length ? `<ul class="err">${errors.map((e) => `<li>${escapeHtml(e)}</li>`).join('')}</ul>` : '<p>All mapping checks passed: every cited declaration was found under its fully qualified name at the pinned commit, every label lies in its excerpt, and every reference resolved.</p>'}
  ${warnings.length ? `<details><summary>${warnings.length} warnings</summary><ul>${warnings.map((w) => `<li>${escapeHtml(w)}</li>`).join('')}</ul></details>` : ''}
</section>
</main>
<script>window.AUDIT_META = ${JSON.stringify({ version: map.version, paper: src.paper.commit, formal: src.formal.commit, checks: reviewChecks.map((c) => c.id), generator: generatorHash, live: liveUrl })};</script>
<script>${js}</script>
</body></html>`;

fs.mkdirSync(outDir, { recursive: true });
const htmlPath = path.join(outDir, outputStem + '.html');
fs.writeFileSync(htmlPath, html);
fs.writeFileSync(path.join(outDir, 'version.json'), JSON.stringify({ version: map.version, paper: src.paper.commit, formal: src.formal.commit, generator: generatorHash }) + '\n');
console.log(`wrote ${htmlPath}`);
if (warnings.length) console.log(`${warnings.length} warnings:\n  ` + warnings.join('\n  '));
if (errors.length) console.error(`${errors.length} ERRORS:\n  ` + errors.join('\n  '));

if (flag('--pdf')) {
  const { chromium } = await import('playwright-core');
  const exe = process.env.CHROMIUM_PATH ?? ['/opt/pw-browsers/chromium-1194/chrome-linux/chrome', '/opt/pw-browsers/chromium'].find((p) => fs.existsSync(p));
  const browser = await chromium.launch(exe ? { executablePath: exe } : {});
  // A4 width minus the 12 mm side margins, so print layout is measured at its real width.
  const page = await browser.newPage({ viewport: { width: Math.round((210 - 24) / 25.4 * 96), height: 1100 } });
  await page.goto('file://' + htmlPath, { waitUntil: 'networkidle' });
  // A printed audit must include the signatures hidden behind screen controls.
  await page.evaluate(() => document.querySelectorAll('details').forEach((el) => { el.open = true; }));
  await page.emulateMedia({ media: 'print' });
  // Printing before the embedded KaTeX fonts are ready yields a PDF laid out
  // with fallback metrics (observed: silently shortened output).
  await page.evaluate(() => document.fonts.ready);
  // Shrink display formulas that are wider than their print column.
  await page.evaluate(() => {
    for (const el of document.querySelectorAll('.dmath')) {
      const ratio = el.clientWidth / el.scrollWidth;
      if (ratio < 1) el.style.fontSize = `${Math.max(0.6, ratio * 0.97)}em`;
    }
  });
  const pdfPath = path.join(outDir, outputStem + '.pdf');
  // Sanity check: every heading becomes an outline entry, so a complete PDF
  // has at least one /Title per heading; retry otherwise.
  const expected = await page.evaluate(() => document.querySelectorAll('h1, h2, h3').length);
  let pages = 0, titles = 0;
  for (let attempt = 1; attempt <= 3; attempt++) {
    await page.pdf({
      path: pdfPath, format: 'A4', printBackground: true, outline: true, tagged: true,
      margin: { top: '14mm', bottom: '16mm', left: '12mm', right: '12mm' }, displayHeaderFooter: true,
      headerTemplate: `<div style="font-size:7px;width:100%;text-align:center;color:#666">${escapeHtml(map.title ?? "Paper–Lean review")} · paper ${src.paper.commit.slice(0, 7)} · Lean ${src.formal.commit.slice(0, 7)}</div>`,
      footerTemplate: '<div style="font-size:7px;width:100%;text-align:center;color:#666"><span class="pageNumber"></span> / <span class="totalPages"></span></div>',
    });
    const bytes = fs.readFileSync(pdfPath).toString('latin1');
    pages = (bytes.match(/\/Type\s*\/Page[^s]/g) ?? []).length;
    titles = (bytes.match(/\/Title\b/g) ?? []).length;
    if (titles >= expected) break;
    console.error(`PDF attempt ${attempt}: outline has ${titles} of ${expected} headings; retrying`);
    await page.waitForTimeout(1000);
  }
  if (titles < expected) errors.push(`PDF appears truncated: outline has ${titles} of ${expected} headings`);
  console.log(`PDF: ${pages} pages, ${titles} outline entries for ${expected} headings`);
  await browser.close();
  console.log(`wrote ${pdfPath}`);
}
if (flag('--check') && errors.length) process.exit(1);
