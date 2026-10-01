import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { TexRenderer, stripComments } from '../texhtml.mjs';
import { findDeclaration } from '../lean.mjs';

function renderer(overrides = {}) {
  return new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map(), ...overrides });
}

function outsideMath(source) {
  return source
    .replace(/\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}[\s\S]*?\\end\{\1\}/g, '')
    .replace(/\$\$[\s\S]*?\$\$|\$[^$\n]*\$|\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]/g, '');
}

test('optional citation arguments balance nested brackets, braces, and escaped closers', () => {
  const r = renderer({ cites: { key: 'K' } });
  assert.equal(r.text(String.raw`\cite[outer [inner] {group}]{key}`),
    '<span class="cite">[K, outer [inner] group]</span>');
  assert.equal(r.text(String.raw`\cite[escaped \] bracket]{key}`),
    '<span class="cite">[K, escaped \\] bracket]</span>');
});

test('comments honor TeX backslash parity', () => {
  assert.equal(stripComments(String.raw`literal \% percent % removed`), String.raw`literal \% percent `);
  assert.equal(stripComments(String.raw`linebreak \\% comment`), String.raw`linebreak \\`);
});

test('inline and display math use matching, escaped delimiters', () => {
  const r = renderer();
  const html = r.text(String.raw`inline $x + \$y$; display $$z^2$$; \(u\) and \[v\].`);
  assert.equal(r.warnings.length, 0);
  assert.equal((html.match(/class="katex"/g) ?? []).length, 4);
  assert.match(html, /class="katex-display"/);
  assert.doesNotMatch(html, /\$\$|\(u\)|\[v\]/);
});

test('unclosed math and environments are visible, warned, and terminate', () => {
  for (const source of [String.raw`before $x + 1`, String.raw`before \(x + 1`, String.raw`before \[x + 1`]) {
    const r = renderer();
    const html = r.text(source);
    assert.match(html, /before <code class="tex-error">/);
    assert.equal(r.warnings.length, 1);
    assert.match(r.warnings[0], /unclosed math delimiter/);
  }

  const r = renderer();
  assert.match(r.text(String.raw`before \begin{proof}unfinished`), /<code class="tex-error">/);
  assert.deepEqual(r.warnings, ['unclosed environment \\begin{proof}']);

  const stringified = renderer();
  const html = stringified.text(String.raw`\begin{proof}The token \string\begin{proof} is shown literally.\end{proof}`);
  assert.match(html, /class="proof"/);
  assert.match(html, /\\begin/);
  assert.equal(stringified.warnings.length, 0);
});

test('nested AI markup carries the source offset and renders nested commands', () => {
  const r = renderer({ refs: { 'lem:test': { text: '4', href: '#lem-test' } } });
  const html = r.text(String.raw`\AIreplace{old \emph{word}}{new \ref{lem:test}} and \AIcomment{ID-7}{\AIadd{note}}`);
  assert.match(html, /<del class="ai-remove">old <em>word<\/em><\/del>/);
  assert.match(html, /<span class="ai-add">new <a href="#lem-test">4<\/a><\/span>/);
  assert.match(html, /id="aic-ID-7"/);
  assert.match(html, /<span class="ai-add">note<\/span>/);
  assert.equal(r.warnings.length, 0);

  const numbered = renderer({ eqAuto: new Map([[7, '42']]) });
  assert.match(numbered.text(String.raw`\AIadd{\begin{equation}x=1\end{equation}}`), /42/);

  const listSource = String.raw`\begin{itemize}\item \begin{equation}x=1\end{equation}\end{itemize}`;
  const listEquation = listSource.indexOf(String.raw`\begin{equation}`);
  const listed = renderer({ eqAuto: new Map([[listEquation, '7']]) }).text(listSource);
  assert.match(listed, /<ul><li>.*7/s);
});

test('hyperref preserves its display text and only links local anchors', () => {
  const r = renderer({ refs: { 'thm:test': { text: '9', href: '#thm-test' } } });
  assert.equal(r.text(String.raw`\hyperref[thm:test]{The \textbf{main result}}`),
    '<a href="#thm-test">The <b>main result</b></a>');

  const hostile = renderer({ refs: { bad: { text: 'unsafe', href: 'javascript:alert(1)' } } });
  assert.equal(hostile.text(String.raw`\ref{bad}`), 'unsafe');
  assert.doesNotMatch(hostile.text(String.raw`\hyperref[bad]{click}`), /<a\s/);
  assert.equal(hostile.warnings.length, 2);
});

test('unknown commands and hostile text stay visible without becoming HTML', () => {
  const r = renderer();
  const html = r.text(String.raw`\futurecmd{<img src=x onerror=alert(1)>}`);
  assert.match(html, /<code>\\futurecmd<\/code>/);
  assert.match(html, /&lt;img src=x onerror=alert\(1\)&gt;/);
  assert.doesNotMatch(html, /<(?:img|svg|script)\b[^>]*\bonerror=/i);
  assert.deepEqual(r.warnings, ['kept unknown text command \\futurecmd']);

  const math = renderer().math(String.raw`\href{javascript:alert(1)}{click}`, true);
  assert.doesNotMatch(math, /href="javascript:|<script\b|onerror=/i);

  const env = renderer().text(String.raw`\begin{odd"><img src=x>}<img src=x>\end{odd"><img src=x>}`);
  assert.match(env, /&lt;img src=x&gt;/);
  assert.doesNotMatch(env, /<img\b/);
});

function pinnedPaper() {
  const testDir = path.dirname(fileURLToPath(import.meta.url));
  const auditDir = path.resolve(testDir, '..');
  const map = JSON.parse(fs.readFileSync(path.join(auditDir, 'paper-lean-map.json'), 'utf8'));
  const candidates = [path.resolve(auditDir, '../..'),
    path.resolve(auditDir, '../../..', 'stafford38-paper')];
  for (const repo of candidates) {
    try {
      const source = execFileSync('git', ['-C', repo, 'show', `${map.sources.paper.commit}:${map.sources.paper.file}`], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
      return { map, repo, source };
    } catch { /* Try the separately maintained manuscript checkout. */ }
  }
  return null;
}

const paperFixture = pinnedPaper();
test('mapped excerpts from the pinned current paper render without dropped commands', { skip: paperFixture ? false : 'sibling paper clone is required for this integration check' }, () => {
  const { map, source } = paperFixture;
  const lines = source.split('\n');
  const macros = { '\\cots': '\\cdots', '\\dd': '\\mathrm{d}', '\\sm': '\\mathrm{sm}', '\\Weyl': 'A_n', '\\Kbar': '\\overline{k}' };
  for (const match of source.matchAll(/\\newcommand\{(\\[A-Za-z]+)\}\{((?:[^{}]|\{[^{}]*\})*)\}/g)) {
    if (!match[2].includes('#')) macros[match[1]] = match[2];
  }
  for (const match of source.matchAll(/\\DeclareMathOperator\{(\\[A-Za-z]+)\}\{([^}]*)\}/g)) {
    macros[match[1]] = `\\operatorname{${match[2]}}`;
  }
  const refs = {};
  for (const match of source.matchAll(/\\label\{([^}]+)\}/g)) refs[match[1]] = { text: match[1] };
  for (const item of map.items) if (item.label) refs[item.label] = { text: item.number ?? item.label, href: `#item-${item.id.replace(/[^A-Za-z0-9_.:-]/g, '-')}` };
  for (const section of map.sections) if (section.label) refs[section.label] = { text: section.number, href: `#sec-${section.number}` };
  for (const [label, text] of Object.entries(map.extra_refs ?? {})) refs[label] = { text };
  const leanRefs = new Map();
  const loadLeanRepo = (repoKey) => {
    const sourceInfo = map.sources[repoKey];
    const testDir = path.dirname(fileURLToPath(import.meta.url));
    const ownRoot = path.resolve(testDir, '../../..');
    const sibling = path.resolve(testDir, '../../../..',
      repoKey === 'formal' ? 'stafford38-formal' : 'algebraic-analysis');
    const root = repoKey === 'formal' && map.sources.paper.repo === sourceInfo.repo
      ? ownRoot : fs.existsSync(sibling) ? sibling
        : path.join(ownRoot, '.lake/packages/algebraicAnalysis');
    return { sourceInfo, root, cache: new Map() };
  };
  const leanRepos = { formal: loadLeanRepo('formal'), library: loadLeanRepo('library') };
  const macroPattern = /\\(leandecl|leanlib)\s*\{([^{}]*)\}\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g;
  for (const match of stripComments(source).matchAll(macroPattern)) {
    const command = match[1], file = match[2].trim(), lineText = match[3].trim(), declaration = match[4].trim();
    const repoKey = command === 'leanlib' ? 'library' : 'formal';
    const repo = leanRepos[repoKey];
    if (!repo.cache.has(file)) {
      repo.cache.set(file, execFileSync('git', ['-C', repo.root, 'show', `${repo.sourceInfo.commit}:${file}`], { encoding: 'utf8' }));
    }
    const found = findDeclaration(repo.cache.get(file), declaration, Number(lineText));
    assert.ok(found?.exact, `${command} ${declaration} must resolve to a source declaration`);
    const url = `https://github.com/${repo.sourceInfo.repo}/blob/${repo.sourceInfo.commit}/${file}#L${found.line}`;
    leanRefs.set([command, file, lineText, declaration].join(String.fromCharCode(0)), url);
  }

  const offsets = [0];
  for (const line of lines) offsets.push(offsets.at(-1) + line.length + 1);
  const rendered = [];
  const warnings = [];
  const expected = { cite: 0, comment: 0, add: 0, remove: 0, replace: 0 };
  for (const item of map.items) {
    if (!item.tex_lines) continue;
    const [first, last] = item.tex_lines;
    const excerpt = stripComments(lines.slice(first - 1, last).join('\n'));
    expected.cite += [...excerpt.replace(/\\string\s*\\cite\b/g, '').matchAll(/\\cite\b/g)].length;
    expected.comment += [...excerpt.matchAll(/\\AIcomment\b/g)].length;
    const textOnly = outsideMath(excerpt);
    expected.add += [...textOnly.matchAll(/\\AIadd\b/g)].length;
    expected.remove += [...textOnly.matchAll(/\\AIremove\b/g)].length;
    expected.replace += [...textOnly.matchAll(/\\AIreplace\b/g)].length;
    const r = renderer({ macros, refs, leanRefs });
    rendered.push(r.block(excerpt, offsets[first - 1]));
    warnings.push(...r.warnings);
  }
  const html = rendered.join('\n');
  assert.equal(warnings.length, 0, `unexpected renderer warnings in ${map.sources.paper.file}@${map.sources.paper.commit}: ${warnings.slice(0, 8).join('; ')}`);
  assert.match(html, /class="ai-comment"/);
  assert.match(html, /class="ai-add"/);
  assert.match(html, /class="ai-remove"/);
  assert.match(html, /class="cite"/);
  assert.match(html, /class="proof"/);
  assert.match(html, /class="katex-display"/);
  const count = (re) => (html.match(re) ?? []).length;
  assert.equal(count(/class="cite"/g), expected.cite);
  assert.equal(count(/class="ai-comment"/g), expected.comment);
  assert.equal(count(/class="ai-add"/g), expected.add + expected.replace);
  assert.equal(count(/class="ai-remove"/g), expected.remove + expected.replace);
});
