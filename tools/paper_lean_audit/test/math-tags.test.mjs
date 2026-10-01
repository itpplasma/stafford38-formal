import test from 'node:test';
import assert from 'node:assert/strict';
import { TexRenderer } from '../texhtml.mjs';

function render(source, tag) {
  const offset = source.indexOf('\\begin{');
  const renderer = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map([[offset, tag]]) });
  const html = renderer.text(source);
  assert.deepEqual(renderer.warnings, []);
  return html;
}

test('unstarred align and gather displays receive computed equation tags', () => {
  assert.match(render(String.raw`\begin{align}a&=b\end{align}`, '3.2'), /3\.2/);
  assert.match(render(String.raw`\begin{gather}a=b\end{gather}`, '4.1'), /4\.1/);
});

test('explicit tags override computed tags on aligned displays', () => {
  const html = render(String.raw`\begin{align}a&=b\tag{Manual}\end{align}`, '3.2');
  assert.match(html, /Manual/);
  assert.doesNotMatch(html, /3\.2/);
});

test('explicit equation tags override the automatic section tag', () => {
  const html = render(String.raw`\begin{equation}a=b\tag{Manual}\end{equation}`, '3.2');
  assert.match(html, /Manual/);
  assert.doesNotMatch(html, /3\.2/);
});

test('AI edit macros render inside math, including removed and replaced text', () => {
  const r = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = r.text(String.raw`$\AIadd{x}+\AIremove{y}+\AIreplace{a}{b}$`);
  assert.match(html, /mathcolor="red"/);
  assert.match(html, /mathcolor="blue"/);
  assert.match(html, /menclose notation="updiagonalstrike"/);
  assert.deepEqual(r.warnings, []);
});

test('psmallmatrix is rendered as a parenthesized smallmatrix', () => {
  const r = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = r.text(String.raw`$\begin{psmallmatrix}a&b\\c&d\end{psmallmatrix}$`);
  assert.match(html, /\\left\(/);
  assert.match(html, /a/);
  assert.match(html, /d/);
  assert.deepEqual(r.warnings, []);
});

test('formal references and declaration macros become pinned GitHub links', () => {
  const url = 'https://github.com/example/formal/blob/0123456789abcdef0123456789abcdef01234567/Foo.lean#L12';
  const refs = new Map([
    [['leandecl', 'Foo.lean', '12', 'Foo.result'].join('\0'), url],
    [['leanlib', 'Bar.lean', '13', 'Bar.helper'].join('\0'), 'https://github.com/example/library/blob/0123456789abcdef0123456789abcdef01234567/Bar.lean#L13'],
  ]);
  const r = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map(), leanRefs: refs });
  const html = r.text(String.raw`\formalref[extends the paper's case]{\leandecl{Foo.lean}{12}{Foo.result}; \leanlib{Bar.lean}{13}{Bar.helper}}`);
  assert.match(html, /Lean<span class="formalref-relation"> \(extends the paper's case\)<\/span>:/);
  assert.match(html, /href="https:\/\/github\.com\/example\/formal\/blob\//);
  assert.match(html, /Foo\.result/);
  assert.match(html, /Bar\.helper/);
  assert.deepEqual(r.warnings, []);
});

test('Lean link renderer refuses an unsafe target', () => {
  const r = new TexRenderer({
    macros: {}, refs: {}, cites: {}, eqAuto: new Map(),
    leanRefs: new Map([[['leandecl', 'Foo.lean', '12', 'Foo.result'].join('\0'), 'javascript:alert(1)']]),
  });
  const html = r.text(String.raw`\leandecl{Foo.lean}{12}{Foo.result}`);
  assert.doesNotMatch(html, /href="javascript:/);
  assert.deepEqual(r.warnings, ['unsafe Lean source URL omitted for Foo.result']);
});
