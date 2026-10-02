import test from 'node:test';
import assert from 'node:assert/strict';
import { TexRenderer } from '../texhtml.mjs';

test('AI addition newline renders as a line break without exposing the TeX command', () => {
  const renderer = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = renderer.block('before\\AIadd{\\newline}after', 0);
  assert.match(html, /<span class="ai-add"><br><\/span>/);
  assert.doesNotMatch(html, /\\newline|code/);
  assert.deepEqual(renderer.warnings, []);
});
