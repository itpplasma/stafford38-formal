// Behavioural tests for the source helpers with hand-written oracles.
import test from 'node:test';
import assert from 'node:assert/strict';
import { findDeclaration, extractStatement, namespaceAt, namedResultType, definitionNames, declarationContext, bindingNames, declarationTrust, highlightLean } from '../lean.mjs';
import { TexRenderer, stripComments, readGroup } from '../texhtml.mjs';

const lean = `namespace A.B
section S
variable (x : Nat)
/-- Doc for foo. -/
theorem foo (h : x = 1) :
    x + 0 = 1 := by
  simpa using h
end S
namespace C
private lemma bar : True := trivial
def P : Prop :=
  ∀ n : Nat, n = n

end C
end A.B
theorem foo : True := trivial
`;

test('namespaces are tracked through sections and nested namespaces', () => {
  const lines = lean.split('\n');
  assert.deepEqual(namespaceAt(lines, 4), ['A', 'B']);
  assert.deepEqual(namespaceAt(lines, 9), ['A', 'B', 'C']);
  assert.deepEqual(namespaceAt(lines, 15), []);
});

test('fully qualified names resolve to the right declaration', () => {
  assert.equal(findDeclaration(lean, 'A.B.foo').line, 5);
  assert.equal(findDeclaration(lean, 'foo').line, 16); // the root-level foo is the exact match
  const partial = findDeclaration(lean, 'B.foo', 5); // misqualified: resolves, but flagged as not exact
  assert.equal(partial.qualified, 'A.B.foo');
  assert.equal(partial.exact, false);
 assert.equal(findDeclaration(lean, 'A.B.C.bar').line, 10);
  assert.equal(findDeclaration(lean, 'A.B.C.bar').visibility, 'private');
  assert.equal(findDeclaration(lean, 'A.B.C.bar').exported, false);
 assert.equal(findDeclaration(lean, 'A.B.missing'), null);
});

test('statements stop before the proof; definitions keep their body', () => {
  const lines = lean.split('\n');
  const thm = extractStatement(lines, 5);
  assert.match(thm.text, /^\/-- Doc for foo\. -\/\ntheorem foo/);
  assert.match(thm.text, /x \+ 0 = 1 :=$/);
  assert.doesNotMatch(thm.text, /simpa/);
  const def = extractStatement(lines, 11, 45, true);
  assert.match(def.text, /∀ n : Nat, n = n$/);
});

test('TeX helpers: comments, groups, AI markup, references', () => {
  assert.equal(stripComments('a % c\n\\% b'), 'a \n\\% b');
  assert.deepEqual(readGroup('{a{b}c}d', 0), ['a{b}c', 7]);
  const r = new TexRenderer({ macros: {}, refs: { 'lem:x': { text: '5.1', href: '#item-lem:x' } }, cites: {}, eqAuto: new Map() });
  const html = r.text('\\AIreplace{old}{new} see Lemma~\\ref{lem:x} and \\eqref{lem:x}. \\AIcomment{ID-1}{note}');
  assert.match(html, /<del class="ai-remove">old<\/del><span class="ai-add">new<\/span>/);
  assert.match(html, /<a href="#item-lem:x">5\.1<\/a>/);
  assert.match(html, /<a href="#item-lem:x">\(5\.1\)<\/a>/);
  assert.match(html, /id="aic-ID-1"/);
  assert.equal(r.warnings.length, 0);
  r.text('\\ref{nope}');
  assert.equal(r.warnings.length, 1);
});

test('named arguments inside a signature do not end the statement', () => {
  const src = ['theorem t (S : Submonoid (A (k := k) n)) (h : True) :', '    S = S := by', '  rfl'];
  const st = extractStatement(src, 1);
  assert.equal(st.text, 'theorem t (S : Submonoid (A (k := k) n)) (h : True) :\n    S = S :=');
  const def = extractStatement(['def algebra : Foo where', '  carrier := {x | x = x}', "  add_mem' := by", '    simp'], 1, 45, true);
  assert.equal(def.text, 'def algebra : Foo where\n  carrier := {x | x = x}\n  …');
});

test('namespace tracking ignores commented scopes and bare end closes the inner scope', () => {
  const src = [
    'namespace A',
    'section S',
    '-- namespace Commented',
    '/- namespace Also.Commented',
    '   /- namespace Nested.Commented -/',
    '-/',
    'end',
    'namespace B',
    'end',
    'theorem visible : True := by',
    '  trivial',
  ];
  assert.deepEqual(namespaceAt(src, 6), ['A']);
  assert.deepEqual(namespaceAt(src, 9), ['A']);
  assert.equal(findDeclaration(src.join('\n'), 'A.visible').line, 10);
  assert.equal(findDeclaration(src.join('\n'), 'A.Also.Commented'), null);
});

test('declaration lookup ignores nested block comments and accepts local declarations', () => {
  const src = `namespace A
/- theorem hidden : True := by
  trivial
/- namespace FalseScope -/
-/
-- theorem lineHidden : True := by trivial
local theorem shown : True := by
  trivial
end A`;
  assert.equal(findDeclaration(src, 'A.hidden'), null);
  assert.equal(findDeclaration(src, 'A.lineHidden'), null);
  assert.equal(findDeclaration(src, 'A.shown').line, 7);
});

test('statement extraction does not stop at assignment text inside comments', () => {
  const src = [
    'theorem commentSafe : True /- fake := by',
    '  theorem fake : False := by',
    '  trivial -/ := by',
    '  trivial',
  ];
  const st = extractStatement(src, 1);
  assert.match(st.text, /commentSafe[\s\S]*-\/ :=$/);
  assert.doesNotMatch(st.text, /\n\s*trivial$/);
});

test('pattern-matching definitions retain all branches and stop at scope commands', () => {
  const lines = ['def weight : Sum Nat Nat → Nat', '  | Sum.inl _ => 0', '  | Sum.inr _ => 1', 'end Example'];
  assert.equal(extractStatement(lines, 1, 45, true).text, lines.slice(0, 3).join('\n'));
  assert.equal(extractStatement(lines, 1, 2, true).truncated, true);
});

test('blank-separated branches and structure fields are not silently dropped', () => {
  const branches = ['def weight : Sum Nat Nat → Nat', '  | Sum.inl _ => 0', '', '  | Sum.inr _ => 1', '', 'end Example'];
  const branch = extractStatement(branches, 1, 45, true);
  assert.equal(branch.text, branches.slice(0, 4).join('\n')); assert.equal(branch.truncated, false);
  const fields = ['structure Pair where', '  first : Nat', '', '  second : Nat', '', 'def next : Nat := 0'];
  assert.equal(extractStatement(fields, 1, 45, true).text, fields.slice(0, 4).join('\n'));
  assert.equal(extractStatement(['def tactic : Nat := by', '  exact 0'], 1, 45, true).truncated, true);
  const split = extractStatement(['def tactic : Nat :=', '  /- proof implementation -/', '  by', '    exact 42'], 1, 45, true);
  assert.equal(split.truncated, true); assert.doesNotMatch(split.text, /exact 42|\bby\b/);
});

test('ambient declarations retain outer assumptions and drop closed scopes', () => {
  const lines = ['universe u', 'namespace A', 'variable (k : Type u)', '  [Field k]', 'section Old', 'variable (unused : Nat)', 'end Old', 'noncomputable section', 'variable [CharZero k]', 'theorem target : True := by trivial', 'end', 'theorem after : True := by trivial', 'end A'];
  assert.deepEqual(declarationContext(lines, 10).map(entry => entry.text), ['universe u', 'variable (k : Type u)\n  [Field k]', 'variable [CharZero k]']);
  assert.deepEqual(declarationContext(lines, 12).map(entry => entry.text), ['universe u', 'variable (k : Type u)\n  [Field k]']);
  assert.equal(findDeclaration(lines.join('\n'), 'A.after').exact, true);
});

test('source context includes local instances and opened notation namespaces', () => {
  const lines = ['namespace A', 'variable (k : Type*) [Field k]', 'open PredicateLibrary', 'local notation "R" => k', 'local instance : Nonempty k := ⟨0⟩', 'theorem target : True := by trivial', 'end A'];
  const context = declarationContext(lines, 6);
  assert.ok(context.some(entry => entry.text === 'open PredicateLibrary'));
  assert.ok(context.some(entry => entry.text === 'local notation "R" => k'));
  assert.ok(context.some(entry => entry.text === 'local instance : Nonempty k :='));
  assert.deepEqual(bindingNames('variable (P Q : Prop) [Field k]'), ['P', 'Q']);
  assert.deepEqual(bindingNames('theorem target (P : Prop) (h : P) : P := h'), ['P', 'h']);
});

test('challenge placeholders and axioms are distinguished from proved declarations', () => {
  const lines = ['theorem proved : True := by', '  trivial -- sorry in comment', '', 'theorem target : False := by', '  sorry', '', 'axiom assumed : False'];
  assert.equal(declarationTrust(lines, 1, 'theorem'), 'source declaration');
  assert.equal(declarationTrust(lines, 4, 'theorem'), 'placeholder');
  assert.equal(declarationTrust(lines, 7, 'axiom'), 'axiom');
});

test('named result detection respects binders, universes and comments', () => {
  const lines = ['theorem target (x : Nat) (h : x = 0) : Fixed.Statement.{u} := by', '  exact proof'];
  assert.equal(namedResultType(lines, 1), 'Fixed.Statement');
  assert.equal(namedResultType(['theorem explicit : ∀ n : Nat, n = n := by'], 1), null);
  assert.equal(namedResultType(['theorem equality : Ring.value = 0 := by'], 1), null);
  assert.equal(namedResultType(['theorem inequality : Module.length R M < Module.length R N := by'], 1), null);
  assert.deepEqual(definitionNames('namespace A\nprivate def hidden : Prop := True\ndef Statement : Prop := True\nend A'), [{ name: 'A.Statement', line: 3 }]);
});


test('external mathematical proof links render labels and reject active URL schemes', () => {
  const r = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = r.text('\\href{https://example.org/proofs.pdf\\#nameddest=COMP-11}{Proof of $P=0$}');
  assert.match(html, /<a href="https:\/\/example\.org\/proofs\.pdf#nameddest=COMP-11">Proof of /);
  assert.match(html, /class="katex"/);
  assert.equal(r.warnings.length, 0);
  const rejected = r.text('\\href{javascript:alert(1)}{Read the proof}');
  assert.equal(rejected, 'Read the proof');
  assert.equal(r.warnings.length, 1);
});

test('Lean identifiers jump to curated definitions without linking comments or strings', () => {
  const output = highlightLean('theorem t [Field k] : True := by\n  -- Field\n  exact "Field"', token => token === 'Field' ? '#definition-field' : null);
  assert.equal((output.match(/href="#definition-field"/g) ?? []).length, 1);
  assert.match(output, /<a class="definition-link" href="#definition-field">Field<\/a>/);
  assert.doesNotMatch(highlightLean('Field', () => 'javascript:alert(1)'), /<a/);
});
