import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const testDir = path.dirname(fileURLToPath(import.meta.url));
const auditDir = path.resolve(testDir, '..');
const buildScript = path.join(auditDir, 'build.mjs');

function git(repo, ...args) {
  return execFileSync('git', ['-C', repo, ...args], { encoding: 'utf8' }).trim();
}

function createRepo(root, name, files) {
  const repo = path.join(root, name);
  fs.mkdirSync(repo, { recursive: true });
  git(repo, 'init', '-q');
  for (const [file, contents] of Object.entries(files)) {
    const target = path.join(repo, file);
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, contents);
  }
  git(repo, 'add', '.');
  execFileSync('git', ['-C', repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'fixture']);
  return { repo, commit: git(repo, 'rev-parse', 'HEAD') };
}

function fixture(t) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'paper-lean-audit-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const paperSource = [
    '\\documentclass{article}',
    '\\newtheorem{theorem}{Theorem}',
    '\\newtheorem{definition}{Definition}',
    '\\numberwithin{equation}{section}',
    '\\section{First}',
    '\\begin{theorem}\\label{thm:covered}',
    'A covered theorem.',
    '\\end{theorem}',
    '\\begin{definition}',
    'An unlabelled definition; see \\eqref{eq:manual} and \\eqref{eq:after-manual}.',
    '\\end{definition}',
    '\\begin{equation}\\label{eq:first} x=1 \\end{equation}',
    '\\begin{align}',
    'a&=b \\nonumber\\\\',
    'c&=d \\label{eq:second}',
    '\\end{align}',
    '\\begin{equation}\\tag{Manual}\\label{eq:manual} m=1 \\end{equation}',
    '\\begin{equation}\\label{eq:after-manual} z=1 \\end{equation}',
    '\\section{Second}',
    '\\begin{equation}\\label{eq:third} y=1 \\end{equation}',
    '\\eqref{eq:first}, \\eqref{eq:second}, \\eqref{eq:third}',
  ].join('\n') + '\n';
  const paper = createRepo(root, 'paper', { 'human_readable_main.tex': paperSource, 'references.bib': '' });
  const formalSource = [
    'namespace Foo',
    'theorem valid : True := by',
    '  trivial',
    '',
    'theorem helper : True := by',
    '  trivial',
    'end Foo',
  ].join('\n') + '\n';
  const formal = createRepo(root, 'formal', { 'Foo.lean': formalSource });
  const library = createRepo(root, 'library', { 'Lib.lean': 'namespace Foo\ntheorem valid : True := by\n  trivial\nend Foo\n' });
  const global = createRepo(root, 'global', { 'Closure.lean': 'namespace GlobalStafford\ntheorem universalStatement : True := by\n  trivial\nend GlobalStafford\n' });

  // New links exist only in the current paper checkout; the paper pin in the
  // map deliberately remains at the commit whose source has no such links.
  fs.appendFileSync(path.join(paper.repo, 'human_readable_main.tex'), [
    '\\leandecl{Foo.lean}{2}{Foo.valid}',
    '\\leanlib{Lib.lean}{2}{Foo.valid}',
    '% \\leandecl{Missing.lean}{1}{Missing.comment}',
    '\\\\leandecl{Missing.lean}{1}{Missing.escaped}',
  ].join('\n') + '\n');
  const currentPaperSource = fs.readFileSync(path.join(paper.repo, 'human_readable_main.tex'), 'utf8');

  const map = {
    schema: 1, version: 'test', title: 'Test audit', subtitle: 'Fixture',
    overview: 'Overview', how_to_use: 'Use it', provenance: 'Fixture provenance', lean_only_intro: 'None',
    sources: {
      paper: { repo: 'paper/test', commit: paper.commit, file: 'human_readable_main.tex' },
      formal: { repo: 'formal/test', commit: formal.commit },
      library: { repo: 'library/test', commit: library.commit },
      global: { repo: 'global/test', commit: global.commit },
    },
    vocab: {
      statement_relation: { exact: { label: 'exact', color: 'green', meaning: 'same' } },
      route_relation: { same: { label: 'same', color: 'green', meaning: 'same' } },
      severity: {},
    },
    review_checks: [
      { id: 'statement', label: 'Statement' }, { id: 'route', label: 'Route' }, { id: 'issues', label: 'Issues' },
    ],
    sections: [{ number: '1', title: 'Statements' }],
    items: [
      {
        id: 'thm', section: '1', kind: 'Theorem', short: 'Theorem', title: 'Covered theorem',
        label: 'thm:covered', tex_lines: [6, 8], statement_relation: 'exact', route_relation: 'same',
        in_graph: false, depends_on: [],
        lean: [{ repo: 'formal', file: 'Foo.lean', line: 2, name: 'Foo.valid', role: 'statement' }],
        steps: [{ title: 'Helper and external sources', note: 'Referenced supporting results.', lean: [
          { repo: 'formal', file: 'Foo.lean', line: 5, name: 'Foo.helper', role: 'helper' },
          { repo: 'library', file: 'Lib.lean', line: 2, name: 'Foo.valid', role: 'helper' },
          { repo: 'global', file: 'Closure.lean', line: 2, name: 'GlobalStafford.universalStatement', role: 'prior result' },
        ] }],
      },
      {
        id: 'def', section: '1', kind: 'Definition', short: 'Definition', title: 'Range coverage',
        tex_lines: [9, 21], statement_relation: 'exact', route_relation: 'same', in_graph: false, depends_on: [],
      },
    ],
    extra_refs: {}, aicomments: [], global_issues: [], lean_only: [],
  };
  const mapPath = path.join(root, 'map.json');
  const out = path.join(root, 'out');
  const reviews = path.join(root, 'reviews');
  fs.mkdirSync(reviews);
  const writeMap = () => fs.writeFileSync(mapPath, JSON.stringify(map, null, 2));
  const run = () => {
    writeMap();
    return spawnSync(process.execPath, [buildScript, '--paper', paper.repo, '--formal', formal.repo,
      '--library', library.repo, '--global', global.repo, '--map', mapPath, '--out', out,
      '--reviews', reviews, '--check'], { encoding: 'utf8' });
  };
  const htmlPath = path.join(out, 'stafford38-paper-lean-audit.html');
  return { root, paper, formal, library, global, map, mapPath, reviews, htmlPath, currentPaperSource, run, writeMap };
}

test('check audits current manuscript links, statement coverage, pins, and section-aware equation tags', (t) => {
  const f = fixture(t);
  let result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  let html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /GlobalStafford/);
  assert.match(html, /id="lean-formal:decl:Foo.lean:Foo.valid"/);
  assert.match(html, /id="lean-library:decl:Lib.lean:Foo.valid"/);
  assert.match(html, /1\.1/);
  assert.match(html, /1\.2/);
  assert.match(html, /2\.1/);
 assert.match(html, /href="#item-def">\(1\.1\)<\/a>/);
 assert.match(html, /href="#item-def">\(1\.2\)<\/a>/);
  assert.match(html, /Manual/);
  assert.match(html, /href="#item-def">\(Manual\)<\/a>/);
  assert.match(html, /href="#item-def">\(1\.4\)<\/a>/);

  fs.appendFileSync(path.join(f.paper.repo, 'human_readable_main.tex'), '\\leandecl{Foo.lean}{1}{Foo.valid}\n\\leanlib{Lib.lean}{2}{Foo.missing}\n\\leandecl{Foo.lean}{2}{Foo.valid\n');
  result = f.run();
  assert.equal(result.status, 1);
  assert.match(result.stderr, /Foo\.valid points to Foo\.lean:1, declaration is at line 2/);
  assert.match(result.stderr, /Foo\.missing not found in library:Lib\.lean/);
  assert.match(result.stderr, /malformed \\leandecl reference/);

  fs.writeFileSync(path.join(f.paper.repo, 'human_readable_main.tex'), f.currentPaperSource);
  f.map.items = f.map.items.filter((item) => item.id !== 'def');
  result = f.run();
  assert.equal(result.status, 1);
  assert.match(result.stderr, /unlabelled definition at human_readable_main\.tex:9-11 is not covered/);
});

test('nested manuscript snapshots load the adjacent bibliography', (t) => {
  const f = fixture(t);
  const directory = path.join(f.paper.repo, 'docs/paper-lean-audit/manuscript');
  fs.mkdirSync(directory, { recursive: true });
  const nestedSource = f.currentPaperSource.replace('A covered theorem.', 'A covered theorem. See \\cite{nested}.');
  fs.writeFileSync(path.join(directory, 'human_readable_main.tex'), nestedSource);
  fs.writeFileSync(path.join(directory, 'references.bib'), '@article{nested,\n  author = {Nested},\n  year = {2026}\n}\n');
  git(f.paper.repo, 'add', '.');
  execFileSync('git', ['-C', f.paper.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'add nested manuscript snapshot']);
  f.map.sources.paper.commit = git(f.paper.repo, 'rev-parse', 'HEAD');
  f.map.sources.paper.file = 'docs/paper-lean-audit/manuscript/human_readable_main.tex';

  const result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /<span class="cite">\[Nested 2026\]<\/span>/);
});

test('private Lean declarations are rejected as public refs and must be marked module-private', (t) => {
  const f = fixture(t);
  fs.writeFileSync(path.join(f.formal.repo, 'Private.lean'), 'namespace Foo\nprivate theorem localFact : True := by\n  trivial\nend Foo\n');
  git(f.formal.repo, 'add', '.');
  execFileSync('git', ['-C', f.formal.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'add private helper']);
  f.map.sources.formal.commit = git(f.formal.repo, 'rev-parse', 'HEAD');
  const localRef = { repo: 'formal', file: 'Private.lean', line: 2, name: 'Foo.localFact', role: 'main-proof' };
  f.map.items[0].steps[0].lean.push(localRef);

  let result = f.run();
  assert.equal(result.status, 1);
  assert.match(result.stderr, /is private; add visibility:module-private/);

  localRef.visibility = 'module-private';
  result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  let html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /module-private; not an exported FQN/);
  assert.match(html, /id="lean-formal:private:Private\.lean:Foo\.localFact"/);

  fs.appendFileSync(path.join(f.paper.repo, 'human_readable_main.tex'), '\\leandecl{Private.lean}{2}{Foo.localFact}\n');
  result = f.run();
  assert.equal(result.status, 1);
  assert.match(result.stderr, /Foo\.localFact is private and is not exported/);
});

test('review hashes cover card metadata and proof bodies referenced only from a step', (t) => {
  const f = fixture(t);
  let result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  let html = fs.readFileSync(f.htmlPath, 'utf8');
  const firstHash = /data-item="thm" data-hash="([a-f0-9]{16})"/.exec(html)?.[1];
  assert.ok(firstHash, 'theorem card review hash is present');

  const reviewPath = path.join(f.reviews, 'review.json');
  const writeReview = (hash, checks = { statement: true, route: true, issues: true }) => fs.writeFileSync(reviewPath, JSON.stringify({
    format: 'stafford38-paper-lean-review/1', reviewer: 'Test', exported: '2026-10-01',
    items: { thm: { hash, checks } },
  }));
  writeReview(firstHash);
  result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /<span class="ok-tag">signed off<\/span>/);

  const updatedFormal = fs.readFileSync(path.join(f.formal.repo, 'Foo.lean'), 'utf8').replace('  trivial\nend Foo', '  exact True.intro\nend Foo');
  fs.writeFileSync(path.join(f.formal.repo, 'Foo.lean'), updatedFormal);
  git(f.formal.repo, 'add', '.');
  execFileSync('git', ['-C', f.formal.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'change step proof']);
  f.map.sources.formal.commit = git(f.formal.repo, 'rev-parse', 'HEAD');
  result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  html = fs.readFileSync(f.htmlPath, 'utf8');
  const newHash = /data-item="thm" data-hash="([a-f0-9]{16})"/.exec(html)?.[1];
  assert.notEqual(newHash, firstHash);
  assert.match(html, /<span class="stale-tag">stale<\/span>/);

  writeReview(newHash);
  f.map.items[0].title = 'Changed assessment card';
  result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  html = fs.readFileSync(f.htmlPath, 'utf8');
  const metadataHash = /data-item="thm" data-hash="([a-f0-9]{16})"/.exec(html)?.[1];
  assert.notEqual(metadataHash, newHash);
  assert.match(html, /<span class="stale-tag">stale<\/span>/);

  writeReview(metadataHash, { statement: 'true', route: true, issues: true });
  result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /<span class="muted">partial<\/span>/);
});

test('theorem cards show named propositions and full proof-step signatures', (t) => {
  const f = fixture(t);
  fs.writeFileSync(path.join(f.formal.repo, 'Target.lean'), [
    'namespace Foo',
    'def Statement : Prop :=',
    '  ∀ n : Nat, ∃ m : Nat, m = n + 1',
    '',
    'theorem target : Statement := by',
    '  intro n',
    '  exact ⟨n + 1, rfl⟩',
    'end Foo',
  ].join('\n'));
  git(f.formal.repo, 'add', 'Target.lean');
  execFileSync('git', ['-C', f.formal.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'named proposition fixture']);
  f.map.sources.formal.commit = git(f.formal.repo, 'rev-parse', 'HEAD');
  f.map.items[0].lean = [{ file: 'Target.lean', name: 'Foo.target', line: 5, role: 'statement' }];
  const result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /Definitions used in theorem statements/);
  assert.match(html, /∀<\/span> n : Nat, <span class="lo">∃<\/span> m : Nat, m = n \+ 1/);
  assert.match(html, /Target\.lean#L2-L3/);
  assert.match(html, /Lean declarations for the proof steps/);
  assert.match(html, /theorem<\/span> helper : True :=/);
  assert.doesNotMatch(html, /intro n|exact ⟨n \+ 1/);
});

test('changing review criterion wording invalidates the prior card digest', (t) => {
  const f = fixture(t);
  let result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const before = /data-item="thm" data-hash="([^"]+)"/.exec(fs.readFileSync(f.htmlPath, 'utf8'))[1];
  f.map.review_checks[0].label = 'Check every displayed hypothesis and conclusion';
  result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const after = /data-item="thm" data-hash="([^"]+)"/.exec(fs.readFileSync(f.htmlPath, 'utf8'))[1];
  assert.notEqual(before, after);
});

test('predicate expansion follows plain open scopes and respects variable shadowing', (t) => {
  const f = fixture(t);
  fs.writeFileSync(path.join(f.formal.repo, 'Predicates.lean'), [
    'namespace PredicateLibrary', 'def Holds : Prop := True', 'end PredicateLibrary',
    'namespace Foo', 'def P : Prop := True', 'open PredicateLibrary',
    'theorem opened : Holds := True.intro', 'section Generic', 'variable (P : Prop)',
    'theorem generic (h : P) : P := h', 'end Generic', 'end Foo',
  ].join('\n'));
  git(f.formal.repo, 'add', 'Predicates.lean');
  execFileSync('git', ['-C', f.formal.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'scope fixture']);
  f.map.sources.formal.commit = git(f.formal.repo, 'rev-parse', 'HEAD');
  f.map.items[0].lean = [{ file: 'Predicates.lean', name: 'Foo.opened', line: 7, role: 'statement' }];
  let result = f.run(); assert.equal(result.status, 0, result.stdout + result.stderr);
  let html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /PredicateLibrary\.Holds/);
  assert.doesNotMatch(html, /Named result <code>Holds<\/code> is not expanded/);
  f.map.items[0].lean = [{ file: 'Predicates.lean', name: 'Foo.generic', line: 10, role: 'statement' }];
  result = f.run(); assert.equal(result.status, 0, result.stdout + result.stderr);
  html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html.replace(/<[^>]+>/g, ''), /variable \(P : Prop\)/);
  assert.doesNotMatch(html, /class="statement-definitions"/);
});

test('changing relation vocabulary invalidates the prior card digest', (t) => {
  const f = fixture(t);
  let result = f.run(); assert.equal(result.status, 0, result.stdout + result.stderr);
  const before = /data-item="thm" data-hash="([^"]+)"/.exec(fs.readFileSync(f.htmlPath, 'utf8'))[1];
  f.map.vocab.statement_relation.exact.meaning = 'Identical assumptions and conclusion, including scope';
  result = f.run(); assert.equal(result.status, 0, result.stdout + result.stderr);
  const after = /data-item="thm" data-hash="([^"]+)"/.exec(fs.readFileSync(f.htmlPath, 'utf8'))[1];
  assert.notEqual(before, after);
});

test('duplicate FQNs in separate modules cannot silently replace a predicate source', (t) => {
  const f = fixture(t);
  const files = {
    'Alpha.lean': 'namespace Foo\ndef P : Prop := True\nend Foo\n',
    'Beta.lean': 'def P : Prop := True\nnamespace Foo\ndef P : Prop := False\nend Foo\n',
    'Target.lean': 'import Alpha\nnamespace Foo\ntheorem target : P := True.intro\nend Foo\n',
  };
  for (const [file, source] of Object.entries(files)) fs.writeFileSync(path.join(f.formal.repo, file), source);
  git(f.formal.repo, 'add', 'Alpha.lean', 'Beta.lean', 'Target.lean');
  execFileSync('git', ['-C', f.formal.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'independent module fixture']);
  f.map.sources.formal.commit = git(f.formal.repo, 'rev-parse', 'HEAD');
  f.map.items[0].lean = [{ file: 'Target.lean', name: 'Foo.target', line: 3, role: 'statement' }];
  f.map.items[1].lean = [
    { file: 'Alpha.lean', name: 'Foo.P', line: 2, role: 'definition' },
    { file: 'Beta.lean', name: 'Foo.P', line: 3, role: 'definition' },
  ];
  let result = f.run(); assert.equal(result.status, 0, result.stdout + result.stderr);
  let html = fs.readFileSync(f.htmlPath, 'utf8');
  let card = html.split('id="item-thm"')[1].split('</section>')[0];
  assert.match(card, /Named result <code>P<\/code> is not expanded/);
  assert.doesNotMatch(card, /def<\/span> P : Prop := False/);
  f.map.items[0].lean[0].expands = [{ file: 'Alpha.lean', name: 'Foo.P', line: 2 }];
  result = f.run(); assert.equal(result.status, 0, result.stdout + result.stderr);
  html = fs.readFileSync(f.htmlPath, 'utf8');
  card = html.split('id="item-thm"')[1].split('</section>')[0];
  assert.match(card, /Alpha\.lean#L2/); assert.doesNotMatch(card, /Named result <code>P<\/code> is not expanded/);
});

test('excerpt checks catch cut markup and preserve a proposed replacement excerpt', (t) => {
  const f = fixture(t);
  let source = f.currentPaperSource.replace('A covered theorem.', '\\AIadd{A covered theorem.\nMore annotated text.}');
  fs.writeFileSync(path.join(f.paper.repo, 'human_readable_main.tex'), source);
  git(f.paper.repo, 'add', 'human_readable_main.tex');
  execFileSync('git', ['-C', f.paper.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'markup fixture']);
  f.map.sources.paper.commit = git(f.paper.repo, 'rev-parse', 'HEAD');
  f.map.items = [f.map.items[0], {...f.map.items[1], tex_lines:[10,22]}];
  f.map.items[0].tex_lines=[6,7];
  let result=f.run(); assert.equal(result.status,1);assert.match(result.stderr,/cuts through \\AIadd/);
  f.map.items[0].tex_lines=[6,9];
  result=f.run();assert.equal(result.status,0,result.stdout+result.stderr);
});

test('unproved goal templates are labeled rather than presented as proved results', (t) => {
  const f=fixture(t);
  fs.writeFileSync(path.join(f.formal.repo,'Goal.lean'),'namespace Foo\ntheorem goal : False := by\n  sorry\nend Foo\n');
  git(f.formal.repo,'add','Goal.lean');
  execFileSync('git',['-C',f.formal.repo,'-c','user.name=Audit Test','-c','user.email=audit@example.test','commit','-qm','target fixture']);
  f.map.sources.formal.commit=git(f.formal.repo,'rev-parse','HEAD');
  f.map.items[0].lean=[{file:'Goal.lean',name:'Foo.goal',line:2,role:'statement'}];
  const result=f.run();assert.equal(result.status,0,result.stdout+result.stderr);
  const html=fs.readFileSync(f.htmlPath,'utf8');
  assert.match(html,/Unproved challenge\/template/);
  assert.match(html,/Target specification or assumption only/);
});

test('a child excerpt of replacement text keeps proposal styling and original source offsets', (t) => {
  const f=fixture(t);
  const source=f.currentPaperSource.replace('A covered theorem.','\\AIreplace{Old covered theorem.}{\nNew covered theorem.\nMore proposed text.}');
  fs.writeFileSync(path.join(f.paper.repo,'human_readable_main.tex'),source);
  git(f.paper.repo,'add','human_readable_main.tex');
  execFileSync('git',['-C',f.paper.repo,'-c','user.name=Audit Test','-c','user.email=audit@example.test','commit','-qm','replacement fixture']);
  f.map.sources.paper.commit=git(f.paper.repo,'rev-parse','HEAD');
  f.map.items[0].tex_lines=[6,10];f.map.items[1].tex_lines=[11,23];
  f.map.items.push({...f.map.items[0],id:'child',label:undefined,tex_lines:[8,8]});
  const result=f.run();assert.equal(result.status,0,result.stdout+result.stderr);
  const html=fs.readFileSync(f.htmlPath,'utf8');const card=html.split('id="item-child"')[1].split('</section>')[0];
  assert.match(card,/Excerpt from a proposed replacement/);
  assert.match(card,/<span class="ai-add">New covered theorem\./);
  assert.doesNotMatch(card,/Old covered theorem/);
});

// A historical duplicate must not redirect a current equation reference.
test('commented historical labels do not shadow active equation targets', (t) => {
  const f = fixture(t);
  const source = f.currentPaperSource.replace('A covered theorem.', 'A covered theorem. \\label{eq:active}')
    .replace('An unlabelled definition;', '% \\label{eq:active}\nAn unlabelled definition; see \\eqref{eq:active};');
  fs.writeFileSync(path.join(f.paper.repo, 'human_readable_main.tex'), source);
  git(f.paper.repo, 'add', 'human_readable_main.tex');
  execFileSync('git', ['-C', f.paper.repo, '-c', 'user.name=Audit Test', '-c', 'user.email=audit@example.test', 'commit', '-qm', 'historical label']);
  f.map.sources.paper.commit = git(f.paper.repo, 'rev-parse', 'HEAD');
  f.map.extra_refs['eq:active'] = 'Active';
  f.map.items[0].tex_lines = [6, 8];
  f.map.items[1].tex_lines = [9, 22];
  const result = f.run();
  assert.equal(result.status, 0, result.stdout + result.stderr);
  const html = fs.readFileSync(f.htmlPath, 'utf8');
  assert.match(html, /href="#item-thm">\(Active\)<\/a>/);
});
