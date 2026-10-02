#!/usr/bin/env node
// Preparation/final-run utility for literal Stafford paper-to-Lean anchors.
// The declaration resolver is loaded verbatim from paper_lean_audit/lean.mjs;
// only its unused texhtml import is replaced so katex/npm installs are not needed.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const fail = (s) => { throw new Error(s); };
function git(repo, args, input) {
  const r = spawnSync('git', ['-C', repo, ...args], { input, encoding: 'utf8' });
  if (r.status !== 0) fail(`git ${args.join(' ')} failed: ${(r.stderr || r.stdout).trim()}`);
  return r.stdout;
}
function parseArgs(argv) {
  const out = { apply: false, preparationOnly: false, patchout: null };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--apply') out.apply = true;
    else if (a === '--preparation-only') out.preparationOnly = true;
    else if (a === '--patch-out') {
      if (!argv[i + 1]) fail('missing value after --patch-out');
      out.patchout = argv[++i];
    }
    else if (['--paper','--formal','--formal-commit','--library','--library-commit'].includes(a)) {
      if (!argv[i + 1]) fail(`missing value after ${a}`);
      out[a.slice(2).replaceAll('-', '')] = argv[++i];
    } else fail(`unknown argument: ${a}`);
  }
  for (const k of ['paper','formal','formalcommit','library','librarycommit']) if (!out[k]) fail(`required option missing: --${k.replace(/[A-Z]/g, x => '-' + x.toLowerCase())}`);
  for (const [label, repo, rev] of [['formal',out.formal,out.formalcommit],['library',out.library,out.librarycommit]]) {
    if (!/^[0-9a-f]{40}$/.test(rev)) fail(`${label} commit must be a full 40-character lowercase object id`);
    const resolved = git(repo, ['rev-parse', `${rev}^{commit}`]).trim();
    if (resolved !== rev) fail(`${label} input is not the exact supplied commit`);
  }
  return out;
}
function sha(s) { return crypto.createHash('sha256').update(s).digest('hex'); }
function getObject(repo, commit, file) {
  return git(repo, ['show', `${commit}:${file}`]);
}
async function loadResolver(formalRepo, formalCommit) {
  let source = getObject(formalRepo, formalCommit, 'tools/paper_lean_audit/lean.mjs');
  const importLine = "import { escapeHtml } from './texhtml.mjs';";
  if (!source.includes(importLine)) fail('expected resolver import missing at pinned formal commit');
  source = source.replace(importLine, 'const escapeHtml = (s) => s;');
  const url = `data:text/javascript;base64,${Buffer.from(source).toString('base64')}`;
  return {module: await import(url), digest: sha(source)};
}
function checkCleanRelevant(repo, commit, files, allowDirty) {
  const dirty = [];
  for (const f of files) {
    const obj = getObject(repo, commit, f);
    const diskPath = path.join(repo, f);
    if (!fs.existsSync(diskPath) || fs.readFileSync(diskPath, 'utf8') !== obj) dirty.push(f);
    const indexed = spawnSync('git', ['-C',repo,'show',`:${f}`], {encoding:'utf8'});
    if (indexed.status !== 0 || indexed.stdout !== obj) if (!dirty.includes(f)) dirty.push(f);
  }
  if (dirty.length && !allowDirty) fail(`referenced source files differ from exact commit in index/worktree: ${dirty.join(', ')}`);
  return dirty;
}
function patchFor(changes) {
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'stafford38-anchor-'));
  try {
    let out = '';
    for (const [file, change] of changes) {
      const a = path.join(temp, 'old'); const b = path.join(temp, 'new');
      fs.writeFileSync(a, change.before); fs.writeFileSync(b, change.after);
      const r = spawnSync('diff', ['-u','-L',`a/${file}`,'-L',`b/${file}`,a,b], {encoding:'utf8'});
      if (r.status === 1) out += r.stdout;
      else if (r.status !== 0) fail(`diff failed for ${file}: ${r.stderr}`);
    }
    return out;
  } finally { fs.rmSync(temp, {recursive:true,force:true}); }
}

try {
  const o = parseArgs(process.argv.slice(2));
  const loaded = await loadResolver(o.formal,o.formalcommit);
  const resolver = loaded.module;
  const teX = ['human_readable_main.tex','ai_review.tex','lean_proof_details.tex'];
  const before = new Map(teX.map(f => [f, fs.readFileSync(path.join(o.paper,f),'utf8')]));
  const after = new Map(before);
  const refs = [];
  const refRe = /\\(leandecl|leanlib)\{([^}]+)\}\{([^}]+)\}\{([^}]+)\}/g;
  for (const file of teX) {
    const text = before.get(file); let m;
    while ((m = refRe.exec(text))) {
      if (!/^\d+$/.test(m[3])) continue; // macro signature/comment examples
      refs.push({paperFile:file, paperLine:text.slice(0,m.index).split('\n').length,
        macro:m[1], sourceFile:m[2], line:Number(m[3]), name:m[4], start:m.index, end:refRe.lastIndex});
    }
  }
  if (!refs.length) fail('no literal source references found');
  const grouped = new Map();
  for (const r of refs) {
    const formal = r.macro === 'leandecl';
    const repo = formal ? o.formal : o.library;
    const commit = formal ? o.formalcommit : o.librarycommit;
    const key = `${formal?'formal':'library'}:${r.sourceFile}`;
    if (!grouped.has(key)) grouped.set(key,{repo,commit,file:r.sourceFile,macro:r.macro,bytes:getObject(repo,commit,r.sourceFile)});
  }
  const dirtyFormal = checkCleanRelevant(o.formal,o.formalcommit,[...grouped.values()].filter(x=>x.macro==='leandecl').map(x=>x.file),o.preparationOnly);
  const dirtyLibrary = checkCleanRelevant(o.library,o.librarycommit,[...grouped.values()].filter(x=>x.macro==='leanlib').map(x=>x.file),o.preparationOnly);
  const updates = new Map(); const manifestRefs = [];
  const resolutionCache = new Map();
  for (const r of refs) {
    const key = `${r.macro==='leandecl'?'formal':'library'}:${r.sourceFile}`;
    const source = grouped.get(key).bytes;
    const cacheKey=`${key}:${r.name}`; let all=resolutionCache.get(cacheKey);
    if (!all) {
      all = new Map();
      // Asking the existing resolver at each source line reveals every exact-FQN
      // match, while retaining its masking, scope and visibility rules.
      const sourceLineCount=source.split('\n').length;
      for (let hint=1; hint<=sourceLineCount; hint++) {
        const d = resolver.findDeclaration(source,r.name,hint);
        if (d?.exact && d.qualified.replace(/^_root_\./,'') === r.name) all.set(d.line,d);
      }
      resolutionCache.set(cacheKey,all);
    }
    if (all.size !== 1) fail(`${r.macro} ${r.sourceFile} ${r.name}: expected one exact declaration, found ${all.size}`);
    const d = [...all.values()][0];
    if (!d.exported || ['private','local'].includes(d.visibility)) fail(`${r.name}: declaration is ${d.visibility}, not exported`);
    const oldText = before.get(r.paperFile); let newText = updates.get(r.paperFile) ?? oldText;
    // Offsets refer to original text. Apply edits right-to-left below.
    manifestRefs.push({...r, targetLine:d.line, targetName:d.qualified,
      lineChanged:d.line!==r.line, sourceCommit:grouped.get(key).commit});
    if (d.line !== r.line) {
      const raw = oldText.slice(r.start,r.end);
      const changed = raw.replace(`}{${r.line}}{`, `}{${d.line}}{`);
      if (changed === raw) fail(`could not isolate literal line argument at ${r.paperFile}:${r.paperLine}`);
      const edits = updates.get(`${r.paperFile}:edits`) ?? [];
      edits.push({start:r.start,end:r.end,changed}); updates.set(`${r.paperFile}:edits`,edits);
    }
  }
  for (const f of teX) {
    const edits = updates.get(`${f}:edits`) ?? []; let text=before.get(f);
    for (const e of edits.sort((a,b)=>b.start-a.start)) text=text.slice(0,e.start)+e.changed+text.slice(e.end);
    if (f==='ai_review.tex') {
      for (const [macro,commit] of [['leanrepo',o.formalcommit],['leanlibrepo',o.librarycommit]]) {
        const re=new RegExp(`(\\\\newcommand\\{\\\\${macro}\\}\\{https://github\\.com/[^/}]+/[^/}]+/blob/)[0-9a-f]{40}(\\})`,'g');
        let count=0; text=text.replace(re,(_m,a,b)=>{count++;return `${a}${commit}${b}`;});
        if (count!==1) fail(`expected exactly one ${macro} commit pin, found ${count}`);
      }
    }
    if (text!==before.get(f)) after.set(f,text);
  }
  const changes=[...after].filter(([f,s])=>s!==before.get(f)).map(([f,s])=>[f,{before:before.get(f),after:s}]);
  const patch=patchFor(changes);
  const patchPath=o.patchout ?? path.join(path.dirname(fileURLToPath(import.meta.url)),'anchor-refresh.patch');
  const patchDir=path.dirname(patchPath); fs.mkdirSync(patchDir,{recursive:true});
  const patchTmp=path.join(patchDir,`.${path.basename(patchPath)}.${process.pid}.tmp`);
  fs.writeFileSync(patchTmp,patch); fs.renameSync(patchTmp,patchPath);
  const manifest={preparationOnly:o.preparationOnly,mode:o.apply?'apply':'dry-run',paperDirectory:o.paper,
    formal:{repository:o.formal,commit:o.formalcommit,dirtyReferencedFiles:dirtyFormal},
    library:{repository:o.library,commit:o.librarycommit,dirtyReferencedFiles:dirtyLibrary},
    references:refs.length,changedReferences:manifestRefs.filter(x=>x.lineChanged).length,
    sourceIntegrity:'Lean bytes read with git show from exact commits; exact FQN/export checks used existing paper_lean_audit resolver',
    resolver:{formalCommit:o.formalcommit,path:'tools/paper_lean_audit/lean.mjs',sha256:loaded.digest},
    paperInputs:Object.fromEntries(teX.map(f=>[f,sha(before.get(f))])),
    patchFile:patchPath,patchSha256:sha(patch),patchBytes:Buffer.byteLength(patch),
    proposedFiles:changes.map(([f,c])=>({file:f,beforeSha256:sha(c.before),afterSha256:sha(c.after)})),
    changedAnchors:manifestRefs.filter(x=>x.lineChanged).map(r=>`${r.paperFile}:${r.paperLine} ${r.name} ${r.line}->${r.targetLine}`)};
  if (o.apply) {
    if (o.preparationOnly) fail('--apply is disabled with --preparation-only');
    for (const f of teX) if (fs.readFileSync(path.join(o.paper,f),'utf8')!==before.get(f)) fail(`paper input changed during run: ${f}`);
    git(o.paper,['apply','--whitespace=error','-'],patch);
    manifest.applied=true;
  }
  process.stdout.write(JSON.stringify(manifest,null,2)+'\n');
} catch (e) { process.stderr.write(`anchor refresh refused: ${e.message}\n`); process.exitCode=1; }
