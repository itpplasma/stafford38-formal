import { chromium } from '/home/ert/proj/stafford38/tools/paper_lean_audit/node_modules/playwright-core/index.mjs';
import {execFileSync} from 'node:child_process';
import fs from 'node:fs';
import assert from 'node:assert/strict';
const map=JSON.parse(fs.readFileSync('/home/ert/proj/stafford38-formal/tools/paper_lean_audit/paper-lean-map.json'));
const repos={formal:'/home/ert/proj/stafford38-formal',library:'/home/ert/proj/algebraic-analysis',global:'/home/ert/proj/global-stafford-formal',mathlib:'/home/ert/proj/stafford38-formal/.lake/packages/mathlib'};
const browser=await chromium.launch({executablePath:'/usr/bin/chromium',headless:true,args:['--no-sandbox']});
try {
 const page=await browser.newPage();await page.goto('file:///tmp/stafford-audit-display-final-reviewed/stafford38-paper-lean-audit.html');
 const blocks=await page.locator('section.card pre.lean-src').evaluateAll(elements=>elements.map(el=>({name:el.closest('.lean')?.querySelector('.lean-name')?.textContent,url:el.previousElementSibling?.tagName==='A' ? el.previousElementSibling.href : el.closest('.lean')?.querySelector('.lean-name')?.href,code:el.textContent})));
 const cache=new Map();let checked=0;
 for(const block of blocks){
  if(!block.code)continue;
  const url=new URL(block.url),m=/^\/([^/]+\/[^/]+)\/blob\/([^/]+)\/(.+)$/.exec(url.pathname),range=/^#L(\d+)(?:-L(\d+))?$/.exec(url.hash);
  assert.ok(m&&range,'exact source range '+block.name);
  const key=Object.keys(repos).find(key=>map.sources[key].repo===m[1]);assert.ok(key,'known source '+m[1]);assert.equal(m[2],map.sources[key].commit);
  const cacheKey=key+':'+m[3];if(!cache.has(cacheKey))cache.set(cacheKey,execFileSync('git',['-C',repos[key],'show',m[2]+':'+m[3]],{encoding:'utf8'}));
  const source=cache.get(cacheKey).split('\n').slice(Number(range[1])-1,Number(range[2]??range[1])).join('\n').trimEnd();
  const shown=block.code.replace(/\n  …$/,'').trimEnd();assert.ok(source.startsWith(shown),'source snippet differs '+block.name);checked++;
 }
 const cards=await page.locator('section.card').evaluateAll(elements=>elements.map(el=>({id:el.id,coverage:el.querySelector('.lean-coverage')?.textContent,leanBlocks:el.querySelectorAll('.lean pre').length,errors:el.querySelectorAll('.lean.missing').length,reviewHash:el.querySelector('[data-hash]')?.dataset.hash})));
 assert.equal(cards.length,55);assert.ok(cards.every(card=>card.coverage&&card.reviewHash&&!card.errors));
 const report={formalReviewBase:'87bce83806c757ade36d455d785b506ebd03a1b2',cardsChecked:cards.length,sourceSnippetsChecked:checked,pinnedFilesChecked:cache.size,result:'passed',oracle:'Every displayed Lean excerpt is a literal prefix of its independently read pinned Git source range; every card has coverage explanation, review hash and no missing declaration.',cards};
 fs.writeFileSync('/tmp/stafford-audit-all-blocks-check.json',JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({...report,cards:undefined}));
}finally{await browser.close();}
