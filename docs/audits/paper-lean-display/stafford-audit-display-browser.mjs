import { chromium } from '/home/ert/proj/stafford38/tools/paper_lean_audit/node_modules/playwright-core/index.mjs';
import assert from 'node:assert/strict';
const browser = await chromium.launch({executablePath:'/usr/bin/chromium',headless:true,args:['--no-sandbox']});
try {
 const page=await browser.newPage({viewport:{width:1600,height:1100}});
 await page.goto('file:///tmp/stafford-audit-display-final-reviewed/stafford38-paper-lean-audit.html');
 const abstract=page.locator('[id="item-abstract"]');
 const text=await abstract.innerText();
 assert.match(text,/∀ \(k : Type/);
 assert.match(text,/∃ F R S/);
 assert.match(text,/ell \^ bernsteinDegree k d/);
 const conv=page.locator('[id="item-conv:H"]');
 const convention=await conv.innerText();
 assert.match(convention,/Notation convention, not a theorem/);
 assert.match(convention,/Sum.inl _ => 0/);assert.match(convention,/Sum.inr _ => 1/);
 assert.match(convention,/AIcomment DUP-01/);
 assert.doesNotMatch(convention,/not covered by an AIcomment/);
 const hidden=await conv.locator('.katex-mathml').first().evaluate(el=>({position:getComputedStyle(el).position,clip:getComputedStyle(el).clip,width:el.getBoundingClientRect().width}));
 assert.equal(hidden.position,'absolute');assert.equal(hidden.width,1);
 const helpers=page.locator('details.helpers').first();await helpers.locator(':scope > summary').click();
 assert.equal(await helpers.getAttribute('open'),'');
 assert.ok(await helpers.locator('pre').count()>0);
 await conv.screenshot({path:'/tmp/stafford-audit-display-convention.png'});
 console.log(JSON.stringify({cards:await page.locator('section.card').count(),statementDefinitions:await page.locator('.statement-definitions').count(),unexpanded:await page.locator('.lean-note').filter({hasText:'not expanded here'}).count(),mathAccessibilityLayer:hidden,checks:'abstract quantifiers, coordinate predicate, weight branches, linked AI comment, expandable full signatures passed'}));
} finally {await browser.close();}
