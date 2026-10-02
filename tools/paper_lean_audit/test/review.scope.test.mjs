import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { chromium } from 'playwright-core';
import { reviewScopeOptions } from '../review-scope.mjs';
import { readFile } from 'node:fs/promises';

const reviewJs = await readFile(new URL('../review.js', import.meta.url), 'utf8');
const meta = { version: 'scope-check', paper: 'a'.repeat(40), formal: 'b'.repeat(40), checks: ['statement', 'route', 'issues'] };
const htmlFor = (items) => {
  const cards = items.map((it, n) => `<section id="item-${it.id}" class="card" data-sev="0" data-review-scope="${it.review_scope ?? 'publication'}"><a data-toc="${it.id}"></a><div class="review" data-item="${it.id}" data-hash="${n.toString(16).padStart(16, '0')}"><input type="checkbox" data-check="statement"><input type="checkbox" data-check="route"><input type="checkbox" data-check="issues"><textarea data-notes></textarea></div></section>`).join('');
  return `<!doctype html><body><nav class="side"><ol class="toc"><li><a href="#challenge-definitions">Challenge definitions</a></li></ol></nav><section id="challenge-definitions"><a class="definition-link" href="#definition-one">jump to definition</a><details id="definition-index"><summary>Definitions entering the challenge</summary><details id="definition-one"><summary>One pinned definition</summary></details></details></section><div class="review-tools"><div id="progress"></div><button id="export"></button><input id="import" type="file"><input id="reviewer"><input id="filter"><input id="only-issues" type="checkbox"><input id="only-open" type="checkbox"><input id="clean-text" type="checkbox"><select id="review-scope">${reviewScopeOptions(items)}</select></div>${cards}<script>window.AUDIT_META=${JSON.stringify(meta)};</script></body>`;
};

async function run(items, assertions) {
  const server = createServer((_, res) => { res.writeHead(200, { 'content-type': 'text/html' }); res.end(htmlFor(items)); });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  let browser;
  try {
    browser = await chromium.launch({ executablePath: '/usr/bin/chromium', headless: true, args: ['--no-sandbox'] });
    const page = await browser.newPage();
    await page.goto('http://127.0.0.1:' + server.address().port);
    await page.addScriptTag({ content: reviewJs });
    await assertions(page);
  } finally {
    if (browser) await browser.close();
    await new Promise((resolve) => server.close(resolve));
  }
}

test('default review shows every mathematical card and leaves context available on demand', async () => {
  const items = [{ id: 'main', review_scope: 'publication' }, { id: 'global-stafford', review_scope: 'publication' }, { id: 'prior-art', review_scope: 'reference' }, { id: 'workflow', review_scope: 'reference' }];
  await run(items, async (page) => {
    assert.equal(await page.locator('#review-scope').inputValue(), 'publication');
    assert.equal(await page.locator('#review-scope option[value="alternative"]').count(), 0);
    assert.equal(await page.locator('.card:not(.hidden)').count(), 2);
    assert.equal(await page.locator('#item-global-stafford').evaluate((el) => el.classList.contains('hidden')), false);
    assert.equal(await page.locator('#item-prior-art').evaluate((el) => el.classList.contains('hidden')), true);
    await page.locator('#review-scope').selectOption('all');
    assert.equal(await page.locator('.card:not(.hidden)').count(), 4);
    assert.equal(await page.locator('#item-prior-art').evaluate((el) => el.classList.contains('hidden')), false);
    await page.locator('.toc a[href="#challenge-definitions"]').click();
    await page.locator('.definition-link').click();
    assert.equal(await page.locator('#definition-index').evaluate((el) => el.open), true);
    assert.equal(await page.locator('#definition-one').evaluate((el) => el.open), true);
  });
});

test('a map with a real alternate route offers and filters that scope', async () => {
  const items = [{ id: 'main', review_scope: 'publication' }, { id: 'prior-art', review_scope: 'reference' }, { id: 'variant', review_scope: 'alternative' }];
  await run(items, async (page) => {
    assert.equal(await page.locator('#review-scope option[value="alternative"]').count(), 1);
    await page.locator('#review-scope').selectOption('alternative');
    assert.equal(await page.locator('.card:not(.hidden)').count(), 1);
    assert.equal(await page.locator('.card:not(.hidden) .review').getAttribute('data-item'), 'variant');
  });
});
