// Exercise the shipped browser controller in Chromium with independent state
// and export oracles; these tests do not inspect implementation source text.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { chromium } from 'playwright-core';

const here = path.dirname(fileURLToPath(import.meta.url));
const reviewScript = path.resolve(here, '../review.js');
const executablePath = process.env.CHROMIUM_PATH ??
  ['/usr/bin/chromium', '/opt/pw-browsers/chromium-1194/chrome-linux/chrome', '/opt/pw-browsers/chromium']
    .find((candidate) => existsSync(candidate));
const meta = {
  version: 'v2',
  paper: 'a'.repeat(40),
  formal: 'b'.repeat(40),
  checks: ['statement', 'route', 'issues'],
};
const currentKey = 'stafford38-audit:v2:' + meta.paper.slice(0, 12) + ':' + meta.formal.slice(0, 12);
const currentHash = 'c'.repeat(16);

function fixture() {
  const controls = '<div class="review-tools">' +
    '<div id="progress"></div><button id="export">Export</button>' +
    '<input id="import" type="file"><input id="reviewer">' +
    '<input id="filter"><input id="only-issues" type="checkbox">' +
    '<input id="only-open" type="checkbox"><input id="clean-text" type="checkbox">' +
    '</div>';
  const card = (id, title) => '<section class="card" data-sev="0"><h2>' + title + '</h2>' +
    '<a data-toc="' + id + '"></a>' +
    '<div class="review" data-item="' + id + '" data-hash="' + currentHash + '">' +
    '<input type="checkbox" data-check="statement">' +
    '<input type="checkbox" data-check="route">' +
    '<input type="checkbox" data-check="issues">' +
    '<textarea data-notes></textarea></div></section>';
  return '<!doctype html><meta charset="utf-8"><body>' + controls +
    card('item-one', 'First claim') + card('item-two', 'Second claim') +
    '<script>window.AUDIT_META = ' + JSON.stringify(meta) + ';</script></body>';
}

async function openReview(browser, url, storage = {}) {
  const page = await browser.newPage();
  await page.goto(url);
  await page.evaluate((entries) => {
    for (const [key, value] of Object.entries(entries)) localStorage.setItem(key, JSON.stringify(value));
  }, storage);
  await page.addScriptTag({ path: reviewScript });
  return page;
}

function signedItem({ reviewer = 'Ada', hash = currentHash, notes = 'reviewed' } = {}) {
  return {
    checks: { statement: true, route: true, issues: true },
    reviewer,
    notes,
    updated: '2026-09-01T12:00:00.000Z',
    hash,
  };
}

test('browser review state is revision-safe, attributable, and importable without corruption', async (t) => {
  assert.ok(executablePath, 'set CHROMIUM_PATH or install Chromium to run browser tests');
  const server = createServer((_, response) => {
    response.writeHead(200, { 'content-type': 'text/html; charset=utf-8' });
    response.end(fixture());
  });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  const url = 'http://127.0.0.1:' + server.address().port;
  let browser;
  try {
    browser = await chromium.launch({ executablePath, headless: true, args: ['--no-sandbox'] });
    await t.test('editing a stale card discards old checkmarks before stamping the new hash', async () => {
      const page = await openReview(browser, url, {
        [currentKey]: {
          reviewer: 'Ada',
          items: { 'item-one': signedItem({ hash: '1'.repeat(16) }) },
        },
      });
      const review = page.locator('[data-item="item-one"]');
      assert.equal(await review.evaluate((el) => el.classList.contains('stale')), true);
      assert.equal(await review.evaluate((el) => el.classList.contains('complete')), false);
      await review.locator('[data-notes]').fill('edited after the paper changed');
      assert.deepEqual(await review.locator('[data-check]').evaluateAll((els) => els.map((el) => el.checked)), [false, false, false]);
      assert.equal(await review.evaluate((el) => el.classList.contains('stale')), false);
      assert.equal(await review.evaluate((el) => el.classList.contains('complete')), false);
      assert.equal(await page.locator('#progress').textContent(), 'Signed off: 0 / 2');
      await page.close();
    });

    await t.test('older pin-key reviews are recovered and visibly marked stale', async () => {
      const oldKey = 'stafford38-audit:v1:' + 'd'.repeat(12) + ':' + 'e'.repeat(12);
      const oldItem = signedItem({ hash: '2'.repeat(16) });
      delete oldItem.reviewer;
      const page = await openReview(browser, url, {
        [oldKey]: {
          reviewer: 'Lin',
          items: { 'item-two': oldItem },
        },
      });
      const review = page.locator('[data-item="item-two"]');
      assert.equal(await review.evaluate((el) => el.classList.contains('stale')), true);
      assert.equal(await review.evaluate((el) => el.classList.contains('complete')), false);
      assert.equal(await review.locator('[data-check="statement"]').isChecked(), true);
      const migrated = await page.evaluate((key) => JSON.parse(localStorage.getItem(key)), currentKey);
      assert.equal(migrated.items['item-two'].reviewer, 'Lin');
      assert.equal(migrated.items['item-two'].hash, '2'.repeat(16));
      await page.close();
    });

    await t.test('checks without a revision hash cannot become a sign-off', async () => {
      const page = await openReview(browser, url);
      const imported = {
        format: 'stafford38-paper-lean-review/1',
        mapping_version: meta.version,
        paper_commit: meta.paper,
        formal_commit: meta.formal,
        reviewer: 'Ada',
        items: { 'item-one': { checks: { statement: true, route: true, issues: true }, reviewer: 'Ada' } },
      };
      await page.locator('#import').setInputFiles({
        name: 'review.json', mimeType: 'application/json', buffer: Buffer.from(JSON.stringify(imported)),
      });
      const review = page.locator('[data-item="item-one"]');
      assert.equal(await review.evaluate((el) => el.classList.contains('complete')), false);
      assert.equal(await review.evaluate((el) => el.classList.contains('stale')), true);
      assert.equal(await page.locator('#progress').textContent(), 'Signed off: 0 / 2');
      await page.close();
    });

    await t.test('invalid JSON and malformed review objects leave existing state untouched', async () => {
      const page = await openReview(browser, url, {
        [currentKey]: { reviewer: 'Alice', items: { 'item-one': signedItem({ reviewer: 'Alice' }) } },
      });
      const pageErrors = [];
      page.on('pageerror', (error) => pageErrors.push(error.message));
      await page.locator('#import').setInputFiles({
        name: 'broken.json', mimeType: 'application/json', buffer: Buffer.from('{ broken'),
      });
      assert.match(await page.locator('#review-status').textContent(), /Import failed: invalid JSON/);
      assert.equal(await page.locator('#reviewer').inputValue(), 'Alice');
      assert.equal(await page.locator('[data-item="item-one"]').evaluate((el) => el.classList.contains('complete')), true);

      const malformed = {
        format: 'stafford38-paper-lean-review/1',
        mapping_version: meta.version,
        paper_commit: meta.paper,
        formal_commit: meta.formal,
        reviewer: 'Mallory',
        items: [],
      };
      await page.locator('#import').setInputFiles({
        name: 'malformed.json', mimeType: 'application/json', buffer: Buffer.from(JSON.stringify(malformed)),
      });
      assert.match(await page.locator('#review-status').textContent(), /Review items must be an object/);
      assert.equal(await page.locator('#reviewer').inputValue(), 'Alice');
      assert.deepEqual(pageErrors, []);
      await page.close();
    });

    await t.test('a new reviewer cannot inherit another reviewer checks; export preserves attribution and revokes its URL', async () => {
      const page = await openReview(browser, url, {
        [currentKey]: {
          reviewer: 'Alice',
          items: {
            'item-one': signedItem({ reviewer: 'Alice' }),
            'item-two': signedItem({ reviewer: 'Alice' }),
          },
        },
      });
      await page.evaluate(() => {
        const create = URL.createObjectURL.bind(URL);
        const revoke = URL.revokeObjectURL.bind(URL);
        window.__urlEvents = [];
        window.__exportBlob = null;
        URL.createObjectURL = (blob) => {
          const url = create(blob);
          window.__exportBlob = blob;
          window.__urlEvents.push(['create', url]);
          return url;
        };
        URL.revokeObjectURL = (url) => {
          window.__urlEvents.push(['revoke', url]);
          revoke(url);
        };
      });
      await page.locator('#reviewer').fill('Bob');
      assert.equal(await page.locator('[data-item="item-two"] [data-reviewer-attribution]').textContent(), 'Recorded reviewer: Alice');
      await page.locator('[data-item="item-one"] [data-notes]').fill('Bob checked this card');
      assert.deepEqual(await page.locator('[data-item="item-one"] [data-check]').evaluateAll((els) => els.map((el) => el.checked)), [false, false, false]);
      assert.equal(await page.locator('[data-item="item-one"]').evaluate((el) => el.classList.contains('complete')), false);
      assert.equal(await page.locator('[data-item="item-one"] [data-reviewer-attribution]').textContent(), 'Recorded reviewer: Bob');
      assert.equal(await page.locator('[data-item="item-two"]').evaluate((el) => el.classList.contains('complete')), true);

      await page.locator('#export').click();
      await page.waitForFunction(() => window.__urlEvents.some((event) => event[0] === 'revoke'));
      const exported = await page.evaluate(async () => JSON.parse(await window.__exportBlob.text()));
      assert.equal(exported.reviewer, 'Bob');
      assert.equal(exported.items['item-one'].reviewer, 'Bob');
      assert.deepEqual(Object.values(exported.items['item-one'].checks), [false, false, false]);
      assert.equal(exported.items['item-two'].reviewer, 'Alice');
      assert.deepEqual(Object.values(exported.items['item-two'].checks), [true, true, true]);
      const urls = await page.evaluate(() => window.__urlEvents);
      assert.equal(urls.length, 2);
      assert.equal(urls[0][0], 'create');
      assert.equal(urls[1][0], 'revoke');
      assert.equal(urls[0][1], urls[1][1]);
      await page.close();
    });

    await t.test('unnamed checked boxes are not exported as a sign-off', async () => {
      const page = await openReview(browser, url);
      await page.locator('[data-item="item-one"] [data-check="statement"]').check();
      assert.equal(await page.locator('[data-item="item-one"]').evaluate((el) => el.classList.contains('complete')), false);
      await page.evaluate(() => {
        const create = URL.createObjectURL.bind(URL);
        window.__exportBlob = null;
        URL.createObjectURL = (blob) => {
          window.__exportBlob = blob;
          return create(blob);
        };
      });
      await page.locator('#export').click();
      const exported = await page.evaluate(async () => JSON.parse(await window.__exportBlob.text()));
      assert.equal(exported.items['item-one'].reviewer, 'anonymous');
      assert.deepEqual(Object.values(exported.items['item-one'].checks), [false, false, false]);
      await page.close();
    });
  } finally {
    if (browser) await browser.close();
    await new Promise((resolve) => server.close(resolve));
  }
});


test('publication queue separates optional variants and blocks stale-version sign-offs', async () => {
  let site;
  let latest = { ...meta, generator: 'd'.repeat(64) };
  const server = createServer((request, response) => {
    if (request.url === '/version.json') {
      response.writeHead(200, { 'content-type': 'application/json' });
      response.end(JSON.stringify(latest)); return;
    }
    const scope = '<select id="review-scope"><option value="publication">Publication</option><option value="alternative">Alternatives</option><option value="all">All</option></select><div id="freshness"></div>';
    let html = fixture().replace('<div id="progress">', scope + '<div id="progress">');
    let count = 0;
    html = html.replace(/class="card"/g, () => 'class="card" data-review-scope="' + (++count === 1 ? 'publication' : 'alternative') + '"');
    html = html.replace(JSON.stringify(meta), JSON.stringify({ ...meta, generator: 'd'.repeat(64), live: site + '/' }));
    response.writeHead(200, { 'content-type': 'text/html' }); response.end(html);
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  site = 'http://127.0.0.1:' + server.address().port;
  const browser = await chromium.launch({ executablePath, headless: true, args: ['--no-sandbox'] });
  try {
    const page = await browser.newPage(); await page.goto(site);
    await page.evaluate(() => { window.setInterval = callback => { window.__checkLatest = callback; return 0; }; });
    await page.addScriptTag({ path: reviewScript });
    await page.addStyleTag({ path: path.resolve(here, '../style.css') });
    const first = page.locator('[data-item="item-one"]').locator('..');
    const second = page.locator('[data-item="item-two"]').locator('..');
    assert.equal(await first.isVisible(), true); assert.equal(await second.isVisible(), false);
    await page.locator('#review-scope').selectOption('alternative');
    assert.equal(await first.isVisible(), false); assert.equal(await second.isVisible(), true);
    await page.locator('#review-scope').selectOption('all');
    assert.equal(await first.isVisible(), true); assert.equal(await second.isVisible(), true);
    await page.waitForFunction(() => document.querySelector('#freshness').textContent === 'Current published review');
    await page.locator('[data-item="item-one"] [data-notes]').fill('Keep this review note');
    latest = { ...latest, version: 'v3' };
    await page.evaluate(() => window.__checkLatest());
    await page.waitForFunction(() => document.querySelector('#freshness').classList.contains('err'));
    assert.equal(await page.locator('[data-check]').first().isDisabled(), true);
    assert.equal(await page.locator('[data-item="item-one"] [data-notes]').inputValue(), 'Keep this review note');
    await page.close();
  } finally { await browser.close(); await new Promise(resolve => server.close(resolve)); }
});


test('definition jumps open the exact target and collapsed parents without signing off', async () => {
  const server=createServer((_request,response)=>{
    response.writeHead(200,{'content-type':'text/html'});
    response.end(fixture().replace('<script>window.AUDIT_META', '<a class="definition-link" href="#definition-mathlib:Field">Field</a><details><summary>Definitions</summary><details id="definition-mathlib:Field"><summary>Field</summary><pre>class Field extends CommRing, DivisionRing</pre></details></details><script>window.AUDIT_META'));
  });
  await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  const browser=await chromium.launch({executablePath,headless:true,args:['--no-sandbox']});
  try {
    const page=await openReview(browser,'http://127.0.0.1:'+server.address().port);
    await page.locator('[data-item="item-one"] [data-notes]').fill('Check factor order');
    await page.locator('a.definition-link').click();
    const target=page.locator('[id="definition-mathlib:Field"]');
    assert.equal(await target.evaluate(el=>el.open && el.parentElement.open),true);
    assert.equal(await target.locator('pre').isVisible(),true);
    assert.equal(await page.locator('[data-item="item-one"] [data-notes]').inputValue(),'Check factor order');
    assert.equal(await page.locator('[data-check]').first().isChecked(),false);
    await page.close();
  } finally {await browser.close();await new Promise(resolve=>server.close(resolve));}
});
