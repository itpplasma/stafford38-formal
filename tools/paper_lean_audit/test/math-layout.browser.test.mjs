// Independent Chromium geometry oracle for tagged display math. This exercises
// the rendered page and CSS, rather than checking how the renderer builds it.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright-core';
import { TexRenderer } from '../texhtml.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const toolDir = path.resolve(here, '..');
const katexDir = path.join(toolDir, 'node_modules/katex/dist');
const executablePath = process.env.CHROMIUM_PATH ?? ['/usr/bin/chromium', '/opt/pw-browsers/chromium-1194/chrome-linux/chrome']
  .find((candidate) => fs.existsSync(candidate));

function fixtureMath() {
  const product = String.raw`\prod_{i=0}^{m} (E-i)`;
  const left = Array.from({ length: 10 }, () => product).join(String.raw` + `);
  const right = Array.from({ length: 3 }, () => product).join(String.raw` + `);
  const tex = String.raw`\begin{equation}${left} = ${right}\tag{Wide-01}\end{equation}`;
  const renderer = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = renderer.text(tex);
  assert.deepEqual(renderer.warnings, []);
  return html;
}

test('wide tagged displays keep the tag beside a separately scrollable formula', async (t) => {
  assert.ok(executablePath, 'set CHROMIUM_PATH or install Chromium to run the layout oracle');
  const rendered = fixtureMath();
  const css = fs.readFileSync(path.join(toolDir, 'style.css'), 'utf8');
  const katexCss = fs.readFileSync(path.join(katexDir, 'katex.min.css'), 'utf8');
  const server = createServer((request, response) => {
    if (request.url === '/katex.css') {
      response.writeHead(200, { 'content-type': 'text/css' }); response.end(katexCss); return;
    }
    if (request.url?.startsWith('/fonts/')) {
      const font = path.join(katexDir, 'fonts', path.basename(request.url));
      if (fs.existsSync(font)) {
        response.writeHead(200, { 'content-type': font.endsWith('.woff2') ? 'font/woff2' : 'font/woff' });
        response.end(fs.readFileSync(font)); return;
      }
      response.writeHead(404); response.end(); return;
    }
    response.writeHead(200, { 'content-type': 'text/html; charset=utf-8' });
    response.end(`<!doctype html><meta charset="utf-8"><link rel="stylesheet" href="/katex.css"><style>${css}</style><main style="max-width:none;padding:0;margin:0"><div id="host" class="col paper"><div class="tex">${rendered}</div></div></main>`);
  });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  let browser;
  try {
    browser = await chromium.launch({ executablePath, headless: true, args: ['--no-sandbox'] });
    const page = await browser.newPage({ viewport: { width: 1400, height: 900 } });
    await page.goto(`http://127.0.0.1:${server.address().port}`, { waitUntil: 'networkidle' });

    async function measure(width) {
      await page.setViewportSize({ width, height: 900 });
      await page.evaluate(() => document.fonts.ready);
      return page.evaluate(() => {
        const host = document.querySelector('#host');
        const layout = document.querySelector('.dmath-layout');
        const formula = document.querySelector('.dmath-formula');
        const tag = document.querySelector('.dmath-tag');
        const rect = (el) => { const r = el.getBoundingClientRect(); return { left: r.left, right: r.right, width: r.width }; };
        return {
          host: rect(host), layout: rect(layout), formula: rect(formula), tag: rect(tag),
          formulaClient: formula.clientWidth, formulaScroll: formula.scrollWidth,
          overflowX: getComputedStyle(formula).overflowX,
          scrollHint: formula.title,
          tagText: tag.innerText.trim(),
        };
      });
    }

    const normal = await measure(1400);
    assert.equal(await page.locator('.dmath-tag').getAttribute('aria-hidden'), 'true',
      'MathML already carries the equation label, so the detached visual copy is hidden from assistive technology');
    assert.ok(normal.formula.right < normal.tag.left, `tag must be outside the formula at normal width: ${JSON.stringify(normal)}`);
    assert.ok(normal.tag.right <= normal.layout.right + 1, `tag must remain in the display at normal width: ${JSON.stringify(normal)}`);
    assert.ok(normal.formulaScroll <= normal.formulaClient + 1, `fixture should fit at normal width: ${JSON.stringify(normal)}`);
    assert.equal(normal.tagText, '(Wide-01)');

    const narrow = await measure(400);
    assert.ok(narrow.formula.right < narrow.tag.left, `tag must not overlap formula at narrow width: ${JSON.stringify(narrow)}`);
    assert.ok(narrow.tag.right <= narrow.layout.right + 1, `tag must remain visible at narrow width: ${JSON.stringify(narrow)}`);
    assert.ok(narrow.formulaScroll > narrow.formulaClient, `wide formula must expose horizontal scrolling at narrow width: ${JSON.stringify(narrow)}`);
    assert.ok(['auto', 'scroll'].includes(narrow.overflowX), `formula overflow must be scrollable: ${JSON.stringify(narrow)}`);
    assert.match(narrow.scrollHint, /scroll horizontally/i);
    const scrollPosition = await page.evaluate(() => {
      const formula = document.querySelector('.dmath-formula');
      formula.scrollLeft = formula.scrollWidth;
      return { left: formula.scrollLeft, max: formula.scrollWidth - formula.clientWidth };
    });
    assert.ok(scrollPosition.max > 0 && scrollPosition.left >= scrollPosition.max - 1,
      `the full formula extent must be reachable by horizontal scrolling: ${JSON.stringify(scrollPosition)}`);
  } finally {
    await browser?.close();
    server.close();
  }
});
