// Review state lives in this browser (localStorage) and is exported as JSON so
// sign-offs can be committed next to the mapping. Nothing is sent anywhere.
(function () {
  const meta = window.AUDIT_META;
  const format = 'stafford38-paper-lean-review/1';
  const prefix = 'stafford38-audit:';
  const key = prefix + meta.version + ':' + meta.paper.slice(0, 12) + ':' + meta.formal.slice(0, 12);
  const checkIds = [...meta.checks];
  const checkSet = new Set(checkIds);
  const boxes = [...document.querySelectorAll('.review')];
  const boxById = new Map(boxes.map((box) => [box.dataset.item, box]));
  const plainRecord = (value) => value !== null && typeof value === 'object' && !Array.isArray(value);
  const cleanReviewer = (value) => typeof value === 'string' ? value.trim() : '';
  const timestamp = (value) => {
    if (typeof value !== 'string' || !value) return -Infinity;
    const parsed = Date.parse(value);
    return Number.isFinite(parsed) ? parsed : -Infinity;
  };
  const emptyState = () => ({ reviewer: '', updated: '', lastEntry: '', items: Object.create(null) });

  function normalizeItem(raw, fallbackReviewer, strict) {
    if (!plainRecord(raw)) {
      if (strict) throw new Error('An item review must be an object.');
      return null;
    }
    if (strict && !plainRecord(raw.checks)) {
      throw new Error('Review checks must be an object.');
    }
    if (strict && raw.notes !== undefined && typeof raw.notes !== 'string') {
      throw new Error('Review notes must be text.');
    }
    if (strict && raw.reviewer !== undefined && typeof raw.reviewer !== 'string') {
      throw new Error('Item reviewer must be text.');
    }
    if (strict && raw.updated !== undefined &&
        (typeof raw.updated !== 'string' || (raw.updated && !Number.isFinite(Date.parse(raw.updated))))) {
      throw new Error('Item update time is invalid.');
    }
    if (strict && raw.hash !== undefined &&
        (typeof raw.hash !== 'string' || (raw.hash !== '' && !/^[a-f0-9]{16}$/i.test(raw.hash)))) {
      throw new Error('Item revision hash is invalid.');
    }

    const checks = Object.create(null);
    const rawChecks = plainRecord(raw.checks) ? raw.checks : {};
    for (const [id, checked] of Object.entries(rawChecks)) {
      if (!checkSet.has(id)) {
        if (strict) throw new Error('Unknown review check: ' + id + '.');
        continue;
      }
      if (typeof checked !== 'boolean') {
        if (strict) throw new Error('Review check ' + id + ' must be true or false.');
        continue;
      }
      checks[id] = checked;
    }
    return {
      checks,
      notes: typeof raw.notes === 'string' ? raw.notes : '',
      reviewer: Object.hasOwn(raw, 'reviewer') ? cleanReviewer(raw.reviewer) : cleanReviewer(fallbackReviewer),
      updated: typeof raw.updated === 'string' ? raw.updated : '',
      // A missing hash is retained as missing evidence and can never sign off.
      hash: typeof raw.hash === 'string' && /^[a-f0-9]{16}$/i.test(raw.hash) ? raw.hash : '',
    };
  }

  function normalizeStoredState(raw) {
    if (!plainRecord(raw) || !plainRecord(raw.items)) return null;
    const state = emptyState();
    state.reviewer = cleanReviewer(raw.reviewer);
    state.updated = typeof raw.updated === 'string' ? raw.updated : '';
    state.lastEntry = typeof raw.lastEntry === 'string' && boxById.has(raw.lastEntry) ? raw.lastEntry : '';
    for (const [id, item] of Object.entries(raw.items)) {
      if (!boxById.has(id)) continue;
      const normalized = normalizeItem(item, state.reviewer, false);
      if (normalized) state.items[id] = normalized;
    }
    return state;
  }

  function load() {
    const state = emptyState();
    let storage;
    try {
      storage = window.localStorage;
      const keys = [];
      for (let i = 0; i < storage.length; i++) {
        const candidate = storage.key(i);
        if (candidate && candidate.startsWith(prefix) && candidate !== key) keys.push(candidate);
      }
      // Read older pin/version keys first. The exact current key wins timestamp ties.
      keys.sort((a, b) => a.localeCompare(b));
      keys.push(key);
      let currentFound = false;
      let legacyFound = false;
      let reviewerSourceTime = -Infinity;
      for (const candidate of keys) {
        let parsed;
        try {
          const stored = storage.getItem(candidate);
          if (stored === null) continue;
          parsed = normalizeStoredState(JSON.parse(stored));
        } catch (_) {
          continue;
        }
        if (!parsed) continue;
        const isCurrent = candidate === key;
        if (isCurrent) {
          currentFound = true;
          state.reviewer = parsed.reviewer;
          state.updated = parsed.updated;
          state.lastEntry = parsed.lastEntry;
        } else {
          legacyFound = true;
          if (!currentFound) {
            const sourceTime = Math.max(timestamp(parsed.updated),
              ...Object.values(parsed.items).map((item) => timestamp(item.updated)));
            if (sourceTime > reviewerSourceTime) {
              reviewerSourceTime = sourceTime;
              state.reviewer = parsed.reviewer;
              state.updated = parsed.updated;
              state.lastEntry = parsed.lastEntry;
            }
          }
        }
        for (const [id, item] of Object.entries(parsed.items)) {
          const previous = state.items[id];
          const newer = previous && timestamp(item.updated) > timestamp(previous.updated);
          const currentTie = isCurrent && previous && timestamp(item.updated) === timestamp(previous.updated);
          if (!previous || newer || currentTie) {
            state.items[id] = item;
          }
        }
      }
      if (!currentFound && Object.keys(state.items).length) {
        state.updated = new Date().toISOString();
        save(state);
      } else if (currentFound && legacyFound) {
        // Persist per-item reviews recovered from older pin/version keys.
        save(state);
      }
    } catch (_) {
      return state;
    }
    return state;
  }

  function save(state) {
    try {
      state.updated = new Date().toISOString();
      window.localStorage.setItem(key, JSON.stringify(state));
    } catch (_) { /* storage unavailable */ }
  }

  function validateImport(data) {
    if (!plainRecord(data)) throw new Error('The file must contain a JSON object.');
    if (data.format !== format) throw new Error('This is not a Stafford paper–Lean review export.');
    if (typeof data.mapping_version !== 'string' || !data.mapping_version) {
      throw new Error('The mapping version is missing.');
    }
    for (const field of ['paper_commit', 'formal_commit']) {
      if (typeof data[field] !== 'string' || !/^[a-f0-9]{40}$/i.test(data[field])) {
        throw new Error('The ' + field.replace('_', ' ') + ' is invalid.');
      }
    }
    if (data.reviewer !== undefined && typeof data.reviewer !== 'string') {
      throw new Error('The reviewer name must be text.');
    }
    if (data.last_entry !== undefined && data.last_entry !== null &&
        (typeof data.last_entry !== 'string' || !boxById.has(data.last_entry))) {
      throw new Error('The last reviewed claim is unknown.');
    }
    if (!plainRecord(data.items)) throw new Error('Review items must be an object.');
    const incoming = emptyState();
    incoming.reviewer = cleanReviewer(data.reviewer);
    incoming.lastEntry = typeof data.last_entry === 'string' ? data.last_entry : '';
    for (const [id, item] of Object.entries(data.items)) {
      if (!boxById.has(id)) throw new Error('Unknown review item: ' + id + '.');
      incoming.items[id] = normalizeItem(item, incoming.reviewer, true);
    }
    return incoming;
  }

  let state = load();
  const reviewer = document.getElementById('reviewer');
  reviewer.value = state.reviewer;
  reviewer.addEventListener('input', () => {
    state.reviewer = cleanReviewer(reviewer.value);
    save(state);
  });

  const status = document.createElement('div');
  status.id = 'review-status';
  status.setAttribute('role', 'status');
  status.setAttribute('aria-live', 'polite');
  const controls = document.querySelector('.review-tools') || reviewer.parentElement || document.body;
  controls.appendChild(status);
  const announce = (message) => { status.textContent = message; };

  function itemReviewer(item) {
    return typeof item.reviewer === 'string' ? item.reviewer : state.reviewer;
  }

  function paint() {
    let done = 0;
    for (const box of boxes) {
      const id = box.dataset.item;
      const item = state.items[id] || { checks: Object.create(null), notes: '', reviewer: '', hash: '' };
      const checks = plainRecord(item.checks) ? item.checks : {};
      box.querySelectorAll('[data-check]').forEach((cb) => { cb.checked = checks[cb.dataset.check] === true; });
      box.querySelector('[data-notes]').value = item.notes || '';
      const hasChecks = checkIds.some((check) => checks[check] === true);
      const hashMatches = item.hash === box.dataset.hash;
      const stale = (Boolean(item.hash) && !hashMatches) || (hasChecks && !hashMatches);
      const namedReviewer = cleanReviewer(itemReviewer(item));
      const hasNamedReviewer = namedReviewer !== '' && namedReviewer.toLowerCase() !== 'anonymous';
      let attribution = box.querySelector('[data-reviewer-attribution]');
      if (!attribution) {
        attribution = document.createElement('div');
        attribution.className = 'muted reviewer-attribution';
        attribution.dataset.reviewerAttribution = '';
        box.insertBefore(attribution, box.firstChild);
      }
      attribution.textContent = hasNamedReviewer ? 'Recorded reviewer: ' + namedReviewer : '';
      attribution.hidden = !hasNamedReviewer;
      const complete = hashMatches && hasNamedReviewer &&
        checkIds.every((check) => checks[check] === true);
      box.classList.toggle('complete', complete);
      box.classList.toggle('stale', stale);
      const toc = document.querySelector('[data-toc="' + CSS.escape(id) + '"]');
      if (toc) toc.classList.toggle('done', complete);
      if (complete) done++;
    }
    document.getElementById('progress').textContent = 'Signed off: ' + done + ' / ' + boxes.length;
    applyFilters();
  }

  for (const box of boxes) {
    const id = box.dataset.item;
    box.addEventListener('input', (event) => {
      const item = state.items[id] || (state.items[id] = {
        checks: Object.create(null), notes: '', reviewer: state.reviewer, updated: '', hash: '',
      });
      const activeReviewer = cleanReviewer(state.reviewer);
      const priorReviewer = cleanReviewer(itemReviewer(item));
      const revisionChanged = item.hash !== box.dataset.hash;
      const reviewerChanged = priorReviewer !== activeReviewer;
      const resetSignoff = revisionChanged || reviewerChanged;
      const activeCheck = event.target instanceof HTMLInputElement &&
        event.target.matches('[data-check]') ? event.target : null;
      const retainCheck = activeCheck && activeCheck.checked ? activeCheck.dataset.check : '';

      if (resetSignoff) {
        item.checks = Object.create(null);
        box.querySelectorAll('[data-check]').forEach((cb) => {
          cb.checked = cb === activeCheck && Boolean(retainCheck);
          if (cb.checked) item.checks[cb.dataset.check] = true;
        });
      } else {
        item.checks = Object.create(null);
        box.querySelectorAll('[data-check]').forEach((cb) => { item.checks[cb.dataset.check] = cb.checked; });
      }
      item.notes = box.querySelector('[data-notes]').value;
      item.reviewer = activeReviewer;
      item.updated = new Date().toISOString();
      item.hash = box.dataset.hash;
      state.lastEntry = id;
      save(state);
      paint();
      updateResumeLink();
    });
  }

  document.getElementById('export').addEventListener('click', () => {
    const items = Object.create(null);
    for (const [id, item] of Object.entries(state.items)) {
      const checks = Object.create(null);
      for (const check of checkIds) checks[check] = item.checks?.[check] === true;
      // Never export an attributable sign-off when the reviewer field was blank.
      const recordedReviewer = cleanReviewer(itemReviewer(item));
      if (!recordedReviewer || recordedReviewer.toLowerCase() === 'anonymous') {
        for (const check of checkIds) checks[check] = false;
      }
      items[id] = {
        checks,
        notes: typeof item.notes === 'string' ? item.notes : '',
        reviewer: recordedReviewer || 'anonymous',
        updated: typeof item.updated === 'string' ? item.updated : '',
        hash: typeof item.hash === 'string' ? item.hash : '',
      };
    }
    const payload = {
      format,
      mapping_version: meta.version,
      paper_commit: meta.paper,
      formal_commit: meta.formal,
      reviewer: cleanReviewer(state.reviewer),
      last_entry: state.lastEntry || null,
      exported: new Date().toISOString(),
      items,
    };
    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
    const a = document.createElement('a');
    const url = URL.createObjectURL(blob);
    try {
      a.href = url;
      a.download = 'review-' + (cleanReviewer(state.reviewer) || 'anonymous').replace(/\W+/g, '_') + '-' + meta.formal.slice(0, 7) + '.json';
      a.click();
      announce('Review JSON exported.');
    } finally {
      // Give the browser time to start reading the download before revoking it.
      setTimeout(() => URL.revokeObjectURL(url), 1000);
    }
  });

  document.getElementById('import').addEventListener('change', async (event) => {
    const input = event.target;
    const file = input.files?.[0];
    if (!file) return;
    try {
      const data = JSON.parse(await file.text());
      const imported = validateImport(data);
      const pinsDiffer = data.mapping_version !== meta.version ||
        data.paper_commit !== meta.paper || data.formal_commit !== meta.formal;
      if (pinsDiffer && !window.confirm('This review was made against different mapping or pinned revisions. Import anyway?')) {
        announce('Import cancelled.');
        return;
      }
      state = imported;
      reviewer.value = state.reviewer;
      save(state);
      paint();
      updateResumeLink();
      announce('Review imported.');
    } catch (error) {
      announce('Import failed: ' + (error instanceof SyntaxError ? 'invalid JSON.' : error.message));
    } finally {
      input.value = '';
    }
  });

  const filter = document.getElementById('filter');
  const onlyIssues = document.getElementById('only-issues');
  const onlyOpen = document.getElementById('only-open');
  const reviewScope = document.getElementById('review-scope');
  function applyFilters() {
    const q = filter.value.trim().toLowerCase();
    const scope = reviewScope?.value ?? 'all';
    document.body.classList.toggle('publication-focus', scope !== 'all');
    let visible = 0, approved = 0;
    document.querySelectorAll('section.card').forEach((card) => {
      const text = card.textContent.toLowerCase();
      const hasIssue = +card.dataset.sev > 0;
      const complete = card.querySelector('.review').classList.contains('complete');
      const scopeMatches = scope === 'all' || (card.dataset.reviewScope ?? 'publication') === scope;
      const show = scopeMatches && (!q || text.includes(q)) && (!onlyIssues.checked || hasIssue) && (!onlyOpen.checked || !complete);
      card.classList.toggle('hidden', !show);
      if (show) { visible++; if (complete) approved++; }
      const toc = document.querySelector('[data-toc="' + CSS.escape(card.querySelector('.review').dataset.item) + '"]');
      if (toc) toc.parentElement.hidden = !show;
    });
    if (reviewScope) document.getElementById('progress').textContent = 'Visible claims signed off: ' + approved + ' / ' + visible;
  }
  [filter, onlyIssues, onlyOpen, reviewScope].filter(Boolean).forEach((el) => el.addEventListener('input', applyFilters));

  const resumeLink = document.getElementById('guided-resume');
  function updateResumeLink() {
    if (!resumeLink) return;
    const box = boxById.get(state.lastEntry);
    const card = box?.closest('section.card');
    resumeLink.hidden = !card;
    if (card) {
      resumeLink.href = '#' + card.id;
      const heading = card.querySelector('.card-head h3, h2, h3')?.textContent.trim() || state.lastEntry;
      resumeLink.textContent = 'Resume at ' + heading;
    } else {
      resumeLink.removeAttribute('href');
      resumeLink.textContent = 'Resume last visited claim';
    }
  }
  function rememberEntry(id) {
    const box = boxById.get(id);
    const card = box?.closest('section.card');
    if (!card) return;
    // Guided links must remain usable even when a sidebar filter hid a claim.
    if (card.classList.contains('hidden')) {
      filter.value = '';
      onlyIssues.checked = false;
      onlyOpen.checked = false;
      if (reviewScope) reviewScope.value = 'all';
      applyFilters();
    }
    state.lastEntry = id;
    save(state);
    updateResumeLink();
  }
  document.addEventListener('click', (event) => {
    const link = event.target.closest('a[data-guided-start], a[data-guided-visit], a[data-guided-resume], a[data-toc]');
    if (!link) return;
    const first = boxes[0]?.dataset.item;
    const id = link.hasAttribute('data-guided-start')
      ? first
      : link.dataset.guidedVisit || link.dataset.toc || state.lastEntry || first;
    rememberEntry(id);
  });
  updateResumeLink();
  document.getElementById('clean-text').addEventListener('change', (event) => document.body.classList.toggle('clean', event.target.checked));
  paint();
  const freshness = document.getElementById('freshness');
  if (freshness && meta.live) {
    const link = document.createElement('a'); link.href = meta.live; link.textContent = 'Open the latest published review';
    freshness.appendChild(link);
    async function checkLatest() {
      if (location.protocol === 'file:') return;
      try {
        const response = await fetch(meta.live + 'version.json', { cache: 'no-store' });
        if (!response.ok) return;
        const latest = await response.json();
        const changed = ['version', 'paper', 'formal', 'generator'].some(k => latest[k] !== meta[k]);
        freshness.classList.toggle('err', changed);
        link.textContent = changed ? 'Newer review available — open it before signing off' : 'Current published review';
        document.querySelectorAll('[data-check]').forEach(el => { el.disabled = changed; });
      } catch (_) { link.textContent = 'Latest version could not be checked — open the published review'; }
    }
    checkLatest(); setInterval(checkLatest, 120000);
  }
})();

// Open the definition and its collapsed ancestors before following an in-page link.
document.addEventListener('click', (event) => {
  const link = event.target.closest('a[href^="#"]');
  if (!link) return;
  const target = document.getElementById(link.hash.slice(1));
  if (!target) return;
  const card = target.closest('section.card');
  if (card) card.classList.remove('hidden');
  for (let element = target; element; element = element.parentElement) {
    if (element.tagName === 'DETAILS') element.open = true;
    if (element.hasAttribute('data-reference-material')) element.setAttribute('data-on-demand', '');
  }
});
