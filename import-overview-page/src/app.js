import { marked } from 'marked';
import DOMPurify from 'dompurify';
import { lanes, phases, phaseOf, laneOwns, matches, seconds, escapeHTML as h, metricStats, spanDepth, resolveDocPath, slug } from './core.js';

const data = window.IMPORT_OVERVIEW;
const main = document.querySelector('main');
const dialog = document.querySelector('#detail');
const $ = (selector, root = main) => root.querySelector(selector);
const all = (selector, root = main) => [...root.querySelectorAll(selector)];
const docURL = path => `#docs/${encodeURIComponent(path)}`;
const rawURL = path => `${data.source}${path.split('/').map(encodeURIComponent).join('/')}`;
const option = (value, text = value) => `<option value="${h(value)}">${h(text)}</option>`;
const empty = text => `<div class="empty">${h(text)}</div>`;
const header = (kicker, title, description) => `<header class="page-header"><div class="eyebrow">${kicker}</div><h1>${title}</h1><p>${description}</p></header>`;
const note = (text, path) => `<div class="notice"><span aria-hidden="true">↳</span><div>${text}${path ? ` <a href="${docURL(path)}">Read the context ↗</a>` : ''}</div></div>`;
const stat = (value, label, foot) => `<div class="stat"><span>${label}</span><strong>${value}</strong><small>${foot}</small></div>`;
const jsonBlock = value => `<pre class="json">${h(JSON.stringify(value, null, 2))}</pre>`;

function showDetail(title, body) {
  $('#detail-content', document).innerHTML = `<h2 id="detail-title">${h(title)}</h2>${body}`;
  if (!dialog.open) dialog.showModal();
  dialog.scrollTop = 0;
}
$('#close-detail', document).addEventListener('click', () => dialog.close());
dialog.addEventListener('click', event => { if (event.target === dialog) dialog.close(); });
dialog.addEventListener('click', event => { if (event.target.closest('a[href^="#"]')) dialog.close(); });

function markdown(text, path) {
  const container = document.createElement('div');
  container.innerHTML = DOMPurify.sanitize(marked.parse(text));
  const ids = new Map();
  all('h1,h2,h3,h4,h5,h6', container).forEach(heading => {
    const base = slug(heading.textContent);
    const count = ids.get(base) || 0;
    ids.set(base, count + 1);
    heading.id = `doc-${base}${count ? `-${count}` : ''}`;
  });
  all('a', container).forEach(link => {
    const href = link.getAttribute('href');
    if (!href) return;
    if (/^https?:/i.test(href)) {
      link.target = '_blank';
      link.rel = 'noopener noreferrer';
    } else if (!/^[a-z]+:|^\//i.test(href)) {
      const target = resolveDocPath(path, href);
      link.href = data.documents.some(doc => doc.path === target.path)
        ? `${docURL(target.path)}${target.fragment ? `/${encodeURIComponent(target.fragment)}` : ''}`
        : `${rawURL(target.path)}${target.fragment ? `#${encodeURIComponent(target.fragment)}` : ''}`;
    }
  });
  all('pre:has(code.language-mermaid)', container).forEach(pre => {
    const details = document.createElement('details');
    const summary = document.createElement('summary');
    summary.textContent = 'Original sequence diagram (Mermaid source)';
    pre.replaceWith(details);
    details.append(summary, pre);
    const link = document.createElement('a');
    link.href = '#pipeline';
    link.textContent = 'Explore the interactive ownership swimlane →';
    details.before(link);
  });
  all('table', container).forEach(table => {
    const scroll = document.createElement('div');
    scroll.className = 'table-scroll';
    table.replaceWith(scroll);
    scroll.append(table);
  });
  return container.innerHTML;
}

function sourceDetail(id) {
  const ref = data.json['source-excerpts'].references.find(ref => ref.id === id);
  if (ref) {
    showDetail(`${id} · ${ref.topic}`, `<p class="badge">SOURCE EXCERPT · ${h(ref.repository)}</p><p class="mono wrap">${h(ref.repository_relative_path)}</p><p class="muted wrap">File SHA-256: ${h(ref.file_sha256)}</p>${ref.excerpts.map(excerpt => `<h3>Lines ${excerpt.start_line}–${excerpt.end_line}</h3><pre class="source-code">${h(excerpt.lines.map((line, index) => `${excerpt.start_line + index}  ${line}`).join('\n'))}</pre>`).join('')}<a href="${docURL('reference/sources.md')}">Repository revisions and complete source map →</a>`);
  } else {
    const external = data.json['collection-status'].external_references.find(ref => ref.id === id);
    showDetail(id, external ? `${jsonBlock(external)}<a href="${external.url ? h(external.url) : rawURL('bin/inputs/')}">Open reference ↗</a>` : `<p>See the source map for this reference.</p><a href="${docURL('reference/sources.md')}">Open source map →</a>`);
  }
}

function workDetail(id) {
  const item = data.json['work-items'].items.find(item => item.id === id);
  const inventory = data.documents.find(doc => doc.path === 'pipeline/work-inventory.md');
  const row = inventory.markdown.split('\n').find(line => line.startsWith(`| ${id} |`));
  showDetail(`${id} · ${item.title}`, `<p class="badge">CONCEPTUAL · DURATION UNKNOWN</p><p>${h(item.condition)}</p><p class="muted">Owners: ${h(item.lanes.join(', '))}</p>${row ? `<div class="prose">${markdown(`| ID | Owner / work | Inputs → outputs; when paid | Multiplicity / reuse | Evidence |\n| --- | --- | --- | --- | --- |\n${row}`, inventory.path)}</div>` : ''}<h3>Inspect supporting evidence</h3><div class="chips">${item.evidence.map(id => `<button data-source="${h(id)}">${h(id)}</button>`).join('')}</div><p class="muted">Presence in the source does not mean this work executes on every sync. No measured span duration has been assigned to this work item.</p>`);
}
dialog.addEventListener('click', event => {
  const button = event.target.closest('[data-source]');
  if (button) sourceDetail(button.dataset.source);
  const span = event.target.closest('[data-span]');
  if (span) spanDetail(span.dataset.span);
});

function renderPipeline() {
  const items = data.json['work-items'].items;
  main.innerHTML = `${header('THE IMPORT, UNPACKED', 'From refresh to ready.', 'Follow the work behind a Kotlin/JVM Gradle sync. Explore who owns it, what triggers it, and where the evidence points.')}
    <div class="stats">${stat(items.length, 'Work items', 'Source-backed & conditional')}${stat(data.json['trace-analysis'].traces.reduce((sum, trace) => sum + trace.span_count, 0), 'Recorded spans', 'Two traces · one supplied export')}${stat(Object.keys(data.json['benchmark-results'].datasets).length, 'Benchmark datasets', 'Separate macOS experiments')}</div>
    <div class="section-heading"><div><span class="eyebrow">OWNERSHIP MAP</span><h2>A logical swimlane, not a stopwatch.</h2></div><a href="${docURL('index.md')}">Read the overview ↗</a></div>
    <div class="toolbar"><label class="search-label">Find work<input id="work-search" type="search" placeholder="Try compiler, dependency, W14…"></label><label>Owner<select id="work-owner">${option('', 'All owners')}${lanes.map(lane => option(lane.id, lane.title)).join('')}</select></label><label>Phase<select id="work-phase">${option('', 'All phases')}${phases.map((phase, i) => option(i, phase)).join('')}</select></label></div>
    <p class="muted small">Read top to bottom. Select a card for triggers, reuse conditions, and source excerpts. A shared W-ID in multiple lanes means shared ownership, not repeated execution.</p>
    <div id="work-count" class="result-count" aria-live="polite"></div><div id="swimlane" class="swimlane-scroll" tabindex="0" aria-label="Scrollable conceptual swimlane"></div>
    ${note('Phases can interleave, repeat and overlap. Lane width and card height encode no duration. Early IDE updates can precede complete configuration; telemetry also has a collector owner and is cross-cutting, not a final sequential step.', 'pipeline/work-inventory.md')}
    <div class="next-grid"><a href="#trace"><span class="eyebrow">OBSERVED</span><h3>Put work on a clock ↗</h3><p>Explore the supplied trace, from enclosing scopes to individual requests.</p></a><a href="#investigation"><span class="eyebrow">HYPOTHESES</span><h3>Find the next experiment ↗</h3><p>Repeated work is a lead, not proof of waste. Start with validation criteria.</p></a></div>`;
  const update = () => {
    const owner = $('#work-owner').value;
    const phase = $('#work-phase').value;
    const filtered = items.filter(item => matches(`${item.id} ${item.title} ${item.condition} ${item.evidence.join(' ')}`, $('#work-search').value) && (!owner || laneOwns(owner, item)) && (phase === '' || phaseOf(item.id) === Number(phase)));
    $('#work-count').textContent = `${filtered.length} of ${items.length} unique work items`;
    const visibleLanes = lanes.filter(lane => !owner || lane.id === owner);
    $('#swimlane').innerHTML = filtered.length ? `<div class="swimlane" style="--lane-count:${visibleLanes.length}"><div class="lane-heading phase-label">LOGICAL ORDER ↓</div>${visibleLanes.map(lane => `<div class="lane-heading ${lane.color}"><span class="lane-dot"></span>${h(lane.title)}</div>`).join('')}${phases.map((title, index) => {
      const group = filtered.filter(item => phaseOf(item.id) === index);
      if (!group.length) return '';
      return `<div class="phase-label"><span>${index === 5 ? '↔' : `0${index + 1}`}</span><b>${title}</b></div>${visibleLanes.map(lane => `<div class="lane-cell ${lane.color}">${group.filter(item => laneOwns(lane.id, item)).map(item => `<button class="work-card" data-work="${item.id}"><span>${item.id}<span aria-hidden="true">↗</span></span><strong>${h(item.title)}</strong><small>${h(item.condition)}</small></button>`).join('') || '<span class="no-work">·</span>'}</div>`).join('')}`;
    }).join('')}</div>` : empty('No work items match. Try another term or clear the filters.');
  };
  $('#work-search').addEventListener('input', update);
  $('#work-owner').addEventListener('change', update);
  $('#work-phase').addEventListener('change', update);
  $('#swimlane').addEventListener('click', event => { const button = event.target.closest('[data-work]'); if (button) workDetail(button.dataset.work); });
  update();
}

let activeTrace;
function spanDetail(id) {
  const span = activeTrace.spans.find(span => span.spanID === id);
  if (!span) return;
  showDetail(span.operation, `<p class="mono">${h(span.spanID)}</p><div class="stats">${stat(seconds(span.start_ms), 'Start offset', 'Relative to this trace')}${stat(seconds(span.duration_ms), 'Inclusive duration', 'May overlap other scopes')}${stat(seconds(span.uncovered_by_direct_children_ms), 'Uncovered interval', 'Not CPU / self time')}</div><p>${h(span.service)} · ${h(span.thread_name || 'Thread unknown')}</p><h3>Parent references</h3>${span.references.length ? span.references.map(ref => `<p>${h(ref.refType)} · ${ref.traceID === activeTrace.traceID && activeTrace.spans.some(s => s.spanID === ref.spanID) ? `<button data-span="${h(ref.spanID)}">${h(ref.spanID)}</button>` : h(ref.spanID)}</p>`).join('') : '<p>No parent reference recorded.</p>'}<h3>Recorded attributes</h3><div class="table-scroll"><table><thead><tr><th>Attribute</th><th>Value</th></tr></thead><tbody>${span.tags.map(tag => `<tr><td>${h(tag.key)}</td><td class="wrap">${h(typeof tag.value === 'object' ? JSON.stringify(tag.value) : tag.value)}</td></tr>`).join('')}</tbody></table></div><details><summary>Full normalized span</summary>${jsonBlock(span)}</details>`);
}

function renderTrace() {
  const traces = [...data.json['trace-analysis'].traces].sort((a, b) => b.span_count - a.span_count);
  activeTrace = traces[0];
  main.innerHTML = `${header('RECORDED, NOT INFERRED', 'The sync, on a clock.', 'Inspect every canonical span in the supplied Jaeger export. This Linux run is separate from the macOS benchmark experiments.')}
    <div class="toolbar"><label class="grow">Trace<select id="trace-select">${traces.map(trace => option(trace.traceID, `${trace.span_count > 2 ? 'Main analysis' : 'Progress only'} · ${trace.span_count} spans · ${trace.traceID}`)).join('')}</select></label><button id="trace-meta">Process & provenance</button></div><div id="trace-stats" class="stats"></div>
    ${note('Inclusive spans overlap: do not add their durations. Uncovered intervals are not CPU time. HTTP error tags do not establish an import failure, and overlapping roots do not prove two builds.', 'measurements/jaeger-trace.md')}
    <div class="toolbar"><label class="search-label">Find spans<input id="span-search" type="search" placeholder="Operation, URL, attribute, span ID…"></label><label>Process / thread<select id="span-owner"></select></label><label>Minimum duration (ms)<input id="span-min" type="number" min="0" step="1" value="0"></label><label>Order<select id="span-sort">${option('time', 'Start time')}${option('duration', 'Longest first')}</select></label><label class="checkbox"><input id="span-errors" type="checkbox"> Error-tagged only</label></div>
    <div class="timeline-actions"><span id="span-count" class="result-count" aria-live="polite"></span><label>Timeline zoom <select id="span-zoom">${[1, 2, 4, 8].map(value => option(value, `${value}×`)).join('')}</select></label></div>
    <p class="small muted">Bars share the full trace time axis. Indentation follows recorded parent references; rows are scopes, not CPU threads. Tiny spans have a 2px minimum hit target.</p>
    <div id="timeline" class="timeline-scroll" tabindex="0" aria-label="Scrollable measured trace timeline"></div><div id="span-pagination" class="pagination"></div>
    <section class="panel"><div class="section-heading"><div><span class="eyebrow">REPOSITORY REQUESTS</span><h2>Same method. Same URL.</h2></div><span id="repeat-count" class="badge"></span></div><p class="muted">Repeated requests are investigation leads, not proven redundant downloads. Select an occurrence to inspect its attributes.</p><div id="repeats"></div></section>`;
  let page = 0;
  const ownerKey = span => `${span.processID} / ${span.thread_name || 'thread unknown'}`;
  function update() {
    const query = $('#span-search').value;
    const owner = $('#span-owner').value;
    const minimum = Math.max(0, Number($('#span-min').value) || 0);
    const rows = activeTrace.spans.filter(span => matches(`${span.operation} ${span.spanID} ${JSON.stringify(span.tags)}`, query) && (!owner || ownerKey(span) === owner) && span.duration_ms >= minimum && (!$('#span-errors').checked || span.error_tag));
    rows.sort($('#span-sort').value === 'time' ? (a, b) => a.start_ms - b.start_ms || b.duration_ms - a.duration_ms : (a, b) => b.duration_ms - a.duration_ms);
    page = Math.min(page, Math.max(0, Math.ceil(rows.length / 100) - 1));
    const shown = rows.slice(page * 100, (page + 1) * 100);
    $('#span-count').textContent = `${rows.length} of ${activeTrace.span_count} spans · ${rows.length ? page * 100 + 1 : 0}–${Math.min((page + 1) * 100, rows.length)} shown`;
    const map = new Map(activeTrace.spans.map(span => [span.spanID, span]));
    $('#timeline').innerHTML = shown.length ? `<div class="timeline" style="--timeline-width:${Number($('#span-zoom').value) * 850}px"><div class="timeline-ruler"><span>OPERATION / OWNER</span><div>${[0, 1, 2, 3, 4].map(tick => `<span style="left:${tick * 25}%">${(activeTrace.envelope_ms / 1000 * tick / 4).toFixed(1)}s</span>`).join('')}</div></div>${shown.map(span => {
      const color = span.error_tag ? 'error' : span.service === 'IntelliJ IDEA' ? 'purple' : span.thread_name === 'idea-tooling-model-converter' ? 'amber' : 'green';
      return `<button class="span-row" data-span="${h(span.spanID)}" title="${h(span.operation)} · ${seconds(span.duration_ms)}"><span class="span-label" style="padding-left:${12 + Math.min(spanDepth(span, map, activeTrace.traceID), 8) * 10}px"><strong>${h(span.operation)}</strong><small>${h(ownerKey(span))} · ${seconds(span.duration_ms)}</small></span><span class="span-track"><span class="span-bar ${color}" style="left:${100 * span.start_ms / activeTrace.envelope_ms}%;width:${100 * span.duration_ms / activeTrace.envelope_ms}%"></span></span></button>`;
    }).join('')}</div>` : empty('No spans match these filters.');
    $('#span-pagination').innerHTML = `<button id="prev-spans" ${page === 0 ? 'disabled' : ''}>← Previous 100</button><span>Page ${page + 1} of ${Math.max(1, Math.ceil(rows.length / 100))}</span><button id="next-spans" ${(page + 1) * 100 >= rows.length ? 'disabled' : ''}>Next 100 →</button>`;
    $('#prev-spans').onclick = () => { page--; update(); };
    $('#next-spans').onclick = () => { page++; update(); };
  }
  function changeTrace() {
    activeTrace = traces.find(trace => trace.traceID === $('#trace-select').value);
    page = 0;
    $('#span-owner').innerHTML = option('', 'All processes / threads') + [...new Set(activeTrace.spans.map(ownerKey))].map(owner => option(owner)).join('');
    $('#trace-stats').innerHTML = stat(seconds(activeTrace.envelope_ms), 'Trace envelope', activeTrace.start_utc.slice(0, 19).replace('T', ' ') + ' UTC') + stat(seconds(activeTrace.http.interval_union_ms), 'Recorded HTTP coverage', `${activeTrace.http.count} GET / HEAD spans · union`) + stat(activeTrace.error_tagged_span_count, 'Error-tagged spans', 'Inspect tags; not an import verdict');
    $('#repeat-count').textContent = `${activeTrace.http.repeated_method_url_count} repeated pairs`;
    $('#repeats').innerHTML = activeTrace.http.repeated_method_urls.map(group => `<details class="request-group"><summary><span class="badge">${h(group.method)} × ${group.count}</span> <span class="wrap">${h(group.url)}</span></summary><div class="chips">${group.requests.map(request => `<button data-span="${h(request.spanID)}">${request.status} · ${seconds(request.duration_ms)} · ${h(request.spanID)}</button>`).join('')}</div></details>`).join('') || empty('No repeated method / URL pairs in this trace.');
    update();
  }
  $('#trace-select').onchange = changeTrace;
  $('#trace-meta').onclick = () => showDetail('Trace provenance & processes', `<p>Source: ${h(data.json['trace-analysis'].source)}</p><p class="mono wrap">SHA-256: ${h(data.json['trace-analysis'].sha256)}</p>${jsonBlock({ traceID: activeTrace.traceID, start_utc: activeTrace.start_utc, end_utc: activeTrace.end_utc, processes: activeTrace.processes })}<a href="${rawURL('bin/traces/yahor/traces-1789726526259.json')}">Original Jaeger export ↗</a>`);
  for (const id of ['span-search', 'span-owner', 'span-min', 'span-sort', 'span-errors', 'span-zoom']) $(`#${id}`).addEventListener(id === 'span-search' || id === 'span-min' ? 'input' : 'change', () => { page = 0; update(); });
  main.addEventListener('click', traceClick);
  changeTrace();
}
function traceClick(event) {
  const button = event.target.closest('[data-span]');
  if (button) spanDetail(button.dataset.span);
}

function renderBenchmarks() {
  const datasets = data.json['benchmark-results'].datasets;
  const scenarios = [...new Map(Object.values(datasets).flatMap(dataset => dataset.scenarios.map(s => [s.definition.name, s.definition.title]))).entries()];
  main.innerHTML = `${header('MEASUREMENTS WITH THEIR CONTEXT', 'Compare the experiments.', 'Independent Gradle Profiler samples, not a phase-by-phase cost model. Medians describe these runs; they do not establish a causal speedup.')}
    ${note('Cold-IDE scenarios also reset daemon/project state. Dependency-addition scenarios failed before producing samples. Different distributions and three measured iterations limit comparisons.', 'measurements/existing-results.md')}
    <div class="toolbar"><label class="grow">Scenario<select id="bench-scenario">${scenarios.map(([name, title]) => option(name, title)).join('')}</select></label><label>Timing metric<select id="bench-metric">${['total execution time', 'Gradle total execution time', 'IDE execution time'].map(metric => option(metric)).join('')}</select></label></div>
    <div class="toolbar"><fieldset class="dataset-filter"><legend>Datasets</legend>${Object.keys(datasets).map(name => `<label class="checkbox"><input type="checkbox" name="dataset" value="${name}" checked>${name}</label>`).join('')}</fieldset><label class="checkbox"><input id="bench-warmups" type="checkbox"> Include warm-ups in statistics</label></div>
    <section class="panel"><div class="section-heading"><h2 id="bench-heading">Median and observed range</h2><span class="badge">SECONDS</span></div><p class="small muted">Solid bar = median · line = observed min–max. No pairing of iterations across datasets. Missing or failed runs remain missing, not zero.</p><div id="bench-chart"></div></section>
    <section class="panel"><h2>Individual iterations & provenance</h2><div id="bench-iterations"></div></section>`;
  $('#bench-scenario').value = scenarios.find(([name]) => name.endsWith('cold-cold-cold'))?.[0] || scenarios[0][0];
  function update() {
    const chosen = all('input[name="dataset"]:checked').map(input => input.value);
    const metric = $('#bench-metric').value;
    const warmups = $('#bench-warmups').checked;
    const rows = chosen.map(name => {
      const scenario = datasets[name].scenarios.find(scenario => scenario.definition.name === $('#bench-scenario').value);
      return { name, scenario, ...metricStats(scenario, metric, warmups) };
    });
    const maximum = Math.max(1, ...rows.map(row => row.max || 0));
    $('#bench-heading').textContent = warmups ? 'Median and range · includes warm-ups' : 'Median and range · measured iterations only';
    $('#bench-chart').innerHTML = rows.map((row, index) => `<div class="benchmark-row"><div><strong>${h(row.name)}</strong><small>${row.scenario ? `${row.count} ${warmups ? 'included' : 'measured'} samples` : 'Scenario not recorded'}</small></div><div class="benchmark-track">${row.median != null ? `<span class="benchmark-bar color-${index}" style="width:${100 * row.median / maximum}%"></span><span class="range" style="left:${100 * row.min / maximum}%;width:${100 * (row.max - row.min) / maximum}%"></span>` : '<span class="missing">No samples</span>'}</div><div class="benchmark-value"><strong>${seconds(row.median)}</strong><small>${row.median != null ? `${seconds(row.min)} – ${seconds(row.max)}` : row.scenario ? 'Failed before samples' : 'Not available'}</small></div></div>`).join('') || empty('Select at least one dataset.');
    $('#bench-iterations').innerHTML = rows.map(row => `<details class="iteration-group" open><summary>${h(row.name)} · ${row.scenario ? h(row.scenario.definition.version) : 'not recorded'}</summary><p class="small muted">${h(datasets[row.name].environment.operatingSystem)} · report ${h(datasets[row.name].date)}</p>${row.rows.length ? `<div class="table-scroll"><table><thead><tr><th>Phase</th><th>Iteration</th><th>${h(metric)}</th></tr></thead><tbody>${row.rows.map(sample => `<tr><td>${h(sample.phase)}</td><td>${h(sample.title)}</td><td>${seconds(sample.values[metric])}</td></tr>`).join('')}</tbody></table></div>` : '<p>No samples for this selection.</p>'}${row.scenario ? `<details><summary>Original scenario definition</summary>${jsonBlock(row.scenario.definition)}</details>` : ''}</details>`).join('');
  }
  all('select,input', main).forEach(control => control.addEventListener('change', update));
  update();
}

function renderDocs(path = 'index.md', fragment = '') {
  const doc = data.documents.find(doc => doc.path === path);
  main.innerHTML = `${header('THE COMPLETE FIELD GUIDE', 'Documentation library.', 'The original documents, kept intact and searchable. Follow links between the pipeline, measurements, investigation notes, and capture instructions.')}<div class="library-layout"><aside class="library-nav"><label>Search all documentation<input id="doc-search" type="search" placeholder="Try fingerprint, telemetry…"></label><div id="doc-results" aria-live="polite"></div></aside><article id="document" class="prose panel">${doc ? `<a class="raw-link" href="${rawURL(doc.path)}">Original Markdown ↗</a>${markdown(doc.markdown, doc.path)}` : '<h2>Document not found</h2><a href="#docs">Return to the library</a>'}</article></div>`;
  function update() {
    const query = $('#doc-search').value;
    const docs = data.documents.filter(doc => matches(`${doc.title} ${doc.markdown}`, query));
    $('#doc-results').innerHTML = `<p class="small muted">${docs.length} documents</p>` + (docs.map(item => {
      const position = query.trim() ? item.markdown.toLowerCase().indexOf(query.trim().toLowerCase()) : -1;
      const snippet = position < 0 ? '' : item.markdown.slice(Math.max(0, position - 35), position + 120).replace(/\n/g, ' ');
      return `<a class="doc-link ${item.path === path ? 'selected' : ''}" href="${docURL(item.path)}" ${item.path === path ? 'aria-current="page"' : ''}><strong>${h(item.title)}</strong><small>${h(item.path)}</small>${snippet ? `<p>${h(snippet)}…</p>` : ''}</a>`;
    }).join('') || empty('No documents match.'));
  }
  $('#doc-search').addEventListener('input', update);
  update();
  if (fragment) requestAnimationFrame(() => document.getElementById(`doc-${fragment}`)?.scrollIntoView());
}

function renderInvestigation() {
  const doc = data.documents.find(doc => doc.path === 'analysis/duplication.md');
  const trace = [...data.json['trace-analysis'].traces].sort((a, b) => b.span_count - a.span_count)[0];
  const serialization = trace.spans.filter(span => span.operation === 'SerializeGradleModel').reduce((sum, span) => sum + span.duration_ms, 0);
  const candidates = doc.markdown.split('\n').filter(line => /^\| \*\*D\d+ /.test(line)).length;
  main.innerHTML = `${header('LEADS, NOT VERDICTS', 'What is worth investigating?', 'Keep repeated observations separate from removable work. Every candidate needs equivalent inputs, correct outputs, and critical-path evidence.')}
    <div class="stats">${stat(trace.http.repeated_method_urls.filter(group => group.method === 'HEAD').length, 'Repeated HEAD pairs', 'Observed in the supplied main trace')}${stat(seconds(serialization), 'Serialization duration sum', 'Not the dominant cost in this run')}${stat(candidates, 'Investigation candidates', 'No optimization or speedup established')}</div>
    <div class="prose panel">${markdown(doc.markdown, doc.path)}</div>`;
}

function renderEvidence() {
  const references = data.json['source-excerpts'].references;
  main.innerHTML = `${header('FOLLOW THE RECEIPTS', 'Evidence archive.', 'Inspect captured source excerpts and open every original input, report, manifest, and derived dataset. The raw evidence remains in import-overview/bin.')}
    ${note('Machine paths, process metadata, logs, and source excerpts may be sensitive. Review access rights and content before publishing. No external analytics, fonts, or runtime CDN requests are used.')}
    <div class="toolbar"><label class="search-label">Find evidence<input id="evidence-search" type="search" placeholder="Citation ID, topic, filename…"></label><label>Show<select id="evidence-kind">${option('sources', 'Source excerpts')}${option('files', 'All original files')}</select></label><a href="${docURL('bin/README.md')}">Schemas & reproduction ↗</a></div><p id="evidence-count" class="result-count" aria-live="polite"></p><div id="evidence-results"></div>`;
  function update() {
    const query = $('#evidence-search').value;
    if ($('#evidence-kind').value === 'sources') {
      const refs = references.filter(ref => matches(`${ref.id} ${ref.topic} ${ref.repository_relative_path}`, query));
      $('#evidence-count').textContent = `${refs.length} source excerpts`;
      $('#evidence-results').innerHTML = `<div class="source-grid">${refs.map(ref => `<button class="source-card" data-source="${h(ref.id)}"><span class="badge">${h(ref.id)} · ${h(ref.repository)}</span><strong>${h(ref.topic)}</strong><small>${h(ref.repository_relative_path)}</small></button>`).join('')}</div>`;
    } else {
      const files = data.files.filter(file => matches(file.path, query));
      $('#evidence-count').textContent = `${files.length} files · links open original evidence`;
      $('#evidence-results').innerHTML = `<div class="panel table-scroll"><table><thead><tr><th>Path</th><th>Size</th><th>Access</th></tr></thead><tbody>${files.map(file => `<tr><td class="mono wrap">${h(file.path)}</td><td>${(file.size_bytes / 1024).toFixed(1)} KB</td><td><a href="${rawURL(file.path)}">Open ↗</a>${file.path.endsWith('.md') ? ` · <a href="${docURL(file.path)}">Read</a>` : ''}</td></tr>`).join('')}</tbody></table></div>`;
    }
  }
  $('#evidence-search').oninput = update;
  $('#evidence-kind').onchange = update;
  $('#evidence-results').onclick = event => { const button = event.target.closest('[data-source]'); if (button) sourceDetail(button.dataset.source); };
  update();
}

function route() {
  if (!data) {
    main.innerHTML = '<h1>Evidence data is missing.</h1><p>Run <code>npm run build</code> in <code>import-overview-page</code> and reload.</p>';
    return;
  }
  let parts;
  try { parts = location.hash.slice(1).split('/').map(decodeURIComponent); }
  catch { parts = ['pipeline']; }
  const [view = 'pipeline', path, fragment] = parts;
  if (view === 'main') { main.focus(); return; }
  main.removeEventListener('click', traceClick);
  if (dialog.open) dialog.close();
  const active = ['trace', 'benchmarks', 'investigation', 'docs', 'evidence'].includes(view) ? view : 'pipeline';
  all('nav a', document).forEach(link => {
    const current = link.getAttribute('href') === `#${active}`;
    link.classList.toggle('active', current);
    if (current) link.setAttribute('aria-current', 'page');
    else link.removeAttribute('aria-current');
  });
  document.title = `${active.charAt(0).toUpperCase() + active.slice(1)} / Import Observatory`;
  ({ pipeline: renderPipeline, trace: renderTrace, benchmarks: renderBenchmarks, investigation: renderInvestigation, docs: () => renderDocs(path, fragment), evidence: renderEvidence })[active]();
  all('label').forEach(label => {
    const control = label.querySelector('input,select');
    const text = [...label.childNodes].filter(node => node.nodeType === Node.TEXT_NODE).map(node => node.textContent.trim()).join(' ').trim();
    if (control && text) control.setAttribute('aria-label', text);
  });
  window.scrollTo(0, 0);
}
window.addEventListener('hashchange', route);
route();
