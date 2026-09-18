export const lanes = [
  { id: 'idea', title: 'IntelliJ orchestration', short: 'IDE', color: 'purple' },
  { id: 'tooling-client', title: 'Tooling API / helper', short: 'CLIENT', color: 'blue' },
  { id: 'gradle', title: 'Gradle + builders', short: 'GRADLE', color: 'green' },
  { id: 'compiler-optional', title: 'Compiler / workers', short: 'WORKER', color: 'amber' },
  { id: 'io', title: 'Repositories / disk', short: 'I/O', color: 'pink' },
  { id: 'idea-model', title: 'IDE model / background', short: 'MODEL', color: 'blue' },
];

export const phases = ['Connection', 'Build preparation', 'Model construction', 'Transfer & conversion', 'Apply & follow-up', 'Cross-cutting telemetry'];

export function phaseOf(id) {
  const n = Number(id.slice(1));
  if (n === 26) return 5;
  return n <= 5 ? 0 : n <= 10 ? 1 : n <= 17 ? 2 : n <= 22 ? 3 : 4;
}

export function laneOwns(lane, item) {
  const aliases = { gradle: ['gradle', 'gradle-converter'], 'idea-model': ['idea-model', 'idea-background'] };
  return item.lanes.some(value => (aliases[lane] || [lane]).includes(value));
}

export function matches(value, query) {
  return String(value).toLowerCase().includes(query.trim().toLowerCase());
}

export function seconds(ms) {
  return ms == null ? 'No samples' : `${(ms / 1000).toLocaleString('en-US', { minimumFractionDigits: 3, maximumFractionDigits: 3 })} s`;
}

export function escapeHTML(value) {
  return String(value ?? '').replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[char]);
}

export function median(values) {
  if (!values.length) return null;
  const sorted = [...values].sort((a, b) => a - b);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2;
}

export function metricStats(scenario, metric, includeWarmups = false) {
  const rows = scenario?.iterations.filter(row => row.phase === 'MEASURE' || (includeWarmups && row.phase === 'WARM_UP')) || [];
  const values = rows.map(row => row.values[metric]).filter(Number.isFinite);
  return { count: values.length, median: median(values), min: values.length ? Math.min(...values) : null, max: values.length ? Math.max(...values) : null, rows };
}

export function spanDepth(span, spans, traceID) {
  let depth = 0;
  const seen = new Set([span.spanID]);
  let current = span;
  while (current) {
    const parent = current.references.find(ref => ref.refType === 'CHILD_OF' && ref.traceID === traceID);
    if (!parent || seen.has(parent.spanID) || !spans.has(parent.spanID)) break;
    seen.add(parent.spanID);
    depth++;
    current = spans.get(parent.spanID);
  }
  return depth;
}

export function resolveDocPath(current, target) {
  const [pathname, fragment = ''] = target.split('#');
  const parts = (pathname ? `${current.slice(0, current.lastIndexOf('/') + 1)}${pathname}` : current).split('/');
  const normalized = [];
  for (const part of parts) {
    if (part === '..') normalized.pop();
    else if (part && part !== '.') normalized.push(part);
  }
  return { path: normalized.join('/'), fragment };
}

export function slug(text) {
  return text.toLowerCase().replace(/[^\p{L}\p{N}\s_-]/gu, '').trim().replace(/\s+/g, '-');
}