import test from 'node:test';
import assert from 'node:assert/strict';
import { seconds, metricStats, median, spanDepth, laneOwns, resolveDocPath, escapeHTML, phaseOf } from '../src/core.js';

test('missing data is not rendered or aggregated as zero', () => {
  assert.equal(seconds(null), 'No samples');
  assert.equal(seconds(0), '0.000 s');
  assert.deepEqual(metricStats(undefined, 'time'), { count: 0, median: null, min: null, max: null, rows: [] });
  assert.equal(median([]), null);
  assert.equal(median([3, 1, 2, 4]), 2.5);
});

test('benchmark stats exclude warmups by default and retain separate iterations', () => {
  const scenario = { iterations: [
    { phase: 'WARM_UP', values: { time: 100 } },
    { phase: 'MEASURE', values: { time: 1 } },
    { phase: 'MEASURE', values: { time: 3 } },
  ] };
  assert.equal(metricStats(scenario, 'time').median, 2);
  assert.equal(metricStats(scenario, 'time', true).median, 3);
  assert.equal(metricStats(scenario, 'missing').count, 0);
});

test('hierarchy follows only same-trace CHILD_OF, tolerating missing parents and cycles', () => {
  const a = { spanID: 'a', references: [] };
  const b = { spanID: 'b', references: [{ refType: 'CHILD_OF', traceID: 't', spanID: 'a' }] };
  const map = new Map([['a', a], ['b', b]]);
  assert.equal(spanDepth(b, map, 't'), 1);
  assert.equal(spanDepth(b, map, 'other'), 0);
  a.references = [{ refType: 'CHILD_OF', traceID: 't', spanID: 'b' }];
  assert.equal(spanDepth(b, map, 't'), 1);
  map.delete('a');
  assert.equal(spanDepth(b, map, 't'), 0);
});

test('relative documentation links and heading links resolve without a server', () => {
  assert.deepEqual(resolveDocPath('measurements/jaeger-trace.md', '../bin/README.md#contents'), { path: 'bin/README.md', fragment: 'contents' });
  assert.deepEqual(resolveDocPath('index.md', 'pipeline/work-inventory.md'), { path: 'pipeline/work-inventory.md', fragment: '' });
  assert.deepEqual(resolveDocPath('bin/README.md', '#contents'), { path: 'bin/README.md', fragment: 'contents' });
});

test('work ownership and phases preserve conditional converter/background lanes', () => {
  assert.equal(laneOwns('gradle', { lanes: ['gradle-converter'] }), true);
  assert.equal(laneOwns('idea-model', { lanes: ['idea-background'] }), true);
  assert.equal(phaseOf('W14'), 2);
  assert.equal(phaseOf('W26'), 5);
});

test('untrusted metadata is escaped before insertion', () => {
  assert.equal(escapeHTML('<script>"&\''), '&lt;script&gt;&quot;&amp;&#39;');
});