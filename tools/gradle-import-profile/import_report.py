"""Build an import anatomy report from real, epoch-aligned spans."""
import collections
import html
import json
from pathlib import Path
import re


def union(intervals):
    result = []
    for start, end in sorted(intervals):
        if end <= start:
            continue
        if result and start <= result[-1][1]:
            result[-1] = (result[-1][0], max(end, result[-1][1]))
        else:
            result.append((start, end))
    return result


def duration(intervals):
    return sum(b - a for a, b in union(intervals))


def category(name):
    lower = name.lower()
    if lower.startswith(('compile script ', 'executing kotlin dsl ', 'snapshot outputs after executing kotlin dsl ')):
        return 'Kotlin DSL compilation / accessors'
    if 'init script' in lower:
        return 'IDE init scripts'
    if name.startswith('Task '):
        return 'Build tasks (including buildSrc)'
    if any(x in lower for x in ('transform', 'resolve ', 'download ', 'snapshot ', 'instrument', 'generate gradle')):
        return 'Dependencies / transforms / generated jars'
    if lower.startswith(('build model ', 'create tooling model ')):
        return 'Tooling models'
    if any(x in lower for x in ('configure ', 'evaluate ', 'apply plugin', 'apply script', 'apply build file', 'apply settings file', 'load build')):
        return 'Configuration'
    return 'Other Gradle operations'


def gradle_operations(path, start, end):
    pending, completed = {}, []
    if not path.exists():
        return []
    with path.open() as stream:
        for line in stream:
            entry = json.loads(line)
            if 'startTime' in entry:
                pending[entry['id']] = entry
            elif 'endTime' in entry and entry['id'] in pending:
                original = pending.pop(entry['id'])
                a, b = original['startTime'], entry['endTime']
                if a < end and b > start:
                    completed.append(dict(id=original['id'], parent=original.get('parentId'),
                                          name=original.get('displayName', original.get('name', 'Unnamed')),
                                          start=max(a, start), end=min(b, end), raw_start=a, raw_end=b,
                                          outcome=(entry.get('result') or {}).get('skipMessage') or
                                          ('NO-ACTIONS' if (entry.get('result') or {}).get('actionable') is False else 'EXECUTED')))
    children = collections.defaultdict(list)
    for op in completed:
        children[op['parent']].append((op['start'], op['end']))
    for op in completed:
        op['self_ms'] = op['end'] - op['start'] - duration(
            (max(a, op['start']), min(b, op['end'])) for a, b in children[op['id']])
        op['category'] = category(op['name'])
    by_id = {o['id']: o for o in completed}
    # Attribute unnamed task internals to the task, preserving explicit nested categories.
    for op in completed:
        if op['category'] != 'Other Gradle operations':
            continue
        parent = by_id.get(op['parent'])
        seen = set()
        while parent and parent['id'] not in seen:
            seen.add(parent['id'])
            if parent['name'].startswith('Task '):
                op['category'] = 'Build tasks (including buildSrc)'
                break
            parent = by_id.get(parent['parent'])
    return completed


IDE_PHASES = {
    'ExternalSystemSyncProjectTask': 'IDEA sync',
    'GetBuildEnvironment': 'Build environment / daemon connection',
    'GradleCall': 'Gradle Tooling API call',
    'WorkspaceModelApply': 'Workspace model update',
    'GradleProjectResolverDataProcessing': 'IDEA resolver → project data',
    'ExternalSystemSyncResultProcessing': 'IDEA model application',
    'ProjectDataServices': 'Project data services',
    'runFinalTasks': 'IDEA final tasks',
}


def anatomy(run_dir, manifest):
    events = manifest.get('events', {})
    start = events.get('import_requested')
    end = events.get('finished', events.get('failed'))
    if start is None or end is None:
        return dict(lanes=[], categories=[], phases=[], operations=[], errors=['Import interval unavailable'])
    operations = gradle_operations(run_dir / 'gradle-operations-log.txt', start, end)
    source = run_dir / 'idea-spans.json'
    spans = json.loads(source.read_text()) if source.exists() else []
    roots = [s for s in spans if s['name'] == 'ExternalSystemSyncProjectTask' and
             start - 10 <= s['start_ns'] / 1e6 < end]
    root = min(roots, key=lambda s: abs(s['start_ns'] / 1e6 - start)) if roots else None
    # Ignore spans from another import, even if it occurred in the same IDE process.
    spans = [s for s in spans if root and s['trace'] == root['trace']]
    lanes, phases = [], []
    def lane(label, items, color):
        if items:
            lanes.append(dict(label=label, color=color, bars=[dict(
                name=name, start=(a-start)/1000, end=(b-start)/1000, **extra) for name,a,b,extra in items]))
    lane('Measured import', [('Refresh → final callback', start, end, {})], 'ide')
    for name, label in IDE_PHASES.items():
        items = [(s['name'], max(start, s['start_ns']/1e6), min(end, s['end_ns']/1e6),
                  dict(full_seconds=(s['end_ns']-s['start_ns'])/1e9)) for s in spans if s['name'] == name]
        lane(label, items, 'ide')
        if items:
            phases.append(dict(name=label, count=len(items), wall_seconds=duration((a,b) for _,a,b,_ in items)/1000,
                               full_seconds=sum(x[3]['full_seconds'] for x in items)))
    phase_names = sorted({s['name'] for s in spans if 'MODEL_PHASE' in s['name']})
    for name in phase_names:
        lane(name.replace('_MODEL_PHASE', ''), [(name, max(start,s['start_ns']/1e6), min(end,s['end_ns']/1e6), {})
             for s in spans if s['name']==name], 'ide')
    builds = [o for o in operations if o['name'] == 'Run build']
    lane('Gradle build operation', [(o['name'],o['start'],o['end'],{}) for o in builds], 'gradle')
    for label, prefix in [('Generated Gradle API jar', 'Generate Gradle API jar'),
                          ('buildSrc · plugin blocks', 'Task :buildSrc:compilePluginsBlocks'),
                          ('buildSrc · plugin accessors', 'Task :buildSrc:generatePrecompiledScriptPluginAccessors'),
                          ('buildSrc · Kotlin compilation', 'Task :buildSrc:compileKotlin')]:
        lane(label, [(o['name'],o['start'],o['end'],dict(self_seconds=o['self_ms']/1000))
                     for o in operations if o['name'].startswith(prefix)], 'gradle')
    groups = collections.defaultdict(list)
    for op in operations:
        groups[op['category']].append(op)
    categories = []
    for name, ops in groups.items():
        categories.append(dict(name=name, count=len(ops), wall_seconds=duration((o['start'],o['end']) for o in ops)/1000,
                               self_seconds=sum(o['self_ms'] for o in ops)/1000))
        # Containers would paint the entire window. Show named work, not generic orchestration.
        if name != 'Other Gradle operations':
            lane(name, [(o['name'],o['start'],o['end'],dict(self_seconds=o['self_ms']/1000)) for o in ops],
                 'hot' if name in ('Kotlin DSL compilation / accessors', 'IDE init scripts') else 'gradle')
    errors = []
    if not root:
        errors.append('IDEA sync root span missing')
    if manifest.get('operations_trace', True) and (not builds or not any(o['raw_start'] >= start and o['raw_end'] <= end for o in builds)):
        errors.append('Complete Gradle Run build operation missing inside measured interval')
    return dict(lanes=lanes, phases=phases, categories=sorted(categories, key=lambda x:-x['self_seconds']),
                operations=operations, errors=errors, start_ms=start, wall_seconds=(end-start)/1000,
                sync_seconds=(root['end_ns']-root['start_ns'])/1e9 if root else None,
                gradle_seconds=duration((o['start'],o['end']) for o in builds)/1000 if builds else None,
                idea_span_count=len(spans))


def render(run_dir, manifest):
    data = anatomy(run_dir, manifest)
    import hashlib
    manifest['report_fingerprint'] = hashlib.sha256(Path(__file__).read_bytes() + (Path(__file__).parent/'report.html').read_bytes()).hexdigest()
    manifest['anatomy'] = {k:v for k,v in data.items() if k not in ('lanes','operations')}
    if data['errors'] and manifest['status'] == 'success':
        manifest.update(status='failed', error='; '.join(data['errors']))
    (run_dir/'anatomy.json').write_text(json.dumps(data, indent=2))
    esc = lambda v: html.escape(str(v))
    fmt = lambda v: '—' if v is None else f'{v:.3f}'
    def rows(values):
        return ''.join('<tr>'+''.join('<td>'+esc(v)+'</td>' for v in row)+'</tr>' for row in values)
    categories = rows((c['name'], c['count'], fmt(c['wall_seconds']), fmt(c['self_seconds'])) for c in data['categories'])
    phases = rows((p['name'], p['count'], fmt(p['wall_seconds'])) for p in data['phases'])
    processes = []
    for metric in manifest.get('process_metrics', []):
        label = {'idea':'IDEA','gradle':'Gradle daemon','kotlin':'Kotlin compiler daemon'}.get(metric['kind'],metric['kind'])
        links = ' · '.join('<a href="'+esc(g['file'])+'">'+('CPU' if g['event']=='cpu' else 'Allocations')+'</a>'
                          for g in manifest.get('graphs',[]) if g['pid']==metric['pid'])
        processes.append('<tr>'+''.join('<td>'+esc(x)+'</td>' for x in (label,metric['pid'],
            fmt(metric.get('recording_wall_seconds')),fmt(metric.get('sampled_cpu_seconds')),
            fmt(metric['estimated_allocated_bytes']/2**30) if 'estimated_allocated_bytes' in metric else '—'))+'<td>'+links+'</td></tr>')
    top = sorted(data['operations'], key=lambda o:-o['self_ms'])[:30]
    top_rows = rows((o['name'],fmt((o['start']-data['start_ms'])/1000),fmt((o['end']-o['start'])/1000),fmt(o['self_ms']/1000)) for o in top)
    kts = next((c['wall_seconds'] for c in data['categories'] if c['name'].startswith('Kotlin DSL')), 0 if data['operations'] else None)
    idea = next((m for m in manifest.get('process_metrics',[]) if m['kind']=='idea'), {})
    scan, index = idea.get('scanning_samples'), idea.get('content_indexing_samples')
    isolation = (f'{scan} scanning samples · {index} content-indexing samples' if scan is not None else 'No CPU sampling in this timing control' if manifest.get('profile') == 'none' else 'No IDEA sampling evidence')
    wrapper = re.search(r'gradle-([\w.\-]+)-(?:bin|all)\.zip', manifest.get('gradle_wrapper',''))
    links = ' · '.join('<a href="'+name+'">'+label+'</a>' for name,label in [
        ('manifest.json','Manifest'),('anatomy.json','Aligned spans'),('idea-spans.json','IDEA spans'),
        ('gradle-operations-log.txt','Gradle operations'),('events.json','Boundary events'),('import.log','Import log')]
        if (run_dir/name).exists() or name=='manifest.json')
    warm = manifest.get('global_caches') == 'warm'
    full = manifest.get('profile', 'full') == 'full'
    tasks = rows((o['name'].removeprefix('Task '), o.get('outcome', 'unknown'), fmt((o['end']-o['start'])/1000))
                 for o in data['operations'] if o['name'].startswith('Task '))
    calibration = ''
    if manifest.get('calibration_report'):
        control_path = Path(manifest['calibration_report'])
        control = json.loads(control_path.with_name('manifest.json').read_text())
        matched = (control.get('status') == 'success' and control.get('cache_snapshot') == manifest.get('cache_snapshot')
                   and control.get('build_fingerprint') == manifest.get('build_fingerprint')
                   and control.get('global_caches') == manifest.get('global_caches')
                   and control.get('kotlin_version') == manifest.get('kotlin_version')
                   and control.get('gradle_version_override') == manifest.get('gradle_version_override'))
        manifest['calibration'] = dict(matched_snapshot=matched, control_wall_seconds=control.get('anatomy',{}).get('wall_seconds'))
        calibration = ('<section><h2>Timing control</h2><p>Without async-profiler or Gradle operation tracing: <b>' +
                       fmt(control.get('anatomy',{}).get('wall_seconds')) + ' s</b>. This profiled import: <b>' +
                       fmt(data.get('wall_seconds')) + ' s</b>. Same initial cache snapshot and build: ' + str(matched) +
                       '. Both runs retain lightweight IDEA span recording. Other workloads can affect the difference; '
                       'it is not a precise overhead estimate.</p><p><a href="'+esc(control_path.as_uri())+'">Timing control report</a></p></section>')
    cache_note = ('<b>Warm global Gradle caches:</b> each run starts from the same frozen copy of the normal Gradle home’s caches, '
                  'including transforms, generated jars, Kotlin DSL scripts/accessors and build-cache entries. '
                  'Project-local build, .gradle and .kotlin directories are removed. Normal user/project cache settings remain in effect. '
                  'Build outputs may be restored FROM-CACHE; check the task outcomes below.' if warm else
                  '<b>Empty global compilation caches:</b> project outputs and global compilation caches are cleared. '
                  'Build and configuration caching are disabled explicitly. This is the aggressive reset mode.')
    values = dict(TITLE='clean-project import' if warm else 'fully cold import',
        KOTLIN=esc(manifest.get('kotlin_version','unknown')) + (' (explicit override)' if manifest.get('kotlin_version_override') else ''),
        CACHE_MODE='warm snapshot' if warm else 'empty', CACHE_NOTE=cache_note,
        SNAPSHOT=esc((manifest.get('cache_snapshot') or {}).get('id','none')),
        INTRO=('Fresh build JVMs. Cleared project outputs. Warm global Gradle caches and IDEA.' if warm else
               'Fresh build JVMs and compilation caches. Warm IDEA.'),
        INSTRUMENTATION='CPU + allocations + Gradle operations' if full else 'Timing control · IDEA spans only',
        CALIBRATION=calibration, TASKS=tasks,
        PROFILE_NOTE=('CPU and allocation profiles are aligned to the measured import interval.' if full else
                      'No CPU/allocation recording or Gradle operation trace in this control. Indexing guards remained active; there is no sampling check.'),
        RUN=esc(run_dir.name),COMMIT=esc(manifest.get('commit','unknown')[:10]),STATUS=esc(manifest['status'].upper()),
        WALL=fmt(data.get('wall_seconds')),SYNC=fmt(data.get('sync_seconds')),GRADLE=fmt(data.get('gradle_seconds')),KTS=fmt(kts),
        IDEA=esc(manifest.get('idea',{}).get('ideaBuild','unknown')),GRADLE_VERSION=esc(manifest.get('gradle_version_override') or (wrapper[1] if wrapper else 'unknown')) + (' (explicit override)' if manifest.get('gradle_version_override') else ''),
        DEPENDENCIES=esc(manifest.get('dependencies','unknown')),INDEXING=esc(manifest.get('indexing','unknown')),
        ISOLATION=esc(isolation),PHASES=phases,CATEGORIES=categories,PROCESSES=''.join(processes),TOP=top_rows,LINKS=links,
        CONTENTION=esc(', '.join(map(str,manifest.get('interfering_pids',[]))) or 'None observed'),
        ERROR=esc('\n'.join(filter(None,[manifest.get('error','')]+manifest.get('conversion_errors',[])+data['errors']))),
        DATA=json.dumps({k:v for k,v in data.items() if k in ('lanes','wall_seconds')}).replace('<','\\u003c'))
    template = (Path(__file__).parent/'report.html').read_text()
    template = re.sub(r'@@([A-Z_]+)@@', lambda m: values[m[1]], template)
    report = run_dir/'index.html'
    report.write_text(template)
    return report
