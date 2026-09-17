import json
from pathlib import Path
import tempfile
import unittest

from import_report import anatomy, category, duration, gradle_operations, render


class AnatomyTest(unittest.TestCase):
    def test_kotlin_dsl_classpath_transforms_are_not_script_compilation(self):
        self.assertEqual(category('Execute transform chain: groovy-json.jar (Gradle Kotlin DSL)'),
                         'Dependencies / transforms / generated jars')
        self.assertEqual(category('Compile script settings.gradle.kts (CLASSPATH)'),
                         'Kotlin DSL compilation / accessors')
        self.assertEqual(category("Fetch model 'KotlinDslScriptAdditionalTask' for build scope"),
                         'Other Gradle operations')

    def test_interval_union_does_not_double_count_nested_or_parallel_work(self):
        self.assertEqual(duration([(0,10),(2,5),(8,12),(15,16),(20,20)]),13)

    def test_operation_self_time_subtracts_union_of_children_and_clips_window(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'operations.jsonl'
            entries = [dict(id=1,startTime=0,displayName='Run build'),
                       dict(id=2,parentId=1,startTime=2,displayName='Task :buildSrc:compileKotlin'),
                       dict(id=3,parentId=1,startTime=3,displayName='Resolve dependencies'),
                       dict(id=2,endTime=6), dict(id=3,endTime=8), dict(id=1,endTime=12)]
            path.write_text('\n'.join(map(json.dumps,entries)))
            ops = {o['id']:o for o in gradle_operations(path,1,10)}
            self.assertEqual(ops[1]['self_ms'],3)
            self.assertEqual((ops[1]['start'],ops[1]['end']),(1,10))
            self.assertEqual(ops[2]['category'],'Build tasks (including buildSrc)')

    def test_report_selects_the_measured_trace_and_rejects_stale_gradle_trace(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            spans = [dict(name='ExternalSystemSyncProjectTask',start_ns=1000_000_000,end_ns=2000_000_000,trace='ours'),
                     dict(name='GradleCall',start_ns=1100_000_000,end_ns=1800_000_000,trace='ours'),
                     dict(name='GradleCall',start_ns=1100_000_000,end_ns=1900_000_000,trace='other')]
            (path/'idea-spans.json').write_text(json.dumps(spans))
            entries=[dict(id=1,startTime=1100,displayName='Run build'),dict(id=1,endTime=1900)]
            (path/'gradle-operations-log.txt').write_text('\n'.join(map(json.dumps,entries)))
            manifest=dict(status='success',events=dict(import_requested=1000,finished=2000))
            result=anatomy(path,manifest)
            self.assertEqual(result['errors'],[])
            self.assertEqual(result['idea_span_count'],2)
            self.assertEqual(result['phases'][1]['wall_seconds'],.7)
            entries[0]['startTime']=10
            (path/'gradle-operations-log.txt').write_text('\n'.join(map(json.dumps,entries)))
            self.assertIn('Complete Gradle Run build operation missing',anatomy(path,manifest)['errors'][0])

    def test_timing_control_does_not_require_gradle_operation_trace(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)
            (path/'idea-spans.json').write_text(json.dumps([dict(name='ExternalSystemSyncProjectTask',
                start_ns=1000000000,end_ns=2000000000,trace='ours')]))
            manifest=dict(status='success',profile='none',operations_trace=False,
                          events=dict(import_requested=1000,finished=2000))
            result=anatomy(path,manifest)
            self.assertEqual(result['errors'],[])
            self.assertIsNone(result['gradle_seconds'])

    def test_missing_anatomy_cannot_look_like_success_and_html_escapes_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)
            manifest=dict(status='success',commit='<script>alert(1)</script>',events=dict(import_requested=1000,finished=2000))
            report=render(path,manifest).read_text()
            self.assertEqual(manifest['status'],'failed')
            self.assertIn('IDEA sync root span missing',report)
            self.assertNotIn('<script>al',report)
            self.assertNotIn('@@',report)


if __name__=='__main__':
    unittest.main()
