import tempfile
import unittest
from pathlib import Path
import subprocess
import struct
from unittest.mock import patch

import profile_import as runner


class CleanupSafetyTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "project"
        self.root.mkdir()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def test_cleans_nested_build_logic_but_preserves_sources_idea_and_symlinks(self):
        for relative in ["build/out", ".gradle/kotlin-dsl/cache", "buildSrc/build/classes", "buildSrc/.gradle/cache", "module/.kotlin/cache"]:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("generated")
        source = self.root / "module/src/Keep.kt"
        source.parent.mkdir(parents=True)
        source.write_text("source")
        idea = self.root / ".idea/build/settings"
        idea.parent.mkdir(parents=True)
        idea.write_text("keep")
        outside = Path(self.temp.name) / "outside"
        (outside / "build").mkdir(parents=True)
        (outside / "build/keep").write_text("external")
        (self.root / "linked").symlink_to(outside, target_is_directory=True)
        removed = runner.clean_project(self.root)
        self.assertIn("buildSrc/.gradle", removed)
        self.assertFalse((self.root / "buildSrc/build").exists())
        self.assertEqual(source.read_text(), "source")
        self.assertEqual(idea.read_text(), "keep")
        self.assertEqual((outside / "build/keep").read_text(), "external")

    def test_tracked_file_aborts_entire_cleanup_before_any_deletion(self):
        generated = self.root / ".gradle/cache"
        generated.parent.mkdir()
        generated.write_text("generated")
        tracked = self.root / "module/build/valuable.txt"
        tracked.parent.mkdir(parents=True)
        tracked.write_text("valuable")
        subprocess.run(["git", "add", "module/build/valuable.txt"], cwd=self.root, check=True)
        with self.assertRaisesRegex(RuntimeError, "tracked files"):
            runner.clean_project(self.root)
        self.assertTrue(generated.exists())
        self.assertEqual(tracked.read_text(), "valuable")

    def test_dependency_seed_copy_is_independent_and_excludes_locks(self):
        source = Path(self.temp.name) / "seed"
        source.mkdir()
        (source / "artifact.jar").write_bytes(b"original")
        (source / "modules-2.lock").write_text("lock")
        target = Path(self.temp.name) / "copy"
        runner.clone_tree(source, target)
        (target / "artifact.jar").write_bytes(b"modified")
        self.assertEqual((source / "artifact.jar").read_bytes(), b"original")
        self.assertFalse((target / "modules-2.lock").exists())

    def test_generated_cache_symlink_aborts_without_touching_target(self):
        outside = Path(self.temp.name) / "cache"
        outside.mkdir()
        (outside / "keep").write_text("external")
        (self.root / ".gradle").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "symlink"):
            runner.clean_project(self.root)
        self.assertEqual((outside / "keep").read_text(), "external")


class GradleHomeTest(unittest.TestCase):
    def test_warm_home_preserves_global_caches_settings_and_resets_from_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root, source, state, snapshot = [base / n for n in ('root','source','state','snapshot')]
            (root / 'gradle/wrapper').mkdir(parents=True)
            (root / 'gradle/wrapper/gradle-wrapper.properties').write_text(
                'distributionUrl=https://services.gradle.org/distributions/gradle-9.8.0-rc-1-all.zip')
            (root / 'gradle.properties').write_text('org.gradle.caching=true\norg.gradle.jvmargs=-Xmx3g\n')
            (source / 'wrapper/dists/gradle-9.8.0-rc-1-all').mkdir(parents=True)
            state.mkdir()
            for name in ('9.8.0-rc-1/kotlin-dsl/scripts/cached','9.8.0-rc-1/transforms/cached',
                         '9.8.0-rc-1/generated-gradle-jars/api.jar','build-cache-1/output','modules-2/artifact'):
                f=snapshot / 'caches' / name
                f.parent.mkdir(parents=True,exist_ok=True)
                f.write_text('snapshot')
            (snapshot / 'gradle.properties').write_text('org.gradle.jvmargs=-Xmx6g\nprivate.token=secret\n')
            with patch.object(runner,'ROOT',root),patch.object(runner,'STATE',state):
                home=runner.prepare_home(source,True,global_caches='warm',snapshot=snapshot)
                properties=(home/'gradle.properties').read_text()
                self.assertNotIn('org.gradle.caching=false',properties)
                self.assertNotIn('org.gradle.configuration-cache=false',properties)
                self.assertIn('org.gradle.jvmargs=-Xmx6g',properties)
                self.assertNotIn('private.token',(home/'measurement-overrides.properties').read_text())
                self.assertEqual((home/'caches/build-cache-1/output').read_text(),'snapshot')
                (home/'caches/build-cache-1/output').write_text('changed by import')
                runner.prepare_home(source,True,global_caches='warm',snapshot=snapshot)
                self.assertEqual((home/'caches/build-cache-1/output').read_text(),'snapshot')
                runner.prepare_home(source,False,global_caches='warm',snapshot=snapshot)
                self.assertFalse((home/'caches/modules-2').exists())
                self.assertTrue((home/'caches/build-cache-1/output').exists())

    def test_snapshot_stays_frozen_until_explicit_refresh(self):
        with tempfile.TemporaryDirectory() as directory:
            base=Path(directory)
            state,source=base/'state',base/'source'
            state.mkdir()
            (source/'caches/build-cache-1').mkdir(parents=True)
            artifact=source/'caches/build-cache-1/output'
            artifact.write_text('before')
            with patch.object(runner,'STATE',state),patch.object(runner,'dependency_fingerprint',return_value='same-build'):
                snapshot=runner.cache_snapshot(source)
                identity=runner.read_json(snapshot/'snapshot.json')['id']
                artifact.write_text('after')
                self.assertEqual(runner.cache_snapshot(source),snapshot)
                self.assertEqual((snapshot/'caches/build-cache-1/output').read_text(),'before')
                self.assertEqual(runner.read_json(snapshot/'snapshot.json')['id'],identity)
                runner.cache_snapshot(source,refresh=True)
                self.assertEqual((snapshot/'caches/build-cache-1/output').read_text(),'after')
                self.assertNotEqual(runner.read_json(snapshot/'snapshot.json')['id'],identity)

    def test_cache_copy_uses_selected_gradle_version(self):
        with tempfile.TemporaryDirectory() as directory:
            base=Path(directory)
            root,source,target=base/'project',base/'caches',base/'copy'
            (root/'gradle/wrapper').mkdir(parents=True)
            (root/'gradle/wrapper/gradle-wrapper.properties').write_text(
                'distributionUrl=../../env/gradle/gradle-9.9.0-bin.zip')
            for name in ('9.9.0/kotlin-dsl','9.8.0-rc-1/kotlin-dsl','build-cache-1','modules-2'):
                (source/name).mkdir(parents=True)
                (source/name/'keep').write_text('cache')
            with patch.object(runner,'ROOT',root):
                runner.clone_caches(source,target,gradle_version='9.8.0-rc-1')
            self.assertFalse((target/'9.9.0').exists())
            self.assertTrue((target/'9.8.0-rc-1/kotlin-dsl/keep').exists())
            self.assertTrue((target/'build-cache-1/keep').exists())
            self.assertTrue((target/'modules-2/keep').exists())

    def test_property_overrides_follow_last_definition_and_continuations(self):
        self.assertEqual(runner.property_value('org.gradle.jvmargs=-Xmx3g\norg.gradle.jvmargs=-Xmx6g\n',
                                              'org.gradle.jvmargs'),'-Xmx6g')

    def test_toolchain_override_is_isolated_and_reset_between_runs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "project"
            state = Path(directory) / "state"
            source = Path(directory) / "normal-home"
            (root / "gradle/wrapper").mkdir(parents=True)
            (root / "gradle/wrapper/gradle-wrapper.properties").write_text(
                "distributionUrl=https://services.gradle.org/distributions/gradle-9.6.1-bin.zip\n")
            (root / "gradle.properties").write_text("org.gradle.jvmargs=-Xmx3g\n")
            (source / "wrapper/dists/gradle-9.6.1-bin").mkdir(parents=True)
            (source / "gradle.properties").write_text("user-setting=keep\n")
            state.mkdir()
            with patch.object(runner, "ROOT", root), patch.object(runner, "STATE", state):
                home = runner.prepare_home(source, False, java_auto_detect="false",
                                           java_installations=["/explicit/jdk11"])
                self.assertIn("org.gradle.java.installations.auto-detect=false\n", (home / "gradle.properties").read_text())
                self.assertIn("org.gradle.java.installations.paths=/explicit/jdk11\n", (home / "gradle.properties").read_text())
                runner.prepare_home(source, False)
                self.assertNotIn("auto-detect", (home / "gradle.properties").read_text())
                self.assertNotIn("installations.paths", (home / "gradle.properties").read_text())
            self.assertEqual((source / "gradle.properties").read_text(), "user-setting=keep\n")
            self.assertEqual((root / "gradle.properties").read_text(), "org.gradle.jvmargs=-Xmx3g\n")


class ReportTimingTest(unittest.TestCase):
    def test_stage_wall_times_partition_import_without_inventing_missing_stages(self):
        events = dict(import_requested=1000, gradle_task_started=1005, model_started=44417,
                      model_applied=44715, model_final_tasks_finished=44987, finished=44988)
        stages = runner.stage_timings(events)
        self.assertEqual([round(s["wall_seconds"], 3) for s in stages], [.005, 43.412, .298, .272, .001])
        self.assertAlmostEqual(sum(s["wall_seconds"] for s in stages), 43.988)
        self.assertEqual(runner.stage_timings({"import_requested": 1000, "failed": 2000}), [])

    def test_jfr_windows_are_cropped_and_overlapping_chunks_not_counted_twice(self):
        with tempfile.TemporaryDirectory() as directory:
            recording = Path(directory) / "test.jfr"
            chunks = []
            for start, duration in [(1, 3), (3, 3)]:
                header = bytearray(68)
                header[:4] = b"FLR\0"
                struct.pack_into(">Q", header, 8, 72)
                struct.pack_into(">QQ", header, 32, start * 10**9, duration * 10**9)
                chunks.append(header + b"data")
            recording.write_bytes(b"".join(chunks))
            self.assertEqual(runner.recording_window(recording, 2000, 5000), 3)
            self.assertEqual(runner.recording_window(recording, 8000, 9000), 0)
            self.assertIsNone(runner.recording_window(recording, None, None))

    def test_sample_metrics_distinguish_background_indexing_from_index_queries(self):
        with tempfile.TemporaryDirectory() as directory:
            collapsed = Path(directory) / "cpu.collapsed"
            collapsed.write_text("root;UnindexedFilesScanner.scan 3\nroot;FileBasedIndex.query 5\nroot;IndexUpdateRunner.run 2\n")
            self.assertEqual(runner.collapsed_totals(collapsed), (10, 5))
            self.assertEqual(runner.cpu_interval_seconds("2ms"), .002)
            self.assertEqual(runner.cpu_interval_seconds("2000000"), .002)

    def test_isolation_counts_workers_but_not_skipped_indexer_or_queue_control(self):
        with tempfile.TemporaryDirectory() as directory:
            collapsed = Path(directory) / "cpu.collapsed"
            collapsed.write_text("root;UnindexedFilesScanner$ScanningSession.scanFiles 3\n"
                                 "root;IndexUpdateRunner$Indexer.indexOneFile 2\n"
                                 "root;UnindexedFilesIndexer.indexFiles;SystemProperties.getBooleanProperty 5\n"
                                 "root;UnindexedFilesScannerExecutorImpl.submitTask 7\n"
                                 "root;FileBasedIndex.query 11\n")
            self.assertEqual(runner.background_work_samples(collapsed),
                             dict(scanning_samples=3, content_indexing_samples=2))


class PreflightTest(unittest.TestCase):
    def test_concurrent_reset_only_stops_this_runners_build_processes(self):
        processes = [dict(pid=1, kind="other", command="idea"),
                     dict(pid=2, kind="gradle", command="java other-experiment"),
                     dict(pid=3, kind="gradle", command="java -agentpath=" + str(runner.STATE) + "/runs/one"),
                     dict(pid=4, kind="other", command="java " + str(runner.STATE) + "/unrelated")]
        with patch.object(runner, "java_processes", return_value=processes), patch.object(runner, "stop_processes") as stop:
            stopped = runner.reset_processes(1, concurrent=True)
            self.assertEqual([p["pid"] for p in stopped], [3])
            stop.assert_called_once_with([processes[2]])

    def test_process_exit_between_ps_state_and_argv_is_rechecked(self):
        uid = runner.os.getuid()
        for latest, expected in [("", []), ("Z (java)", []), ("R /bin/java OtherMain", [2])]:
            with self.subTest(latest=latest), patch.object(runner, "run", side_effect=[
                subprocess.CompletedProcess([], 0, stdout="2 /bin/java\n"),
                subprocess.CompletedProcess([], 0, stdout=f"2 1 {uid} R (java)\n"),
            ]), patch.object(runner.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, stdout=latest)):
                self.assertEqual([p["pid"] for p in runner.java_processes()], expected)

    def test_exited_java_children_are_not_running_jvms(self):
        uid = runner.os.getuid()
        comms = "1 /bin/idea\n2 /bin/java\n3 /bin/java\n"
        args = f"1 0 {uid} S /bin/idea\n2 1 {uid} Z (java)\n3 1 {uid} R /bin/java Main\n"
        with patch.object(runner, "run", side_effect=[
            subprocess.CompletedProcess([], 0, stdout=comms),
            subprocess.CompletedProcess([], 0, stdout=args),
        ]):
            processes = runner.java_processes()
        self.assertEqual([p["pid"] for p in processes], [1, 3])
        self.assertEqual(processes[1]["command"], "/bin/java Main")

    def test_stale_driver_cannot_silently_measure_without_indexing_pause(self):
        with patch.object(runner, "rpc", return_value={"prepared": True}):
            with self.assertRaisesRegex(RuntimeError, "did not confirm"):
                runner.prepare_session("paused")
            self.assertEqual(runner.prepare_session("normal"), {"prepared": True})
        with patch.object(runner, "rpc", return_value={"prepared": True, "indexingPaused": True}):
            with self.assertRaisesRegex(RuntimeError, "did not confirm"):
                runner.prepare_session("paused")
        current = {"prepared": True, "indexingPaused": True, "scanningDeferred": True}
        with patch.object(runner, "rpc", return_value=current):
            with self.assertRaisesRegex(RuntimeError, "did not confirm"):
                runner.prepare_session("paused")
        current["contentIndexingDeferred"] = True
        with patch.object(runner, "rpc", return_value=current):
            self.assertEqual(runner.prepare_session("paused"), current)

    def test_startup_metadata_corrects_transient_rosetta_probe_classification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            runner.write_json(root / "jvm-2.json", dict(pid=2, kind="probe", mainClass="JavaProbe"))
            runner.write_json(root / "jvm-3.json", dict(pid=3, kind="kotlin"))
            processes = {1: dict(pid=1, kind="idea"), 2: dict(pid=2, kind="other")}
            manifest = {}
            runner.merge_child_metadata(root, processes, manifest)
            self.assertEqual(set(processes), {1, 3})
            self.assertEqual(manifest["excluded_probes"]["2"]["mainClass"], "JavaProbe")

    def test_unrelated_jvm_prevents_any_process_termination(self):
        processes = [dict(pid=1, kind="other", executable="idea"),
                     dict(pid=2, kind="gradle", executable="java"),
                     dict(pid=3, kind="other", executable="java")]
        with patch.object(runner, "java_processes", return_value=processes), patch.object(runner, "stop_processes") as stop:
            with self.assertRaisesRegex(RuntimeError, "Unrelated JVMs"):
                runner.reset_processes(1)
            stop.assert_not_called()

    def test_no_recordings_cannot_produce_a_successful_report(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = dict(status="success", dependencies="cached")
            report = runner.create_report(Path(directory), manifest, "unused", {})
            self.assertEqual(manifest["status"], "failed")
            self.assertIn("Gradle startup recording is missing", report.read_text())


if __name__ == "__main__":
    unittest.main()
