#!/usr/bin/env python3
"""Clean-project Gradle reimport in a warm IDEA. Python standard library only; macOS/Linux."""
import argparse
import fcntl
import hashlib
import html
import json
import os
from pathlib import Path
import re
import shutil
import signal
import struct
import subprocess
import sys
import time
import uuid
import zipfile

TOOL = Path(__file__).resolve().parent
ROOT = TOOL.parent.parent
STATE = Path(os.environ.get("IMPORT_PROFILE_STATE", str(Path.home() / ".cache" / "coroutines-import-profile"))) / hashlib.sha256(str(ROOT).encode()).hexdigest()[:12]
KINDS = {"org.gradle.launcher.daemon.bootstrap.GradleDaemon": "gradle",
         "org.jetbrains.kotlin.daemon.KotlinCompileDaemon": "kotlin",
         "GradleWorkerMain": "worker",
         "org.jetbrains.jps.cmdline.Launcher": "jps",
         "JavaProbe": "probe"}


def log(message):
    print(message, flush=True)


def run(args, **kwargs):
    return subprocess.run([str(x) for x in args], check=True, text=True, **kwargs)


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(value, indent=2))
    tmp.replace(path)


def read_json(path):
    return json.loads(path.read_text())


def alive(pid):
    try:
        os.kill(int(pid), 0)
        return True
    except ProcessLookupError:
        return False


def bridge_alive():
    try:
        value = read_json(STATE / "bridge.json")
        return alive(value["pid"]) and time.time() * 1000 - value["heartbeat"] < 15000
    except (FileNotFoundError, ValueError, KeyError):
        return False


def rpc(command, timeout=30, **values):
    request_id = uuid.uuid4().hex
    inbox = STATE / "inbox" / (request_id + ".json")
    reply = STATE / "replies" / inbox.name
    write_json(inbox, dict(command=command, **values))
    deadline = time.monotonic() + timeout
    while not reply.exists():
        if time.monotonic() > deadline:
            inbox.unlink(missing_ok=True)
            raise RuntimeError("IDEA driver did not answer " + command)
        time.sleep(.1)
    response = read_json(reply)
    reply.unlink()
    if not response["ok"]:
        raise RuntimeError(response["error"])
    return response["result"]


def idea_contents(explicit=None):
    if explicit:
        path = Path(explicit).expanduser().resolve()
        return path / "Contents" if path.suffix == ".app" else path
    candidates = [Path.home() / "Applications/IntelliJ IDEA.app/Contents", Path("/Applications/IntelliJ IDEA.app/Contents")]
    for path in candidates:
        if path.exists():
            return path
    raise RuntimeError("Supply --idea with the IDEA application/Contents path")


def find_jdk(explicit=None):
    if explicit:
        return Path(explicit).expanduser().resolve()
    candidates = []
    if os.environ.get("JAVA_HOME"):
        candidates.append(Path(os.environ["JAVA_HOME"]))
    candidates += sorted((Path.home() / "Library/Java/JavaVirtualMachines").glob("*/Contents/Home"), reverse=True)
    for path in candidates:
        if (path / "bin/javac").exists():
            version = run([path / "bin/javac", "-version"], capture_output=True).stdout
            if int(re.search(r"javac (\d+)", version)[1]) >= 21:
                return path
    raise RuntimeError("Supply --jdk with a JDK 21+ containing javac")


def install(args):
    fingerprint = hashlib.sha256((TOOL / "IdeaBridge.java").read_bytes() + (TOOL / "ImportTelemetry.java").read_bytes()).hexdigest()
    if bridge_alive():
        current = rpc("info")
        if current.get("driverFingerprint") == fingerprint:
            return
        if current.get("prepared"):
            raise RuntimeError("Restore the active measurement before updating the IDEA driver")
        log("Updating the IDEA driver without restarting IDEA.")
        rpc("close")
    contents = idea_contents(args.idea)
    jdk = find_jdk(args.jdk)
    build = STATE / "driver"
    build.mkdir(parents=True, exist_ok=True)
    # Compile directly against this IDEA installation, without starting Gradle.
    jars = list((contents / "lib").glob("*.jar")) + list((contents / "plugins/gradle-plugin/lib").glob("*.jar"))
    classpath = os.pathsep.join(map(str, jars))
    run([jdk / "bin/javac", "-proc:none", "--release", "21", "-classpath", classpath,
         "-d", build, TOOL / "IdeaBridge.java", TOOL / "ImportTelemetry.java"])
    jar = STATE / "driver.jar"
    with zipfile.ZipFile(jar, "w", zipfile.ZIP_DEFLATED) as archive:
        for path in build.rglob("*.class"):
            archive.write(path, path.relative_to(build))
    # Groovy's default script loader cannot see Gradle's content modules. Parent
    # the tiny driver to the actual Gradle manager's plugin class loader.
    literal = lambda value: "'" + str(value).replace("\\", "\\\\").replace("'", "\\'") + "'"
    script = STATE / "install.groovy"
    script.write_text("""import com.intellij.openapi.externalSystem.util.ExternalSystemApiUtil
import com.intellij.openapi.externalSystem.model.ProjectSystemId
try {
  def parent = ExternalSystemApiUtil.getManager(new ProjectSystemId('GRADLE')).class.classLoader
  def loader = new URLClassLoader([new File(JAR).toURI().toURL()] as URL[], parent)
  loader.loadClass('coroutines.profile.IdeaBridge').getMethod('install', String, String, String, String, String)
    .invoke(null, STATE, TOOL, ROOT, PYTHON, FINGERPRINT)
} catch (Throwable error) {
  def writer = new StringWriter(); error.printStackTrace(new PrintWriter(writer))
  new File(ERROR).text = writer.toString()
}
""".replace("JAR", literal(jar)).replace("STATE", literal(STATE)).replace("TOOL", literal(TOOL))
        .replace("ROOT", literal(ROOT)).replace("PYTHON", literal(sys.executable)).replace("FINGERPRINT", literal(fingerprint))
        .replace("ERROR", literal(STATE / "install-error.log")))
    (STATE / "install-error.log").unlink(missing_ok=True)
    launcher = contents / "MacOS/idea" if sys.platform == "darwin" else contents / "bin/idea.sh"
    run([launcher, "ideScript", script])
    deadline = time.monotonic() + 45
    while not bridge_alive():
        if (STATE / "install-error.log").exists():
            raise RuntimeError((STATE / "install-error.log").read_text())
        if time.monotonic() > deadline:
            raise RuntimeError("IDEA did not load the driver. Check idea.log for ideScript errors; enable bundled Groovy scripting if necessary.")
        time.sleep(.2)
    write_json(STATE / "installation.json", {"idea": str(contents), "jdk": str(jdk), "tool": str(TOOL),
                                           "asprof": shutil.which("asprof"), "jfrconv": shutil.which("jfrconv")})
    log("Installed Tools → Profile Cold Gradle Import in IDEA PID " + str(rpc("info")["pid"]))


def java_processes():
    comms = {}
    for line in run(["ps", "-axo", "pid=,comm="], capture_output=True).stdout.splitlines():
        fields = line.strip().split(None, 1)
        if len(fields) == 2:
            comms[int(fields[0])] = fields[1]
    result = []
    for line in run(["ps", "-axo", "pid=,ppid=,uid=,stat=,args="], capture_output=True).stdout.splitlines():
        fields = line.strip().split(None, 4)
        if len(fields) != 5:
            continue
        pid, ppid, uid = map(int, fields[:3])
        executable = comms.get(pid, "")
        if uid != os.getuid() or fields[3].startswith("Z") or Path(executable).name not in ("java", "idea"):
            continue
        command = fields[4]
        # On macOS the process may exit between ps reading its state and argv.
        # Recheck an unavailable argv before treating the stale row as a live JVM.
        if command == "(" + Path(executable).name + ")":
            latest = subprocess.run(["ps", "-p", str(pid), "-o", "stat=,args="],
                                    text=True, capture_output=True).stdout.strip().split(None, 1)
            if not latest or latest[0].startswith("Z"):
                continue
            if len(latest) == 2:
                command = latest[1]
        kind = next((kind for marker, kind in KINDS.items() if marker in command), "other")
        result.append(dict(pid=pid, ppid=ppid, kind=kind, executable=executable, command=command))
    return result


def stop_processes(processes):
    for proc in processes:
        if alive(proc["pid"]):
            log("Stopping {} JVM {}".format(proc["kind"], proc["pid"]))
            try:
                os.kill(proc["pid"], signal.SIGTERM)
            except ProcessLookupError:
                pass
    deadline = time.monotonic() + 10
    while any(alive(p["pid"]) for p in processes) and time.monotonic() < deadline:
        time.sleep(.1)
    for proc in processes:
        if alive(proc["pid"]):
            os.kill(proc["pid"], signal.SIGKILL)
    deadline = time.monotonic() + 5
    while any(alive(p["pid"]) for p in processes) and time.monotonic() < deadline:
        time.sleep(.1)
    if any(alive(p["pid"]) for p in processes):
        raise RuntimeError("A JVM did not exit; refusing to clear caches")


def owned_daemon(pid):
    return any((STATE / "gradle-home/daemon").glob("*/daemon-" + str(pid) + ".out.log"))


def reset_processes(idea_pid, concurrent=False):
    if concurrent:
        # Only processes whose command names this runner's isolated state belong to us.
        processes = [p for p in java_processes() if p["pid"] != idea_pid
                     and p["kind"] in ("gradle", "kotlin", "worker", "jps")
                     and (str(STATE) + "/" in p["command"] or owned_daemon(p["pid"]))]
        stop_processes(processes)
        return [{k: v for k, v in p.items() if k != "command"} for p in processes]

    processes = [p for p in java_processes() if p["pid"] != idea_pid]
    unknown = [p for p in processes if p["kind"] == "other"]
    if unknown:
        raise RuntimeError("Unrelated JVMs are running; close them before measuring: " +
                           ", ".join(str(p["pid"]) + " " + p["executable"] for p in unknown))
    stop_processes(processes)
    remaining = [p for p in java_processes() if p["pid"] != idea_pid]
    if remaining:
        raise RuntimeError("JVMs appeared during reset: " + str([p["pid"] for p in remaining]))
    return [{k: v for k, v in p.items() if k != "command"} for p in processes]


def cleanup_candidates(root):
    candidates = []
    for parent, directories, _ in os.walk(root, followlinks=False):
        for name in list(directories):
            path = Path(parent) / name
            if path.is_symlink() and name in {"build", ".gradle", ".kotlin"}:
                raise RuntimeError("Refusing to follow a generated-cache symlink: " + str(path))
            if name in {".git", ".idea", "node_modules"} or path.is_symlink():
                directories.remove(name)
            elif name in {"build", ".gradle", ".kotlin"}:
                candidates.append(path)
                directories.remove(name)
    return candidates


def clean_project(root=None):
    root = ROOT if root is None else root
    candidates = cleanup_candidates(root)
    tracked = run(["git", "ls-files", "-z"], cwd=root, capture_output=True).stdout.split("\0")
    for path in candidates:
        prefix = path.relative_to(root).as_posix() + "/"
        if any(name.startswith(prefix) for name in tracked if name):
            raise RuntimeError("Refusing to delete tracked files in " + str(path))
    for path in candidates:
        shutil.rmtree(path)
    return [str(p.relative_to(root)) for p in candidates]


def clone_file(src, dst):
    # APFS copy-on-write clones are independent files (never hard links).
    if sys.platform == "darwin":
        copied = subprocess.run(["cp", "-c", str(src), str(dst)], capture_output=True)
        if copied.returncode == 0:
            return str(dst)
    return shutil.copy2(src, dst)


def clone_tree(src, dst):
    if sys.platform == "darwin":
        dst.parent.mkdir(parents=True, exist_ok=True)
        copied = subprocess.run(["cp", "-cR", str(src), str(dst)], capture_output=True)
        if copied.returncode == 0:
            for pattern in ("*.lock", "gc.properties"):
                for path in dst.rglob(pattern):
                    if path.is_file():
                        path.unlink()
            return
        if dst.exists():
            shutil.rmtree(dst)
    shutil.copytree(src, dst, copy_function=clone_file,
                    ignore=shutil.ignore_patterns("*.lock", "gc.properties"))


def dependency_fingerprint():
    digest = hashlib.sha256()
    paths = list(ROOT.rglob("*.gradle.kts")) + list((ROOT / "buildSrc/src").rglob("*.kt")) + list((ROOT / "gradle").glob("*.toml"))
    for path in sorted(set(paths)):
        if any(p in {".gradle", "build", ".git"} for p in path.relative_to(ROOT).parts):
            continue
        digest.update(str(path.relative_to(ROOT)).encode()); digest.update(path.read_bytes())
    for path in [ROOT / "gradle.properties", ROOT / "gradle/wrapper/gradle-wrapper.properties"]:
        digest.update(path.read_bytes())
    return digest.hexdigest()


def property_value(text, key, default=None):
    # Gradle properties use Java continuation lines and last-definition-wins semantics.
    text = re.sub(r"\\\r?\n[ \t]*", "", text)
    matches = re.findall(r"^[ \t]*" + re.escape(key) + r"[ \t]*[=:][ \t]*(.*)$", text, re.M)
    return matches[-1].strip() if matches else default


def clone_caches(source, target, gradle_version=None):
    target.mkdir(parents=True, exist_ok=True)
    wrapper = (ROOT / "gradle/wrapper/gradle-wrapper.properties").read_text()
    version = gradle_version or re.search(r"gradle-(.+)-(?:bin|all)\.zip", wrapper)[1]
    for entry in source.iterdir():
        # Version-specific caches from other Gradle distributions cannot serve this build.
        if re.match(r"^\d+\.\d", entry.name) and entry.name != version:
            continue
        if entry.name.endswith(".lock"):
            continue
        if entry.is_dir():
            clone_tree(entry, target / entry.name)
        elif entry.is_file():
            clone_file(entry, target / entry.name)


def cache_snapshot(source, refresh=False, gradle_version=None):
    snapshot = STATE / "global-cache-snapshot"
    stamp = snapshot / "snapshot.json"
    identity = dict(source=str(source), build=dependency_fingerprint(), gradle_version=gradle_version)
    if stamp.exists() and not refresh and read_json(stamp).get("identity") == identity:
        return snapshot
    log("Snapshotting global Gradle caches (outside the measured interval).")
    temporary = STATE / "global-cache-snapshot.tmp"
    if temporary.exists():
        shutil.rmtree(temporary)
    temporary.mkdir()
    for name in ("caches", "gradle.properties", "init.d", "init.gradle", "init.gradle.kts"):
        original = source / name
        if original.is_dir():
            clone_caches(original, temporary / name, gradle_version) if name == "caches" else clone_tree(original, temporary / name)
        elif original.is_file():
            clone_file(original, temporary / name)
    write_json(temporary / "snapshot.json", dict(identity=identity, id=uuid.uuid4().hex,
                                                created_at=time.strftime("%Y-%m-%dT%H:%M:%S%z")))
    if snapshot.exists():
        shutil.rmtree(snapshot)
    temporary.rename(snapshot)
    return snapshot


def prepare_home(source, cached, agent="", java_auto_detect="default", java_installations=(),
                 global_caches="empty", snapshot=None, kotlin_version=None, gradle_version=None):
    home = STATE / "gradle-home"
    if home.exists():
        shutil.rmtree(home)
    home.mkdir()
    # Provision tools without executing Gradle. Leave the user's normal home untouched.
    wrapper = (ROOT / "gradle/wrapper/gradle-wrapper.properties").read_text()
    distribution = re.search(r"distributionUrl=.*[/](gradle-[^/]+)\.zip", wrapper)[1]
    if gradle_version:
        distribution = next(("gradle-" + gradle_version + "-" + kind for kind in ("all", "bin")
                             if (source / "wrapper/dists" / ("gradle-" + gradle_version + "-" + kind)).is_dir()),
                            "gradle-" + gradle_version + "-all")
    original_distribution = source / "wrapper/dists" / distribution
    if not original_distribution.is_dir():
        raise RuntimeError("Gradle distribution must be provisioned first: " + str(original_distribution))
    clone_tree(original_distribution, home / "wrapper/dists" / distribution)
    if (source / "jdks").exists():
        clone_tree(source / "jdks", home / "jdks")
    original_properties = ""
    if global_caches == "warm":
        if snapshot is None:
            raise ValueError("Warm global caches require a frozen snapshot")
        for name in ("caches", "init.d", "init.gradle", "init.gradle.kts"):
            original = snapshot / name
            if original.is_dir():
                clone_caches(original, home / name, gradle_version) if name == "caches" else clone_tree(original, home / name)
            elif original.is_file():
                clone_file(original, home / name)
        if (snapshot / "gradle.properties").exists():
            original_properties = (snapshot / "gradle.properties").read_text()
    modules = home / "caches/modules-2"
    if cached and (STATE / "seed/modules-2").exists():
        # The seed changes only downloaded artifacts, never the frozen compilation caches.
        if modules.exists():
            shutil.rmtree(modules)
        clone_tree(STATE / "seed/modules-2", modules)
    elif not cached and modules.exists():
        shutil.rmtree(modules)
    properties = (ROOT / "gradle.properties").read_text()
    jvmargs = property_value(original_properties, "org.gradle.jvmargs",
                            property_value(properties, "org.gradle.jvmargs", "-Xmx3g"))
    overrides = ("org.gradle.caching=false\norg.gradle.configuration-cache=false\n"
                 if global_caches == "empty" else "")
    overrides += "org.gradle.jvmargs=" + jvmargs + (" " + agent if agent else "") + "\n"
    if kotlin_version:
        overrides += "kotlin_version=" + kotlin_version + "\n"
    if java_auto_detect != "default":
        overrides += "org.gradle.java.installations.auto-detect=" + java_auto_detect + "\n"
    if java_installations:
        overrides += "org.gradle.java.installations.paths=" + ",".join(java_installations) + "\n"
    (home / "gradle.properties").write_text(original_properties + "\n" + overrides)
    # Do not copy unrelated user properties (which may include credentials) into the report.
    (home / "measurement-overrides.properties").write_text(overrides)
    return home


def profiler_tools():
    installation = read_json(STATE / "installation.json") if (STATE / "installation.json").exists() else {}
    asprof = shutil.which("asprof") or installation.get("asprof")
    converter = shutil.which("jfrconv") or installation.get("jfrconv")
    if not asprof or not converter:
        raise RuntimeError("asprof and jfrconv must be on PATH")
    prefix = Path(asprof).resolve().parent.parent
    library = next(iter((prefix / "lib").glob("libasyncProfiler.*")), None)
    if library is None:
        raise RuntimeError("Cannot find async-profiler library below " + str(prefix))
    return asprof, converter, library


def build_child_agent(library):
    """Compile outside the measurement, and cache by source and profiler version."""
    api = library.parent.parent / "libexec/async-profiler.jar"
    target = STATE / "child-profiler.jar"
    fingerprint = hashlib.sha256((TOOL / "ChildProfiler.java").read_bytes() + api.read_bytes()).hexdigest()
    stamp = STATE / "child-profiler.sha256"
    if target.exists() and stamp.exists() and stamp.read_text() == fingerprint:
        return target
    jdk = Path(read_json(STATE / "installation.json")["jdk"])
    classes = STATE / "child-profiler-classes"
    classes.mkdir(exist_ok=True)
    run([jdk / "bin/javac", "--release", "8", "-proc:none", "-cp", api, "-d", classes, TOOL / "ChildProfiler.java"])
    with zipfile.ZipFile(target, "w", zipfile.ZIP_DEFLATED) as jar:
        jar.writestr("META-INF/MANIFEST.MF", "Manifest-Version: 1.0\nPremain-Class: coroutines.profile.ChildProfiler\n\n")
        for path in classes.rglob("*.class"):
            jar.write(path, path.relative_to(classes))
        with zipfile.ZipFile(api) as source:
            for name in source.namelist():
                if name.startswith("one/profiler/") and name.endswith(".class"):
                    jar.writestr(name, source.read(name))
    stamp.write_text(fingerprint)
    return target


def wait_import(run_dir, timeout, observe=lambda: None):
    deadline = time.monotonic() + timeout
    while not (run_dir / "result.json").exists():
        observe()
        if time.monotonic() > deadline:
            raise RuntimeError("Import timed out; see events.json and import.log")
        if not bridge_alive():
            raise RuntimeError("IDEA driver stopped responding")
        time.sleep(.2)
    observe()
    result = read_json(run_dir / "result.json")
    if not result["ok"]:
        raise RuntimeError("IDEA import failed: " + result["error"])
    return result


def prepare_session(indexing):
    prepared = rpc("prepare", timeout=150, indexing=indexing)
    if indexing == "paused" and not (prepared.get("indexingPaused") and prepared.get("scanningDeferred")
                                    and prepared.get("contentIndexingDeferred")):
        raise RuntimeError("IDEA did not confirm the indexing pause; uninstall and reinstall the driver")
    return prepared


def gradle_installation(home, version):
    if not version:
        return ""
    candidates = sorted((home / "wrapper/dists").glob("gradle-" + version + "-*/*/gradle-" + version))
    return str(next((p for p in candidates if (p / "bin/gradle").is_file()), ""))


def seed_dependencies(source, args, info):
    seed = STATE / "seed"
    fingerprint = dependency_fingerprint()
    stamp = seed / "manifest.json"
    if (stamp.exists() and not args.refresh_seed and read_json(stamp).get("fingerprint") == fingerprint
            and read_json(stamp).get("ideaBuild") == info["ideaBuild"]
            and read_json(stamp).get("kotlin_version") == args.kotlin_version
            and read_json(stamp).get("gradle_version") == args.gradle_version):
        return
    log("Preparing dependency seed with an unmeasured IDEA import (once per build configuration).")
    run_dir = STATE / "seed-imports" / time.strftime("%Y%m%d-%H%M%S")
    run_dir.mkdir(parents=True)
    try:
        prepare_session(args.indexing)
        reset_processes(info["pid"], args.allow_concurrent)
        clean_project()
        home = prepare_home(source, False, kotlin_version=args.kotlin_version, gradle_version=args.gradle_version)
        # Existing downloads are a starting point only. The real import fills any gaps.
        if (source / "caches/modules-2").exists():
            clone_tree(source / "caches/modules-2", home / "caches/modules-2")
        rpc("import", run=str(run_dir), gradleHome=str(home), offline=False, gradleInstallation=gradle_installation(home, args.gradle_version))
        wait_import(run_dir, args.timeout)
        reset_processes(info["pid"], args.allow_concurrent)
        if seed.exists():
            shutil.rmtree(seed)
        clone_tree(home / "caches/modules-2", seed / "modules-2")
        write_json(stamp, {"fingerprint": fingerprint, "ideaBuild": info["ideaBuild"], "primingImport": str(run_dir), "kotlin_version": args.kotlin_version, "gradle_version": args.gradle_version})
    finally:
        try:
            reset_processes(info["pid"], concurrent=True)
        finally:
            rpc("restore")


PROCESS_LABELS = {"idea": "IDEA", "gradle": "Gradle daemon", "kotlin": "Kotlin compiler daemon",
                  "worker": "Gradle worker", "jps": "IDEA build process"}


def stage_timings(events):
    boundaries = [("Import dispatch", "import_requested", "gradle_task_started"),
                  ("Gradle resolution", "gradle_task_started", "model_started"),
                  ("Final IDEA model application", "model_started", "model_applied"),
                  ("Model finalization", "model_applied", "model_final_tasks_finished"),
                  ("Completion", "model_final_tasks_finished", "finished")]
    return [dict(stage=label, wall_seconds=(events[end] - events[start]) / 1000)
            for label, start, end in boundaries if start in events and end in events and events[end] >= events[start]]


def recording_window(recording, start, end):
    """JFR chunk timestamps, intersected with the measured interval; not busy time."""
    if start is None or end is None:
        return None
    spans = []
    with recording.open("rb") as stream:
        while header := stream.read(68):
            if len(header) < 68 or header[:4] != b"FLR\0":
                raise ValueError("Invalid JFR chunk: " + str(recording))
            size = struct.unpack_from(">Q", header, 8)[0]
            epoch, duration = struct.unpack_from(">QQ", header, 32)
            if size < 68:
                raise ValueError("Unclosed JFR chunk: " + str(recording))
            spans.append((max(start / 1000, epoch / 1e9), min(end / 1000, (epoch + duration) / 1e9)))
            stream.seek(size - 68, 1)
    # Merge any overlapping chunks instead of counting their intervals twice.
    total, previous = 0, float("-inf")
    for left, right in sorted(spans):
        total += max(0, right - max(left, previous))
        previous = max(previous, right)
    return total


def collapsed_totals(path):
    total = background = 0
    for line in path.read_text().splitlines():
        stack, count = line.rsplit(" ", 1)
        count = int(count)
        total += count
        if re.search(r"UnindexedFiles|IndexUpdateRunner|IndexUpdateWriter", stack):
            background += count
    return total, background


def background_work_samples(path):
    """Count worker stacks, excluding queue control, skipped indexers and index queries."""
    result = dict(scanning_samples=0, content_indexing_samples=0)
    for line in path.read_text().splitlines():
        stack, count = line.rsplit(" ", 1)
        count = int(count)
        if re.search(r"UnindexedFilesScanner(?:\$ScanningSession|\.scan|\.perform)", stack):
            result["scanning_samples"] += count
        if re.search(r"IndexUpdateRunner|IndexUpdateWriter", stack):
            result["content_indexing_samples"] += count
    return result


def cpu_interval_seconds(interval):
    match = re.fullmatch(r"([0-9]+)(ns|us|ms|s)?", interval)
    if not match:
        return None
    return int(match[1]) * {None: 1e-9, "ns": 1e-9, "us": 1e-6, "ms": 1e-3, "s": 1}[match[2]]


def create_report(run_dir, manifest, converter, processes):
    graphs, errors, metrics = [], [], []
    events = manifest.get("events", {})
    start, end = events.get("import_requested"), events.get("finished", events.get("failed"))
    interval = cpu_interval_seconds(manifest.get("cpu_interval", "2ms"))
    environment = os.environ.copy()
    if (STATE / "installation.json").exists():
        environment["JAVA_HOME"] = read_json(STATE / "installation.json")["jdk"]
    for recording in sorted(run_dir.glob("*.jfr")):
        pid = int(recording.stem.split("-")[-1])
        kind = processes.get(pid, {}).get("kind", "jvm")
        metric = dict(kind=kind, pid=pid)
        try:
            metric["recording_wall_seconds"] = recording_window(recording, start, end)
        except ValueError as error:
            errors.append(str(error))
        for event in ("cpu", "alloc"):
            target = run_dir / (kind + "-" + str(pid) + "-" + event + ".html")
            command = [converter, "--" + event, "--title", PROCESS_LABELS.get(kind, kind) + " " + event + " (PID " + str(pid) + ")"]
            if event == "alloc":
                command += ["--total"]
            if start is not None and end is not None:
                command += ["--from", str(start), "--to", str(end)]
            try:
                run(command + [recording, target], capture_output=True, env=environment)
                collapsed = target.with_suffix(".collapsed")
                run(command + ["-o", "collapsed", recording, collapsed], capture_output=True, env=environment)
                total, background = collapsed_totals(collapsed)
                if total == 0:
                    raise ValueError("Empty " + event + " profile: " + str(recording))
                if event == "cpu":
                    metric.update(cpu_samples=total, sampled_cpu_seconds=total * interval if interval else None)
                    if kind == "idea":
                        metric["background_indexing_sample_percent"] = background * 100 / total
                        metric.update(background_work_samples(collapsed))
                else:
                    metric["estimated_allocated_bytes"] = total
                graphs.append(dict(kind=kind, pid=pid, event=event, file=target.name))
            except subprocess.CalledProcessError as error:
                errors.append(str(recording) + ": " + (error.stderr or error.stdout))
            except ValueError as error:
                errors.append(str(error))
        metrics.append(metric)
    manifest.update(conversion_errors=errors, graphs=graphs, process_metrics=metrics, stages=stage_timings(events))
    if manifest.get("profile", "full") == "full" and not any(g["kind"] == "gradle" for g in graphs) and manifest["status"] == "success":
        manifest.update(status="failed", error="Gradle startup recording is missing")
    if errors:
        manifest["status"] = "failed"
    if manifest.get("indexing") == "paused" and any(
            m.get("scanning_samples", 0) or m.get("content_indexing_samples", 0) for m in metrics):
        manifest.update(status="failed", error="Background scanning/indexing ran during the import; isolation check failed")
    from import_report import render
    report = render(run_dir, manifest)
    write_json(run_dir / "manifest.json", manifest)
    return report


def merge_child_metadata(run_dir, processes, manifest):
    for metadata in run_dir.glob("jvm-*.json"):
        entry = read_json(metadata)
        if entry["kind"] == "probe":
            manifest.setdefault("excluded_probes", {})[str(entry["pid"])] = entry
            # Under Rosetta, ps can briefly expose an incomplete argv before
            # JavaProbe appears. The startup agent's metadata is authoritative.
            processes.pop(entry["pid"], None)
        else:
            processes.setdefault(entry["pid"], {}).update(entry)


def measure(args):
    install(args)
    expected_build = dependency_fingerprint()
    wrapper_text = (ROOT / "gradle/wrapper/gradle-wrapper.properties").read_text()
    distribution_url = property_value(wrapper_text, "distributionUrl", "")
    if not args.gradle_version and not re.match(r"https?", distribution_url):
        local_zip = Path(distribution_url.removeprefix("file:")).expanduser()
        if not local_zip.is_absolute():
            local_zip = ROOT / "gradle/wrapper" / local_zip
        if not local_zip.is_file():
            raise RuntimeError("Local Gradle distribution is missing: " + str(local_zip.resolve()))
    info = rpc("info")
    source = Path(info.get("gradleHome") or os.environ.get("GRADLE_USER_HOME", str(Path.home() / ".gradle"))).expanduser().resolve()
    if source == STATE / "gradle-home":
        raise RuntimeError("IDEA still uses the measurement home; run restore before retrying")
    asprof, converter, library = profiler_tools()
    child_jar = build_child_agent(library) if args.profile == "full" else None
    snapshot = cache_snapshot(source, args.refresh_cache_snapshot, args.gradle_version) if args.global_caches == "warm" else None
    if args.dependencies == "cached":
        seed_dependencies(source, args, info)
    run_dir = STATE / "runs" / (time.strftime("%Y%m%d-%H%M%S") + "-" + uuid.uuid4().hex[:6])
    run_dir.mkdir(parents=True)
    # Agent options use commas as delimiters; reject ambiguous paths rather than escaping them incorrectly.
    if any(c in str(run_dir) + str(library) for c in (",", " ", "\n")):
        raise RuntimeError("Profiler/state paths must not contain spaces, commas or newlines")
    agent = "-agentpath:{}=start,event=cpu,alloc={},interval={},file={}/jvm-%p.jfr".format(library, args.alloc_interval, args.cpu_interval, run_dir)
    if args.toolchain_experiment:
        from toolchain_experiment import build_agent, configure
        experiment_jar = build_agent(source)
        configuration = configure(args, run_dir)
        (run_dir / "toolchain-agent.sha256").write_text(hashlib.sha256(experiment_jar.read_bytes()).hexdigest() + "\n")
        agent += " -javaagent:{}={}".format(experiment_jar, configuration)
    child_config = run_dir / "child-profiler.properties"
    child_config.write_text("library={}\ncpu={}\nalloc={}\n".format(library, args.cpu_interval, args.alloc_interval))
    child_agent = "-javaagent:{}={}".format(child_jar, child_config) if child_jar else ""
    if args.profile == "none":
        agent = ""
    processes = {info["pid"]: dict(pid=info["pid"], kind="idea")}
    manifest = dict(status="running", dependencies=args.dependencies, idea=info, project=str(ROOT),
                    cpu_interval=args.cpu_interval, alloc_interval=args.alloc_interval, indexing=args.indexing,
                    java_auto_detect=args.java_auto_detect, allow_concurrent=args.allow_concurrent,
                    toolchain_experiment=args.toolchain_experiment,
                    java_installations=args.java_installation,
                    asprof=run([asprof, "--version"], capture_output=True).stdout.strip(),
                    commit=run(["git", "rev-parse", "HEAD"], capture_output=True, cwd=ROOT).stdout.strip(),
                    build_fingerprint=dependency_fingerprint(),
                    gradle_wrapper=(ROOT / "gradle/wrapper/gradle-wrapper.properties").read_text(),
                    git_status=run(["git", "status", "--porcelain"], capture_output=True, cwd=ROOT).stdout,
                    global_caches=args.global_caches, profile=args.profile, gradle_version_override=args.gradle_version,
                    kotlin_version=args.kotlin_version or property_value((ROOT / "gradle.properties").read_text(), "kotlin_version"),
                    kotlin_version_override=args.kotlin_version,
                    operations_trace=args.profile == "full",
                    compilation_caches="snapshot" if snapshot else "empty",
                    cache_snapshot=read_json(snapshot / "snapshot.json") if snapshot else None,
                    calibration_report=getattr(args, "calibration_report", None),
                    build_cache="project/user settings" if snapshot else False,
                    configuration_cache="project/user settings" if snapshot else False,
                    offline=args.dependencies == "cached", child_instrumentation="premain-excluding-jdk-probes-v1",
                    harness_fingerprint=hashlib.sha256(b"".join((TOOL / name).read_bytes() for name in
                        ["profile_import.py", "IdeaBridge.java", "ImportTelemetry.java", "ChildProfiler.java", "import_report.py", "report.html"])).hexdigest())
    profiled_idea = False
    tracking = False

    def observe():
        if not tracking:
            return
        current = java_processes()
        owned = {p["pid"] for p in current if owned_daemon(p["pid"]) or str(run_dir) in p["command"] or str(STATE / "gradle-home") in p["command"] or (run_dir / ("jvm-" + str(p["pid"]) + ".jfr")).exists()}
        for _ in current:
            owned.update(p["pid"] for p in current if p["ppid"] in owned)
        for process in current:
            if process["pid"] == info["pid"]:
                continue
            # JAVA_TOOL_OPTIONS agents do not appear in ps argv. Track all build
            # JVMs after the strict preflight and verify their recordings below.
            if process["pid"] in owned or (process["kind"] == "probe" and process["ppid"] == info["pid"]):
                if process["kind"] == "probe":
                    # The in-process Tooling API can validate its daemon JDK
                    # directly from IDEA before the instrumented daemon starts.
                    manifest.setdefault("excluded_probes", {})[str(process["pid"])] = {k: v for k, v in process.items() if k != "command"}
                else:
                    processes[process["pid"]] = {k: v for k, v in process.items() if k != "command"}
            else:
                manifest.setdefault("interfering_pids", [])
                if process["pid"] not in manifest["interfering_pids"]:
                    manifest["interfering_pids"].append(process["pid"])
                    manifest.setdefault("interfering_processes", []).append(process)

    try:
        manifest["preparation"] = prepare_session(args.indexing)
        manifest["stopped_processes"] = reset_processes(info["pid"], args.allow_concurrent)
        if dependency_fingerprint() != expected_build:
            raise RuntimeError("Build files changed during preparation; retry with a stable checkout")
        manifest["cleared_project_paths"] = clean_project()
        trace_option = " -Dorg.gradle.internal.operations.trace=" + str(run_dir / "gradle-operations") if args.profile == "full" else ""
        home = prepare_home(source, args.dependencies == "cached", agent + trace_option,
                            args.java_auto_detect, args.java_installation, args.global_caches, snapshot, args.kotlin_version, args.gradle_version)
        shutil.copyfile(home / "measurement-overrides.properties", run_dir / "gradle.properties")
        if not args.allow_concurrent and any(p["pid"] != info["pid"] for p in java_processes()):
            raise RuntimeError("Another JVM started during preparation; retry when other builds are stopped")
        log("Recording import into " + str(run_dir))
        if args.profile == "full":
            # Do not interrupt an existing user profiling session.
            status = run([asprof, "status", str(info["pid"])], capture_output=True)
            if "not active" not in (status.stdout + status.stderr).lower():
                raise RuntimeError("IDEA already has an active profiler: " + status.stdout + status.stderr)
            run([asprof, "start", "-e", "cpu", "--alloc", args.alloc_interval, "-i", args.cpu_interval,
                 "-f", run_dir / ("idea-" + str(info["pid"]) + ".jfr"), str(info["pid"])], capture_output=True)
            profiled_idea = True
        if dependency_fingerprint() != expected_build:
            raise RuntimeError("Build files changed before import; retry with a stable checkout")
        tracking = True
        rpc("import", run=str(run_dir), gradleHome=str(home), offline=args.dependencies == "cached", agent=child_agent, trace=True, globalCaches=args.global_caches,
            gradleInstallation=gradle_installation(home, args.gradle_version))
        result = wait_import(run_dir, args.timeout, observe)
        manifest["events"] = result["events"]
        if dependency_fingerprint() != expected_build:
            raise RuntimeError("Build files changed during import; this is not a valid measurement")
        manifest["before_restore"] = rpc("info")
        if args.indexing == "paused" and not manifest["before_restore"].get("contentIndexingDeferred"):
            raise RuntimeError("The content-indexing guard was released during import")
        manifest["status"] = "success"
    except BaseException as error:
        manifest["status"] = "failed"
        manifest["error"] = str(error)
        log("Measurement failed: " + str(error))
    finally:
        observe()
        for pid, process in processes.items():
            if args.profile == "none":
                continue
            if pid == info["pid"] and not profiled_idea:
                continue
            if alive(pid):
                recording = run_dir / (("idea-" if pid == info["pid"] else "jvm-") + str(pid) + ".jfr")
                result = subprocess.run([asprof, "stop", "-o", "jfr", "-f", str(recording), str(pid)], text=True, capture_output=True)
                if result.returncode:
                    manifest.setdefault("profiler_errors", []).append(dict(pid=pid, error=result.stdout + result.stderr))
                    manifest["status"] = "failed"
        try:
            rpc("restore")
            manifest["after_restore"] = rpc("info")
        except Exception as error:
            manifest["restore_error"] = str(error)
            manifest["status"] = "failed"
        try:
            stop_processes([p for pid, p in processes.items() if pid != info["pid"]])
        except Exception as error:
            manifest["teardown_error"] = str(error)
            manifest["status"] = "failed"
    merge_child_metadata(run_dir, processes, manifest)
    if args.toolchain_experiment:
        trace = run_dir / "toolchain-trace.jsonl"
        entries = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
        if not any(e["event"] == "enter" and e["method"].endswith(".getJavaToolchainHome") for e in entries):
            manifest["status"] = "failed"
            manifest["error"] = "Toolchain experiment did not intercept the IDEA compiler-home query"
        if args.toolchain_experiment == "known-sdk" and not any(e["event"] == "fast-home" for e in entries):
            manifest["status"] = "failed"
            manifest["error"] = "Toolchain prototype did not exercise its fast path"
    if list(run_dir.glob("*.experiment-error.txt")):
        manifest["status"] = "failed"
        manifest["error"] = "Toolchain experiment instrumentation failed"
    if list(run_dir.glob("*.agent-error.txt")):
        manifest["status"] = "failed"
        manifest["error"] = "Child profiler failed: " + "; ".join(p.read_text() for p in run_dir.glob("*.agent-error.txt"))
    for pid, process in processes.items():
        if args.profile == "none":
            continue
        recording = run_dir / (("idea-" if process["kind"] == "idea" else "jvm-") + str(pid) + ".jfr")
        if not recording.exists():
            manifest.setdefault("missing_recordings", []).append(dict(pid=pid, kind=process["kind"]))
            manifest["status"] = "failed"
    if manifest.get("interfering_pids") and not args.allow_concurrent:
        manifest["status"] = "failed"
        manifest["error"] = "Unrelated JVMs appeared during measurement: " + str(manifest["interfering_pids"])
    if (run_dir / "events.json").exists():
        manifest["events"] = read_json(run_dir / "events.json")
    manifest["processes"] = list(processes.values())
    report = create_report(run_dir, manifest, converter, processes)
    write_json(STATE / "latest.json", {"report": str(report), "status": manifest["status"]})
    log("Report: " + report.as_uri())
    if not args.no_open:
        run(["open" if sys.platform == "darwin" else "xdg-open", report])
    return 0 if manifest["status"] == "success" else 1


def main():
    global ROOT, STATE
    parser = argparse.ArgumentParser(prog="./measure", description=__doc__)
    parser.add_argument("command", choices=["install", "run", "status", "restore", "uninstall"], nargs="?", default="run")
    parser.add_argument("--project", type=Path, help="Measure another checkout already open in this IDEA instance")
    parser.add_argument("--idea", help="IDEA .app or Contents directory")
    parser.add_argument("--jdk", help="JDK home for compiling the small IDEA driver")
    parser.add_argument("--dependencies", choices=["cached", "download"], default="cached")
    parser.add_argument("--gradle-version", help="Use an already downloaded Gradle version instead of the project wrapper")
    parser.add_argument("--kotlin-version", help="Explicit Kotlin version override in the isolated Gradle home")
    parser.add_argument("--global-caches", choices=["warm", "empty"], default="warm",
                        help="Reuse a frozen copy of normal global caches (default), or force all compilations cold")
    parser.add_argument("--refresh-cache-snapshot", action="store_true",
                        help="Refresh the frozen global cache snapshot from the normal Gradle home")
    parser.add_argument("--profile", choices=["full", "none"], default="full",
                        help="CPU + allocations + operation trace, or an IDEA-span-only timing control")
    parser.add_argument("--calibrate", action="store_true",
                        help="Run a timing control, then profile using the same initial cache snapshot")
    parser.add_argument("--indexing", choices=["paused", "normal"], default="paused")
    parser.add_argument("--java-auto-detect", choices=["default", "true", "false"], default="default",
                        help="Override org.gradle.java.installations.auto-detect in the isolated Gradle home")
    parser.add_argument("--java-installation", action="append", default=[], metavar="JDK_HOME",
                        help="Explicit toolchain location in the isolated Gradle home (repeatable)")
    parser.add_argument("--allow-concurrent", action="store_true",
                        help="Leave unrelated JVMs running; record their presence without rejecting the run")
    # Local experiments can extend this runner without becoming a dependency of ./measure.
    parser.set_defaults(toolchain_experiment=None, toolchain_baseline=None)
    if (TOOL / "toolchain_experiment.py").is_file():
        parser.add_argument("--toolchain-experiment", choices=["trace", "known-sdk"],
                            help="Time toolchain queries; known-sdk applies the scoped IDEA prototype")
        parser.add_argument("--toolchain-baseline", type=Path,
                            help="Successful trace run used to verify the prototype task allowlist")
    parser.add_argument("--refresh-seed", action="store_true")
    parser.add_argument("--cpu-interval", default="2ms")
    parser.add_argument("--alloc-interval", default="512k")
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--no-open", action="store_true")
    args = parser.parse_args()
    if args.project:
        ROOT = args.project.expanduser().resolve()
        if not (ROOT / "gradle/wrapper/gradle-wrapper.properties").is_file():
            parser.error("Project must contain gradle/wrapper/gradle-wrapper.properties")
        STATE = STATE.parent / hashlib.sha256(str(ROOT).encode()).hexdigest()[:12]
    if args.gradle_version and not re.fullmatch(r"[0-9][A-Za-z0-9_.-]+", args.gradle_version):
        parser.error("Invalid Gradle version")
    if args.kotlin_version and not re.fullmatch(r"[A-Za-z0-9_.+-]+", args.kotlin_version):
        parser.error("Invalid Kotlin version")
    if args.calibrate and args.profile != "full":
        parser.error("--calibrate requires --profile full")
    if args.profile == "none" and args.toolchain_experiment:
        parser.error("Toolchain experiments require profiling")
    args.java_installation = [str(Path(path).expanduser().resolve()) for path in args.java_installation]
    for path in args.java_installation:
        if any(c in path for c in (",", "\n", "\r", "\\")) or not (Path(path) / "bin/java").is_file():
            parser.error("Invalid Java installation: " + path)
    for value in [args.cpu_interval, args.alloc_interval]:
        if not re.fullmatch(r"[1-9][0-9]*(ns|us|ms|s|k|m|g)?", value):
            parser.error("Invalid sampling interval: " + value)
    STATE.mkdir(parents=True, exist_ok=True)
    STATE.chmod(0o700)
    with (STATE / "runner.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("An import measurement is already running")
        if args.command == "install":
            install(args)
        elif args.command == "run":
            if args.calibrate:
                control = argparse.Namespace(**vars(args))
                control.profile = "none"
                control.no_open = True
                if measure(control):
                    return 1
                args.calibration_report = read_json(STATE / "latest.json")["report"]
                args.refresh_cache_snapshot = False
                args.refresh_seed = False
            return measure(args)
        elif args.command == "status":
            log(json.dumps(rpc("info") if bridge_alive() else {"active": False}, indent=2))
        elif args.command == "restore":
            log(rpc("restore"))
        else:
            rpc("restore"); log(rpc("close"))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        log("ERROR: " + str(error))
        sys.exit(1)
