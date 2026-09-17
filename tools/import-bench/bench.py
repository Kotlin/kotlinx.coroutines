#!/usr/bin/env python3
"""Cold Gradle-import benchmark for kotlinx.coroutines.

Measures how long IntelliJ IDEA takes to import this project from a cold Gradle
state, headlessly and reproducibly, and writes a self-contained HTML report with
a total time, CPU time and a swimchart.

    ./bench                                        # use the project's wrapper
    ./bench --gradle env/gradle/gradle-9.9.0-bin.zip
    ./bench --gradle 9.8.0-rc-1 --kotlin-version 2.3.21
    ./bench --runs 3 --open

Requirements: Python 3.8+, an IntelliJ IDEA installation. No other tooling, no
plugins, no running IDE. Your checkout is never modified: the project is
hardlink-copied into the output directory and measured there.

The number reported is the `ExternalSystemSyncProjectTask` OpenTelemetry span,
never the "Elapsed time" that the IDE prints at the end of a warmup run -- that
one includes the indexing tail, which is not part of the import.
"""

import argparse
import hashlib
import html
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import threading
import time
import urllib.request
import zipfile
from pathlib import Path

TOOL = Path(__file__).resolve().parent
ROOT = TOOL.parent.parent

# Directories that are build output or IDE state. Never copied, and removed from
# the working copy before every measured run so that each run is a cold import.
GENERATED = {"build", ".gradle", ".kotlin", ".idea", "out", "target"}
SKIP_COPY = GENERATED | {".git", ".gradletasknamecache", "kotlin-js-store"}


# --------------------------------------------------------------------------- util

def log(*parts):
    print("[bench]", *parts, flush=True)


def die(message):
    raise SystemExit("[bench] error: " + message)


def rmtree(path):
    shutil.rmtree(path, ignore_errors=True)


def read_properties(text):
    """Minimal java.util.Properties reader: enough for wrapper/gradle properties."""
    text = re.sub(r"\\\r?\n[ \t]*", "", text)
    values = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line[0] in "#!":
            continue
        match = re.match(r"([^=:\s]+)\s*[=:]?\s*(.*)$", line)
        if match:
            values[match.group(1)] = match.group(2).replace("\\:", ":").replace("\\=", "=")
    return values


def set_property(text, key, value):
    """Replace or append a single property, preserving the rest of the file."""
    pattern = re.compile(r"^[ \t]*" + re.escape(key) + r"[ \t]*[=:].*$", re.M)
    line = key + "=" + value
    if pattern.search(text):
        return pattern.sub(lambda _: line, text, count=1)
    return text.rstrip("\n") + "\n" + line + "\n"


# ------------------------------------------------------------------- IDE discovery

def find_ide(explicit):
    candidates = []
    if explicit:
        candidates.append(Path(explicit).expanduser())
    if os.environ.get("IDEA_HOME"):
        candidates.append(Path(os.environ["IDEA_HOME"]))
    if sys.platform == "darwin":
        for base in (Path.home() / "Applications", Path("/Applications")):
            candidates += sorted(base.glob("IntelliJ IDEA*.app"), reverse=True)
    else:
        for base in (Path.home() / ".local/share/JetBrains/Toolbox/apps", Path("/opt"), Path("/usr/local")):
            candidates += sorted(base.glob("**/idea-I*"), reverse=True)[:5]
            candidates += sorted(base.glob("idea*"), reverse=True)[:5]
    for path in candidates:
        launcher = ide_launcher(path)
        if launcher and launcher.is_file():
            return path, launcher
    die("could not find IntelliJ IDEA -- pass --idea /path/to/'IntelliJ IDEA.app' or set IDEA_HOME")


def ide_launcher(home):
    for relative in ("Contents/MacOS/idea", "MacOS/idea", "bin/idea.sh", "bin/idea"):
        candidate = home / relative
        if candidate.is_file():
            return candidate
    return None


def ide_jbr(home):
    for relative in ("Contents/jbr/Contents/Home", "jbr/Contents/Home", "jbr"):
        candidate = home / relative
        if (candidate / "bin/java").is_file():
            return candidate
    return None


def resolve_jdk(explicit, ide_home):
    """Pick the JDK the Gradle daemon runs on.

    A headless IDE has no JDK table, so it cannot resolve "Gradle JVM" by itself and
    the import fails with `Invalid Gradle JDK configuration`. We always pass one
    explicitly: whatever was asked for, else JAVA_HOME, else the IDE's bundled JBR,
    which is always present and always a full JDK.
    """
    if explicit:
        return explicit, "--java-home"
    # The bundled JBR is preferred over an ambient JAVA_HOME so that two people with
    # the same IDE measure on the same JVM. Pass --java-home to use something else.
    bundled = ide_jbr(ide_home)
    if bundled:
        return bundled.resolve(), "bundled JBR"
    ambient = os.environ.get("JAVA_HOME")
    if ambient and (Path(ambient) / "bin/java").is_file():
        return Path(ambient).resolve(), "JAVA_HOME"
    die("no JDK found for the Gradle daemon -- pass --java-home")


def jdk_label(java_home):
    try:
        out = subprocess.run([str(Path(java_home) / "bin/java"), "-version"],
                             capture_output=True, text=True, timeout=20).stderr
        return re.search(r'version "([^"]+)"', out).group(1)
    except Exception:
        return Path(java_home).name


def ide_build(home):
    for relative in ("Contents/Resources/build.txt", "build.txt", "Resources/build.txt"):
        candidate = home / relative
        if candidate.is_file():
            return candidate.read_text().strip()
    return "unknown"


# ------------------------------------------------------------ Gradle distribution

def extract_distribution(archive, target):
    """Extract a Gradle zip once, preserving the executable bit the launcher needs."""
    marker = target / ".extracted"
    if marker.is_file():
        return next(p.parent.parent for p in target.glob("*/bin/gradle"))
    rmtree(target)
    target.mkdir(parents=True)
    with zipfile.ZipFile(archive) as zf:
        for entry in zf.infolist():
            destination = target / entry.filename
            if not str(destination.resolve()).startswith(str(target.resolve())):
                die("refusing to extract outside the target directory: " + entry.filename)
            if entry.is_dir():
                destination.mkdir(parents=True, exist_ok=True)
                continue
            destination.parent.mkdir(parents=True, exist_ok=True)
            with zf.open(entry) as source, open(destination, "wb") as sink:
                shutil.copyfileobj(source, sink)
            mode = entry.external_attr >> 16
            if mode:
                destination.chmod(mode)
    found = [p.parent.parent for p in target.glob("*/bin/gradle")]
    if len(found) != 1:
        die("archive does not contain exactly one Gradle distribution: " + str(archive))
    marker.write_text("ok\n")
    return found[0]


def download(url, target):
    if target.is_file():
        return target
    target.parent.mkdir(parents=True, exist_ok=True)
    log("downloading", url)
    temporary = target.with_suffix(".part")
    with urllib.request.urlopen(url) as response, open(temporary, "wb") as sink:
        shutil.copyfileobj(response, sink)
    temporary.rename(target)
    return target


def resolve_gradle(spec, project, state):
    """Return (distribution directory, human label).

    `spec` is a path to a distribution zip, a path to an extracted distribution,
    a bare version such as 9.8.0-rc-1, or None to follow the project's wrapper.
    """
    if spec is None:
        wrapper = read_properties((project / "gradle/wrapper/gradle-wrapper.properties").read_text())
        url = wrapper.get("distributionUrl", "")
        if not url:
            die("the project has no distributionUrl and --gradle was not given")
        if url.startswith(("http://", "https://")):
            spec = re.search(r"gradle-([^/]+?)-(?:bin|all)\.zip", url).group(1)
        else:
            local = Path(url[5:] if url.startswith("file:") else url)
            spec = str(local if local.is_absolute() else (project / "gradle/wrapper" / local).resolve())

    candidate = Path(str(spec)).expanduser()
    if candidate.is_dir():
        if not (candidate / "bin/gradle").is_file():
            die("not a Gradle distribution directory: " + str(candidate))
        return candidate.resolve(), candidate.name
    if candidate.is_file() and candidate.suffix == ".zip":
        digest = hashlib.sha256(candidate.read_bytes()).hexdigest()[:16]
        home = extract_distribution(candidate, state / "distributions" / digest)
        return home, candidate.name
    if re.fullmatch(r"[0-9][A-Za-z0-9.+-]*", str(spec)):
        version = str(spec)
        for name in ("bin", "all"):
            existing = sorted((Path.home() / ".gradle/wrapper/dists").glob(
                "gradle-%s-%s/*/gradle-%s" % (version, name, version)))
            for path in existing:
                if (path / "bin/gradle").is_file():
                    return path.resolve(), "gradle-" + version
        archive = download("https://services.gradle.org/distributions/gradle-%s-bin.zip" % version,
                           state / "downloads" / ("gradle-%s-bin.zip" % version))
        return extract_distribution(archive, state / "distributions" / version), "gradle-" + version
    die("--gradle must be a distribution zip, an extracted distribution, or a version: " + str(spec))


def distribution_version(home):
    receipt = next(iter(sorted((home / "lib").glob("gradle-base-services-[0-9]*.jar"))), None)
    if receipt is None:
        return home.name
    return re.sub(r"^gradle-base-services-|\.jar$", "", receipt.name)


# -------------------------------------------------------------------- working copy

def write_unlinked(path, text):
    """Write a file in the working copy without writing through a hardlink.

    The copy is made with hardlinks, so opening a file for writing would truncate the
    inode the real checkout still points at and silently edit the user's tree. Replace
    the entry with a fresh file instead.
    """
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        path.unlink()
    path.write_text(text)


def copy_project(source, target):
    """Hardlink the checkout into the output directory, minus generated state."""
    rmtree(target)
    files = 0
    for directory, names, filenames in os.walk(source):
        relative = Path(directory).relative_to(source)
        names[:] = [n for n in names if n not in SKIP_COPY and not (relative == Path(".") and n == "build")]
        if any(part in SKIP_COPY for part in relative.parts):
            continue
        (target / relative).mkdir(parents=True, exist_ok=True)
        for name in filenames:
            origin, destination = Path(directory) / name, target / relative / name
            if origin.is_symlink():
                os.symlink(os.readlink(origin), destination)
                continue
            try:
                os.link(origin, destination)
            except OSError:
                shutil.copy2(origin, destination)
            files += 1
    return files


def reset_project(project, keep_build_logic=False):
    """Put the working copy back into the state a fresh checkout is in.

    With `keep_build_logic` the outputs under `buildSrc` survive, so the convention
    plugins are up to date and only the project's own Kotlin DSL scripts recompile.
    """
    for directory, names, _ in os.walk(project, topdown=True):
        inside_build_logic = "buildSrc" in Path(directory).relative_to(project).parts
        for name in list(names):
            if name not in GENERATED:
                continue
            if keep_build_logic and name != ".idea" and (inside_build_logic or name == "buildSrc"):
                continue
            rmtree(Path(directory) / name)
            names.remove(name)


def write_idea_config(project, distribution, gradle_home, java_home):  # noqa: D401
    """Link the project to Gradle explicitly, so the import needs no guessing."""
    idea = project / ".idea"
    idea.mkdir(parents=True, exist_ok=True)
    jvm = '\n        <option name="gradleJvm" value="#JAVA_HOME" />' 
    write_unlinked(idea / "gradle.xml",
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<project version="4">\n'
        '  <component name="GradleMigrationSettings" migrationVersion="1" />\n'
        '  <component name="GradleSettings">\n'
        '    <option name="linkedExternalProjectsSettings">\n'
        '      <GradleProjectSettings>\n'
        '        <option name="distributionType" value="LOCAL" />\n'
        '        <option name="externalProjectPath" value="$PROJECT_DIR$" />\n'
        '        <option name="gradleHome" value="%s" />%s\n'
        '        <option name="modules">\n'
        '          <set>\n'
        '            <option value="$PROJECT_DIR$" />\n'
        '          </set>\n'
        '        </option>\n'
        '      </GradleProjectSettings>\n'
        '    </option>\n'
        '    <option name="serviceDirectoryPath" value="%s" />\n'
        '  </component>\n'
        '</project>\n' % (html.escape(str(distribution)), jvm, html.escape(str(gradle_home))))


def apply_overrides(project, kotlin_version):
    if not kotlin_version:
        return
    path = project / "gradle.properties"
    write_unlinked(path, set_property(path.read_text(), "kotlin_version", kotlin_version))


def seed_gradle_home(gradle_home, source=None):
    """Prime the isolated Gradle home from the user's real one, cheaply.

    Without this the first preparation run downloads every dependency from
    scratch. Artifact and build-cache entries are content-addressed and never
    mutated, so they can be hardlinked; anything Gradle writes in place (metadata
    stores, lock files, journals) is copied instead, so the real cache is safe.
    """
    source = source or Path(os.environ.get("GRADLE_USER_HOME", Path.home() / ".gradle"))
    marker = gradle_home / ".seeded"
    if marker.is_file() or not (source / "caches").is_dir():
        return 0
    linked = 0
    for relative, linkable in (("caches/modules-2", "files-2.1"), ("caches/build-cache-1", "")):
        origin = source / relative
        if not origin.is_dir():
            continue
        for directory, names, filenames in os.walk(origin):
            names[:] = [n for n in names if not n.endswith(".lock")]
            target = gradle_home / relative / Path(directory).relative_to(origin)
            target.mkdir(parents=True, exist_ok=True)
            immutable = linkable == "" or linkable in Path(directory).relative_to(origin).parts
            for name in filenames:
                if name.endswith(".lock"):
                    continue
                a, b = Path(directory) / name, target / name
                if b.exists():
                    continue
                try:
                    os.link(a, b) if immutable else shutil.copy2(a, b)
                    linked += 1
                except OSError:
                    pass
    marker.write_text("ok\n")
    return linked


def write_gradle_home(gradle_home, trace_prefix, java_home, jvmargs):
    """Properties for the isolated Gradle home.

    The build-operation trace has to be a *daemon JVM argument*. Passing it as
    `systemProp.` is silently ignored, because the daemon is already running by
    the time project properties are read.
    """
    gradle_home.mkdir(parents=True, exist_ok=True)
    lines = ["# Written by tools/import-bench. Do not edit; it is regenerated per run.",
             "org.gradle.jvmargs=%s -Dorg.gradle.internal.operations.trace=%s" % (jvmargs, trace_prefix)]
    if java_home:
        lines.append("org.gradle.java.home=" + str(java_home))
    (gradle_home / "gradle.properties").write_text("\n".join(lines) + "\n")


# ----------------------------------------------------------------------- sandbox

def write_sandbox(sandbox, traces, heap):
    for name in ("config", "system", "plugins", "log"):
        (sandbox / name).mkdir(parents=True, exist_ok=True)
    # `warmup` is registered as an internal app starter, so it is hidden from
    # --list-commands and only runs with idea.is.internal=true.
    (sandbox / "idea.properties").write_text("\n".join([
        "idea.config.path=" + str(sandbox / "config"),
        "idea.system.path=" + str(sandbox / "system"),
        "idea.plugins.path=" + str(sandbox / "plugins"),
        "idea.log.path=" + str(sandbox / "log"),
        "idea.is.internal=true",
        # Default telemetry output is aggregate metric counters, which are useless
        # for phase timing. This switches it to a Jaeger-format span tree.
        "idea.diagnostic.opentelemetry.file=" + str(traces / "opentelemetry.json"),
        "idea.initially.ask.config=never",
        "idea.trust.all.projects=true",
        "jb.privacy.policy.eua.accepted=true",
        "jb.consents.confirmation.enabled=false",
        "idea.suppress.statistics.report=true",
    ]) + "\n")
    (sandbox / "idea.vmoptions").write_text(
        "-Xmx%s\n-XX:ReservedCodeCacheSize=1g\n-Djava.awt.headless=true\n" % heap)


# -------------------------------------------------------------------- CPU sampler

def parse_cpu(value):
    """Parse the cumulative CPU column of ps: [[dd-]hh:]mm:ss[.ff]."""
    days = 0
    if "-" in value:
        head, value = value.split("-", 1)
        days = int(head)
    parts = value.split(":")
    try:
        numbers = [float(p) for p in parts]
    except ValueError:
        return 0.0
    seconds = 0.0
    for number in numbers:
        seconds = seconds * 60 + number
    return seconds + days * 86400


class CpuSampler(threading.Thread):
    """Polls `ps` and keeps the peak cumulative CPU of every process we care about.

    Build JVMs are grandchildren that the IDE stops when it closes the project, so
    their usage has to be captured while they are alive rather than read at the end.
    """

    def __init__(self, marker, interval=0.25):
        super().__init__(daemon=True)
        self.marker = str(marker)
        self.interval = interval
        self.peaks = {}
        self.names = {}
        self._done = threading.Event()

    def sample(self):
        try:
            out = subprocess.run(["ps", "-Ao", "pid=,time=,command="],
                                 capture_output=True, text=True, timeout=10).stdout
        except (OSError, subprocess.SubprocessError):
            return
        for line in out.splitlines():
            parts = line.split(None, 2)
            if len(parts) < 3 or self.marker not in parts[2]:
                continue
            pid, cpu, command = parts[0], parse_cpu(parts[1]), parts[2]
            if cpu >= self.peaks.get(pid, -1.0):
                self.peaks[pid] = cpu
                self.names[pid] = classify_process(command)

    def run(self):
        while not self._done.is_set():
            self.sample()
            self._done.wait(self.interval)

    def stop(self):
        self.sample()
        self._done.set()

    def totals(self):
        per_kind = {}
        for pid, cpu in self.peaks.items():
            per_kind[self.names[pid]] = per_kind.get(self.names[pid], 0.0) + cpu
        return per_kind


def classify_process(command):
    if "GradleDaemon" in command or "gradle-launcher" in command:
        return "Gradle daemon"
    if "KotlinCompileDaemon" in command or "kotlin-daemon" in command:
        return "Kotlin compiler daemon"
    if "GradleWorkerMain" in command or "worker.GradleWorkerMain" in command:
        return "Gradle workers"
    return "other build JVMs"


# ------------------------------------------------------------------------- run

def forget_project(sandbox):
    """Drop the IDE's cached workspace model so the next open really re-imports.

    `system/projects/<project>` holds `project-model-cache` and `external_build_system`;
    with those in place the IDE decides the project is already configured and performs
    no Gradle import at all. The shared indexes in `system/index` and `system/caches`
    are left alone, which is what keeps indexing out of the measurement.
    """
    projects = sandbox / "system/projects"
    if projects.is_dir():
        for entry in projects.iterdir():
            rmtree(entry)


# Compiled build logic lives in the Gradle home, not the project. Clearing the
# project alone leaves it behind, and from the second run onwards the import skips
# several seconds of Kotlin DSL compilation that a fresh checkout genuinely pays --
# script bodies come back out of the local build cache, the rest out of kotlin-dsl.
# Downloaded dependencies (modules-2) are always kept, so no run needs the network.
SCRIPT_CACHES = ("kotlin-dsl", "groovy-dsl", "scripts", "scripts-remapped")

# ... but not everything under those directories is compiled build logic. These entries
# are keyed by the content hash of a dependency, not by anything in this project, so a
# fresh checkout on a machine that has built anything else in Kotlin already has them.
# Deleting them models a machine that has never seen this Gradle version, which is a
# different and much rarer thing, and it costs 1-1.7 s per run: the daemon blocks in
# KotlinCompileClasspathFingerprinter while the Kotlin Build Tools API re-snapshots
# every jar on three script classpaths.
KEEP_WITHIN_SCRIPT_CACHES = {"kotlin-dsl": ("classpath-snapshots",)}


def cool_caches(gradle_home):
    for version in (gradle_home / "caches").glob("*"):
        if not version.is_dir():
            continue
        for name in SCRIPT_CACHES:
            directory = version / name
            keep = KEEP_WITHIN_SCRIPT_CACHES.get(name)
            if keep and directory.is_dir():
                for entry in directory.iterdir():
                    if entry.name not in keep:
                        rmtree(entry)
            else:
                rmtree(directory)
    rmtree(gradle_home / "caches/build-cache-1")


def run_import(args, paths, label):
    reset_project(paths["project"], keep_build_logic=args.state == "scripts")
    forget_project(paths["sandbox"])
    if args.state != "warm":
        cool_caches(paths["gradle_home"])
    write_idea_config(paths["project"], paths["distribution"], paths["gradle_home"], args.java_home)
    rmtree(paths["traces"])
    paths["traces"].mkdir(parents=True, exist_ok=True)
    for stale in paths["gradle_home"].glob("ops-trace*"):
        stale.unlink()

    environment = dict(os.environ)
    environment["IDEA_PROPERTIES"] = str(paths["sandbox"] / "idea.properties")
    environment["IDEA_VM_OPTIONS"] = str(paths["sandbox"] / "idea.vmoptions")
    environment["GRADLE_USER_HOME"] = str(paths["gradle_home"])
    environment["JAVA_HOME"] = str(args.java_home)

    sampler = CpuSampler(paths["gradle_home"])
    sampler.start()
    started = time.time()
    with open(paths["runs"] / (label + ".log"), "wb") as sink:
        process = subprocess.run(
            [str(paths["launcher"]), "warmup",
             "--project-dir=" + str(paths["project"]), "--configure-project=true"],
            env=environment, stdout=sink, stderr=subprocess.STDOUT)
    elapsed = time.time() - started
    sampler.stop()
    sampler.join(timeout=5)

    trace = paths["traces"] / "opentelemetry.json"
    if trace.is_file():
        shutil.copyfile(trace, paths["runs"] / (label + ".otel.json"))
    # The operations log is overwritten by every build, so take it immediately.
    operations = paths["gradle_home"] / "ops-trace-log.txt"
    if operations.is_file():
        shutil.copyfile(operations, paths["runs"] / (label + ".ops.txt"))

    return dict(label=label, exit_code=process.returncode, process_seconds=elapsed,
                cpu=sampler.totals(),
                otel=paths["runs"] / (label + ".otel.json"),
                operations=paths["runs"] / (label + ".ops.txt"))


# ----------------------------------------------------------------------- parsing

def salvage_spans(text):
    """Parse span objects out of a truncated telemetry file.

    The IDE writes this file as it goes and the warmup entry point can exit before
    the exporter has flushed, so the JSON is routinely cut off mid-object. The sync
    spans we care about are written long before that, so parse objects one at a time
    and stop at the first one that does not decode.
    """
    decoder, spans, cursor = json.JSONDecoder(), [], text.find('"spans":[')
    while cursor != -1:
        index = text.index("[", cursor) + 1
        while True:
            while index < len(text) and text[index] in " \t\r\n,":
                index += 1
            if index >= len(text) or text[index] != "{":
                break
            try:
                span, index = decoder.raw_decode(text, index)
            except ValueError:
                break
            spans.append(span)
        cursor = text.find('"spans":[', index)
    return spans


def load_spans(path):
    """Read the IDE's OpenTelemetry file. Times come back as epoch milliseconds."""
    if not path or not Path(path).is_file():
        return []
    text = Path(path).read_text(errors="replace")
    try:
        document = json.loads(text)
    except ValueError:
        document = dict(data=[dict(spans=salvage_spans(text))])
    spans = []
    if isinstance(document, dict) and "data" in document:
        for trace in document["data"]:
            for span in trace.get("spans", []):
                parent = next((r.get("spanID") for r in span.get("references", [])
                               if r.get("refType") == "CHILD_OF"), None)
                spans.append(dict(id=span.get("spanID"), parent=parent,
                                  name=span.get("operationName", "?"),
                                  start=span["startTime"] / 1000.0,
                                  end=(span["startTime"] + span.get("duration", 0)) / 1000.0))
    elif isinstance(document, list):
        for span in document:
            spans.append(dict(id=span.get("id"), parent=span.get("parent"),
                              name=span.get("name", "?"),
                              start=span["start_ns"] / 1e6, end=span["end_ns"] / 1e6))
    return spans


def load_operations(path, window):
    """Read Gradle's build-operation trace, keeping only the measured build."""
    if not path or not Path(path).is_file():
        return []
    starts, ends = {}, {}
    with open(path, "r", errors="replace") as handle:
        for line in handle:
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                record = json.loads(line)
            except ValueError:
                continue
            identifier = record.get("id")
            if identifier is None:
                continue
            if "startTime" in record:
                starts[identifier] = record
            elif "endTime" in record:
                ends[identifier] = record
    low, high = window
    operations = []
    for identifier, record in starts.items():
        end = ends.get(identifier)
        if end is None:
            continue
        start_ms, end_ms = float(record["startTime"]), float(end["endTime"])
        if end_ms < low or start_ms > high:
            continue
        operations.append(dict(id=identifier, parent=record.get("parentId"),
                               name=record.get("displayName", "?"),
                               start=start_ms, end=end_ms))
    operations.sort(key=lambda o: (o["start"], -o["end"]))
    return operations


def self_times(items):
    """Duration minus the union of direct children: what an operation itself cost."""
    children = {}
    for item in items:
        children.setdefault(item.get("parent"), []).append(item)
    for item in items:
        covered, last = 0.0, None
        for child in sorted(children.get(item["id"], []), key=lambda c: c["start"]):
            start = child["start"] if last is None else max(child["start"], last)
            if child["end"] > start:
                covered += child["end"] - start
                last = child["end"]
        item["self"] = max(0.0, (item["end"] - item["start"]) - covered)
    return items


CATEGORIES = (
    ("Kotlin DSL compilation", (r"Compile script", r"Kotlin DSL", r"COMPILE_KOTLIN_SCRIPT",
                                r"GENERATE_PROJECT_ACCESSORS", r"PLUGIN_SPEC_BUILDER")),
    ("Tooling models", (r"^Build model", r"^Fetch model", r"nested tooling build actions")),
    ("Dependencies & transforms", (r"^Resolve ", r"TRANSFORM", r"transform chain", r"^Fingerprint",
                                   r"^Snapshot", r"build cache entry")),
    ("Configuration", (r"^Configure ", r"^Apply ", r"^Evaluate ", r"afterEvaluate", r"^Load build",
                       r"^Notify ", r"^Realize task", r"container callback")),
    ("Tasks", (r"^Task :", r"^Run tasks", r"^Execute .* for :", r"task graph")),
    ("Init scripts", (r"init script", r"^Run init")),
)


def categorise(name):
    for category, patterns in CATEGORIES:
        for pattern in patterns:
            if re.search(pattern, name):
                return category
    return "Other Gradle work"


# Spans the external-system/Gradle import emits. Used to reconstruct the import
# interval when the root span itself is missing from a truncated telemetry file.
IMPORT_SPAN = re.compile(
    r"^(GradleExecution|GradleConnection|GradleCall|GetBuildEnvironment|Gradle\w*SyncContributor"
    r"|GradleProjectResolverDataProcessing|ExternalSystemSyncResultProcessing|ProjectDataServices"
    r"|postImportTasks|runFinalTasks|.*_PHASE-idea)$")


def import_interval(spans):
    """The measured interval: the sync span if it survived, else its known children.

    The IDE exports spans as they finish, so the root finishes last and is the first
    casualty when the warmup entry point exits before the exporter has flushed.
    """
    root = next((s for s in spans if s["name"] == "ExternalSystemSyncProjectTask"), None)
    if root is not None:
        return dict(root, reconstructed=False)
    parts = [s for s in spans if IMPORT_SPAN.match(s["name"])]
    if not parts:
        return None
    return dict(name="import (reconstructed)", id=None, parent=None, reconstructed=True,
                start=min(s["start"] for s in parts), end=max(s["end"] for s in parts))


def import_failure(log_path):
    """Pull the first real error out of a warmup log, for a useful message."""
    if not Path(log_path).is_file():
        return None
    reasons = []
    for line in Path(log_path).read_text(errors="replace").splitlines():
        text = line.replace("[Gradle]:", "").replace("STDERR:", "").strip()
        if not text or text.startswith(("*", ">", "at ", "Run with")):
            continue
        if re.search(r"Build failed|FAILURE|Unresolved reference|Could not |Execution failed|"
                     r"^e: |ExternalSystemJdkException|Failed to load project", text):
            if text not in reasons:
                reasons.append(text)
        if len(reasons) >= 4:
            break
    return reasons or None


def analyse(result):
    spans = self_times(load_spans(result["otel"]))
    sync = import_interval(spans)
    if sync is None:
        return None
    window = (sync["start"] - 1000, sync["end"] + 1000)
    operations = self_times(load_operations(result["operations"], window))
    build = next((o for o in operations if o["name"] == "Run build"), None)
    call = next((s for s in spans if s["name"] == "GradleCall"), None)

    categories = {}
    for operation in operations:
        category = categorise(operation["name"])
        entry = categories.setdefault(category, dict(name=category, count=0, self=0.0))
        entry["count"] += 1
        entry["self"] += operation["self"]

    analysis = dict(
        label=result["label"],
        reconstructed=sync.get("reconstructed", False),
        sync_seconds=(sync["end"] - sync["start"]) / 1000.0,
        gradle_seconds=((build["end"] - build["start"]) / 1000.0) if build else None,
        call_seconds=((call["end"] - call["start"]) / 1000.0) if call else None,
        daemon_start_seconds=((build["start"] - call["start"]) / 1000.0) if (build and call) else None,
        ide_seconds=(sync["end"] - sync["start"]) / 1000.0 - (
            (call["end"] - call["start"]) / 1000.0 if call else 0.0),
        process_seconds=result["process_seconds"],
        cpu=result["cpu"],
        cpu_seconds=sum(result["cpu"].values()),
        operations=len(operations),
        categories=sorted(categories.values(), key=lambda c: -c["self"]),
        origin=sync["start"],
        spans=spans, ops=operations, sync=sync,
    )
    return analysis


# ------------------------------------------------------------------------ report

PALETTE = {
    "IDE": "#2a78d6",
    "Kotlin DSL compilation": "#eb6834",
    "Tooling models": "#7b61c4",
    "Dependencies & transforms": "#1baf7a",
    "Configuration": "#d6a12a",
    "Tasks": "#3fa2c4",
    "Init scripts": "#c4407a",
    "Other Gradle work": "#9aa0a8",
}

CSS = """
:root{--bg:#f7f7f5;--surface:#fff;--surface-2:#f1f1ee;--ink:#16171a;--ink-2:#4e5157;--ink-3:#7c8089;
--rule:#e2e2dd;--mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
--sans:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#141414;--surface:#1b1b1a;
--surface-2:#242423;--ink:#f2f2ee;--ink-2:#b8b7b0;--ink-3:#8a8983;--rule:#333331}}
:root[data-theme="dark"]{--bg:#141414;--surface:#1b1b1a;--surface-2:#242423;--ink:#f2f2ee;
--ink-2:#b8b7b0;--ink-3:#8a8983;--rule:#333331}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.55 var(--sans);-webkit-font-smoothing:antialiased}
.wrap{max-width:1160px;margin:0 auto;padding:40px 16px 72px}
h1{font:700 clamp(24px,4vw,34px)/1.15 var(--mono);letter-spacing:-.02em;margin:0}
h2{font:700 18px/1.3 var(--mono);margin:0 0 14px}
p{margin:0}
.lede{color:var(--ink-2);max-width:70ch;margin-top:12px}
.meta{display:flex;flex-wrap:wrap;gap:6px;margin-top:18px}
.chip{font:11.5px var(--mono);color:var(--ink-2);background:var(--surface);border:1px solid var(--rule);
border-radius:5px;padding:3px 8px}
section{margin-top:44px}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:1px;background:var(--rule);
border:1px solid var(--rule);border-radius:9px;overflow:hidden;margin-top:28px}
.stat{background:var(--surface);padding:15px 16px}
.stat .k{font:10.5px var(--mono);letter-spacing:.11em;text-transform:uppercase;color:var(--ink-3)}
.stat .v{font:700 26px/1 var(--mono);letter-spacing:-.03em;margin-top:7px;font-variant-numeric:tabular-nums}
.stat .s{font-size:12.5px;color:var(--ink-2);margin-top:6px}
.tw{overflow-x:auto;border:1px solid var(--rule);border-radius:9px;background:var(--surface)}
table{border-collapse:collapse;width:100%;min-width:520px;font-size:13.5px}
th,td{text-align:right;padding:8px 13px;border-bottom:1px solid var(--rule);white-space:nowrap}
th:first-child,td:first-child{text-align:left}
thead th{font:500 10.5px var(--mono);letter-spacing:.09em;text-transform:uppercase;color:var(--ink-3);
background:var(--surface-2)}
tbody tr:last-child td{border-bottom:0}
td.n{font-family:var(--mono);font-variant-numeric:tabular-nums}
.chart{border:1px solid var(--rule);border-radius:9px;background:var(--surface);overflow:hidden}
.legend{display:flex;flex-wrap:wrap;gap:14px;padding:11px 14px;border-bottom:1px solid var(--rule);
background:var(--surface-2);font:11.5px var(--mono);color:var(--ink-2)}
.legend i{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:5px;vertical-align:-1px}
.rows{padding:8px 14px 14px}
.row{display:grid;grid-template-columns:minmax(150px,290px) 1fr;align-items:center;gap:10px;height:20px}
.name{font:11.5px/1.2 var(--mono);color:var(--ink-2);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.track{position:relative;height:13px;border-left:1px solid var(--rule)}
.bar{position:absolute;top:1px;height:11px;border-radius:3px;min-width:2px}
.bar span{position:absolute;top:-1px;font:10.5px/13px var(--mono);color:var(--ink-3);white-space:nowrap}
.axis{display:grid;grid-template-columns:minmax(150px,290px) 1fr;gap:10px;padding:0 14px 12px;
font:10px var(--mono);color:var(--ink-3)}
.ticks{display:flex;justify-content:space-between}
.note{border:1px solid var(--rule);border-left:3px solid var(--ink-3);border-radius:0 8px 8px 0;
background:var(--surface);padding:13px 16px;font-size:13.5px;color:var(--ink-2);margin-top:16px}
.note b{color:var(--ink)}
code{font-family:var(--mono);font-size:12.5px;background:var(--surface-2);padding:1px 5px;border-radius:3px}
@media (max-width:640px){.row,.axis{grid-template-columns:110px 1fr}.name{font-size:10px}}
"""


def esc(value):
    return html.escape(str(value))


def chart_rows(analysis, limit=60):
    """Pick what to draw: the import's own IDE spans, then the longest Gradle work.

    The IDE emits hundreds of unrelated startup spans; only the external-system ones
    belong on this chart, and the rest of the budget goes to Gradle operations.
    """
    origin, end = analysis["origin"], analysis["sync"]["end"]
    total = max(end - origin, 1.0)
    rows = []
    ide = [s for s in analysis["spans"]
           if IMPORT_SPAN.match(s["name"]) and s["end"] > origin and s["start"] < end]
    ide.sort(key=lambda s: (s["start"], -(s["end"] - s["start"])))
    for span in ide[:14]:
        rows.append((span, "IDE", 0))

    index = {o["id"]: o for o in analysis["ops"]}
    depth = {}
    for operation in analysis["ops"]:
        parent, level = operation.get("parent"), 0
        while parent in index and level < 8:
            level += 1
            parent = index[parent].get("parent")
        depth[operation["id"]] = level
    candidates = sorted(analysis["ops"], key=lambda o: -(o["end"] - o["start"]))
    chosen = sorted(candidates[:max(0, limit - len(rows))], key=lambda o: (o["start"], depth[o["id"]]))
    for operation in chosen:
        rows.append((operation, categorise(operation["name"]), depth[operation["id"]]))

    parts = []
    for item, category, level in rows:
        left = max(0.0, 100.0 * (item["start"] - origin) / total)
        width = max(0.25, min(100.0 - left, 100.0 * (item["end"] - item["start"]) / total))
        seconds = (item["end"] - item["start"]) / 1000.0
        text = ("%.2f s" % seconds) if seconds >= 0.1 else "%d ms" % round(seconds * 1000)
        # Labels sit beside the bar, flipping to its left once the bar reaches the
        # right-hand edge, so nothing is clipped and nothing needs a readable
        # foreground colour on seven different backgrounds.
        style = "left:calc(100% + 5px)" if left + width < 88 else "right:calc(100% + 5px)"
        parts.append(
            '<div class="row"><div class="name" title="%s">%s</div><div class="track">'
            '<div class="bar" style="left:%.3f%%;width:%.3f%%;background:%s">'
            '<span style="%s">%s</span></div></div></div>'
            % (esc(item["name"]), ("&nbsp;" * level * 2) + esc(item["name"][:70]),
               left, width, PALETTE.get(category, "#9aa0a8"), style, text))
    return "".join(parts), total / 1000.0


def render(analyses, context, path):
    best = analyses[len(analyses) // 2]
    syncs = sorted(a["sync_seconds"] for a in analyses)
    median = statistics.median(syncs)
    cpu_total = statistics.median([a["cpu_seconds"] for a in analyses])
    bars, span_seconds = chart_rows(best)

    legend = "".join('<span><i style="background:%s"></i>%s</span>' % (colour, esc(name))
                     for name, colour in PALETTE.items())

    runs = "".join(
        "<tr><td>%s</td><td class='n'>%.2f</td><td class='n'>%s</td><td class='n'>%s</td>"
        "<td class='n'>%.2f</td><td class='n'>%.1f</td></tr>" % (
            esc(a["label"]), a["sync_seconds"],
            "%.2f" % a["gradle_seconds"] if a["gradle_seconds"] else "&ndash;",
            "%.2f" % a["daemon_start_seconds"] if a["daemon_start_seconds"] else "&ndash;",
            a["ide_seconds"], a["cpu_seconds"])
        for a in analyses)

    categories = "".join(
        "<tr><td>%s</td><td class='n'>%d</td><td class='n'>%.2f</td><td class='n'>%.0f%%</td></tr>" % (
            esc(c["name"]), c["count"], c["self"] / 1000.0,
            100.0 * c["self"] / max(sum(x["self"] for x in best["categories"]), 1.0))
        for c in best["categories"])

    cpu_rows = "".join(
        "<tr><td>%s</td><td class='n'>%.1f</td></tr>" % (esc(k), v)
        for k, v in sorted(best["cpu"].items(), key=lambda kv: -kv[1]))

    chips = "".join('<span class="chip">%s</span>' % esc(c) for c in context["chips"])

    document = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Cold Import Benchmark</title><style>%s</style></head><body><div class="wrap">
<header>
<p style="font:11.5px var(--mono);letter-spacing:.14em;text-transform:uppercase;color:var(--ink-3)">%s</p>
<h1>Cold Gradle import</h1>
<p class="lede">Time from the start of IntelliJ&rsquo;s sync task to the moment the workspace model is
committed, measured headlessly with project build state cleared and IDE indexes warm. The number is the
<code>ExternalSystemSyncProjectTask</code> span, not the elapsed time the IDE prints.</p>
<div class="meta">%s</div>
</header>

<div class="stats">
  <div class="stat"><div class="k">Import</div><div class="v">%.2f s</div>
    <div class="s">median of %d run%s, spread %.2f s</div></div>
  <div class="stat"><div class="k">Inside Gradle</div><div class="v">%s</div>
    <div class="s">%s of the import</div></div>
  <div class="stat"><div class="k">CPU</div><div class="v">%.0f s</div>
    <div class="s">build JVMs, summed across threads</div></div>
  <div class="stat"><div class="k">Parallelism</div><div class="v">%.2f&times;</div>
    <div class="s">build CPU &divide; Gradle wall time</div></div>
</div>

<section>
<h2>Runs</h2>
<div class="tw"><table><thead><tr><th>Run</th><th>Import s</th><th>Gradle s</th>
<th>Daemon start s</th><th>IDE s</th><th>Build CPU s</th></tr></thead><tbody>%s</tbody></table></div>
<div class="note">%sDaemon start is the gap between the Tooling API call opening and Gradle&rsquo;s
<code>Run build</code> operation beginning &mdash; the JVM booting. IDE s is everything outside the
Tooling API call. Build CPU comes from sampling <code>ps</code> at 4&nbsp;Hz, so it is accurate to about a
second per process.</div>
</section>

<section>
<h2>Swimchart &mdash; %s</h2>
<div class="chart">
  <div class="legend">%s</div>
  <div class="rows">%s</div>
  <div class="axis"><div></div><div class="ticks"><span>0 s</span><span>%.1f s</span></div></div>
</div>
<div class="note">IDE spans first, then the longest Gradle build operations in start order, indented by
nesting depth. Both clocks are epoch wall-clock, so the two processes line up exactly with no estimation.
Bars nest &mdash; do not add them up.</div>
</section>

<section>
<h2>Where the Gradle time goes</h2>
<div class="tw"><table><thead><tr><th>Category</th><th>Operations</th><th>Self-time s</th>
<th>Share</th></tr></thead><tbody>%s</tbody></table></div>
<div class="note">Self-time is an operation&rsquo;s duration minus the union of its direct children, so
these add up. It is <b>not</b> CPU time: an operation waiting on another process still accrues self-time.</div>
</section>

<section>
<h2>CPU by process</h2>
<div class="tw"><table><thead><tr><th>Process</th><th>CPU s</th></tr></thead><tbody>%s</tbody></table></div>
</section>

<footer style="margin-top:56px;padding-top:18px;border-top:1px solid var(--rule);
font:12.5px var(--mono);color:var(--ink-3)">%s</footer>
</div></body></html>""" % (
        CSS, esc(context["subtitle"]), chips,
        median, len(analyses), "" if len(analyses) == 1 else "s", syncs[-1] - syncs[0],
        "%.2f s" % best["gradle_seconds"] if best["gradle_seconds"] else "&ndash;",
        "%.0f%%" % (100.0 * best["gradle_seconds"] / best["sync_seconds"]) if best["gradle_seconds"] else "&ndash;",
        cpu_total,
        (best["cpu_seconds"] / best["gradle_seconds"]) if best["gradle_seconds"] else 0.0,
        runs,
        ("<b>The IDE's telemetry file was truncated, so the import interval was reconstructed "
         "from its phase spans.</b> The total may be a few milliseconds short. ")
        if best.get("reconstructed") else "",
        esc(best["label"]), legend, bars, span_seconds, categories, cpu_rows,
        esc(context["footer"]))
    path.write_text(document)


# -------------------------------------------------------------------------- main

def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Measure a cold IntelliJ Gradle import of this project.")
    parser.add_argument("--gradle", help="distribution zip, extracted distribution, or version "
                                         "(default: whatever the project's wrapper points at)")
    parser.add_argument("--kotlin-version", help="override the kotlin_version project property")
    parser.add_argument("--runs", type=int, default=3,
                        help="measured runs, median is reported (default 3; the first run of a "
                             "series reads high, so fewer than 3 is not advisable)")
    parser.add_argument("--idea", help="IntelliJ IDEA installation to drive")
    parser.add_argument("--java-home", type=Path, help="JDK for the Gradle daemon")
    parser.add_argument("--out", type=Path, help="output directory (default build/import-bench)")
    parser.add_argument("--heap", default="8g", help="IDE heap (default 8g)")
    parser.add_argument("--gradle-jvmargs", default="-Xmx3g", help="daemon JVM args (default -Xmx3g)")
    parser.add_argument("--state", choices=("scripts", "cold", "warm"), default="scripts",
                        help="what is cold. scripts (default): buildSrc stays built, the project's "
                             "Kotlin DSL scripts recompile. cold: everything recompiles, like a "
                             "fresh clone. warm: nothing recompiles, measures a re-import")
    parser.add_argument("--no-seed", action="store_true",
                        help="do not prime the isolated Gradle home from ~/.gradle (downloads everything)")
    parser.add_argument("--fresh", action="store_true", help="discard previous state and start clean")
    parser.add_argument("--open", action="store_true", help="open the report when finished")
    args = parser.parse_args(argv)

    if args.runs < 1:
        die("--runs must be at least 1")
    if args.java_home:
        args.java_home = args.java_home.expanduser().resolve()
        if not (args.java_home / "bin/java").is_file():
            die("not a JDK: " + str(args.java_home))

    state = (args.out or (ROOT / "build/import-bench")).expanduser().resolve()
    if args.fresh:
        rmtree(state)
    for name in ("runs", "report"):
        (state / name).mkdir(parents=True, exist_ok=True)

    ide_home, launcher = find_ide(args.idea)
    log("IDE:", ide_home, "(" + ide_build(ide_home) + ")")
    args.java_home, jdk_origin = resolve_jdk(args.java_home, ide_home)
    log("Gradle JVM:", args.java_home, "(" + jdk_origin + ")")

    project = state / "project"
    log("copying the checkout into", project)
    files = copy_project(ROOT, project)
    log("linked", files, "files")

    distribution, label = resolve_gradle(args.gradle, project, state)
    version = distribution_version(distribution)
    log("Gradle:", version, "at", distribution)
    apply_overrides(project, args.kotlin_version)

    gradle_home = state / "gradle-home"
    if not args.no_seed:
        seeded = seed_gradle_home(gradle_home)
        if seeded:
            log("seeded the isolated Gradle home with", seeded, "cached files")
    write_gradle_home(gradle_home, gradle_home / "ops-trace", args.java_home, args.gradle_jvmargs)
    sandbox = state / "sandbox"
    traces = sandbox / "traces"
    write_sandbox(sandbox, traces, args.heap)

    paths = dict(project=project, sandbox=sandbox, traces=traces, gradle_home=gradle_home,
                 runs=state / "runs", launcher=launcher, distribution=distribution)

    # Preparation leaves the Gradle home and buildSrc in a state that depends on
    # --state, so changing it has to re-prepare or the first run measures the old one.
    prepared = state / ".prepared"
    stamp = "%s|%s|%s" % (args.state, distribution, args.kotlin_version)
    if prepared.is_file() and prepared.read_text().strip() != stamp:
        log("configuration changed since the last run, preparing again")
        prepared.unlink()
    if not prepared.is_file():
        # One discarded import. It downloads dependencies, fills the Gradle caches and
        # populates the IDE index, so that the measured runs are not dominated by any
        # of the three. Its numbers are thrown away.
        # Two imports, both discarded. The first fills the dependency cache and the IDE
        # index; the second exists because the build logic is only genuinely up to date
        # from the second import onwards, and without it run 1 reads several seconds high.
        log("preparing (two unmeasured imports: dependencies, caches, IDE indexes)")
        run_import(args, paths, "prepare")
        run_import(args, paths, "prepare-2")
        prepared.write_text(stamp + "\n")

    analyses = []
    for index in range(1, args.runs + 1):
        log("run %d/%d" % (index, args.runs))
        result = run_import(args, paths, "run-%d" % index)
        analysis = analyse(result)
        if analysis is None:
            reasons = import_failure(paths["runs"] / ("run-%d.log" % index))
            detail = ("\n         " + "\n         ".join(reasons)) if reasons else ""
            die("run %d produced no import spans -- the import probably failed.%s\n"
                "       full log: %s" % (index, detail, paths["runs"] / ("run-%d.log" % index)))
        log("  import %.2f s | gradle %s | build CPU %.0f s"
            % (analysis["sync_seconds"],
               "%.2f s" % analysis["gradle_seconds"] if analysis["gradle_seconds"] else "n/a",
               analysis["cpu_seconds"]))
        analyses.append(analysis)

    analyses.sort(key=lambda a: a["sync_seconds"])
    context = dict(
        subtitle="%s · %s · %s" % (ROOT.name, version, time.strftime("%d %B %Y")),
        chips=[platform.platform(terse=True), "%d cores" % (os.cpu_count() or 0),
               ide_build(ide_home), version,
               "kotlin " + (args.kotlin_version or read_properties(
                   (project / "gradle.properties").read_text()).get("kotlin_version", "?")),
               "%d run%s" % (args.runs, "" if args.runs == 1 else "s"),
               "daemon JVM: " + jdk_label(args.java_home),
               {"scripts": "DSL scripts cold", "cold": "build logic cold",
                "warm": "build logic warm"}[args.state], "indexes warm", "dependencies cached"],
        footer="tools/import-bench · raw traces in %s" % (state / "runs"))

    report = state / "report/index.html"
    render(analyses, context, report)
    summary = dict(
        gradle=version, gradle_distribution=str(distribution), gradle_label=label,
        kotlin_version=args.kotlin_version, ide=ide_build(ide_home),
        median_seconds=statistics.median([a["sync_seconds"] for a in analyses]),
        runs=[dict(label=a["label"], sync_seconds=a["sync_seconds"],
                   gradle_seconds=a["gradle_seconds"], ide_seconds=a["ide_seconds"],
                   daemon_start_seconds=a["daemon_start_seconds"],
                   cpu_seconds=a["cpu_seconds"], cpu=a["cpu"],
                   categories={c["name"]: round(c["self"] / 1000.0, 3) for c in a["categories"]})
              for a in analyses])
    (state / "report/summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    log("median import %.2f s" % summary["median_seconds"])
    log("report:", report.as_uri())
    if args.open:
        opener = "open" if sys.platform == "darwin" else "xdg-open"
        subprocess.run([opener, str(report)], check=False)
    return 0


if __name__ == "__main__":
    sys.exit(main())
