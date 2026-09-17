# Measure Gradle import in IDEA

Open this checkout in IDEA, then run from the repository root:

```sh
./measure
```

The command installs or updates a small IDEA driver automatically. IDEA stays
running. A successful run opens an HTML report and prints its `file:///.../index.html`
URL. The report shows an aligned IDEA/Gradle timeline, stage wall times, Gradle operation
costs, task cache outcomes, and CPU/allocation flamegraphs for IDEA and the build JVMs
that actually start. A cache hit can avoid starting the Kotlin compiler daemon.

Results, raw JFR recordings, logs, and measurement settings are kept outside the
checkout under `~/.cache/coroutines-import-profile/<project-path-hash>/runs/`.
`latest.json` in that state directory points to the latest report. Failed imports,
incomplete recordings, and detected background indexing are reported as failures.

You can also use **Tools → Profile Cold Gradle Import** after the first run, or
open `tools/gradle-import-profile/Run.command`.

## Options

```sh
./measure --dependencies download       # Include dependency downloads in the measurement
./measure --refresh-seed                # Refresh the downloaded dependency seed
./measure --refresh-cache-snapshot      # Take a new snapshot of normal global Gradle caches
./measure --project /path/to/checkout    # Another checkout already open in the same IDEA
./measure --gradle-version 9.8.0-rc-1   # Use an installed distribution without changing the wrapper
./measure --kotlin-version 2.3.21        # Explicit override if the branch needs an unavailable snapshot
./measure --global-caches empty         # Opt into the old, fully cold compilation mode
./measure --calibrate                   # Timing control followed by a profiled import
./measure --profile none                # Timing control only; no async-profiler/Gradle trace
./measure --no-open                     # Print the report URL without opening the browser
./measure --cpu-interval 2ms --alloc-interval 512k
./measure --java-auto-detect false --java-installation /path/to/required/jdk
./measure status
./measure restore
./measure uninstall
```

`--dependencies cached` is the default. The first run, or a build configuration
change, prepares a dependency seed with an unmeasured IDEA import. Later runs
reuse downloaded dependency artifacts and metadata and perform the measured import
offline. Use `--refresh-seed` after dependency or repository changes that are not
captured by the build fingerprint. Dependency seeding does not seed compilation caches.

`--global-caches warm` is the default. The runner snapshots the normal Gradle home's
caches, properties and init scripts once per build fingerprint. Each run gets an
independent copy of that frozen snapshot, including Kotlin DSL caches, transforms,
generated jars and build-cache entries. The normal Gradle home stays untouched.
Use `--refresh-cache-snapshot` after changing global settings or to capture newly
warmed caches. Setup and copying are outside the measurement.

`--global-caches empty` opts into clearing global compilation caches and disabling
build/configuration caching. It is substantially colder than a fresh checkout.

`--calibrate` runs an IDEA-span-only timing control, resets project outputs and build
JVMs, restores the same global cache snapshot, and runs the profiler. The final report
links both runs. It displays their observed times without claiming their difference
is a precise overhead estimate. Both keep IDEA warm and pause indexing. The control
has no CPU samples, so it can verify the indexing guard but cannot sample-check it.

`--java-auto-detect default|true|false` controls toolchain discovery only in the
isolated Gradle home. `default` leaves it unchanged. `--java-installation` can be
repeated to supply required JDKs. These flags do not edit project properties.

`--indexing normal` allows scanning and indexing to overlap the import. The default
is `paused`. `--timeout` sets the import timeout in seconds; the default is 900.

## What a measurement includes

* IDEA stays warm: its classes, JIT, project model, and IDE caches remain loaded.
* All project-local `build`, `.gradle`, and `.kotlin` directories are cleared,
  including nested build logic. Tracked files abort cleanup. Symlinks are not
  traversed. Sources and IDEA project metadata remain.
* A fresh isolated Gradle home is copied from the frozen global cache snapshot.
  Normal user/project build and configuration cache settings remain enabled or
  disabled as configured. Project-local configuration-cache entries are cleared.
  Build task outputs can be restored FROM-CACHE; the report lists actual outcomes.
* Gradle and Kotlin use fresh JVMs. `./measure` stops only build processes that
  name this runner's isolated state. Other Java work stays running and is recorded
  in the manifest. Stop it yourself when you need a quiet machine. IDEA is never
  stopped. Only one measurement of this checkout can run at a time.
* Gradle distributions and downloaded toolchains are copied from the normal
  Gradle home, which is not modified. OS filesystem caches and globally installed
  tools, including Kotlin/Native distributions, stay warm.
* Timing starts immediately before the explicit IDEA refresh request. It ends
  after both successful Gradle sync and IDEA's final model-application tasks.
  Setup, profiler attachment, recorder shutdown, and catch-up indexing are outside
  this interval. Indexing completion is not awaited.

## Excluding indexing

Before cleanup, the driver suppresses scanning requests in every open project in
that IDEA process, defers indexing queue flushes, and waits for existing work to
finish. It also temporarily sets `idea.indexes.pretendNoFiles=true`. This prevents
VFS-triggered indexers from bypassing the deferred queue. The indexer returns
before consuming queued files.

The driver pauses the scanning-to-dumb-mode observer so deferred files do not keep
IDEA in dumb mode. Other dumb tasks and index queries remain enabled; Kotlin DSL
model application needs them. Simply suspending all indexing tasks can deadlock
that model application.

After recording, the driver restores the previous system property, queue behavior,
observer, Gradle home, offline setting, and auto-reload setting. It requests a full
catch-up scan in each affected project. Restoration also runs on normal failures
and interruption. `./measure restore` recovers after an externally killed runner.

The manifest records the guard state before and after import. The report counts
active scanning and content-indexing worker samples separately from queue
bookkeeping and skipped indexer calls. A paused run fails validation if those
workers appear in the CPU profile. No indexing samples are removed from a profile.
This is a sampling check, not a proof that no sub-sample work occurred.

These controls use internal IDEA APIs and are intended for local performance
experiments. They were developed against IDEA IU-262.10968.63 on macOS ARM64.

## Reading the report

The headline starts at the explicit refresh request and ends at the final import
callback. The report also shows the real `ExternalSystemSyncProjectTask` span.
IDEA stage spans nest and can overlap streamed model updates. Do not add them.
Gradle category coverage is the union of operation intervals. Operation self time
subtracts the union of direct child intervals; its sum includes parallel work and
waits. It is not CPU time or a partition of the import wall time. Process recording
windows overlap and include idle time; do not add them. Sampled CPU seconds sum across threads and
can exceed wall time. Allocation graphs are weighted by estimated allocated bytes.
The Kotlin compiler daemon compiles build logic, including `buildSrc`; its entire
recording window is not a compilation-task timer.

IDEA is attached before import. Gradle loads async-profiler at JVM startup. A small
Java agent profiles Kotlin and worker JVMs from startup and inventories JDK probe
processes without loading the native profiler into them. CPU and allocations are
recorded together and converted separately. Graphs are cropped to the import
interval; raw recordings retain setup and shutdown margins. All timings include
profiler and operation-tracing overhead in full-profile mode.

## Requirements and checks

Requires Python 3.9+, `asprof` and `jfrconv` on PATH, a JDK 21+ with `javac`, and IDEA's
bundled Groovy scripting support with in-process Gradle tooling. The wrapper's
Gradle distribution must already be downloaded in the normal Gradle home.

Use `--idea '/path/IntelliJ IDEA.app' --jdk /path/to/jdk` for nondefault installations.
The helper compiles directly against the installed IDEA jars; it does not start
Gradle to build itself. Profiler/state paths must not contain spaces or commas.

Run the cleanup, process-ownership, isolation, and report checks without importing:

```sh
python3 -m unittest discover -s tools/gradle-import-profile -p 'test_*.py' -v
```

### Timeline capture

The bridge temporarily wraps IDEA's telemetry manager for `external.system`
tracers. A local OpenTelemetry SDK records the existing sync spans in memory.
Other telemetry scopes delegate to the original manager. The wrapper replaces
external-system export for this interval and restores the original manager on
teardown; it does not change the global SDK. This uses an internal test API.

Gradle receives `-Dorg.gradle.internal.operations.trace` in its daemon JVM options.
The report parses the operation log, pairs starts and ends, and aligns both traces
by epoch timestamps. A successful profiled report requires an IDEA sync root and a complete
Gradle `Run build` inside the measurement interval. Timing controls require the IDEA
sync root and successful import callbacks; they do not record Gradle operations. Raw data is retained in
`idea-spans.json`, `gradle-operations-log.txt`, and `anatomy.json`.

The default approximates a fresh checkout on a machine that has already used Gradle:
project outputs are empty, while global caches remain available. IDEA remains open,
so its project model is warm. The report records the measured revision and wrapper;
it does not equate timings from different branches or Gradle versions.
