# Cold import benchmark

Measures how long IntelliJ IDEA takes to import this project from a cold Gradle state,
and writes a self-contained HTML report with a total time, CPU time and a swimchart.

```sh
./bench                                            # the Gradle the wrapper points at
./bench --gradle env/gradle/gradle-9.9.0-bin.zip   # a locally built distribution
./bench --gradle 9.8.0-rc-1                        # a released version, downloaded if needed
./bench --gradle 9.8.0-rc-1 --kotlin-version 2.3.21 --runs 5 --open
```

The report lands in `../../build/import-bench-xxh3`, with machine-readable numbers
next to it in `summary.json`.

## Requirements

Python 3.8+ and an IntelliJ IDEA installation. That is all — no plugins, no profiler, no
JDK on `PATH`, and the IDE does not have to be running. On macOS and Linux the
installation is found automatically; otherwise pass `--idea` or set `IDEA_HOME`.

The benchmark starts its own headless IDE against a throwaway sandbox, so it will not
touch the IDE you are working in. **Your checkout is never modified** — the project is
hardlink-copied into `../../build/import-bench-xxh3` and measured there.

## What the number means

The headline is the **`ExternalSystemSyncProjectTask` OpenTelemetry span**: from the
moment the IDE starts the sync task to the moment the workspace model is committed.

It is *not* the "Elapsed time" the IDE prints at the end of a warmup run. That includes
the indexing tail, which on this project is comparable to the import itself and is not
part of it.

Each measured run is a **cold Gradle import on a warm machine**:

* the project's build output, IDE state and compiled Kotlin DSL scripts are deleted first,
  so the build scripts really are recompiled (see `--state` below for exactly how much);
* the Gradle daemon is fresh — the IDE starts one and stops it when the project closes,
  so daemon startup and cold JIT are inside the number, which is what a first import
  after opening the IDE actually costs;
* the Gradle home is isolated under `../../build/import-bench-xxh3`, primed once from
  your `~/.gradle` by hardlinking, so dependencies are never re-downloaded and almost no
  extra disk is used — `du` will report tens of gigabytes that are not really there;
* the IDE's cached workspace model is dropped between runs, because otherwise the IDE
  decides the project is already configured and performs no import at all;
* the IDE sandbox indexes are kept between runs, so indexing has almost nothing left to do
  and does not compete with Gradle for cores.

The first invocation performs two extra, discarded imports to settle those caches. Their
numbers are thrown away. Changing `--state`, `--gradle` or `--kotlin-version` re-does it.

### What `--state` controls

| `--state` | buildSrc / convention plugins | project `*.gradle.kts` | what it models |
| --- | --- | --- | --- |
| `scripts` *(default)* | stay built | recompiled every run | a fresh checkout whose build logic is cached |
| `cold` | recompiled every run | recompiled every run | a fresh clone on a machine that has never built this |
| `warm` | stay built | stay compiled | re-importing a project you already built |

`scripts` is the one to compare numbers with. `cold` additionally starts a Kotlin compiler
daemon and compiles the convention plugins, which adds several seconds and a lot of
variance; `warm` hides Kotlin DSL compilation entirely, which is usually the largest single
cost in the import.

## Reading the report

* **Import** — the span above, **median** across runs, with the observed spread. The first
  measured run of a series reads consistently high — a few seconds, spread evenly across
  every category, so it looks like a slower machine rather than more work. Three runs is the
  default for exactly that reason: the median ignores it, and runs 2 and 3 typically agree to
  within 1%. Do not read anything into a sub-second difference between two configurations
  unless it survives repeated runs.
* **Inside Gradle** — the `Run build` operation. Everything else is the IDE.
* **Daemon start** — the gap between the Tooling API call opening and `Run build`
  beginning: the daemon JVM booting.
* **CPU** — cumulative CPU of every build JVM, summed across threads, sampled from `ps`
  at 4 Hz. Accurate to roughly a second per process; good enough to see that a 15-second
  import uses about one core of however many you have.
* **Parallelism** — build CPU divided by Gradle wall time. A value near 1 means the build
  is a chain, not a contention problem.
* **Swimchart** — IDE spans, then the longest Gradle build operations in start order,
  indented by nesting. Both clocks are epoch wall-clock, so the two processes align
  exactly. Bars nest; do not add them up.
* **Self-time** — an operation's duration minus the union of its direct children. These
  do add up. It is not CPU time: an operation blocked on another process still accrues
  self-time, which is how a 5-second wait can look like 5 seconds of work.

## Options

| Flag | Meaning |
| --- | --- |
| `--gradle` | distribution zip, extracted distribution, or version. Defaults to the wrapper. |
| `--kotlin-version` | overrides the `kotlin_version` project property in the working copy. |
| `--runs N` | measured runs, default 3; the median is reported and every run is listed. |
| `--java-home` | JDK for the Gradle daemon (sets `org.gradle.java.home`). |
| `--idea` | IntelliJ installation to drive. |
| `--out` | output directory, default `../../build/import-bench-xxh3`. |
| `--heap`, `--gradle-jvmargs` | IDE heap and daemon JVM args. |
| `--no-seed` | do not prime the isolated Gradle home from `~/.gradle`. Downloads everything. |
| `--state` | `scripts` (default), `cold` or `warm`; see the table above. |
| `--fresh` | throw away all previous benchmark state and start over. |
| `--open` | open the report when finished. |

## Caveats

* Gradle's build-operation trace is always on, because the swimchart needs it. It costs a
  few percent. Comparisons between runs of this tool are fair; comparisons against a
  hand-timed import are not.
* Changing the Gradle distribution invalidates the build cache for `buildSrc`, so the first
  run on a new distribution really compiles the convention plugins and reads several seconds
  high. The preparation run absorbs this, but if a run looks anomalous, run it again.
* The daemon runs on the IDE's bundled JBR by default, so two people with the same IDE
  measure on the same JVM regardless of their `JAVA_HOME`. Pass `--java-home` to change it;
  the JVM in use is printed and shown in the report.
* The IDE's telemetry file is written as the run goes and the warmup entry point can exit
  before it is flushed, so it is often truncated. The tool parses what survived and, if the
  root span itself was lost, reconstructs the interval from the phase spans and says so in
  the report.
* The benchmark drives an internal IDE entry point (`warmup`) that needs
  `idea.is.internal=true`; the sandbox sets it. If a future IDE renames or removes it, the
  run fails with no sync span and the log under `../../build/import-bench-xxh3` says why.
* Everything is one process tree on one machine: a busy laptop measures a busy laptop.
  Close other builds before caring about the last half second.
