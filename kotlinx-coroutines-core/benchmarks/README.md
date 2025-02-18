## kotlinx-coroutines-core benchmarks

Multiplatform benchmarks for kotlinx-coroutines-core.

This source-set contains benchmarks that leverage `internal` API (e.g. `suspendCancellableCoroutineReusable`) or
that are multiplatform (-> only supported with `kotlinx-benchmarks` which is less convenient than `jmh` plugin).
For JVM-only non-internal benchmarks, consider using `benchmarks` top-level project.

### Usage

```
// JVM only
./gradlew :kotlinx-coroutines-core:jvmBenchmarkBenchmarkJar
java -jar kotlinx-coroutines-core/build/benchmarks/jvmBenchmark/jars/kotlinx-coroutines-core-jvmBenchmark-jmh-*-JMH.jar

// Native, OS X
./gradlew :kotlinx-coroutines-core:macosArm64BenchmarkBenchmark

// Figure out what to use
./gradlew :kotlinx-coroutines-core:tasks | grep -i bench
```
