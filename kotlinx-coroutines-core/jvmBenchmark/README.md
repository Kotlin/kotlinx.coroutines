## kotlinx-coroutines-core benchmarks

This source-set contains benchmarks that leverage `internal` API (e.g. `suspendCancellableCoroutineReusable`)
and thus cannot be written in `benchmarks` module.

This is an interim solution unless we introduce clear separation of responsibilities in benchmark modules
and decide on their usability.


### Usage

```
./gradlew :kotlinx-coroutines-core:jvmBenchmarkBenchmarkJar
java -jar kotlinx-coroutines-core/build/benchmarks/jvmBenchmark/jars/kotlinx-coroutines-core-jvmBenchmark-jmh-*-JMH.jar
```
