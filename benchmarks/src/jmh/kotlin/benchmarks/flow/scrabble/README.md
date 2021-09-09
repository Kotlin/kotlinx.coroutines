## Reactive scrabble benchmarks

This package contains reactive scrabble benchmarks.

Reactive Scrabble benchmarks were originally developed by José Paumard and are [available](https://github.com/JosePaumard/jdk8-stream-rx-comparison-reloaded) under Apache 2.0,
Flow version is adaptation of this work.
All Rx and Reactive benchmarks are based on (or copied from) [David Karnok work](https://github.com/akarnokd/akarnokd-misc).

### Benchmark classes

The package (split into two sourcesets, `kotlin` and `java`), contains different benchmarks with different purposes 
 
  * `RxJava2PlaysScrabble` and `RxJava2PlaysScrabbleOpt` are copied as is and used for comparison. The infrastructure (e.g. `FlowableSplit`)
     is copied from `akarnokd-misc` in order for the latter benchmark to work.
     This is the original benchmark for `RxJava`.
  * `ReactorPlaysScrabble` is an original benchmark for `Reactor`, but rewritten into Kotlin.
     It is disabled by default and had the only purpose -- verify that Kotlin version performs as the original Java version
     (which could have been different due to lambdas translation, implicit boxing, etc.). It is disabled because
     it has almost no difference compared to `RxJava` benchmark.
  * `FlowPlaysScrabbleBase` is a scrabble benchmark rewritten on top of the `Flow` API without using any optimizations or tricky internals.
  * `FlowPlaysScrabbleOpt` is an optimized version of benchmark that follows the same guidelines as `RxJava2PlaysScrabbleOpt`: it still is 
  lazy, reactive and uses only `Flow` abstraction.
  * `SequencePlaysScrabble` is a version of benchmark built on top of `Sequence` without suspensions, used as a lower bound.
  * `SaneFlowPlaysScrabble` is a `SequencePlaysScrabble` that produces `Flow`.
     This benchmark is not identical (in terms of functions pipelining) to `FlowPlaysScrabbleOpt`, but rather is used as a lower bound of `Flow` performance
     on this particular task.
     
### Results

Benchmark results for throughput mode, Java `1.8.0_172` 
running on `Intel(R) Core(TM) i9-9880H CPU @ 2.30GHz`
under `Darwin Kernel Version 18.7.0`.
Full command: `java -jar benchmarks.jar -f 2 -jvmArgsPrepend "-XX:+UseParallelGC" '.*Scrabble.*'`.

```
Benchmark                     Mode  Cnt   Score   Error  Units  

FlowPlaysScrabbleBase.play    avgt   14  62.480 ± 1.018  ms/op
FlowPlaysScrabbleOpt.play     avgt   14  13.958 ± 0.278  ms/op

RxJava2PlaysScrabble.play     avgt   14  88.456 ± 0.950  ms/op
RxJava2PlaysScrabbleOpt.play  avgt   14  23.653 ± 0.379  ms/op

SaneFlowPlaysScrabble.play    avgt   14  13.608 ± 0.332  ms/op
SequencePlaysScrabble.play    avgt   14   9.824 ± 0.190  ms/op
```
