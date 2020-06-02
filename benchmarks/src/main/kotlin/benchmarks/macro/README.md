# Macro Benchmarks
This package contains a set of custom (not JMH-based) benchmarks 
which test different parts of Kotlin Coroutines library.

Most of the benchmarks either simulate real-world scenarios 
or use a wider range of workloads than in typical micro-benchmarks.

## Producer-Consumer Benchmark for Channels with Monte-Carlo Workload Simulation
This benchmark tests channels under high contention 
and is similar to `ChannelProducerConsumerBenchmark.kt`, 
but performs the analysis on different workloads under 
the specified bound, and counts the _average_ performance 
characteristics using the Monte-Carlo approach.

**How to Run** 
The special `runChanProdConsMCBench` should be used to run
the benchmark, the corresponding results will locate in 
`out/results_channel_prod_cons_montecarlo.csv` in this module:

```
../gradlew runChanProdConsMCBench
``` 

The benchmark is also provided by a script that generates 
a set of plots to help with further analysis; please run 
the following command from this module to get ones:

```
python3 scripts/generate_plots_channel_prod_cons_monte_carlo.py
```