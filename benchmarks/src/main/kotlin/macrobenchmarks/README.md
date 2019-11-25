# Macrobenchmarks

This package contains various macrobenchmarks that test different aspects of the performance of coroutines. These benchmarks try to emulate real life applications that could use coroutines in them. The idea is to test not a specific part of the implementation but to test the performance in general.

## Bfs channel benchmark

The benchmark implements the parallel version of the BFS graph algorithm using LinkedListChannel channel as a queue for the algorithm. It is designed to test the performance of the channel under contention.

You can find more details of the benchmark in the `BfsChannelBenchmark.kt`. All the configuration for this benchmark are contained there, too. You can change them according your desire to test different work load.

This benchmark could be run using gradle task `./gradlew runBfsChannelBenchmark`.