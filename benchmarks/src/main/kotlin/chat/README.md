## In memory chat benchmark

This package contains the in memory chat macro benchmark.

The benchmark tests the performance of different types of channel. The application emulate real world user chats. It creates chat users that communicate with other users via channels. 

All the configuration for this benchmark are contained in `BenchmarkConfiguration.kt` file. You can change them according your desire to test different load.

This benchmark could be run using gradle task `./gradlew runInMemoryChatBenchmark`.