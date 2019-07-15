## In memory chat benchmark

This package contains the in memory chat macro benchmark.

The benchmark tests different types of channel and different ways to use them. The application emulate real world user chats. It creates chat users that communicate with other users via channels. 

All the properties for this benchmark are contained in `BenchmarkProperties.kt` file. You can change them according your desire to test different ways to use channels and different load.

This benchmark could be run using gradle task `./gradlew runInMemoryChatBenchmark`.