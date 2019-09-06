## In memory chat benchmark

This package contains in memory chat macro benchmark.

Benchmark is designed to test the performance of different channels and dispatchers. For this purpose application emulates chat workload creating users that communicate with each other. A new java process is created for each benchmark configuration.

Benchmark creates users which represented by coroutines, sets to each user message sending speed – rational number which means how many messages a user can send if it got a message from other user. Then it starts all coroutines, waits for some time and collects all the results.
Right after start, user sends `message sending speed` messages and waits for messages from other users. After getting a message, user increases number of messages to send by `message sending speed`, and sends messages to users `number of messages to send` messages.

All the configuration for this benchmark are contained in `BenchmarkConfiguration.kt` file. You can change them according your desire to test different work load.

This benchmark could be run using gradle task `./gradlew runInMemoryChatBenchmark`.

NB: before running this benchmark please ensure that kotlinx.coroutines issue #504 is fixed.