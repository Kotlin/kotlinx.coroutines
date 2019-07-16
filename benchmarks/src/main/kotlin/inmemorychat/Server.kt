package inmemorychat

import java.util.concurrent.atomic.AtomicLong

class Server(private val properties: BenchmarkProperties) {
    private var idSequence = AtomicLong()

    fun registerClient(shouldCountMetrics : Boolean): User {
        val userId = idSequence.incrementAndGet()
        val messagesChannel = properties.channelType.createChannel<Message>()

        return when (properties.benchmarkMode) {
            BenchmarkModes.USER_WITH_TWO_JOBS -> UserWithTwoJobs(userId, messagesChannel, properties, shouldCountMetrics)
            BenchmarkModes.USER_WITH_ONE_JOB -> UserWithOneJob(userId, messagesChannel, properties, shouldCountMetrics)
            BenchmarkModes.USER_WITH_SELECT -> UserWithSelect(userId, messagesChannel, properties.channelType.createChannel(),
                    properties, shouldCountMetrics)
        }
    }
}