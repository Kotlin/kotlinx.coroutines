@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.selects

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class SelectLoopTest : TestBase() {
    // https://github.com/Kotlin/kotlinx.coroutines/issues/1130
    @Test
    fun testChannelSelectLoop() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val channel = Channel<Unit>()
        val job = launch {
            expect(2)
            channel.send(Unit)
            expect(3)
            throw TestException()
        }
        try {
            while (true) {
                select<Unit> {
                    channel.onReceiveCatching {
                        expectUnreached()
                    }
                    job.onJoin {
                        expectUnreached()
                    }
                }
            }
        } catch (e: CancellationException) {
            // select will get cancelled because of the failure of job
            finish(4)
        }
    }
}
