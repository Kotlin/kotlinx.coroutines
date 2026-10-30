package kotlinx.coroutines.selects

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import kotlin.test.*

@Suppress("DEPRECATION")
class SelectMutexStressTest : TestBase() {
    @Test
    fun testSelectCancelledResourceRelease() = runTest {
        val n = 1_000 * stressTestMultiplier
        val mutex = Mutex(true) as MutexImpl // locked
        expect(1)
        repeat(n) { i ->
            val job = launch(kotlin.coroutines.coroutineContext) {
                expect(i + 2)
                select {
                    mutex.onLock {
                        expectUnreached() // never able to lock
                    }
                }
            }
            yield() // to the launched job, so that it suspends
            job.cancel() // cancel the job and select
            yield() // so it can cleanup after itself
        }
        assertTrue(mutex.isLocked)
        finish(n + 2)
    }
}
