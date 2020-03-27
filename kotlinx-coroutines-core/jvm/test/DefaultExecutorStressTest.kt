/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import kotlin.test.*

class DefaultExecutorStressTest : TestBase() {
    @Test
    fun testDelay() = runTest {
        val iterations = 100_000 * stressTestMultiplier
        withContext(DefaultExecutor) {
            expect(1)
            var expected = 1
            repeat(iterations) {
                expect(++expected)
                val deferred = async {
                    expect(++expected)
                    val largeArray = IntArray(10_000) { it }
                    delay(Long.MAX_VALUE)
                    println(largeArray) // consume to avoid DCE, actually unreachable
                }

                expect(++expected)
                yield()
                deferred.cancel()
                try {
                    deferred.await()
                } catch (e: CancellationException) {
                    expect(++expected)
                }
            }

        }
        finish(2 + iterations * 4)
    }

    @Test
    fun testWorkerShutdown() = withVirtualTimeSource {
        val iterations = 1_000 * stressTestMultiplier
        // wait for the worker to shut down
        suspend fun awaitWorkerShutdown() {
            val executorTimeoutMs = 1000L
            delay(executorTimeoutMs)
            while (DefaultExecutor.isThreadPresent) { delay(10) } // hangs if the thread refuses to stop
            assertFalse(DefaultExecutor.isThreadPresent) // just to make sure
        }
        runTest {
            awaitWorkerShutdown() // so that the worker shuts down after the initial launch
            repeat (iterations) {
                val job = launch(Dispatchers.Unconfined) {
                    // this line runs in the main thread
                    delay(1)
                    // this line runs in the DefaultExecutor worker
                }
                delay(100) // yield the execution, allow the worker to spawn
                assertTrue(DefaultExecutor.isThreadPresent) // the worker spawned
                job.join()
                awaitWorkerShutdown()
            }
        }
    }
}
