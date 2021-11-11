/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.exceptions.*
import kotlinx.coroutines.internal.*
import kotlin.test.*

class ConcurrentExceptionsStressTest : TestBase() {
    private val nWorkers = 4
    private val nRepeat = 1000 * stressTestMultiplier

    private var workers: Array<CloseableCoroutineDispatcher> = emptyArray()

    @AfterTest
    fun tearDown() {
        workers.forEach {
            it.close()
        }
    }

    @Test
    fun testStress() = runMtTest {
        workers = Array(nWorkers) { index ->
            newSingleThreadContext("JobExceptionsStressTest-$index")
        }

        repeat(nRepeat) {
            testOnce()
        }
    }

    @Suppress("SuspendFunctionOnCoroutineScope") // workaround native inline fun stacktraces
    private suspend fun CoroutineScope.testOnce() {
        val deferred = async(NonCancellable) {
            repeat(nWorkers) { index ->
                // Always launch a coroutine even if parent job was already cancelled (atomic start)
                launch(workers[index], start = CoroutineStart.ATOMIC) {
                    randomWait()
                    throw StressException(index)
                }
            }
        }
        deferred.join()
        assertTrue(deferred.isCancelled)
        val completionException = deferred.getCompletionExceptionOrNull()
        val cause = completionException as? StressException
            ?: unexpectedException("completion", completionException)
        val suppressed = cause.suppressed
        val indices = listOf(cause.index) + suppressed.mapIndexed { index, e ->
            (e as? StressException)?.index ?: unexpectedException("suppressed $index", e)
        }
        repeat(nWorkers) { index ->
            assertTrue(index in indices, "Exception $index is missing: $indices")
        }
        assertEquals(nWorkers, indices.size, "Duplicated exceptions in list: $indices")
    }

    private fun unexpectedException(msg: String, e: Throwable?): Nothing {
        throw IllegalStateException("Unexpected $msg exception", e)
    }

    private class StressException(val index: Int) : SuppressSupportingThrowable()
}

