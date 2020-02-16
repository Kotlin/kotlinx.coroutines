/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.exceptions.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.test.*

// Check that exception is not leaked to the global exception handler
class LeakedExceptionTest : TestBase() {

    private val handler: (Throwable) -> Unit =
        { assertTrue { it is UndeliverableException && it.cause is TestException } }

    @Test
    fun testSingle() = withExceptionHandler(handler) {
        withFixedThreadPool(4) { dispatcher ->
            val flow = rxSingle<Unit>(dispatcher) { throw TestException() }.toFlowable().asFlow()
            runBlocking {
                repeat(10000) {
                    combine(flow, flow) { _, _ -> Unit }
                        .catch {}
                        .collect {}
                }
            }
        }
    }

    @Test
    fun testObservable() = withExceptionHandler(handler) {
        withFixedThreadPool(4) { dispatcher ->
            val flow = rxObservable<Unit>(dispatcher) { throw TestException() }
                .toFlowable(BackpressureStrategy.BUFFER)
                .asFlow()
            runBlocking {
                repeat(10000) {
                    combine(flow, flow) { _, _ -> Unit }
                        .catch {}
                        .collect {}
                }
            }
        }
    }

    @Test
    fun testFlowable() = withExceptionHandler(handler) {
        withFixedThreadPool(4) { dispatcher ->
            val flow = rxFlowable<Unit>(dispatcher) { throw TestException() }.asFlow()
            runBlocking {
                repeat(10000) {
                    combine(flow, flow) { _, _ -> Unit }
                        .catch {}
                        .collect {}
                }
            }
        }
    }

    /**
     * This test doesn't test much and was added to display a problem with straighforward use of
     * [withExceptionHandler].
     *
     * If one was to remove `dispatcher` and launch `rxFlowable` with an empty coroutine context,
     * this test would fail fairly often, while other tests were also vulnerable, but the problem is
     * much more difficult to reproduce. Thus, this test is a justification for adding `dispatcher`
     * to other tests.
     *
     * See the commit that introduced this test for a better explanation.
     */
    @Test
    fun testResettingExceptionHandler() = withExceptionHandler(handler) {
        withFixedThreadPool(4) { dispatcher ->
            val flow = rxFlowable<Unit>(dispatcher) {
                if ((0..1).random() == 0) {
                    Thread.sleep(100)
                }
                throw TestException()
            }.asFlow()
            runBlocking {
                combine(flow, flow) { _, _ -> Unit }
                    .catch {}
                    .collect {}
            }
        }
    }

    /**
     * Run in a thread pool, then wait for all the tasks to finish.
     */
    private fun withFixedThreadPool(numberOfThreads: Int, block: (CoroutineDispatcher) -> Unit) {
        val pool = Executors.newFixedThreadPool(numberOfThreads)
        val dispatcher = pool.asCoroutineDispatcher()
        block(dispatcher)
        pool.shutdown()
        while (!pool.awaitTermination(10, TimeUnit.SECONDS)) {
            /* deliberately empty */
        }
    }
}
