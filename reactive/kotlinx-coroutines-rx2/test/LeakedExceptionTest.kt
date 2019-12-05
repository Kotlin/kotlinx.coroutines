/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.exceptions.*
import io.reactivex.plugins.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import java.io.*
import kotlin.test.*

// Check that exception is not leaked to the global exception handler
class LeakedExceptionTest : TestBase() {

    private val handler: (Throwable) -> Unit =
        { assertTrue { it is UndeliverableException && it.cause is TestException } }

    @Test
    fun testSingle() = withExceptionHandler(handler) {
        val flow = rxSingle<Unit> { throw TestException() }.toFlowable().asFlow()
        runBlocking {
            repeat(10000) {
                combine(flow, flow) { _, _ -> Unit }
                    .catch {}
                    .collect { }
            }
        }
    }

    @Test
    fun testObservable() = withExceptionHandler(handler) {
        val flow = rxObservable<Unit> { throw TestException() }.toFlowable(BackpressureStrategy.BUFFER).asFlow()
        runBlocking {
            repeat(10000) {
                combine(flow, flow) { _, _ -> Unit }
                    .catch {}
                    .collect { }
            }
        }
    }

    @Test
    fun testFlowable() = withExceptionHandler(handler) {
        val flow = rxFlowable<Unit> { throw TestException() }.asFlow()
        runBlocking {
            repeat(10000) {
                combine(flow, flow) { _, _ -> Unit }
                    .catch {}
                    .collect { }
            }
        }
    }
}
