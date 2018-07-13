/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.hamcrest.MatcherAssert.assertThat
import org.hamcrest.core.IsEqual
import org.junit.Test
import java.util.concurrent.Executor
import java.util.concurrent.Executors
import kotlin.coroutines.*

class DelayJvmTest : TestBase() {
    /**
     * Test that delay works properly in contexts with custom [ContinuationInterceptor]
     */
    @Test
    fun testDelayInArbitraryContext() = runBlocking {
        var thread: Thread? = null
        val pool = Executors.newFixedThreadPool(1) { runnable ->
            Thread(runnable).also { thread = it }
        }
        val context = CustomInterceptor(pool)
        val c = async(context) {
            assertThat(Thread.currentThread(), IsEqual(thread))
            delay(100)
            assertThat(Thread.currentThread(), IsEqual(thread))
            42
        }
        assertThat(c.await(), IsEqual(42))
        pool.shutdown()
    }

    @Test
    fun testDelayWithoutDispatcher() = runBlocking(CoroutineName("testNoDispatcher.main")) {
        // launch w/o a specified dispatcher
        val c = async(CoroutineName("testNoDispatcher.inner")) {
            delay(100)
            42
        }
        assertThat(c.await(), IsEqual(42))
    }

    @Test
    fun testNegativeDelay() = runBlocking {
        expect(1)
        val job = async(coroutineContext) {
            expect(3)
            delay(0)
            expect(4)
        }

        delay(-1)
        expect(2)
        job.await()
        finish(5)
    }

    class CustomInterceptor(val pool: Executor) : AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
            Wrapper(pool, continuation)
    }

    class Wrapper<T>(val pool: Executor, val cont: Continuation<T>) : Continuation<T> {
        override val context: CoroutineContext
            get() = cont.context

        override fun resumeWith(result: SuccessOrFailure<T>) {
            pool.execute { cont.resumeWith(result) }
        }
    }
}