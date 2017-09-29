/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import org.hamcrest.MatcherAssert.assertThat
import org.hamcrest.core.IsEqual
import org.junit.Test
import java.util.concurrent.Executor
import java.util.concurrent.Executors
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

class DelayTest : TestBase() {
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

    class CustomInterceptor(val pool: Executor) : AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
            Wrapper(pool, continuation)
    }

    class Wrapper<T>(val pool: Executor, val cont: Continuation<T>) : Continuation<T> {
        override val context: CoroutineContext
            get() = cont.context

        override fun resume(value: T) {
            pool.execute { cont.resume(value) }
        }

        override fun resumeWithException(exception: Throwable) {
            pool.execute { cont.resumeWithException(exception) }
        }
    }

}