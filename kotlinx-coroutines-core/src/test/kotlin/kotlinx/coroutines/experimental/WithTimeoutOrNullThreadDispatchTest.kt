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

import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNull
import org.junit.After
import org.junit.Assert
import org.junit.Assert.assertThat
import org.junit.Test
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.ThreadFactory
import kotlin.coroutines.experimental.CoroutineContext

class WithTimeoutOrNullThreadDispatchTest : TestBase() {
    var executor: ExecutorService? = null

    @After
    fun tearDown() {
        executor?.shutdown()
    }

    @Test
    fun testCancellationDispatchScheduled() {
        checkCancellationDispatch {
            executor = Executors.newScheduledThreadPool(1, it)
            executor!!.asCoroutineDispatcher()
        }
    }

    @Test
    fun testCancellationDispatchNonScheduled() {
        checkCancellationDispatch {
            executor = Executors.newSingleThreadExecutor(it)
            executor!!.asCoroutineDispatcher()
        }
    }

    @Test
    fun testCancellationDispatchCustomNoDelay() {
        checkCancellationDispatch {
            executor = Executors.newSingleThreadExecutor(it)
            object : CoroutineDispatcher() {
                override fun dispatch(context: CoroutineContext, block: Runnable) {
                    executor!!.execute(block)
                }
            }
        }
    }

    private fun checkCancellationDispatch(factory: (ThreadFactory) -> CoroutineDispatcher) = runBlocking {
        expect(1)
        var thread: Thread? = null
        val dispatcher = factory(ThreadFactory { Thread(it).also { thread = it } })
        run(dispatcher) {
            expect(2)
            Assert.assertThat(Thread.currentThread(), IsEqual(thread))
            val result =
                withTimeoutOrNull(100) {
                    try {
                        expect(3)
                        delay(1000)
                        expectUnreached()
                    } catch (e: CancellationException) {
                        expect(4)
                        Assert.assertThat(Thread.currentThread(), IsEqual(thread))
                    }
                    expect(5)
                    "FAIL"
                }
            assertThat(result, IsNull())
            expect(6)
        }
        finish(7)
    }
}