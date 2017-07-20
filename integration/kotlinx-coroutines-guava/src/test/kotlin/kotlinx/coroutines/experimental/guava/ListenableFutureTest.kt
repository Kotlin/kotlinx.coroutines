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

package kotlinx.coroutines.experimental.guava

import com.google.common.util.concurrent.MoreExecutors
import com.google.common.util.concurrent.SettableFuture
import guide.test.ignoreLostThreads
import kotlinx.coroutines.experimental.*
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsInstanceOf
import org.junit.Assert.*
import org.junit.Before
import org.junit.Test
import java.util.concurrent.Callable
import java.util.concurrent.ExecutionException
import java.util.concurrent.ForkJoinPool

class ListenableFutureTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("ForkJoinPool.commonPool-worker-")
    }

    @Test
    fun testSimpleAwait() {
        val service = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = future {
            service.submit(Callable<String> {
                "O"
            }).await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedFuture() {
        val toAwait = SettableFuture.create<String>()
        toAwait.set("O")
        val future = future {
            toAwait.await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForFuture() {
        val toAwait = SettableFuture.create<String>()
        val future = future {
            toAwait.await() + "K"
        }
        assertFalse(future.isDone)
        toAwait.set("O")
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedFutureExceptionally() {
        val toAwait = SettableFuture.create<String>()
        toAwait.setException(IllegalArgumentException("O"))
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                assertThat(e, IsInstanceOf(IllegalArgumentException::class.java))
                e.message!!
            } + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForFutureWithException() {
        val toAwait = SettableFuture.create<String>()
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                assertThat(e, IsInstanceOf(IllegalArgumentException::class.java))
                e.message!!
            } + "K"
        }
        assertFalse(future.isDone)
        toAwait.setException(IllegalArgumentException("O"))
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testExceptionInsideCoroutine() {
        val service = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = future {
            if (service.submit(Callable<Boolean> { true }).await()) {
                throw IllegalStateException("OK")
            }
            "fail"
        }
        try {
            future.get()
            fail("'get' should've throw an exception")
        } catch (e: ExecutionException) {
            assertThat(e.cause, IsInstanceOf(IllegalStateException::class.java))
            assertThat(e.cause!!.message, IsEqual("OK"))
        }
    }

    @Test
    fun testCompletedDeferredAsListenableFuture() = runBlocking {
        expect(1)
        val deferred = async(context, CoroutineStart.UNDISPATCHED) {
            expect(2) // completed right away
            "OK"
        }
        expect(3)
        val future = deferred.asListenableFuture()
        assertThat(future.await(), IsEqual("OK"))
        finish(4)
    }

    @Test
    fun testWaitForDeferredAsListenableFuture() = runBlocking {
        expect(1)
        val deferred = async(context) {
            expect(3) // will complete later
            "OK"
        }
        expect(2)
        val future = deferred.asListenableFuture()
        assertThat(future.await(), IsEqual("OK")) // await yields main thread to deferred coroutine
        finish(4)
    }

    @Test
    fun testCancellableAwait() = runBlocking {
        expect(1)
        val toAwait = SettableFuture.create<String>()
        val job = launch(context, CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                toAwait.await() // suspends
            } catch (e: CancellationException) {
                expect(5) // should throw cancellation exception
                throw e
            }
        }
        expect(3)
        job.cancel() // cancel the job
        toAwait.set("fail") // too late, the waiting job was already cancelled
        expect(4) // job processing of cancellation was scheduled, not executed yet
        yield() // yield main thread to job
        finish(6)
    }
}
