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

import org.junit.Assert.assertTrue
import org.junit.Test
import java.io.IOException

class AsyncTest : TestBase() {
    @Test
    fun testSimple(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext) {
            expect(3)
            42
        }
        expect(2)
        check(d.isActive)
        check(d.await() == 42)
        check(!d.isActive)
        expect(4)
        check(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testUndispatched(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            42
        }
        expect(3)
        check(!d.isActive)
        check(d.await() == 42)
        finish(4)
    }

    @Test(expected = IOException::class)
    fun testSimpleException(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext) {
            finish(3)
            throw IOException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test(expected = IOException::class)
    fun testDeferAndYieldException(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext) {
            expect(3)
            yield() // no effect, parent waiting
            finish(4)
            throw IOException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferWithTwoWaiters() = runBlocking {
        expect(1)
        val d = async(coroutineContext) {
            expect(5)
            yield()
            expect(9)
            42
        }
        expect(2)
        launch(coroutineContext) {
            expect(6)
            check(d.await() == 42)
            expect(11)
        }
        expect(3)
        launch(coroutineContext) {
            expect(7)
            check(d.await() == 42)
            expect(12)
        }
        expect(4)
        yield() // this actually yields control to async, which produces results and resumes both waiters (in order)
        expect(8)
        yield() // yield again to "d", which completes
        expect(10)
        yield() // yield to both waiters
        finish(13)
    }

    @Test
    fun testAsyncWithFinally() = runBlocking {
        expect(1)
        val d = async<String>(coroutineContext) {
            expect(3)
            try {
                yield() // to main, will cancel
            } finally {
                expect(6) // will go there on await
                return@async "Fail" // result will not override cancellation
            }
            expectUnreached()
            "Fail2"
        }
        expect(2)
        yield() // to async
        expect(4)
        check(d.isActive && !d.isCompleted && !d.isCompletedExceptionally && !d.isCancelled)
        check(d.cancel())
        check(!d.isActive && !d.isCompleted && !d.isCompletedExceptionally && d.isCancelled)
        check(!d.cancel()) // second attempt returns false
        check(!d.isActive && !d.isCompleted && !d.isCompletedExceptionally && d.isCancelled)
        expect(5)
        try {
            d.await() // awaits
            expectUnreached() // does not complete normally
        } catch (e: Throwable) {
            expect(7)
            check(e is CancellationException)
        }
        check(!d.isActive && d.isCompleted && d.isCompletedExceptionally && d.isCancelled)
        finish(8)
    }

    class BadClass {
        override fun equals(other: Any?): Boolean = error("equals")
        override fun hashCode(): Int = error("hashCode")
        override fun toString(): String = error("toString")
    }


    @Test
    fun blockingAsync() = runBlocking {
        val d = blockingAsync { 42 }
        check(d.await() == 42)
    }

    @Test
    fun blockingAsyncLazy() = runBlocking {
        val d = blockingAsync(start = CoroutineStart.LAZY) { 42 }
        check(d.await() == 42)
    }

    @Test(expected = IllegalArgumentException::class)
    fun blockingAsyncUndispatched() = runBlocking {
        blockingAsync(start = CoroutineStart.UNDISPATCHED) { 42 }
    }

    @Test
    fun testDeferBadClass() = runBlocking {
        val bad = BadClass()
        val d = async(coroutineContext) {
            expect(1)
            bad
        }
        assertTrue(d.await() === bad)
        finish(2)
    }
}
