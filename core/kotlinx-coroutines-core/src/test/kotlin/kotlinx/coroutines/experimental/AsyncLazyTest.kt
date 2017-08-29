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

import org.junit.Test
import java.io.IOException

class AsyncLazyTest : TestBase() {
    @Test
    fun testSimple(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(3)
            42
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        check(d.await() == 42)
        check(!d.isActive && d.isCompleted && !d.isCompletedExceptionally)
        expect(4)
        check(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testLazyDeferAndYield(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(3)
            yield() // this has not effect, because parent coroutine is waiting
            expect(4)
            42
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        check(d.await() == 42)
        check(!d.isActive && d.isCompleted && !d.isCompletedExceptionally)
        expect(5)
        check(d.await() == 42) // second await -- same result
        finish(6)
    }

    @Test
    fun testLazyDeferAndYield2(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(7)
            42
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        launch(coroutineContext) { // see how it looks from another coroutine
            expect(4)
            check(!d.isActive && !d.isCompleted)
            yield() // yield back to main
            expect(6)
            check(d.isActive && !d.isCompleted) // implicitly started by main's await
            yield() // yield to d
        }
        expect(3)
        check(!d.isActive && !d.isCompleted)
        yield() // yield to second child (lazy async is not computing yet)
        expect(5)
        check(!d.isActive && !d.isCompleted)
        check(d.await() == 42) // starts computing
        check(!d.isActive && d.isCompleted && !d.isCompletedExceptionally)
        finish(8)
    }

    @Test(expected = IOException::class)
    fun testSimpleException(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            finish(3)
            throw IOException()
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        d.await() // will throw IOException
    }

    @Test(expected = IOException::class)
    fun testLazyDeferAndYieldException(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(3)
            yield() // this has not effect, because parent coroutine is waiting
            finish(4)
            throw IOException()
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        d.await() // will throw IOException
    }

    @Test
    fun testCatchException(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(3)
            throw IOException()
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        try {
            d.await() // will throw IOException
        } catch (e: IOException) {
            check(!d.isActive && d.isCompleted && d.isCompletedExceptionally && !d.isCancelled)
            expect(4)
        }
        finish(5)
    }

    @Test
    fun testStart(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(4)
            42
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        check(d.start())
        check(d.isActive && !d.isCompleted)
        expect(3)
        check(!d.start())
        yield() // yield to started coroutine
        check(!d.isActive && d.isCompleted && !d.isCompletedExceptionally) // and it finishes
        expect(5)
        check(d.await() == 42) // await sees result
        finish(6)
    }

    @Test(expected = CancellationException::class)
    fun testCancelBeforeStart(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expectUnreached()
            42
        }
        expect(2)
        check(!d.isActive && !d.isCompleted)
        check(d.cancel())
        check(!d.isActive && d.isCompleted && d.isCompletedExceptionally && d.isCancelled)
        check(!d.cancel())
        check(!d.start())
        finish(3)
        check(d.await() == 42) // await shall throw CancellationException
        expectUnreached()
    }

    @Test(expected = CancellationException::class)
    fun testCancelWhileComputing(): Unit = runBlocking {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.LAZY) {
            expect(4)
            yield() // yield to main, that is going to cancel us
            expectUnreached()
            42
        }
        expect(2)
        check(!d.isActive && !d.isCompleted && !d.isCancelled)
        check(d.start())
        check(d.isActive && !d.isCompleted && !d.isCancelled)
        expect(3)
        yield() // yield to d
        expect(5)
        check(d.isActive && !d.isCompleted && !d.isCancelled)
        check(d.cancel())
        check(!d.isActive && !d.isCompletedExceptionally && d.isCancelled) // cancelling !
        check(!d.cancel())
        check(!d.isActive && !d.isCompletedExceptionally && d.isCancelled) // still cancelling
        finish(6)
        check(d.await() == 42) // await shall throw CancellationException
        expectUnreached()
    }
}