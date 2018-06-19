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

import kotlin.coroutines.experimental.coroutineContext
import kotlin.test.*

class AwaitTest : TestBase() {

    @Test
    fun testAwaitAll() = runTest {
        expect(1)
        val d = async(coroutineContext) {
            expect(3)
            "OK"
        }

        val d2 = async(coroutineContext) {
            yield()
            expect(4)
            1L
        }

        expect(2)
        require(d2.isActive && !d2.isCompleted)

        assertEquals(listOf("OK", 1L), awaitAll(d, d2))
        expect(5)

        require(d.isCompleted && d2.isCompleted)
        require(!d.isCancelled && !d2.isCancelled)
        finish(6)
    }

    @Test
    fun testAwaitAllLazy() = runTest {
        expect(1)
        val d = async(
            coroutineContext,
            start = CoroutineStart.LAZY
        ) { expect(2); 1 }
        val d2 = async(
            coroutineContext,
            start = CoroutineStart.LAZY
        ) { expect(3); 2 }
        assertEquals(listOf(1, 2), awaitAll(d, d2))
        finish(4)
    }

    @Test
    fun testAwaitAllTyped() = runTest {
        val d1 = async(coroutineContext) { 1L }
        val d2 = async(coroutineContext) { "" }
        val d3 = async(coroutineContext) { }

        assertEquals(listOf(1L, ""), listOf(d1, d2).awaitAll())
        assertEquals(listOf(1L, Unit), listOf(d1, d3).awaitAll())
        assertEquals(listOf("", Unit), listOf(d2, d3).awaitAll())
    }

    @Test
    fun testAwaitAllExceptionally() = runTest {
        expect(1)
        val d = async(coroutineContext) {
            expect(3)
            "OK"
        }

        val d2 = async(coroutineContext) {
            yield()
            throw TestException()
        }

        val d3 = async(coroutineContext) {
            expect(4)
            delay(Long.MAX_VALUE)
            1
        }

        expect(2)
        try {
            awaitAll(d, d2, d3)
        } catch (e: TestException) {
            expect(5)
        }

        yield()
        require(d.isCompleted && d2.isCompletedExceptionally && d3.isActive)
        d3.cancel()
        finish(6)
    }

    @Test
    fun testAwaitAllMultipleExceptions() = runTest {
        val d = async(coroutineContext) {
            expect(2)
            throw TestException()
        }

        val d2 = async(coroutineContext) {
            yield()
            throw TestException()
        }

        val d3 = async(coroutineContext) {
            yield()
        }

        expect(1)
        try {
            awaitAll(d, d2, d3)
        } catch (e: TestException) {
            expect(3)
        }

        finish(4)
    }

    @Test
    fun testAwaitAllCancellation() = runTest {
        val outer = async(coroutineContext) {

            expect(1)
            val inner = async(coroutineContext) {
                expect(4)
                delay(Long.MAX_VALUE)
            }

            expect(2)
            awaitAll(inner)
            expectUnreached()
        }

        yield()
        expect(3)
        yield()
        require(outer.isActive)
        outer.cancel()
        require(outer.isCancelled)
        finish(5)
    }

    @Test
    fun testAwaitAllPartiallyCompleted() = runTest {
        val d1 = async(coroutineContext) { expect(1); 1 }
        d1.await()
        val d2 = async(coroutineContext) { expect(3); 2 }
        expect(2)
        assertEquals(listOf(1, 2), awaitAll(d1, d2))
        require(d1.isCompleted && d2.isCompleted)
        finish(4)
    }

    @Test
    fun testAwaitAllPartiallyCompletedExceptionally() = runTest {
        val d1 = async(coroutineContext) {
            expect(1)
            throw TestException()
        }

        yield()

        // This job is called after exception propagation
        val d2 = async(coroutineContext) { expect(4) }

        expect(2)
        try {
            awaitAll(d1, d2)
            expectUnreached()
        } catch (e: TestException) {
            expect(3)
        }

        require(d2.isActive)
        d2.await()
        require(d1.isCompleted && d2.isCompleted)
        finish(5)
    }

    @Test
    fun testAwaitAllFullyCompleted() = runTest {
        val d1 = CompletableDeferred(Unit)
        val d2 = CompletableDeferred(Unit)
        val job = async(coroutineContext) { expect(3) }
        expect(1)
        awaitAll(d1, d2)
        expect(2)
        job.await()
        finish(4)
    }

    @Test
    fun testAwaitOnSet() = runTest {
        val d1 = CompletableDeferred(Unit)
        val d2 = CompletableDeferred(Unit)
        val job = async(coroutineContext) { expect(2) }
        expect(1)
        listOf(d1, d2, job).awaitAll()
        finish(3)
    }

    @Test
    fun testAwaitAllFullyCompletedExceptionally() = runTest {
        val d1 = CompletableDeferred<Unit>(parent = null)
            .apply { completeExceptionally(TestException()) }
        val d2 = CompletableDeferred<Unit>(parent = null)
            .apply { completeExceptionally(TestException()) }
        val job = async(coroutineContext) { expect(3) }
        expect(1)
        try {
            awaitAll(d1, d2)
        } catch (e: TestException) {
            expect(2)
        }

        job.await()
        finish(4)
    }

    @Test
    fun testAwaitAllSameJobMultipleTimes() = runTest {
        val d = async(coroutineContext) { "OK" }
        // Duplicates are allowed though kdoc doesn't guarantee that
        assertEquals(listOf("OK", "OK", "OK"), awaitAll(d, d, d))
    }

    @Test
    fun testAwaitAllSameThrowingJobMultipleTimes() = runTest {
        val d1 =
            async(coroutineContext) { throw TestException() }
        val d2 = async(coroutineContext) { } // do nothing

        try {
            expect(1)
            // Duplicates are allowed though kdoc doesn't guarantee that
            awaitAll(d1, d2, d1, d2)
            expectUnreached()
        } catch (e: TestException) {
            finish(2)
        }
    }

    @Test
    fun testAwaitAllEmpty() = runTest {
        expect(1)
        assertEquals(emptyList(), awaitAll<Unit>())
        assertEquals(emptyList(), emptyList<Deferred<Unit>>().awaitAll())
        finish(2)
    }

    // joinAll

    @Test
    fun testJoinAll() = runTest {
        val d1 = launch(coroutineContext) { expect(2) }
        val d2 = async(coroutineContext) {
            expect(3)
            "OK"
        }
        val d3 = launch(coroutineContext) { expect(4) }

        expect(1)
        joinAll(d1, d2, d3)
        finish(5)
    }

    @Test
    fun testJoinAllLazy() = runTest {
        expect(1)
        val d = async(
            coroutineContext,
            start = CoroutineStart.LAZY
        ) { expect(2) }
        val d2 = launch(
            coroutineContext,
            start = CoroutineStart.LAZY
        ) { expect(3) }
        joinAll(d, d2)
        finish(4)
    }

    @Test
    fun testJoinAllExceptionally() = runTest {
        val d1 = launch(coroutineContext) {
            expect(2)
        }
        val d2 = async(coroutineContext) {
            expect(3)
            throw TestException()
        }
        val d3 = async(coroutineContext) {
            expect(4)
        }

        expect(1)
        joinAll(d1, d2, d3)
        finish(5)
    }

    @Test
    fun testJoinAllCancellation() = runTest {
        val outer = launch(coroutineContext) {
            expect(2)
            val inner = launch(coroutineContext) {
                expect(3)
                delay(Long.MAX_VALUE)
            }

            joinAll(inner)
            expectUnreached()
        }

        expect(1)
        yield()
        require(outer.isActive)
        yield()
        outer.cancel()
        outer.join()
        finish(4)
    }

    @Test
    fun testJoinAllAlreadyCompleted() = runTest {
        val job = launch(coroutineContext) {
            expect(1)
        }

        job.join()
        expect(2)

        joinAll(job)
        finish(3)
    }

    @Test
    fun testJoinAllEmpty() = runTest {
        expect(1)
        joinAll()
        listOf<Job>().joinAll()
        finish(2)
    }

    @Test
    fun testJoinAllSameJob() = runTest {
        val job = launch(coroutineContext) { }
        joinAll(job, job, job)
    }

    @Test
    fun testJoinAllSameJobExceptionally() = runTest {
        val job =
            async(coroutineContext) { throw TestException() }
        joinAll(job, job, job)
    }

    private class TestException : Exception()
}
