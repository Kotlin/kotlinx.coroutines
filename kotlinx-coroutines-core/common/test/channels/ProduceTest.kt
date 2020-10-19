/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*

class ProduceTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        val c = produce {
            expect(2)
            send(1)
            expect(3)
            send(2)
            expect(6)
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        check(c.receive() == 2)
        expect(5)
        check(c.receiveOrNull() == null)
        finish(7)
    }

    @Test
    fun testCancelWithoutCause() = runTest {
        val c = produce(NonCancellable) {
            expect(2)
            send(1)
            expect(3)
            try {
                send(2) // will get cancelled
                expectUnreached()
            } catch (e: Throwable) {
                expect(7)
                check(e is CancellationException)
                throw e
            }
            expectUnreached()
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        c.cancel()
        expect(5)
        assertFailsWith<CancellationException> { c.receiveOrNull() }
        expect(6)
        yield() // to produce
        finish(8)
    }

    @Test
    fun testCancelWithCause() = runTest {
        val c = produce(NonCancellable) {
            expect(2)
            send(1)
            expect(3)
            try {
                send(2) // will get cancelled
                expectUnreached()
            } catch (e: Throwable) {
                expect(6)
                check(e is TestCancellationException)
                throw e
            }
            expectUnreached()
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        c.cancel(TestCancellationException())
        try {
            assertNull(c.receiveOrNull())
            expectUnreached()
        } catch (e: TestCancellationException) {
            expect(5)
        }
        yield() // to produce
        finish(7)
    }

    @Test
    fun testCancelOnCompletionUnconfined() = runTest {
        cancelOnCompletion(Dispatchers.Unconfined)
    }

    @Test
    fun testCancelOnCompletion() = runTest {
        cancelOnCompletion(coroutineContext)
    }

    @Test
    fun testAwaitConsumerCancellation() = runTest {
        val parent = Job()
        val channel = produce<Int>(parent) {
            expect(2)
            awaitClose { expect(4) }
        }
        expect(1)
        yield()
        expect(3)
        channel.cancel()
        parent.complete()
        parent.join()
        finish(5)
    }

    @Test
    fun testAwaitProducerCancellation() = runTest {
        val parent = Job()
        produce<Int>(parent) {
            expect(2)
            launch {
                expect(3)
                this@produce.cancel()
            }
            awaitClose { expect(4) }
        }
        expect(1)
        parent.complete()
        parent.join()
        finish(5)
    }

    @Test
    fun testAwaitParentCancellation() = runTest {
        val parent = Job()
        produce<Int>(parent) {
            expect(2)
            awaitClose { expect(4) }
        }
        expect(1)
        yield()
        expect(3)
        parent.cancelAndJoin()
        finish(5)
    }

    @Test
    fun testAwaitIllegalState() = runTest {
        val channel = produce<Int> { }
        assertFailsWith<IllegalStateException> { (channel as ProducerScope<*>).awaitClose() }
        callbackFlow<Unit> {
            expect(1)
            launch {
                expect(2)
                assertFailsWith<IllegalStateException> {
                    awaitClose { expectUnreached() }
                    expectUnreached()
                }
            }
            close()
        }.collect()
        finish(3)
    }

    private suspend fun cancelOnCompletion(coroutineContext: CoroutineContext) = CoroutineScope(coroutineContext).apply {
        val source = Channel<Int>()
        expect(1)
        val produced = produce<Int>(coroutineContext, onCompletion = { source.cancelConsumed(it) }) {
            expect(2)
            source.receive()
        }

        yield()
        expect(3)
        produced.cancel()
        try {
            source.receive()
        } catch (e: CancellationException) {
            finish(4)
        }
    }
}
