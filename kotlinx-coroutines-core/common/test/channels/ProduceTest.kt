package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
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
        assertNull(c.receiveCatching().getOrNull())
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
        assertFailsWith<CancellationException> { c.receiveCatching().getOrThrow() }
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
            c.receive()
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
    fun testCancelWhenTheChannelIsClosed() = runTest {
        val channel = produce<Int> {
            send(1)
            close()
            expect(2)
            launch {
                expect(3)
                hang { expect(5) }
            }
        }

        expect(1)
        channel.receive()
        yield()
        expect(4)
        channel.cancel()
        (channel as Job).join()
        finish(6)
    }

    @Test
    fun testAwaitCloseOnlyAllowedOnce() = runTest {
        expect(1)
        val c = produce<Int> {
            try {
                awaitClose()
            } catch (e: CancellationException) {
                assertFailsWith<IllegalStateException> {
                    awaitClose()
                }
                finish(2)
                throw e
            }
        }
        yield() // let the `produce` procedure run
        c.cancel()
    }

    @Test
    fun testInvokeOnCloseWithAwaitClose() = runTest {
        expect(1)
        produce<Int> {
            invokeOnClose { }
            assertFailsWith<IllegalStateException> {
                awaitClose()
            }
            finish(2)
        }
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

    @Test
    fun testUncaughtExceptionsInProduce() = runTest(
        unhandled = listOf({ it is TestException })
    ) {
        val c = produce<Int> {
            launch(SupervisorJob()) {
                throw TestException()
            }.join()
            send(3)
        }
        assertEquals(3, c.receive())
    }

    @Test
    fun testCancellingProduceCoroutineButNotChannel() = runTest {
        val c = produce<Int>(Job(), capacity = Channel.UNLIMITED) {
            launch { throw TestException() }
            try {
                yield()
            } finally {
                repeat(10) { trySend(it) }
            }
        }
        repeat(10) { assertEquals(it, c.receive()) }
    }

    @Test
    fun testReceivingValuesAfterFailingTheCoroutine() = runTest {
        val produceJob = Job()
        val c = produce<Int>(produceJob, capacity = Channel.UNLIMITED) {
            repeat(5) { send(it) }
            throw TestException()
        }
        produceJob.join()
        assertTrue(produceJob.isCancelled)
        repeat(5) { assertEquals(it, c.receive()) }
        assertFailsWith<TestException> { c.receive() }
    }

    @Test
    fun testSilentKillerInProduce() = runTest {
        val parentScope = CoroutineScope(SupervisorJob() + Dispatchers.Default)
        val channel = parentScope.produce<Int>(capacity = Channel.UNLIMITED) {
            repeat(5) {
                send(it)
            }
            parentScope.cancel()
            // suspending after this point would fail, but sending succeeds
            send(-1)
        }
        launch {
            for (c in channel) {
                println(c) // 0, 1, 2, 3, 4, -1
            } // throws an exception after reaching -1
            fail("unreached")
        }
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
