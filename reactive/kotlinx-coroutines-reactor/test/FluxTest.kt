package kotlinx.coroutines.reactor

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import kotlin.test.*

class FluxTest : TestBase() {
    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val flux = flux(currentDispatcher()) {
            expect(4)
            send("OK")
        }
        expect(2)
        flux.subscribe { value ->
            expect(5)
            assertEquals("OK", value)
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val flux = flux<String>(currentDispatcher()) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        flux.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertIs<RuntimeException>(error)
            assertEquals("OK", error.message)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val flux = flux<String>(currentDispatcher()) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        val sub = flux.subscribe({
            expectUnreached()
        }, {
            expectUnreached()
        })
        expect(3)
        yield() // to started coroutine
        expect(5)
        sub.dispose() // will cancel coroutine
        yield()
        finish(6)
    }

    @Test
    fun testNotifyOnceOnCancellation() = runTest {
        expect(1)
        val observable =
            flux(currentDispatcher()) {
                expect(5)
                send("OK")
                try {
                    delay(Long.MAX_VALUE)
                } catch (e: CancellationException) {
                    expect(11)
                }
            }
            .doOnNext {
                expect(6)
                assertEquals("OK", it)
            }
            .doOnCancel {
                expect(10) // notified once!
            }
        expect(2)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(3)
            observable.collect {
                expect(8)
                assertEquals("OK", it)
            }
        }
        expect(4)
        yield() // to observable code
        expect(7)
        yield() // to consuming coroutines
        expect(9)
        job.cancel()
        job.join()
        finish(12)
    }

    @Test
    fun testFailingConsumer() = runTest {
        val pub = flux(currentDispatcher()) {
            repeat(3) {
                expect(it + 1) // expect(1), expect(2) *should* be invoked
                send(it)
            }
        }
        try {
            pub.collect {
                throw TestException()
            }
        } catch (e: TestException) {
            finish(3)
        }
    }

    @Test
    fun testIllegalArgumentException() {
        assertFailsWith<IllegalArgumentException> { flux<Int>(Job()) { } }
    }

    @Test
    fun testLeakedException() = runBlocking {
        // Test exception is not reported to global handler
        val flow = flux<Unit> { throw TestException() }.asFlow()
        repeat(2000) {
            combine(flow, flow) { _, _ -> Unit }
                .catch {}
                .collect { }
        }
    }

    /** Tests that `trySend` doesn't throw in `flux`. */
    @Test
    fun testTrySendNotThrowing() = runTest {
        var producerScope: ProducerScope<Int>? = null
        expect(1)
        val flux = flux<Int>(Dispatchers.Unconfined) {
            producerScope = this
            expect(3)
            delay(Long.MAX_VALUE)
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            flux.awaitFirstOrNull()
            expectUnreached()
        }
        job.cancel()
        expect(4)
        val result = producerScope!!.trySend(1)
        assertTrue(result.isFailure)
        finish(5)
    }

    /** Tests that all methods on `flux` fail without closing the channel when attempting to emit `null`. */
    @Test
    fun testEmittingNull() = runTest {
        val flux = flux {
            assertFailsWith<NullPointerException> { send(null) }
            assertFailsWith<NullPointerException> { trySend(null) }
            send("OK")
        }
        assertEquals("OK", flux.awaitFirstOrNull())
    }
}
