/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.exceptions.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import org.reactivestreams.*
import java.lang.IllegalStateException
import java.lang.RuntimeException
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.test.*

@RunWith(Parameterized::class)
class IntegrationTest(
    private val ctx: Ctx,
    private val delay: Boolean
) : TestBase() {

    enum class Ctx {
        MAIN        { override fun invoke(context: CoroutineContext): CoroutineContext = context.minusKey(Job) },
        DEFAULT     { override fun invoke(context: CoroutineContext): CoroutineContext = Dispatchers.Default },
        UNCONFINED  { override fun invoke(context: CoroutineContext): CoroutineContext = Dispatchers.Unconfined };

        abstract operator fun invoke(context: CoroutineContext): CoroutineContext
    }

    companion object {
        @Parameterized.Parameters(name = "ctx={0}, delay={1}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = Ctx.values().flatMap { ctx ->
            listOf(false, true).map { delay ->
                arrayOf(ctx, delay)
            }
        }
    }

    @Test
    fun testEmpty(): Unit = runBlocking {
        val pub = publish<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            // does not send anything
        }
        assertFailsWith<NoSuchElementException> { pub.awaitFirst() }
        assertEquals("OK", pub.awaitFirstOrDefault("OK"))
        assertNull(pub.awaitFirstOrNull())
        assertEquals("ELSE", pub.awaitFirstOrElse { "ELSE" })
        assertFailsWith<NoSuchElementException> { pub.awaitLast() }
        assertFailsWith<NoSuchElementException> { pub.awaitSingle() }
        assertEquals("OK", pub.awaitSingleOrDefault("OK"))
        assertNull(pub.awaitSingleOrNull())
        assertEquals("ELSE", pub.awaitSingleOrElse { "ELSE" })
        var cnt = 0
        pub.collect { cnt++ }
        assertEquals(0, cnt)
    }

    @Test
    fun testSingle() = runBlocking {
        val pub = publish(ctx(coroutineContext)) {
            if (delay) delay(1)
            send("OK")
        }
        assertEquals("OK", pub.awaitFirst())
        assertEquals("OK", pub.awaitFirstOrDefault("!"))
        assertEquals("OK", pub.awaitFirstOrNull())
        assertEquals("OK", pub.awaitFirstOrElse { "ELSE" })
        assertEquals("OK", pub.awaitLast())
        assertEquals("OK", pub.awaitSingle())
        assertEquals("OK", pub.awaitSingleOrDefault("!"))
        assertEquals("OK", pub.awaitSingleOrNull())
        assertEquals("OK", pub.awaitSingleOrElse { "ELSE" })
        var cnt = 0
        pub.collect {
            assertEquals("OK", it)
            cnt++
        }
        assertEquals(1, cnt)
    }

    @Test
    fun testCancelWithoutValue() = runTest {
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            publish<String> {
                hang {}
            }.awaitFirst()
        }

        job.cancel()
        job.join()
    }

    @Test
    fun testEmptySingle() = runTest(unhandled = listOf { e -> e is NoSuchElementException }) {
        expect(1)
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            publish<String> {
                yield()
                expect(2)
                // Nothing to emit
            }.awaitFirst()
        }

        job.join()
        finish(3)
    }

    /**
     * Test that the continuation is not being resumed after it has already failed due to there having been too many
     * values passed.
     */
    @Test
    fun testNotCompletingFailedAwait() = runTest {
        try {
            expect(1)
            Publisher<Int> { sub ->
                sub.onSubscribe(object: Subscription {
                    override fun request(n: Long) {
                        expect(2)
                        sub.onNext(1)
                        sub.onNext(2)
                        expect(4)
                        sub.onComplete()
                    }

                    override fun cancel() {
                        expect(3)
                    }
                })
            }.awaitSingle()
        } catch (e: java.lang.IllegalArgumentException) {
            expect(5)
        }
        finish(6)
    }

    /**
     * Test the behavior of [awaitOne] on unconforming publishers.
     */
    @Test
    fun testAwaitOnNonconformingPublishers() = runTest {
        fun <T> publisher(block: Subscriber<in T>.(n: Long) -> Unit) =
            Publisher<T> { subscriber ->
                subscriber.onSubscribe(object: Subscription {
                    override fun request(n: Long) {
                        subscriber.block(n)
                    }

                    override fun cancel() {
                    }
                })
            }
        val dummyMessage = "dummy"
        val dummyThrowable = RuntimeException(dummyMessage)
        suspend fun <T> assertDetectsBadPublisher(
            operation: suspend Publisher<T>.() -> T,
            message: String,
            block: Subscriber<in T>.(n: Long) -> Unit,
        ) {
            assertCallsExceptionHandlerWith<IllegalStateException> {
                try {
                    publisher(block).operation()
                } catch (e: Throwable) {
                    if (e.message != dummyMessage)
                        throw e
                }
            }.let {
                assertTrue("Expected the message to contain '$message', got '${it.message}'") {
                    it.message?.contains(message) ?: false
                }
            }
        }

        // Rule 1.1 broken: the publisher produces more values than requested.
        assertDetectsBadPublisher<Int>({ awaitFirst() }, "provided more") {
            onNext(1)
            onNext(2)
            onComplete()
        }

        // Rule 1.7 broken: the publisher calls a method on a subscriber after reaching the terminal state.
        assertDetectsBadPublisher<Int>({ awaitSingle() }, "terminal state") {
            onNext(1)
            onError(dummyThrowable)
            onComplete()
        }
        assertDetectsBadPublisher<Int>({ awaitSingleOrDefault(2) }, "terminal state") {
            onComplete()
            onError(dummyThrowable)
        }
        assertDetectsBadPublisher<Int>({ awaitFirst() }, "terminal state") {
            onNext(0)
            onComplete()
            onComplete()
        }
        assertDetectsBadPublisher<Int>({ awaitFirstOrDefault(1) }, "terminal state") {
            onComplete()
            onNext(3)
        }
        assertDetectsBadPublisher<Int>({ awaitSingle() }, "terminal state") {
            onError(dummyThrowable)
            onNext(3)
        }

        // Rule 1.9 broken (the first signal to the subscriber was not 'onSubscribe')
        assertCallsExceptionHandlerWith<IllegalStateException> {
            try {
                Publisher<Int> { subscriber ->
                    subscriber.onNext(3)
                    subscriber.onComplete()
                }.awaitFirst()
            } catch (e: NoSuchElementException) {
                // intentionally blank
            }
        }.let { assertTrue(it.message?.contains("onSubscribe") ?: false) }
    }

    @Test
    fun testPublishWithTimeout() = runTest {
        val publisher = publish<Int> {
            expect(2)
            withTimeout(1) { delay(100) }
        }
        try {
            expect(1)
            publisher.awaitFirstOrNull()
        } catch (e: CancellationException) {
            expect(3)
        }
        finish(4)
    }

}

@OptIn(ExperimentalContracts::class)
internal suspend inline fun <reified E: Throwable> assertCallsExceptionHandlerWith(
    crossinline operation: suspend (CoroutineExceptionHandler) -> Unit): E {
    contract {
        callsInPlace(operation, InvocationKind.EXACTLY_ONCE)
    }
    val handler = CapturingHandler()
    return withContext(handler) {
        operation(handler)
        handler.getException().let {
            assertTrue(it is E, it.toString())
            it
        }
    }
}