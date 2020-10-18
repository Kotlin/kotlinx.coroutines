/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import org.reactivestreams.*
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
    fun testNumbers() = runBlocking<Unit> {
        val n = 100 * stressTestMultiplier
        val pub = publish(ctx(coroutineContext)) {
            for (i in 1..n) {
                send(i)
                if (delay) delay(1)
            }
        }
        assertEquals(1, pub.awaitFirst())
        assertEquals(1, pub.awaitFirstOrDefault(0))
        assertEquals(1, pub.awaitFirstOrNull())
        assertEquals(1, pub.awaitFirstOrElse { 0 })
        assertEquals(n, pub.awaitLast())
        assertFailsWith<IllegalArgumentException> { pub.awaitSingle() }
        assertFailsWith<IllegalArgumentException> { pub.awaitSingleOrDefault(0) }
        assertFailsWith<IllegalArgumentException> { pub.awaitSingleOrNull() }
        assertFailsWith<IllegalArgumentException> { pub.awaitSingleOrElse { 0 } }
        checkNumbers(n, pub)
        val channel = pub.openSubscription()
        checkNumbers(n, channel.asPublisher(ctx(coroutineContext)))
        channel.cancel()
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
    fun testEmptySingle() = runTest(unhandled = listOf({e -> e is NoSuchElementException})) {
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

    private suspend fun checkNumbers(n: Int, pub: Publisher<Int>) {
        var last = 0
        pub.collect {
            assertEquals(++last, it)
        }
        assertEquals(n, last)
    }

}