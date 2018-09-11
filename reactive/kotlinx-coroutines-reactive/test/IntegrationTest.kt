/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.*
import org.hamcrest.MatcherAssert.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import org.reactivestreams.*
import kotlin.coroutines.experimental.*

@RunWith(Parameterized::class)
class IntegrationTest(
    private val ctx: Ctx,
    private val delay: Boolean
) : TestBase() {

    enum class Ctx {
        MAIN        { override fun invoke(context: CoroutineContext): CoroutineContext = context },
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
        val pub = CoroutineScope(ctx(coroutineContext)).publish<String> {
            if (delay) delay(1)
            // does not send anything
        }
        assertNSE { pub.awaitFirst() }
        assertThat(pub.awaitFirstOrDefault("OK"), IsEqual("OK"))
        assertThat(pub.awaitFirstOrNull(), IsNull())
        assertThat(pub.awaitFirstOrElse { "ELSE" }, IsEqual("ELSE"))
        assertNSE { pub.awaitLast() }
        assertNSE { pub.awaitSingle() }
        var cnt = 0
        pub.consumeEach { cnt++ }
        assertThat(cnt, IsEqual(0))
    }

    @Test
    fun testSingle() = runBlocking {
        val pub = publish(ctx(coroutineContext)) {
            if (delay) delay(1)
            send("OK")
        }
        assertThat(pub.awaitFirst(), IsEqual("OK"))
        assertThat(pub.awaitFirstOrDefault("!"), IsEqual("OK"))
        assertThat(pub.awaitFirstOrNull(), IsEqual("OK"))
        assertThat(pub.awaitFirstOrElse { "ELSE" }, IsEqual("OK"))
        assertThat(pub.awaitLast(), IsEqual("OK"))
        assertThat(pub.awaitSingle(), IsEqual("OK"))
        var cnt = 0
        pub.consumeEach {
            assertThat(it, IsEqual("OK"))
            cnt++
        }
        assertThat(cnt, IsEqual(1))
    }

    @Test
    fun testNumbers() = runBlocking<Unit> {
        val n = 100 * stressTestMultiplier
        val pub = CoroutineScope(ctx(coroutineContext)).publish {
            for (i in 1..n) {
                send(i)
                if (delay) delay(1)
            }
        }
        assertThat(pub.awaitFirst(), IsEqual(1))
        assertThat(pub.awaitFirstOrDefault(0), IsEqual(1))
        assertThat(pub.awaitLast(), IsEqual(n))
        assertThat(pub.awaitFirstOrNull(), IsEqual(1))
        assertThat(pub.awaitFirstOrElse { 0 }, IsEqual(1))
        assertIAE { pub.awaitSingle() }
        checkNumbers(n, pub)
        val channel = pub.openSubscription()
        checkNumbers(n, channel.asPublisher(ctx(coroutineContext)))
        channel.cancel()
    }

    @Test
    fun testCancelWithoutValue() = runTest {
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            publish<String>(coroutineContext) {
                yield()
                expectUnreached()
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
        pub.consumeEach {
            assertThat(it, IsEqual(++last))
        }
        assertThat(last, IsEqual(n))
    }

    private inline fun assertIAE(block: () -> Unit) {
        try {
            block()
            expectUnreached()
        } catch (e: Throwable) {
            assertThat(e, IsInstanceOf(IllegalArgumentException::class.java))
        }
    }

    private inline fun assertNSE(block: () -> Unit) {
        try {
            block()
            expectUnreached()
        } catch (e: Throwable) {
            assertThat(e, IsInstanceOf(NoSuchElementException::class.java))
        }
    }
}