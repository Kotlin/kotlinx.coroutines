/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import kotlinx.coroutines.experimental.*
import org.hamcrest.MatcherAssert.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.experimental.*

@RunWith(Parameterized::class)
class IntegrationTest(
    val ctx: Ctx,
    val delay: Boolean
) : TestBase() {

    enum class Ctx {
        MAIN        { override fun invoke(context: CoroutineContext): CoroutineContext = context },
        COMMON_POOL { override fun invoke(context: CoroutineContext): CoroutineContext = CommonPool },
        UNCONFINED  { override fun invoke(context: CoroutineContext): CoroutineContext = Unconfined };

        abstract operator fun invoke(context: CoroutineContext): CoroutineContext
    }

    companion object {
        @Parameterized.Parameters(name = "ctx={0}, delay={1}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = Ctx.values().flatMap { ctx ->
            listOf(false, true).map { delay ->
                arrayOf<Any>(ctx, delay)
            }
        }
    }

    @Test
    fun testEmpty(): Unit = runBlocking {
        val observable = rxObservable<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            // does not send anything
        }
        assertNSE { observable.awaitFirst() }
        assertThat(observable.awaitFirstOrDefault("OK"), IsEqual("OK"))
        assertThat(observable.awaitFirstOrNull(), IsNull())
        assertThat(observable.awaitFirstOrElse { "ELSE" }, IsEqual("ELSE"))
        assertNSE { observable.awaitLast() }
        assertNSE { observable.awaitSingle() }
        var cnt = 0
        observable.consumeEach {
            cnt++
        }
        assertThat(cnt, IsEqual(0))
    }

    @Test
    fun testSingle() = runBlocking<Unit> {
        val observable = rxObservable<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            send("OK")
        }
        assertThat(observable.awaitFirst(), IsEqual("OK"))
        assertThat(observable.awaitFirstOrDefault("OK"), IsEqual("OK"))
        assertThat(observable.awaitFirstOrNull(), IsEqual("OK"))
        assertThat(observable.awaitFirstOrElse { "ELSE" }, IsEqual("OK"))
        assertThat(observable.awaitLast(), IsEqual("OK"))
        assertThat(observable.awaitSingle(), IsEqual("OK"))
        var cnt = 0
        observable.consumeEach {
            assertThat(it, IsEqual("OK"))
            cnt++
        }
        assertThat(cnt, IsEqual(1))
    }

    @Test
    fun testNumbers() = runBlocking<Unit> {
        val n = 100 * stressTestMultiplier
        val observable = rxObservable<Int>(ctx(coroutineContext)) {
            for (i in 1..n) {
                send(i)
                if (delay) delay(1)
            }
        }
        assertThat(observable.awaitFirst(), IsEqual(1))
        assertThat(observable.awaitFirstOrDefault(0), IsEqual(1))
        assertThat(observable.awaitFirstOrNull(), IsEqual(1))
        assertThat(observable.awaitFirstOrElse { 0 }, IsEqual(1))
        assertThat(observable.awaitLast(), IsEqual(n))
        assertIAE { observable.awaitSingle() }
        checkNumbers(n, observable)
        val channel = observable.openSubscription()
        checkNumbers(n, channel.asObservable(ctx(coroutineContext)))
        channel.cancel()
    }

    private suspend fun checkNumbers(n: Int, observable: Observable<Int>) {
        var last = 0
        observable.consumeEach {
            assertThat(it, IsEqual(++last))
        }
        assertThat(last, IsEqual(n))
    }


    inline fun assertIAE(block: () -> Unit) {
        try {
            block()
            expectUnreached()
        } catch (e: Throwable) {
            assertThat(e, IsInstanceOf(IllegalArgumentException::class.java))
        }
    }

    inline fun assertNSE(block: () -> Unit) {
        try {
            block()
            expectUnreached()
        } catch (e: Throwable) {
            assertThat(e, IsInstanceOf(NoSuchElementException::class.java))
        }
    }
}