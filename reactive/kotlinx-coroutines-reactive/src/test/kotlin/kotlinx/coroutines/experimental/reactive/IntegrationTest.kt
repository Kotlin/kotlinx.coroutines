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

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.*
import org.hamcrest.MatcherAssert.assertThat
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsInstanceOf
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext

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
        val pub = publish<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            // does not send anything
        }
        assertNSE { pub.awaitFirst() }
        assertThat(pub.awaitFirstOrDefault("OK"), IsEqual("OK"))
        assertNSE { pub.awaitLast() }
        assertNSE { pub.awaitSingle() }
        var cnt = 0
        pub.consumeEach { cnt++ }
        assertThat(cnt, IsEqual(0))
    }

    @Test
    fun testSingle() = runBlocking<Unit> {
        val pub = publish<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            send("OK")
        }
        assertThat(pub.awaitFirst(), IsEqual("OK"))
        assertThat(pub.awaitFirstOrDefault("!"), IsEqual("OK"))
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
        val pub = publish<Int>(ctx(coroutineContext)) {
            for (i in 1..n) {
                send(i)
                if (delay) delay(1)
            }
        }
        assertThat(pub.awaitFirst(), IsEqual(1))
        assertThat(pub.awaitFirstOrDefault(0), IsEqual(1))
        assertThat(pub.awaitLast(), IsEqual(n))
        assertIAE { pub.awaitSingle() }
        checkNumbers(n, pub)
        val channel = pub.openSubscription()
        checkNumbers(n, channel.asPublisher(ctx(coroutineContext)))
        channel.close()
    }

    private suspend fun checkNumbers(n: Int, pub: Publisher<Int>) {
        var last = 0
        pub.consumeEach {
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