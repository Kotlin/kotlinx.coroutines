/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.util.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class MonoActorTest : TestBase() {

    private class DecomposingActor(ctx: CoroutineContext) : MonoActor<Int>(ctx) {

        private val workers: List<MonoActor<Int>>
        var result: Int = 0

        init {
            workers = MutableList(2) { _ ->
                actor<Int>(ctx, parent = this) { i ->
                    if (i == 239) throw AssertionError()
                    result += i
                }
            }
        }

        override suspend fun receive(message: Int) {
            if (message == 314) {
                throw AssertionError()
            }
            workers[Random().nextInt(2)].send(message)
        }
    }

    @Test
    fun testTransparentDecomposition() = runTest {
        val actor = DecomposingActor(coroutineContext)

        for (i in 1..100) {
            actor.send(i)
        }

        actor.close()
        actor.join()
        assertEquals(50 * 101, actor.result)
    }

    @Test
    fun testEagerChildActorFailure() = runTest(unhandled = unhandledFailures(3)) {
        val actor = DecomposingActor(coroutineContext.minusKey(Job))
        actor.send(239)
        actor.join()
    }

    @Test
    fun testChildActorFailure() = runTest(unhandled = unhandledFailures(3)) {
        val actor = DecomposingActor(coroutineContext.minusKey(Job))

        for (i in 1..100) {
            actor.send(i)
        }

        actor.send(239)
        actor.join()
        assertEquals(50 * 101, actor.result)
    }

    @Test
    fun testEagerParentActorFailure() = runTest(unhandled = unhandledFailures(2)) {
        val actor = DecomposingActor(coroutineContext.minusKey(Job))
        actor.send(314)
        actor.join()
    }

    @Test
    fun testParentActorFailure() = runTest(unhandled = unhandledFailures(2)) {
        val actor = DecomposingActor(coroutineContext.minusKey(Job))
        for (i in 1..100) {
            actor.send(i)
        }

        actor.send(314)
        actor.join()
        assertEquals(50 * 101, actor.result)
    }

    private fun unhandledFailures(count: Int): List<(Throwable) -> Boolean> {
        return MutableList(count) { { e: Throwable -> e is AssertionError } }
    }
}
