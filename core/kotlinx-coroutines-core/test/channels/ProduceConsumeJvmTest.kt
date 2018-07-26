/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Assert.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.experimental.*

@RunWith(Parameterized::class)
class ProduceConsumeJvmTest(
    private val capacity: Int,
    private val number: Int
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "capacity={0}, number={1}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            listOf(0, 1, 10, 1000, Channel.UNLIMITED).flatMap { capacity ->
                listOf(1, 10, 1000).map { number ->
                    arrayOf<Any>(capacity, number)
                }
            }
    }

    @Test
    fun testProducer() = runTest {
        var sentAll = false
        val producer = produce(coroutineContext, capacity = capacity) {
            for (i in 1..number) {
                send(i)
            }
            sentAll = true
        }
        var consumed = 0
        for (x in producer) {
            consumed++
        }
        assertTrue(sentAll)
        assertEquals(number, consumed)
    }

    @Test
    fun testActor() = runTest {
        val received = CompletableDeferred<Int>()
        val actor = actor<Int>(coroutineContext, capacity = capacity) {
            var n = 0
            for(i in channel) {
                n++
            }
            received.complete(n)
        }
        for(i in 1..number) {
            actor.send(i)
        }
        actor.close()
        assertEquals(number, received.await())
    }
}
