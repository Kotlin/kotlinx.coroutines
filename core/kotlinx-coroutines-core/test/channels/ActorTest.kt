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

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import org.junit.runner.*
import org.junit.runners.*
import java.io.*
import kotlin.coroutines.experimental.*

@RunWith(Parameterized::class)
class ActorTest(private val capacity: Int) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "Capacity: {0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(0, 1, Channel.UNLIMITED, Channel.CONFLATED).map { arrayOf<Any>(it) }
    }

    @Test
    fun testEmpty() = runBlocking {
        expect(1)
        val actor = actor<String>(coroutineContext, capacity) {
            expect(3)
        }
        actor as Job // type assertion
        assertThat(actor.isActive, IsEqual(true))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(2)
        yield() // to actor code
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(true))
        assertThat(actor.isClosedForSend, IsEqual(true))
        finish(4)
    }

    @Test
    fun testOne() = runBlocking {
        expect(1)
        val actor = actor<String>(coroutineContext, capacity) {
            expect(3)
            assertThat(receive(), IsEqual("OK"))
            expect(6)
        }
        actor as Job // type assertion
        assertThat(actor.isActive, IsEqual(true))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(2)
        yield() // to actor code
        assertThat(actor.isActive, IsEqual(true))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(4)
        // send message to actor
        actor.send("OK")
        expect(5)
        yield() // to actor code
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(true))
        assertThat(actor.isClosedForSend, IsEqual(true))
        finish(7)
    }

    @Test
    fun testCloseWithoutCause() = runTest {
        val actor = actor<Int>(coroutineContext, capacity) {
            val element = channel.receiveOrNull()
            expect(2)
            assertEquals(42, element)
            val next = channel.receiveOrNull()
            assertNull(next)
            expect(3)
        }

        expect(1)
        actor.send(42)
        yield()
        actor.close()
        yield()
        finish(4)
    }

    @Test
    fun testCloseWithCause() = runTest {
        val actor = actor<Int>(coroutineContext, capacity) {
            val element = channel.receiveOrNull()
            expect(2)
            require(element!! == 42)
            try {
                channel.receiveOrNull()
            } catch (e: IOException) {
                expect(3)
            }
        }

        expect(1)
        actor.send(42)
        yield()
        actor.close(IOException())
        yield()
        finish(4)
    }

    @Test
    fun testCancelEnclosingJob() = runTest {
        val job = async(coroutineContext) {
            actor<Int>(coroutineContext, capacity) {
                expect(1)
                channel.receiveOrNull()
                expectUnreached()
            }
        }

        yield()
        yield()

        expect(2)
        yield()
        job.cancel()

        try {
            job.await()
            expectUnreached()
        } catch (e: JobCancellationException) {
            assertTrue(e.message?.contains("Job was cancelled normally") ?: false)
        }

        finish(3)
    }

    @Test
    fun testThrowingActor() = runTest(unhandled = listOf({e -> e is IllegalArgumentException})) {
        val parent = Job()
        val actor = actor<Int>(context = coroutineContext, parent = parent) {
            channel.consumeEach {
                expect(1)
                throw IllegalArgumentException()
            }
        }

        actor.send(1)
        parent.cancel()
        parent.join()
        finish(2)
    }
}
