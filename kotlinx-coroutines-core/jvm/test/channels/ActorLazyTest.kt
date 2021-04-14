/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class ActorLazyTest : TestBase() {
    @Test
    fun testEmptyStart() = runBlocking {
        expect(1)
        val actor = actor<String>(start = CoroutineStart.LAZY) {
            expect(5)
        }
        actor as Job // type assertion
        assertFalse(actor.isActive)
        assertFalse(actor.isCompleted)
        assertFalse(actor.isClosedForSend)
        expect(2)
        yield() // to actor code --> nothing happens (not started!)
        assertFalse(actor.isActive)
        assertFalse(actor.isCompleted)
        assertFalse(actor.isClosedForSend)
        expect(3)
        // start actor explicitly
        actor.start()
        expect(4)
        yield() // to started actor
        assertFalse(actor.isActive)
        assertTrue(actor.isCompleted)
        assertTrue(actor.isClosedForSend)
        finish(6)
    }

    @Test
    fun testOne() = runBlocking {
        expect(1)
        val actor = actor<String>(start = CoroutineStart.LAZY) {
            expect(4)
            assertEquals("OK", receive())
            expect(5)
        }
        actor as Job // type assertion
        assertFalse(actor.isActive)
        assertFalse(actor.isCompleted)
        assertFalse(actor.isClosedForSend)
        expect(2)
        yield() // to actor code --> nothing happens (not started!)
        assertFalse(actor.isActive)
        assertFalse(actor.isCompleted)
        assertFalse(actor.isClosedForSend)
        expect(3)
        // send message to actor --> should start it
        actor.send("OK")
        assertFalse(actor.isActive)
        assertTrue(actor.isCompleted)
        assertTrue(actor.isClosedForSend)
        finish(6)
    }

    @Test
    fun testCloseFreshActor() = runTest {
        val job = launch {
            expect(2)
            val actor = actor<Int>(start = CoroutineStart.LAZY) {
                expect(3)
                for (i in channel) { }
                expect(4)
            }

            actor.close()
        }

        expect(1)
        job.join()
        finish(5)
    }

    @Test
    fun testCancelledParent() = runTest({ it is CancellationException }) {
        cancel()
        expect(1)
        actor<Int>(start = CoroutineStart.LAZY) {
            expectUnreached()
        }
        finish(2)
    }
}
