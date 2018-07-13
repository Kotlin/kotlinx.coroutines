/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*

class ActorLazyTest : TestBase() {
    @Test
    fun testEmptyStart() = runBlocking {
        expect(1)
        val actor = actor<String>(start = CoroutineStart.LAZY) {
            expect(5)
        }
        actor as Job // type assertion
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(2)
        yield() // to actor code --> nothing happens (not started!)
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(3)
        // start actor explicitly
        actor.start()
        expect(4)
        yield() // to started actor
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(true))
        assertThat(actor.isClosedForSend, IsEqual(true))
        finish(6)
    }

    @Test
    fun testOne() = runBlocking {
        expect(1)
        val actor = actor<String>(start = CoroutineStart.LAZY) {
            expect(4)
            assertThat(receive(), IsEqual("OK"))
            expect(5)
        }
        actor as Job // type assertion
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(2)
        yield() // to actor code --> nothing happens (not started!)
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(false))
        assertThat(actor.isClosedForSend, IsEqual(false))
        expect(3)
        // send message to actor --> should start it
        actor.send("OK")
        assertThat(actor.isActive, IsEqual(false))
        assertThat(actor.isCompleted, IsEqual(true))
        assertThat(actor.isClosedForSend, IsEqual(true))
        finish(6)
    }
}