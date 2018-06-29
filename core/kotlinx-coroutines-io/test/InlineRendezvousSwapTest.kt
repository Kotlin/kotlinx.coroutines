/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.io.internal.*
import org.junit.Ignore
import org.junit.Test
import kotlin.coroutines.experimental.*
import kotlin.test.*

@Ignore
class InlineRendezvousSwapTest : TestBase() {
    @Test
    fun smokeTest1() = runTest {
        val swap = InlineRendezvousSwap<String>()

        launch(coroutineContext) {
            assertEquals("1", swap.receive())
        }

        launch(coroutineContext) {
            swap.send("1")
        }
    }

    @Test
    fun smokeTest2() = runTest {
        val swap = InlineRendezvousSwap<String>()

        launch(coroutineContext) {
            swap.send("1")
        }

        launch(coroutineContext) {
            assertEquals("1", swap.receive())
        }
    }

    @Test
    fun testLoop1() = runTest {
        val swap = InlineRendezvousSwap<String>()
        val received = Channel<String>(1)

        launch(coroutineContext) {
            while (true) {
                val s = swap.receive()
                if (s.isEmpty()) break
                received.send(s)
            }
            received.close()
        }

        launch(coroutineContext) {
            for (i in 1..10) {
                swap.send(i.toString())
            }
            swap.send("")
        }

        assertEquals((1..10).map { it.toString() }, received.toList())
    }

    @Test
    @Ignore
    fun testLoop2() = runTest {
        val swap = InlineRendezvousSwap<String>()
        val received = Channel<String>(1)

        launch(coroutineContext) {
            while (true) {
                val s = swap.receive()
                if (s.isEmpty()) break
                received.send(s)
            }
            received.close()
        }

        launch(coroutineContext) {
            for (i in 1..10) {
                yield()
                swap.send(i.toString())
            }
            swap.send("")
        }

        assertEquals((1..10).map { it.toString() }, received.toList())
    }

    @Test
    fun testLoop3() = runTest {
        val swap = InlineRendezvousSwap<String>()
        val received = Channel<String>(1)

        launch(coroutineContext) {
            while (true) {
                yield()
                val s = swap.receive()
                if (s.isEmpty()) break
                received.send(s)
            }
            received.close()
        }

        launch(coroutineContext) {
            for (i in 1..10) {
                swap.send(i.toString())
            }
            swap.send("")
        }

        assertEquals((1..10).map { it.toString() }, received.toList())
    }

}