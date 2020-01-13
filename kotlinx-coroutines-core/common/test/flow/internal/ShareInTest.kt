/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.sync.*
import kotlin.test.*

class ShareInTest : TestBase() {

    @Test
    fun oneConsumer_completesSource() = runTest {

        var startInvocations = 0
        var completeInvocations = 0

        val flow = flowOf(1, 2, 3, 4, 5)
            .onStart { startInvocations++ }
            .onCompletion { completeInvocations++ }
            .shareIn(this)

        val one = flow.toList()

        assertEquals(listOf(1, 2, 3, 4, 5), one)

        assertEquals(1, startInvocations)
        assertEquals(1, completeInvocations)

    }

    @Test
    fun sequentialConsumers_completeSourceEachTime() = runTest {

        var startInvocations = 0
        var completeInvocations = 0

        val flow = flowOf(1, 2, 3, 4, 5)
            .onStart { startInvocations++ }
            .onCompletion { completeInvocations++ }
            .shareIn(this)

        val one = flow.toList()
        val two = flow.toList()

        assertEquals(listOf(1, 2, 3, 4, 5), one)
        assertEquals(listOf(1, 2, 3, 4, 5), two)

        assertEquals(2, startInvocations)
        assertEquals(2, completeInvocations)

    }

    @Test
    fun concurrentConsumers_shareOneSource() = runTest {

        var startInvocations = 0
        var completeInvocations = 0

        val lock = Channel<Unit>()

        val flow = flowOf(1, 2, 3, 4, 5)
            .onStart { startInvocations++ }
            .onCompletion { completeInvocations++ }
            .shareIn(this)

        val one = async {
            flow.onEach {
                lock.receive()
                lock.send(Unit)
            }
                .toList()
        }

        val two = async {
            flow.onEach {
                lock.send(Unit)
                lock.receive()
            }
                .toList()
        }

        assertEquals(listOf(1, 2, 3, 4, 5), one.await())
        assertEquals(listOf(1, 2, 3, 4, 5), two.await())

        assertEquals(1, startInvocations)
        assertEquals(1, completeInvocations)
    }

    @Test
    fun lateConsumer_onlyGetsNewValues() = runTest {

        val lock = BroadcastChannel<Unit>(1)

        val sharedLock = lock.openSubscription()
        val oneLock = lock.openSubscription()

        val flow = flowOf(1, 2, 3, 4, 5)
            .onEach { sharedLock.receive() }
            .shareIn(this)

        val one = async {
            flow.onEach { oneLock.receive() }
                .toList()
        }

        lock.send(Unit) // emit(1)
        lock.send(Unit) // emit(2)

        val two = async {

            lock.send(Unit) // emit(3) after this coroutine has started

            flow.onEach {
                lock.send(Unit)
            }
                .toList()
        }

        assertEquals(listOf(1, 2, 3, 4, 5), one.await())
        assertEquals(listOf(3, 4, 5), two.await())
    }

    @Test
    fun cache_replaysForLateConsumers() = runTest {

        val sourceLock = Mutex(true)
        val collectorLock = Mutex(true)

        val flow = flowOf(1, 2, 3, 4, 5)
            .onEach { if (it == 4) sourceLock.withLock { } } // wait for second consumer to begin before continuing
            .shareIn(this, 2)

        val one = async {
            flow.onEach { if (it == 2) collectorLock.unlock() }
                .toList()
        }

        val two = async {

            collectorLock.withLock {
                flow.onEach { if (it == 3) sourceLock.unlock() }
                    .toList()
            }
        }

        assertEquals(listOf(1, 2, 3, 4, 5), one.await())
        assertEquals(listOf(2, 3, 4, 5), two.await())

    }

    @Test
    fun refCountOfZero_resetsCache() = runTest {

        val flow = flowOf(1, 2, 3, 4, 5)
            .shareIn(this, 2)

        val collect1 = flow.toList()

        assertEquals(listOf(1, 2, 3, 4, 5), collect1)

        val collect2 = flow.toList()

        assertEquals(listOf(1, 2, 3, 4, 5), collect2)

    }


    @Test
    fun refCountOfZero_cancelsSourceFlow() = runTest {

        val sourceBroadcastChannel = BroadcastChannel<Int>(1)

        val sourceFlow = sourceBroadcastChannel.asFlow()

        val sharedFlow = sourceFlow.shareIn(this)

        /*
        first sharing session begins
         */
        val listOneDeferred = async(start = CoroutineStart.UNDISPATCHED) {
            expect(1)
            sharedFlow
                .take(1)
                .toList()
        }

        expect(2)
        yield() // ensure that the "listOneDeferred" async has begun collection before sending
        expect(3)

        sourceBroadcastChannel.send(1)

        assertEquals(listOf(1), listOneDeferred.await())

        val newReceiveChannel = sourceBroadcastChannel.openSubscription()

        val sendList = listOf(2, 3, 4, 5)

        /*
        second sharing session begins
         */
        val listTwoDeferred = async(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            sharedFlow.take(sendList.size)
                .toList()
        }

        val listThreeDeferred = async {
            newReceiveChannel.consumeAsFlow()
                .shareIn(this)
                .take(sendList.size)
                .toList()
        }

        assertEquals(false, sourceBroadcastChannel.isClosedForSend)

        expect(5)
        yield() // ensure that the "listTwoDeferred" async has begun collection before sending
        expect(6)

        sendList.forEach {
            sourceBroadcastChannel.send(it)
        }

        expect(7)

        // Reaching here means that the sends aren't suspending,
        // which means that the internal channel created during the first sharing session was properly closed,
        // else there would be deadlock.
        assertEquals(sendList, listTwoDeferred.await())
        assertEquals(sendList, listThreeDeferred.await())

        assertEquals(false, sourceBroadcastChannel.isClosedForSend)

        finish(8)
    }

}
