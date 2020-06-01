/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.sync.*
import kotlin.native.concurrent.*
import kotlin.test.*

class WorkerDispatcherTest : TestBase() {
    private val dispatcher = newSingleThreadContext("WorkerCoroutineDispatcherTest")
    private val mainThread = currentThread()

    @AfterTest
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testWithContext() = runTest {
        val atomic = AtomicInt(0) // can be captured & shared
        expect(1)
        val result = withContext(dispatcher) {
            expect(2)
            assertEquals(dispatcher.thread, currentThread())
            atomic.value = 42
            "OK"
        }
        assertEquals(mainThread, currentThread())
        assertEquals("OK", result)
        assertEquals(42, atomic.value)
        finish(3)
    }

    @Test
    fun testLaunchJoin() = runTest {
        val atomic = AtomicInt(0) // can be captured & shared
        expect(1)
        val job = launch(dispatcher) {
            assertEquals(dispatcher.thread, currentThread())
            atomic.value = 42
        }
        job.join()
        assertEquals(mainThread, currentThread())
        assertEquals(42, atomic.value)
        finish(2)
    }

    @Test
    fun testLaunchLazyJoin() = runTest {
        expect(1)
        val job = launch(dispatcher, start = CoroutineStart.LAZY) {
            expect(3)
            assertEquals(dispatcher.thread, currentThread())
        }
        expect(2)
        job.join() // lazy start here
        finish(4)
    }

    @Test
    fun testAsyncAwait() = runTest {
        val atomic = AtomicInt(0) // can be captured & shared
        expect(1)
        val deferred = async(dispatcher) {
            assertEquals(dispatcher.thread, currentThread())
            atomic.value = 42
            "OK"
        }
        val result = deferred.await()
        assertEquals(mainThread, currentThread())
        assertEquals("OK", result)
        assertEquals(42, atomic.value)
        finish(2)
    }

    @Test
    fun testAsyncLazyAwait() = runTest {
        expect(1)
        val deferred = async(dispatcher, start = CoroutineStart.LAZY) {
            expect(3)
            assertEquals(dispatcher.thread, currentThread())
            "OK"
        }
        expect(2)
        val result = deferred.await() // lazy start here
        assertEquals("OK", result)
        finish(4)
    }

    @Test
    fun testProduceConsumeRendezvous() = checkProduceConsume(Channel.RENDEZVOUS)

    @Test
    fun testProduceConsumeUnlimited() = checkProduceConsume(Channel.UNLIMITED)

    @Test
    fun testProduceConsumeBuffered() = checkProduceConsume(10)

    private fun checkProduceConsume(capacity: Int) {
        runTest {
            val atomic = AtomicInt(0) // can be captured & shared
            expect(1)
            val channel = produce(dispatcher, capacity) {
                assertEquals(dispatcher.thread, currentThread())
                atomic.value = 42
                expect(2)
                send(Data("A"))
                send(Data("B"))
            }
            val result1 = channel.receive()
            expect(3)
            assertEquals(mainThread, currentThread())
            assertEquals("A", result1.s)
            assertTrue(result1.isFrozen)
            assertEquals(42, atomic.value)
            val result2 = channel.receive()
            assertEquals("B", result2.s)
            assertEquals(null, channel.receiveOrNull()) // must try to receive the last one to dispose memory
            finish(4)
        }
    }

    @Test
    fun testChannelIterator() = runTest {
        expect(1)
        val channel = RendezvousChannel<Int>(null)
        launch(dispatcher) {
            channel.send(1)
            channel.send(2)
            channel.close()
        }
        var expected = 1
        for (x in channel) {
            assertEquals(expected++, x)
        }
        finish(2)
    }

    @Test
    fun testArrayBroadcast() = runTest {
        expect(1)
        val broadcast = BroadcastChannel<Data>(10)
        val sub = broadcast.openSubscription()
        launch(dispatcher) {
            assertEquals(dispatcher.thread, currentThread())
            expect(2)
            broadcast.send(Data("A"))
            broadcast.send(Data("B"))
        }
        val result1 = sub.receive()
        expect(3)
        assertEquals(mainThread, currentThread())
        assertEquals("A", result1.s)
        assertTrue(result1.isFrozen)
        val result2 = sub.receive()
        assertEquals("B", result2.s)
        sub.cancel()
        broadcast.close() // dispose memory
        finish(4)
    }

    @Test
    fun testConflatedBroadcast() = runTest {
        expect(1)
        val latch = Channel<Unit>()
        val broadcast = ConflatedBroadcastChannel<Data>()
        val sub = broadcast.openSubscription()
        launch(dispatcher) {
            assertEquals(dispatcher.thread, currentThread())
            expect(2)
            broadcast.send(Data("A"))
            latch.receive()
            expect(4)
            broadcast.send(Data("B"))
        }
        val result1 = sub.receive()
        expect(3)
        assertEquals(mainThread, currentThread())
        assertEquals("A", result1.s)
        assertTrue(result1.isFrozen)
        latch.send(Unit)
        val result2 = sub.receive()
        assertEquals("B", result2.s)
        sub.cancel()
        broadcast.close() // dispose memory
        latch.close() // dispose memory
        finish(5)
    }

    @Test
    fun testFlowOn() = runTest {
        expect(1)
        val flow = flow {
            expect(3)
            assertEquals(dispatcher.thread, currentThread())
            emit(Data("A"))
            emit(Data("B"))
        }.flowOn(dispatcher)
        expect(2)
        val result = flow.toList()
        assertEquals(listOf(Data("A"), Data("B")), result)
        assertTrue(result.all { it.isFrozen })
        finish(4)
    }

    @Test
    fun testWithContextDelay() = runTest {
        expect(1)
        withContext(dispatcher) {
            expect(2)
            delay(10)
            assertEquals(dispatcher.thread, currentThread())
            expect(3)
        }
        finish(4)
    }

    @Test
    fun testWithTimeoutAroundWithContextNoTimeout() = runTest {
        expect(1)
        withTimeout(1000) {
            withContext(dispatcher) {
                expect(2)
            }
        }
        finish(3)
    }

    @Test
    fun testWithTimeoutAroundWithContextTimedOut() = runTest {
        expect(1)
        assertFailsWith<TimeoutCancellationException> {
            withTimeout(100) {
                withContext(dispatcher) {
                    expect(2)
                    delay(1000)
                }
            }
        }
        finish(3)
    }

    @Test // Can sometimes hang tho
    fun testMutexStress() = runTest {
        expect(1)
        val mutex = Mutex()
        val atomic = AtomicInt(0)
        val n = 100
        val k = 239 // mutliplier
        val job = launch(dispatcher) {
            repeat(n) {
                mutex.withLock {
                    atomic.value = atomic.value + 1 // unsafe mutation but under mutex
                }
            }
        }
        // concurrently mutate
        repeat(n) {
            mutex.withLock {
                atomic.value = atomic.value + k
            }
        }
        // join job
        job.join()
        assertEquals((k + 1) * n, atomic.value)
        finish(2)
    }

    @Test
    fun testSemaphoreStress() = runTest {
        expect(1)
        val semaphore = Semaphore(1)
        val atomic = AtomicInt(0)
        val n = 100
        val k = 239 // mutliplier
        val job = launch(dispatcher) {
            repeat(n) {
                semaphore.withPermit {
                    atomic.value = atomic.value + 1 // unsafe mutation but under mutex
                }
            }
        }
        // concurrently mutate
        repeat(n) {
            semaphore.withPermit {
                atomic.value = atomic.value + k
            }
        }
        // join job
        job.join()
        assertEquals((k + 1) * n, atomic.value)
        finish(2)
    }

    @Test
    fun testBroadcastAsFlow() = runTest {
        expect(1)
        withContext(dispatcher) {
            expect(2)
            broadcast {
                expect(3)
                send("OK")
            }.asFlow().collect {
                expect(4)
                assertEquals("OK", it)
            }
            expect(5)
        }
        finish(6)
    }

    @Test
    fun testAwaitAll() = runTest {
        expect(1)
        val d1 = async(dispatcher) {
            "A"
        }
        val d2 = async(dispatcher) {
            "B"
        }
        assertEquals("AB", awaitAll(d1, d2).joinToString(""))
        finish(2)
    }

    @Test
    fun testEnsureNeverFrozenWithContext() = runTest {
        expect(1)
        val x = Data("OK")
        x.ensureNeverFrozen()
        assertFailsWith<FreezingException> {
            val s = withContext(dispatcher) { x.s }
            println(s) // does not actually execute
        }
        finish(2)
    }

    private data class Data(val s: String)
}
