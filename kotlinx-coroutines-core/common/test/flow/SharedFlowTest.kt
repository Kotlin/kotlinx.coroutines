/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.random.*
import kotlin.test.*

class SharedFlowTest : TestBase() {
    @Test
    fun testRendezvousSharedFlowBasic() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int?>(0)
        assertTrue(sh.replayCache.isEmpty())
        assertEquals(0, sh.subscriptionCount.value)
        sh.emit(1) // no suspend
        assertTrue(sh.replayCache.isEmpty())
        assertEquals(0, sh.subscriptionCount.value)
        expect(2)
        // one collector
        val job1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(3)
            sh.collect {
                when(it) {
                    4 -> expect(5)
                    6 -> expect(7)
                    10 -> expect(11)
                    13 -> expect(14)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(4)
        assertEquals(1, sh.subscriptionCount.value)
        sh.emit(4)
        assertTrue(sh.replayCache.isEmpty())
        expect(6)
        sh.emit(6)
        expect(8)
        // one more collector
        val job2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(9)
            sh.collect {
                when(it) {
                    10 -> expect(12)
                    13 -> expect(15)
                    17 -> expect(18)
                    null -> expect(20)
                    21 -> expect(22)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(10)
        assertEquals(2, sh.subscriptionCount.value)
        sh.emit(10) // to both collectors now!
        assertTrue(sh.replayCache.isEmpty())
        expect(13)
        sh.emit(13)
        expect(16)
        job1.cancel() // cancel the first collector
        yield()
        assertEquals(1, sh.subscriptionCount.value)
        expect(17)
        sh.emit(17) // only to second collector
        expect(19)
        sh.emit(null) // emit null to the second collector
        expect(21)
        sh.emit(21) // non-null again
        expect(23)
        job2.cancel() // cancel the second collector
        yield()
        assertEquals(0, sh.subscriptionCount.value)
        expect(24)
        sh.emit(24) // does not go anywhere
        assertEquals(0, sh.subscriptionCount.value)
        assertTrue(sh.replayCache.isEmpty())
        finish(25)
    }

    @Test
    fun testRendezvousSharedFlowResetBuffer() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int>(0)
        val barrier = Channel<Unit>(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            sh.collect {
                when (it) {
                    3 -> {
                        expect(4)
                        barrier.receive() // hold on before collecting next one
                    }
                    9 -> expect(11)
                    14 -> expect(15)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(3)
        sh.emit(3) // rendezvous
        expect(5)
        assertFalse(sh.tryEmit(5)) // collector is not ready now
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(6)
            sh.emit(6) // suspends, resumed by resetBuffer
            expect(9)
            sh.emit(9) // suspends again
        }
        expect(7)
        yield() // no wakeup -> all suspended
        expect(8)
        // now reset buffer --> emitter wakes up
        sh.resetBuffer()
        yield()
        expect(10)
        // now resume collector
        barrier.send(Unit)
        yield()
        // now collector is suspended
        expect(12)
        sh.resetBuffer() // nothing happens
        yield()
        expect(13)
        assertFalse(sh.tryEmit(13)) // rendezvous does not work this way
        expect(14)
        sh.emit(14)
        yield()
        expect(16)
        job.cancel()
        finish(17)
    }

    @Test
    fun testLastOneSharedFlowBasic() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int?>(1)
        assertTrue(sh.replayCache.isEmpty())
        assertEquals(0, sh.subscriptionCount.value)
        sh.emit(1) // no suspend
        assertEquals(listOf(1), sh.replayCache)
        assertEquals(0, sh.subscriptionCount.value)
        expect(2)
        sh.emit(2) // no suspend
        assertEquals(listOf(2), sh.replayCache)
        expect(3)
        // one collector
        val job1 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(4)
            sh.collect {
                when(it) {
                    2 -> expect(5) // got it immediately from replay cache
                    6 -> expect(8)
                    null -> expect(14)
                    17 -> expect(18)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(6)
        assertEquals(1, sh.subscriptionCount.value)
        sh.emit(6) // does not suspend, but buffers
        assertEquals(listOf(6), sh.replayCache)
        expect(7)
        yield()
        expect(9)
        // one more collector
        val job2 = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(10)
            sh.collect {
                when(it) {
                    6 -> expect(11) // from replay cache
                    null -> expect(15)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(12)
        assertEquals(2, sh.subscriptionCount.value)
        sh.emit(null)
        expect(13)
        assertEquals(listOf(null), sh.replayCache)
        yield()
        assertEquals(listOf(null), sh.replayCache)
        expect(16)
        job2.cancel()
        yield()
        assertEquals(1, sh.subscriptionCount.value)
        expect(17)
        sh.emit(17)
        assertEquals(listOf(17), sh.replayCache)
        yield()
        expect(19)
        job1.cancel()
        yield()
        assertEquals(0, sh.subscriptionCount.value)
        assertEquals(listOf(17), sh.replayCache)
        finish(20)
    }

    @Test
    fun testLastOneResetBuffer() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int>(1)
        assertEquals(listOf(), sh.replayCache)
        val barrier = Channel<Unit>(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            sh.collect {
                when (it) {
                    4 -> {
                        expect(5)
                        barrier.receive()
                    }
                    11 -> expect(12)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(3)
        assertTrue(sh.tryEmit(3)) // buffered
        assertEquals(listOf(3), sh.replayCache)
        sh.resetBuffer() // dropped
        assertEquals(listOf(), sh.replayCache)
        expect(4)
        assertTrue(sh.tryEmit(4)) // buffered
        assertEquals(listOf(4), sh.replayCache)
        yield() // to collector
        expect(6)
        assertTrue(sh.tryEmit(6)) // buffered
        assertEquals(listOf(6), sh.replayCache)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(7)
            sh.emit(7) // buffer full, suspended
            expect(10)
        }
        expect(8)
        assertEquals(listOf(6), sh.replayCache)
        sh.resetBuffer() // clear both buffered value & emitter
        assertEquals(listOf(), sh.replayCache)
        expect(9)
        yield() // emitter resumes
        expect(11)
        assertEquals(listOf(), sh.replayCache)
        assertTrue(sh.tryEmit(11)) // buffered now!
        assertEquals(listOf(11), sh.replayCache)
        barrier.send(Unit) // resume collector
        yield()
        expect(13)
        job.cancel()
        assertEquals(listOf(11), sh.replayCache)
        finish(14)
    }

    @Test
    fun testLastOneResetBufferInitialValue() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int?>(1, initialValue = null)
        assertEquals(listOf(null), sh.replayCache)
        val barrier = Channel<Unit>(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            var cnt = 0
            sh.collect {
                when (it) {
                    null -> {
                        when (cnt++) {
                            0 -> {
                                expect(3)
                                barrier.receive()
                            }
                            1 -> {
                                expect(6)
                                barrier.receive()
                            }
                            2 -> expect(15)
                        }
                    }
                    7 -> {
                        expect(10)
                        barrier.receive()
                    }
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(4)
        assertTrue(sh.tryEmit(4)) // buffered
        assertEquals(listOf(4), sh.replayCache)
        sh.resetBuffer() // reset
        assertEquals(listOf(null), sh.replayCache)
        barrier.send(Unit) // resume collector
        expect(5)
        yield() // must receive null again (no distinctUntilChanged is set)
        expect(7)
        assertTrue(sh.tryEmit(7)) // buffered
        assertEquals(listOf(7), sh.replayCache)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(8)
            sh.emit(8) // buffer full, suspended, resumes adding it to buffer
            expect(12)
            sh.emit(12) // buffer full gain, resumed by resetBuffer
            expect(13)
        }
        expect(9)
        barrier.send(Unit) // resume collector
        yield()
        expect(11)
        yield() // to emitter again
        assertEquals(listOf(8), sh.replayCache) // 8 is buffered, 12 waiting
        sh.resetBuffer() // reset it all now
        assertEquals(listOf(null), sh.replayCache)
        yield() // resume emitter
        expect(14)
        barrier.send(Unit)
        yield() // resume collector to get initial value again
        job.cancel()
        finish(16)
    }

    @Test
    fun test3BufferAnd2ReplayWithInitialValue() = runTest {
        expect(1)
        val sh = MutableSharedFlow(
            bufferCapacity = 3,
            replayCapacity = 2,
            initialValue = 0
        )
        assertEquals(listOf(0), sh.replayCache)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            var cnt = 0
            sh.collect {
                when (it) {
                    0 -> when (cnt++) {
                        0 -> expect(3)
                        1 -> expect(12)
                    }
                    1 -> expect(6)
                    2 -> expect(7)
                    3 -> expect(8)
                    14 -> expect(15)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(4)
        assertTrue(sh.tryEmit(1)) // buffered
        assertEquals(listOf(0, 1), sh.replayCache)
        assertTrue(sh.tryEmit(2)) // buffered
        assertEquals(listOf(1, 2), sh.replayCache)
        assertTrue(sh.tryEmit(3)) // buffered (buffer size is 3)
        assertEquals(listOf(2, 3), sh.replayCache)
        expect(5)
        yield() // to collector
        expect(9)
        assertEquals(listOf(2, 3), sh.replayCache)
        assertTrue(sh.tryEmit(4)) // can buffer now
        assertEquals(listOf(3, 4), sh.replayCache)
        assertTrue(sh.tryEmit(5)) // can buffer now
        assertEquals(listOf(4, 5), sh.replayCache)
        assertTrue(sh.tryEmit(0)) // can buffer one more, let it be equal to initial
        assertEquals(listOf(5, 0), sh.replayCache)
        expect(10)
        assertFalse(sh.tryEmit(10)) // cannot buffer anymore!
        sh.resetBuffer() // reset it all now!
        assertEquals(listOf(0), sh.replayCache) // last value only
        expect(11)
        yield() // resume collector, will get only initial value
        expect(13)
        sh.resetBuffer() // reset again
        assertEquals(listOf(0), sh.replayCache) // last value only
        yield() // collector gets nothing -- no change
        expect(14)
        assertTrue(sh.tryEmit(14))
        assertEquals(listOf(0, 14), sh.replayCache)
        yield() // gets it
        expect(16)
        job.cancel()
        finish(17)
    }

    @Test
    fun testCapacityCombos() {
        for (bufferCapacity in 1..10) {
            for (replayCapacity in 0..bufferCapacity) {
                try {
                    val sh = MutableSharedFlow<Int>(bufferCapacity, replayCapacity)
                    // repeat the whole test a few times to make sure it works correctly when slots are reused
                    repeat(3) {
                        testCapacityCombo(sh, replayCapacity)
                    }
                } catch (e: Throwable) {
                    error("Failed for bufferCapacity=$bufferCapacity, replayCapacity=$replayCapacity", e)
                }
            }
        }
    }

    private fun testCapacityCombo(sh: MutableSharedFlow<Int>, replayCapacity: Int) = runTest {
        reset()
        expect(1)
        val n = 100 // initially emitted to fill buffer
        for (i in 1..n) assertTrue(sh.tryEmit(i))
        // initial expected replayCache
        val rcStart = n - replayCapacity + 1
        val rcRange = rcStart..n
        val rcSize = n - rcStart + 1
        assertEquals(rcRange.toList(), sh.replayCache)
        // create collectors
        val m = 10 // collectors created
        var ofs = 0
        val k = 42 // emissions to collectors
        val ecRange = n + 1..n + k
        val jobs = List(m) { jobIndex ->
            launch(start = CoroutineStart.UNDISPATCHED) {
                sh.collect { i ->
                    when (i) {
                        in rcRange -> expect(2 + i - rcStart + jobIndex * rcSize)
                        in ecRange -> expect(2 + ofs + jobIndex)
                        else -> expectUnreached()
                    }
                }
                expectUnreached() // does not complete normally
            }
        }
        ofs = rcSize * m + 2
        expect(ofs)
        // emit to all k times
        for (p in ecRange) {
            sh.emit(p)
            expect(1 + ofs) // buffered, no suspend
            yield()
            ofs += 2 + m
            expect(ofs)
        }
        assertEquals(ecRange.toList().takeLast(replayCapacity), sh.replayCache)
        // cancel all collectors
        jobs.forEach { it.cancel() }
        yield()
        // replay cache is still there
        assertEquals(ecRange.toList().takeLast(replayCapacity), sh.replayCache)
        finish(1 + ofs)
    }

    @Test
    fun testDropLatest() = testKeepOrDropLatest(BufferOverflow.DROP_LATEST)

    @Test
    fun testKeepLatest() = testKeepOrDropLatest(BufferOverflow.KEEP_LATEST)

    private fun testKeepOrDropLatest(bufferOverflow: BufferOverflow) = runTest {
        reset()
        expect(1)
        val sh = MutableSharedFlow<Int?>(1, onBufferOverflow = bufferOverflow)
        sh.emit(1)
        sh.emit(2)
        // always keeps last w/o collectors
        assertEquals(listOf(2), sh.replayCache)
        assertEquals(0, sh.subscriptionCount.value)
        // one collector
        val valueAfterOverflow = when (bufferOverflow) {
            BufferOverflow.KEEP_LATEST -> 5
            BufferOverflow.DROP_LATEST -> 4
            else -> error("not supported in this test: $bufferOverflow")
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            sh.collect {
                when(it) {
                    2 -> { // replayed
                        expect(3)
                        yield() // and suspends, busy waiting
                    }
                    valueAfterOverflow -> expect(7)
                    8 -> expect(9)
                    else -> expectUnreached()
                }
            }
            expectUnreached() // does not complete normally
        }
        expect(4)
        assertEquals(1, sh.subscriptionCount.value)
        assertEquals(listOf(2), sh.replayCache)
        sh.emit(4) // buffering, collector is busy
        assertEquals(listOf(4), sh.replayCache)
        expect(5)
        sh.emit(5) // Buffer overflow here, will not suspend
        assertEquals(listOf(valueAfterOverflow), sh.replayCache)
        expect(6)
        yield() // to the job
        expect(8)
        sh.emit(8) // not busy now
        assertEquals(listOf(8), sh.replayCache) // buffered
        yield() // to process
        expect(10)
        job.cancel() // cancel the job
        yield()
        assertEquals(0, sh.subscriptionCount.value)
        finish(11)
    }

    @Test
    public fun testOnSubscription() = runTest {
        expect(1)
        val sh = MutableSharedFlow<String>(1)
        sh
            .onSubscription {
                emit("collector->A")
                sh.tryEmit("shared->A")
            }
            .onSubscription {
                emit("collector->B")
                sh.tryEmit("shared->B")
            }
            .onStart {
                emit("collector->C")
                sh.tryEmit("shared->C")
            }
            .onStart {
                emit("collector->D")
                sh.tryEmit("shared->D")
            }
            .onEach {
                when (it) {
                    "collector->D" -> expect(2)
                    "collector->C" -> expect(3)
                    "collector->A" -> expect(4)
                    "collector->B" -> expect(5)
                    "shared->C" -> {
                        expect(6)
                        currentCoroutineContext().cancel()
                    }
                }
            }
            .launchIn(this)
            .join()
        finish(7)
    }

    @Test
    fun testStateFlowModel() = runTest {
        val stateFlow = MutableStateFlow<Data?>(null)
        val expect = modelLog(stateFlow)
        val sharedFlow = SharedFlowImpl<Data?>(
            bufferCapacity = 1,
            replayCapacity = 1,
            onBufferOverflow = BufferOverflow.KEEP_LATEST,
            initialValue = null
        )
        val actual = modelLog(sharedFlow) { distinctUntilChanged() }
        for (i in 0 until minOf(expect.size, actual.size)) {
            if (actual[i] != expect[i]) {
                for (j in maxOf(0, i - 10)..i) println("Actual log item #$j: ${actual[j]}")
                assertEquals(expect[i], actual[i], "Log item #$i")
            }
        }
        assertEquals(expect.size, actual.size)
    }

    private suspend fun modelLog(
        sh: MutableSharedFlow<Data?>,
        op: Flow<Data?>.() -> Flow<Data?> = { this }
    ): List<String> = coroutineScope {
        val rnd = Random(1)
        val result = ArrayList<String>()
        val job = launch {
            sh.op().collect { value ->
                result.add("Collect: $value")
                repeat(rnd.nextInt(0..2)) {
                    result.add("Collect: yield")
                    yield()
                }
            }
        }
        repeat(1000) { index ->
            val value = rnd.nextData()
            if (index % 100 == 50) {
                result.add("resetBuffer")
                sh.resetBuffer()
            } else {
                result.add("Emit: $value")
                sh.emit(value)
            }
            repeat(rnd.nextInt(0..2)) {
                result.add("Emit: yield")
                yield()
            }
        }
        result.add("main: cancel")
        job.cancel()
        result.add("main: yield")
        yield()
        result.add("main: join")
        job.join()
        result
    }

    data class Data(val x: Int)
    private val dataCache = (1..5).associateWith { Data(it) }

    // Note that we test proper null support here, too
    private fun Random.nextData(): Data? {
        val x = nextInt(0..5)
        if (x == 0) return null
        // randomly reuse ref or create a new instance
        return if(nextBoolean()) dataCache[x] else Data(x)
    }
}

