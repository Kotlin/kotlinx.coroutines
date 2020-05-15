package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.random.*
import kotlin.test.*

class SharedFlowTest : TestBase() {
    @Test
    fun testSyncSharedFlowBasic() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int?>(0)
        assertTrue(sh.replayCache.isEmpty())
        assertEquals(0, sh.collectorsCount.value)
        sh.emit(1) // no suspend
        assertTrue(sh.replayCache.isEmpty())
        assertEquals(0, sh.collectorsCount.value)
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
        assertEquals(1, sh.collectorsCount.value)
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
        assertEquals(2, sh.collectorsCount.value)
        sh.emit(10) // to both collectors now!
        assertTrue(sh.replayCache.isEmpty())
        expect(13)
        sh.emit(13)
        expect(16)
        job1.cancel() // cancel the first collector
        yield()
        assertEquals(1, sh.collectorsCount.value)
        expect(17)
        sh.emit(17) // only to second collector
        expect(19)
        sh.emit(null) // emit null to the second collector
        expect(21)
        sh.emit(21) // non-null again
        expect(23)
        job2.cancel() // cancel the second collector
        yield()
        assertEquals(0, sh.collectorsCount.value)
        expect(24)
        sh.emit(24) // does not go anywhere
        assertEquals(0, sh.collectorsCount.value)
        assertTrue(sh.replayCache.isEmpty())
        finish(25)
    }

    @Test
    fun testLastOneSharedFlowBasic() = runTest {
        expect(1)
        val sh = MutableSharedFlow<Int?>(1)
        assertTrue(sh.replayCache.isEmpty())
        assertEquals(0, sh.collectorsCount.value)
        sh.emit(1) // no suspend
        assertEquals(listOf(1), sh.replayCache)
        assertEquals(0, sh.collectorsCount.value)
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
        assertEquals(1, sh.collectorsCount.value)
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
        assertEquals(2, sh.collectorsCount.value)
        sh.emit(null)
        expect(13)
        assertEquals(listOf(null), sh.replayCache)
        yield()
        assertEquals(listOf(null), sh.replayCache)
        expect(16)
        job2.cancel()
        yield()
        assertEquals(1, sh.collectorsCount.value)
        expect(17)
        sh.emit(17)
        assertEquals(listOf(17), sh.replayCache)
        yield()
        expect(19)
        job1.cancel()
        yield()
        assertEquals(0, sh.collectorsCount.value)
        assertEquals(listOf(17), sh.replayCache)
        finish(20)
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
        var ofs: Int = 0
        val k = 42 // emisions to collectors
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
    fun testDropLatest() = testDropLatestOrOldest(SharedBufferOverflow.DROP_LATEST)

    @Test
    fun testDropOldest() = testDropLatestOrOldest(SharedBufferOverflow.DROP_OLDEST)

    private fun testDropLatestOrOldest(bufferOverflow: SharedBufferOverflow) = runTest {
        reset()
        expect(1)
        val sh = MutableSharedFlow<Int?>(1, bufferOverflow = bufferOverflow)
        sh.emit(1)
        sh.emit(2)
        // always keeps last w/o collectors
        assertEquals(listOf(2), sh.replayCache)
        assertEquals(0, sh.collectorsCount.value)
        // one collector
        val valueAfterOverflow = when (bufferOverflow) {
            SharedBufferOverflow.DROP_OLDEST -> 5
            SharedBufferOverflow.DROP_LATEST -> 4
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
        assertEquals(1, sh.collectorsCount.value)
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
        assertEquals(listOf(8), sh.replayCache) // byffered
        yield() // to process
        expect(10)
        job.cancel() // cancel the job
        yield()
        assertEquals(0, sh.collectorsCount.value)
        finish(11)
    }

    /**
     * Tests that `distinctUntilChanged` parameter is equivalent to the effect of [distinctUntilChanged] operator.
     * It also tests a base-line of just transferring a large list of data via a shared flow with [Equivalent.Never].
     */
    @Test
    fun testDistinctUntilChangedEquivalence() {
        for (bufferCapacity in 1..10) {
            for (replayCapacity in 1..bufferCapacity) {
                for (eq in listOf(Equivalent.Never, Equivalent.ByValue, Equivalent.ByReference)) {
                    try {
                        testDistinctUntilChangedEquivalence(bufferCapacity, replayCapacity, eq)
                    } catch (e: Throwable) {
                        error("Failed for bufferCapacity=$bufferCapacity, replayCapacity=$replayCapacity with distinctUntilChanged($eq)", e)
                    }
                }
            }
        }
    }

    private fun testDistinctUntilChangedEquivalence(
        bufferCapacity: Int,
        replayCapacity: Int,
        eq: ValueEquivalence<Any?>
    ) = runTest {
        val rnd = Random(1)
        val list = List(100) { rnd.nextData() }
        val flow = list.asFlow() // generate a source list once
        val expected = flow.distinctUntilChanged(eq).toList()
        val actual = processFlow(flow, MutableSharedFlow(bufferCapacity, replayCapacity, distinctUntilChanged = eq))
        assertSameList(expected, actual)
    }

    private suspend fun <T> processFlow(flow: Flow<T>, sharedFlow: MutableSharedFlow<T>): List<T> = coroutineScope {
        val result = ArrayList<T>()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            sharedFlow.collect { item ->
                result.add(item)
            }
        }
        sharedFlow.emitAll(flow)
        yield() // finish processing
        job.cancelAndJoin()
        result
    }

    private fun <T> assertSameList(expected: List<T>, actual: List<T>) {
        assertEquals(expected.size, actual.size)
        for (i in expected.indices) assertSame(expected[i], actual[i])
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

