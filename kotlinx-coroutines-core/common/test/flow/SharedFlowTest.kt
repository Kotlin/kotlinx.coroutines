package kotlinx.coroutines.flow

import kotlinx.coroutines.*
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




        job1.cancel()
        finish(10)
    }


}