package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import kotlin.test.assertEquals
import kotlin.time.ExperimentalTime
import kotlin.time.milliseconds
import kotlin.time.seconds

class TestCoroutineDispatcherOrderTest : TestBase() {

    @Test
    fun testAdvanceTimeBy_progressesOnEachDelay() {
        val dispatcher = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(dispatcher)

        expect(1)
        scope.launch {
            expect(2)
            delay(1_000)
            assertEquals(1_000, dispatcher.currentTime)
            expect(4)
            delay(5_00)
            assertEquals(1_500, dispatcher.currentTime)
            expect(5)
            delay(501)
            assertEquals(2_001, dispatcher.currentTime)
            expect(7)
        }
        expect(3)
        assertEquals(0, dispatcher.currentTime)
        dispatcher.advanceTimeBy(2_000)
        expect(6)
        assertEquals(2_000, dispatcher.currentTime)
        dispatcher.advanceTimeBy(2)
        expect(8)
        assertEquals(2_002, dispatcher.currentTime)
        scope.cleanupTestCoroutines()
        finish(9)
    }

    @Test
    @OptIn(ExperimentalTime::class)
    fun testAdvanceTimeBy_duration_progressesOnEachDelay() {
        val dispatcher = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(dispatcher)

        expect(1)
        scope.launch {
            expect(2)
            delay(1.seconds)
            assertEquals(1_000, dispatcher.currentTime)
            expect(4)
            delay(500)
            assertEquals(1_500, dispatcher.currentTime)
            expect(5)
            delay(501)
            assertEquals(2_001, dispatcher.currentTime)
            expect(7)
        }
        expect(3)
        assertEquals(0, dispatcher.currentTime)
        dispatcher.advanceTimeBy(2.seconds)
        expect(6)
        assertEquals(2_000, dispatcher.currentTime)
        dispatcher.advanceTimeBy(2.milliseconds)
        expect(8)
        assertEquals(2_002, dispatcher.currentTime)
        scope.cleanupTestCoroutines()
        finish(9)
    }
}