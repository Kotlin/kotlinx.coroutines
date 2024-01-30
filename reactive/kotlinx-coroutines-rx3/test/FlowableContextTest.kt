package kotlinx.coroutines.rx3

import kotlinx.coroutines.testing.*
import io.reactivex.rxjava3.core.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class FlowableContextTest : TestBase() {
    private val dispatcher = newSingleThreadContext("FlowableContextTest")

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testFlowableCreateAsFlowThread() = runTest {
        expect(1)
        val mainThread = Thread.currentThread()
        val dispatcherThread = withContext(dispatcher) { Thread.currentThread() }
        assertTrue(dispatcherThread != mainThread)
        Flowable.create<String>({
            assertEquals(dispatcherThread, Thread.currentThread())
            it.onNext("OK")
            it.onComplete()
        }, BackpressureStrategy.BUFFER)
            .asFlow()
            .flowOn(dispatcher)
            .collect {
                expect(2)
                assertEquals("OK", it)
                assertEquals(mainThread, Thread.currentThread())
            }
        finish(3)
    }
}
