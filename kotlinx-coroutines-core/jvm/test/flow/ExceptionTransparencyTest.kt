package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class ExceptionTransparencyTest : TestBase() {

    @Test
    fun testViolation() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(3)
                emit(2)
            }
        }.take(1)

        assertFailsWith<IllegalStateException> { flow.collect { expect(2) } }
        finish(4)
    }

    @Test
    fun testViolationResumeWith() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
                yield()
                expectUnreached()
            } catch (e: CancellationException) {
                expect(3)
                emit(2)
            }
        }.take(1)

        assertFailsWith<IllegalStateException> {
            flow.collect {
                yield()
                expect(2)
            }
        }
        finish(4)
    }

    @Test
    fun testViolationAfterInvariantVariation() = runTest {
        val flow = flow<Int> {
            coroutineScope {
                try {
                    expect(1)
                    launch {
                        expect(2)
                        emit(1)
                    }.join()
                    expectUnreached()
                } catch (e: Throwable) {
                    try {
                        emit(2)
                    } catch (e: IllegalStateException) {
                        assertTrue { e.message!!.contains("exception transparency") }
                        emit(3)
                    }
                }
            }
        }
        val e = assertFailsWith<IllegalStateException> { flow.collect { expectUnreached() } }
        assertTrue { e.message!!.contains("channelFlow") }
        finish(3)
    }
}
