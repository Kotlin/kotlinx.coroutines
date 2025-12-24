package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class FlowSuppressionTest : TestBase() {
    @Test
    fun testSuppressionForPrimaryException() = runTest {
        val flow = flow {
            try {
                emit(1)
            } finally {
                throw TestException()
            }
        }.catch { expectUnreached() }.onEach { throw TestException2() }

        try {
            flow.collect()
        } catch (e: Throwable) {
            assertIs<TestException>(e)
            assertIs<TestException2>(e.suppressed[0])
        }
    }

    @Test
    fun testSuppressionForPrimaryExceptionRetry() = runTest {
        val flow = flow {
            try {
                emit(1)
            } finally {
                throw TestException()
            }
        }.retry { expectUnreached(); true }.onEach { throw TestException2() }

        try {
            flow.collect()
        } catch (e: Throwable) {
            assertIs<TestException>(e)
            assertIs<TestException2>(e.suppressed[0])

        }
    }

    @Test
    fun testCancellationSuppression() = runTest {
        val flow = flow {
            try {
                expect(1)
                emit(1)
            } finally {
                expect(3)
                throw CancellationException("")
            }
        }.catch { expectUnreached() }.onEach {
            expect(2)
            throw TestException("")
        }

        try {
            flow.collect()
        } catch (e: Throwable) {
            assertIs<TestException>(e)
            assertIs<CancellationException>(e.suppressed[0])
        }
        finish(4)
    }
}
