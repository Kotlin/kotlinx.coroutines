package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class CollectLatestTest : TestBase() {
    @Test
    fun testSuspension() = runTest {
        flowOf(1, 2, 3).collectLatest {
            yield()
            expect(1)
        }
        finish(2)
    }

    @Test
    fun testUpstreamErrorSuspension() = runTest({it is TestException}) {
        try {
            flow {
                emit(1)
                yield()
                throw TestException()
            }.collectLatest { expect(1) }
            expectUnreached()
        } finally {
            finish(2)
        }
    }

    @Test
    fun testDownstreamError() = runTest({it is TestException}) {
        try {
            flow {
                emit(1)
                hang { expect(1) }
            }.collectLatest {
                throw TestException()
            }
            expectUnreached()
        } finally {
            finish(2)
        }

    }

    /** Tests that if new values appear immediately, they cancel processing the old value. */
    @Test
    fun testNoSuspension() = runTest {
        flowOf(3, 2, 1).collectLatest { value ->
            expect(value)
        }
        finish(2)
    }

    /** Tests that upstream errors that happen immediately after emitting a value cancel processing the old value. */
    @Test
    fun testUpstreamErrorNoSuspension() = runTest({it is TestException}) {
        flow {
            emit(1)
            throw TestException()
        }.collectLatest { expectUnreached() }
        expectUnreached()
    }
}
