package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.Test
import kotlin.test.assertEquals

class RepeatWhenTest : TestBase() {

    @Test
    fun testRepeatWhen() = runTest {
        val repeatFlow = flow {
            emit("Repeat")
        }

        val result = flowOf(1, 2, 3, 4).repeatWhen(repeatFlow).toList()
        assertEquals(listOf(1, 2, 3, 4, 1, 2, 3, 4), result)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val repeatFlow = flow {
            emit("Repeat")
        }

        val result = emptyFlow<Unit>().repeatWhen(repeatFlow).toList()
        assertEquals(emptyList(), result)
    }

    @Test
    fun testCancelPreviousFlow() = runTest {
        val repeatFlow = flow {
            emit("Repeat")
        }

        val flow = flow {
            emit(1)
            emit(2)
            yield()
            emit(3)
            emit(4)
        }

        val result = flow.repeatWhen(repeatFlow).toList()
        assertEquals(listOf(1, 2, 1, 2, 3, 4), result)
    }

    @Test
    fun testRepeatFlowError() = runTest {
        val repeatFlow = flow<Unit> {
            throw TestException()
        }

        val flow = flowOf(1).repeatWhen(repeatFlow)
        assertFailsWith<TestException>(flow)
    }

    @Test
    fun testFlowError() = runTest {
        val repeatFlow = flow {
            emit("Repeat")
        }

        val flow = flow<Unit> {
            throw TestException()
        }.repeatWhen(repeatFlow)
        assertFailsWith<TestException>(flow)
    }
}
