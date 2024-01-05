package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class LintTest: TestBase() {
    /**
     * Tests that using [SharedFlow.toList] and similar functions by passing a mutable collection does add values
     * to the provided collection.
     */
    @Test
    fun testSharedFlowToCollection() = runTest {
        val sharedFlow = MutableSharedFlow<Int>()
        val list = mutableListOf<Int>()
        val set = mutableSetOf<Int>()
        val jobs = listOf(suspend { sharedFlow.toList(list) }, { sharedFlow.toSet(set) }).map {
            launch(Dispatchers.Unconfined) { it() }
        }
        repeat(10) {
            sharedFlow.emit(it)
        }
        jobs.forEach { it.cancelAndJoin() }
        assertEquals((0..9).toList(), list)
        assertEquals((0..9).toSet(), set)
    }
}
