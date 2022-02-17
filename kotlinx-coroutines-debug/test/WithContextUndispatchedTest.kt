/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.*

// Test four our internal optimization "withContextUndispatched"
class WithContextUndispatchedTest : DebugTestBase() {

    @Test
    fun testZip() = runTest {
        val f1 = flowOf("a")
        val f2 = flow {
            nestedEmit()
            yield()
        }
        f1.zip(f2) { i, j -> i + j }.collect {
            bar(false)
        }
    }

    private suspend fun FlowCollector<Int>.nestedEmit() {
        emit(1)
        emit(2)
    }

    @Test
    fun testUndispatchedFlowOn() = runTest {
        val flow = flowOf(1, 2, 3).flowOn(CoroutineName("..."))
        flow.collect {
            bar(true)
        }
    }

    @Test
    fun testUndispatchedFlowOnWithNestedCaller() = runTest {
        val flow = flow {
            nestedEmit()
        }.flowOn(CoroutineName("..."))
        flow.collect {
            bar(true)
        }
    }

    private suspend fun bar(forFlowOn: Boolean) {
        yield()
        if (forFlowOn) {
            verifyFlowOn()
        } else {
            verifyZip()
        }
        yield()
    }

    private suspend fun verifyFlowOn() {
        yield() // suspend
        verifyPartialDump(1, "verifyFlowOn", "bar")
    }

    private suspend fun verifyZip() {
        yield() // suspend
        verifyPartialDump(2, "verifyZip", "bar", "nestedEmit")
    }
}
