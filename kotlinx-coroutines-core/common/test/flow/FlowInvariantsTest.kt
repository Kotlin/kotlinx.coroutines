/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class FlowInvariantsTest : TestBase() {

    @Test
    fun testWithContextContract() = runTest {
        flow {
            kotlinx.coroutines.withContext(NonCancellable) {
                // This one cannot be prevented :(
                emit(1)
            }
        }.collect {
            assertEquals(1, it)
        }
    }

    @Test
    fun testWithContextContractViolated() = runTest({ it is IllegalStateException }) {
        flow {
            kotlinx.coroutines.withContext(NamedDispatchers("foo")) {
                emit(1)
            }
        }.collect {
            fail()
        }
    }

    @Test
    fun testWithContextDoesNotChangeExecution() = runTest {
        val flow = flow {
            emit(NamedDispatchers.name())
        }.flowOn(NamedDispatchers("original"))

        var result = "unknown"
        withContext(NamedDispatchers("misc")) {
            flow
                .flowOn(NamedDispatchers("upstream"))
                .launchIn(this + NamedDispatchers("consumer")) {
                    onEach {
                        result = it
                    }
                }.join()
        }

        assertEquals("original", result)
    }
}
