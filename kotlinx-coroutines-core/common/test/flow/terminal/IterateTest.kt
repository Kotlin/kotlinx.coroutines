/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class IterateTest : TestBase() {
    @Test
    fun testIterateToList() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }
        val list = flow.iterate {
            val mutableList = mutableListOf<Int>()
            while (hasNext()) {
                mutableList.add(next())
            }
            mutableList
        }
        assertEquals(listOf(1, 2), list)
    }

    @Test
    fun testCancelsAfterDone() = runTest {
        val flow = flow {
            emit(1)
            error("Should not be executed")
        }
        val result = flow.iterate { next() }
        assertEquals(1, result)
    }

    @Test
    fun testDoesNotRace() = runTest {
        val flow = flow {
            emit(1)
            error("Should not be executed")
        }
        val result = flow.iterate {
            next().also {
                yield()
                // not obvious if this results in a deterministic test?
                // advanceUntilIdle would make this clearly deterministic
            }
        }
        assertEquals(1, result)
    }

    @Test
    fun testBackingFlowFailure() = runTest {
        val flow = flow {
            emit(1)
            throw IllegalStateException()
        }
        assertFailsWith<IllegalStateException> {
            flow.iterate {
                while (hasNext()) {
                    next()
                }
            }
        }
    }
}
