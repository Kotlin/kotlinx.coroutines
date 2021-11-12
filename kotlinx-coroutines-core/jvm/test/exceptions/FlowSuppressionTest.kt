/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

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
}
