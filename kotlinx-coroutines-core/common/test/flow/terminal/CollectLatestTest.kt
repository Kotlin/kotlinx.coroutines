/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class CollectLatestTest : TestBase() {
    @Test
    fun testNoSuspension() = runTest {
        flowOf(1, 2, 3).collectLatest {
            expect(it)
        }
        finish(4)
    }

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
}