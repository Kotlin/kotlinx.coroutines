/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import kotlin.test.*

class RunBlockingTestExceptionsTest : TestBase() {

    @Test(expected = TestException::class)
    fun testThrowException() = runBlockingTest {
        throw TestException()
    }

    @Test(expected = TestException::class)
    fun testThrowExceptionAfterSuspension() = runBlockingTest {
        expect(1)
        val job = launch {
            yield()
            expect(3)
        }
        expect(2)
        job.join()
        finish(4)
        throw TestException()
    }

    @Test(expected = TestException::class)
    fun testThrowExceptionInChild() = runBlockingTest {
        expect(1)
        launch {
            yield()
            finish(3)
            throw TestException()
        }
        expect(2)
    }

    @Test
    fun testNestedCancellationIsNotPropagated() = runBlockingTest {
        expect(1)
        launch {
            yield()
            expect(3)
            cancel()
            finish(4)
            ensureActive()
            expectUnreached()
        }
        expect(2)
    }
}
