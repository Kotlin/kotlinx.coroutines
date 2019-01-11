/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class CoroutineExceptionHandlerJvmTest : TestBase() {

    private val exceptionHandler = Thread.getDefaultUncaughtExceptionHandler()
    private lateinit var caughtException: Throwable

    @Before
    fun setUp() {
        Thread.setDefaultUncaughtExceptionHandler({ _, e -> caughtException = e })
    }

    @After
    fun tearDown() {
        Thread.setDefaultUncaughtExceptionHandler(exceptionHandler)
    }

    @Test
    fun testFailingHandler() = runBlocking {
        expect(1)
        val job = GlobalScope.launch(CoroutineExceptionHandler { _, _ -> throw AssertionError() }) {
            expect(2)
            throw TestException()
        }

        job.join()
        assertTrue(caughtException is RuntimeException)
        assertTrue(caughtException.cause is AssertionError)
        assertTrue(caughtException.suppressed[0] is TestException)

        finish(3)
    }
}
