/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlin.test.*

@Suppress("DEPRECATION_ERROR")
class TestCoroutineExceptionHandlerTest {
    @Test
    fun whenExceptionsCaught_availableViaProperty() {
        val subject = TestCoroutineExceptionHandler()
        val expected = IllegalArgumentException()
        subject.handleException(subject, expected)
        assertEquals(listOf(expected), subject.uncaughtExceptions)
    }
}
