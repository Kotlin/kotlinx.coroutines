/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class TestCoroutineScopeTest {
    @Test
    fun whenGivenInvalidExceptionHandler_throwsException() {
        val handler = CoroutineExceptionHandler {  _, _ -> Unit }
        assertFails {
            TestCoroutineScope(handler)
        }
    }

    @Test
    fun whenGivenInvalidDispatcher_throwsException() {
        assertFails {
            TestCoroutineScope(newSingleThreadContext("incorrect call"))
        }
    }
}
