/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlin.time.*

class TestRunTest {

    @Test
    fun testWithContextDispatching() = runTest {
        var counter = 0
        withContext(Dispatchers.Default) {
            counter += 1
        }
        assertEquals(counter, 1)
    }

    @Test
    fun testJoiningForkedJob() = runTest {
        var counter = 0
        val job = GlobalScope.launch {
            counter += 1
        }
        job.join()
        assertEquals(counter, 1)
    }

    @Test
    fun testSuspendCancellableCoroutine() = runTest {
        val answer = suspendCoroutine<Int> {
            it.resume(42)
        }
        assertEquals(42, answer)
    }

    @Test
    fun testNestedRunTestForbidden() = runTest {
        assertFailsWith<IllegalStateException> {
            runTest { }
        }
    }

}
