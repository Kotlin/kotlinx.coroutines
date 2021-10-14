/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlin.time.*

class RunTestTest {

    /** Tests that [withContext] that sends work to other threads works in [runTest]. */
    @Test
    fun testWithContextDispatching() = runTest {
        var counter = 0
        withContext(Dispatchers.Default) {
            counter += 1
        }
        assertEquals(counter, 1)
    }

    /** Tests that joining [GlobalScope.launch] works in [runTest]. */
    @Test
    fun testJoiningForkedJob() = runTest {
        var counter = 0
        val job = GlobalScope.launch {
            counter += 1
        }
        job.join()
        assertEquals(counter, 1)
    }

    /** Tests [suspendCoroutine] not failing [runTest]. */
    @Test
    fun testSuspendCoroutine() = runTest {
        val answer = suspendCoroutine<Int> {
            it.resume(42)
        }
        assertEquals(42, answer)
    }

    /** Tests that [runTest] attempts to detect it being run inside another [runTest] and failing in such scenarios. */
    @Test
    fun testNestedRunTestForbidden() = runTest {
        assertFailsWith<IllegalStateException> {
            runTest { }
        }
    }

}
