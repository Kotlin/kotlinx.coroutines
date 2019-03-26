/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class CompletableJobTest {
    @Test
    fun testComplete() {
        val job = Job()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertTrue(job.complete())
        assertTrue(job.isCompleted)
        assertFalse(job.isActive)
        assertFalse(job.isCancelled)
        assertFalse(job.complete())
    }

    @Test
    fun testCompleteWithException() {
        val job = Job()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertTrue(job.completeExceptionally(TestException()))
        assertTrue(job.isCompleted)
        assertFalse(job.isActive)
        assertTrue(job.isCancelled)
        assertFalse(job.completeExceptionally(TestException()))
        assertFalse(job.complete())
    }

    @Test
    fun testCompleteWithChildren() {
        val parent = Job()
        val child = Job(parent)
        assertTrue(parent.complete())
        assertFalse(parent.complete())
        assertTrue(parent.isActive)
        assertFalse(parent.isCompleted)
        assertTrue(child.complete())
        assertTrue(child.isCompleted)
        assertTrue(parent.isCompleted)
        assertFalse(child.isActive)
        assertFalse(parent.isActive)
    }
}