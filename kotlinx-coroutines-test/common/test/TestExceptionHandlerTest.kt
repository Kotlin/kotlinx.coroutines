/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.random.*
import kotlin.test.*

class TestExceptionHandlerTest {

    /** Tests that passing a [TestExceptionHandler] to [TestCoroutineScope] overrides the exception handling there. */
    @Test
    fun testPassingToCoroutineScope() {
        var enteredHandler = false
        var observedScope: TestCoroutineScope? = null
        val handler = TestExceptionHandler { _, throwable ->
            assertTrue(throwable is TestException)
            observedScope = this
            enteredHandler = true
        }
        val scope = createTestCoroutineScope(handler + SupervisorJob())
        scope.launch {
            throw TestException("test")
        }
        scope.runCurrent()
        assertTrue(enteredHandler)
        assertSame(scope, observedScope)
        scope.cleanupTestCoroutines()
    }

    /** Tests that passing a [TestCoroutineScope] to the [TestExceptionHandler] will link, but won't affect the
     * coroutine context of [TestCoroutineScope]. */
    @Test
    fun testExplicitLinking() {
        var observedScope: TestCoroutineScope? = null
        val scope = createTestCoroutineScope(SupervisorJob())
        val handler = TestExceptionHandler(scope) { _, throwable ->
            assertTrue(throwable is TestException)
            observedScope = this
        }
        scope.launch(handler) {
            throw TestException("test1")
        }
        scope.launch {
            throw TestException("test2")
        }
        scope.runCurrent()
        assertSame(scope, observedScope)
        try {
            scope.cleanupTestCoroutines()
            throw AssertionError("won't reach")
        } catch (e: TestException) {
            assertEquals("test2", e.message)
        }
    }

    /** Tests that passing a [TestExceptionHandler] that's already linked to another [TestCoroutineScope] will cause it
     * to be copied. */
    @Test
    fun testRelinking() {
        val encountered = mutableListOf<TestCoroutineScope>()
        val handler = TestExceptionHandler { _, throwable ->
            assertTrue(throwable is TestException)
            encountered.add(this)
        }
        val scopes = List(3) { createTestCoroutineScope(handler + SupervisorJob()) }
        val events = List(10) { Random.nextInt(0, 3) }.map { scopes[it] }
        events.forEach {
            it.launch {
                throw TestException()
            }
            it.runCurrent()
        }
        assertEquals(events, encountered)
    }

    /** Tests that throwing inside [TestExceptionHandler] is reported. */
    @Test
    fun testThrowingInsideHandler() {
        val handler = TestExceptionHandler { _, throwable ->
            assertEquals("y", throwable.message)
            throw TestException("x")
        }
        val scope = createTestCoroutineScope(handler)
        scope.launch {
            throw TestException("y")
        }
        scope.runCurrent()
        try {
            scope.cleanupTestCoroutines()
            throw AssertionError("can't be reached")
        } catch (e: TestException) {
            assertEquals("x", e.message)
        }
    }

    /** Tests that throwing inside [TestExceptionHandler] after the scope is cleaned up leads to problems. */
    @Test
    @Ignore // difficult to check on JS and Native, where the error is simply logged
    fun testThrowingInsideHandlerAfterCleanup() {
        val handler = TestExceptionHandler { _, throwable ->
            reportException(throwable)
        }
        val scope = createTestCoroutineScope(handler)
        scope.cleanupTestCoroutines()
        handler.handleException(EmptyCoroutineContext, TestException())
    }

}