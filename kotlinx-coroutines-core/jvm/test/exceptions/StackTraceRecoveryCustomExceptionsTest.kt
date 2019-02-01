/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

@Suppress("UNREACHABLE_CODE", "UNUSED", "UNUSED_PARAMETER")
class StackTraceRecoveryCustomExceptionsTest : TestBase() {

    internal class NonCopyable(val customData: Int) : Throwable() {
        // Bait
        public constructor(cause: Throwable) : this(42)
    }

    internal class Copyable(val customData: Int) : Throwable(), CopyableThrowable<Copyable> {
        // Bait
        public constructor(cause: Throwable) : this(42)

        override fun createCopy(): Copyable {
            val copy = Copyable(customData)
            copy.initCause(this)
            return copy
        }
    }

    @Test
    fun testStackTraceNotRecovered() = runTest {
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw NonCopyable(239)
            }
            expectUnreached()
        } catch (e: NonCopyable) {
            assertEquals(239, e.customData)
            assertNull(e.cause)
        }
    }

    @Test
    fun testStackTraceRecovered() = runTest {
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw Copyable(239)
            }
            expectUnreached()
        } catch (e: Copyable) {
            assertEquals(239, e.customData)
            val cause = e.cause
            assertTrue(cause is Copyable)
            assertEquals(239, cause.customData)
        }
    }
}
