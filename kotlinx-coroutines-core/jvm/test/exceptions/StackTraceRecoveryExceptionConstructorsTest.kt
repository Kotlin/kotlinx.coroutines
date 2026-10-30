package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.produce
import kotlin.test.*

class StackTraceRecoveryExceptionConstructorsTest: TestBase() {
    @Suppress("UNUSED")
    internal class NonCopyable(val customData: Int) : Throwable() {
        // Bait
        constructor(cause: Throwable) : this(42)
    }

    @Test
    fun testStackTraceNotRecovered() = runTest {
        val exception = NonCopyable(239)
        assertFailsWith<NonCopyable> {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw exception
            }
        }.apply {
            assertSame(exception, this)
        }
    }

    internal class WithDefault(message: String = "default") : Exception(message)

    @Test
    fun testStackTraceRecoveredWithCustomMessage() = runTest {
        assertFailsWith<WithDefault> {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw WithDefault("custom")
            }
        }.apply {
            assertEquals("custom", message)
            val cause = cause
            assertIs<WithDefault>(cause)
            assertEquals("custom", cause.message)
        }
    }

    class WrongMessageException(token: String) : RuntimeException("Token $token")

    @Test
    fun testWrongMessageException() = runTest {
        val result = runCatching {
            coroutineScope<Unit> {
                throw WrongMessageException("OK")
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertIs<WrongMessageException>(ex)
        assertEquals("Token OK", ex.message)
    }


    @Test
    fun testNestedExceptionWithCause() = runTest {
        val result = runCatching {
            coroutineScope<Unit> {
                throw NestedException(IllegalStateException("ERROR"))
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertIs<NestedException>(ex)
        assertIs<NestedException>(ex.cause)
        val originalCause = ex.cause?.cause
        assertIs<IllegalStateException>(originalCause)
        assertEquals("ERROR", originalCause.message)
    }

    @Suppress("UNUSED")
    class NestedException : RuntimeException {
        constructor(cause: Throwable) : super(cause)
        constructor() : super()
    }

    @Test
    fun testWrongMessageExceptionInChannel() = runTest {
        val result = produce<Unit>(SupervisorJob() + Dispatchers.Unconfined) {
            throw WrongMessageException("OK")
        }
        val ex = runCatching {
            @Suppress("ControlFlowWithEmptyBody", "UNUSED")
            for (unit in result) {
                // Iterator has a special code path
            }
        }.exceptionOrNull() ?: error("Expected to fail")
        assertIs<WrongMessageException>(ex)
        assertEquals("Token OK", ex.message)
    }
}
