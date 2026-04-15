package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.produce
import kotlin.test.*

class StackTraceRecoveryExceptionConstructorsTest: TestBase() {
    internal class NonCopyable(val customData: Int) : Throwable() {
        // Bait
        constructor(cause: Throwable) : this(42)
    }

    @Test
    fun testStackTraceNotRecovered() = runTest {
        val exception = NonCopyable(239)
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw exception
            }
        } catch (e: NonCopyable) {
            assertSame(exception, e)
        }
    }

    internal class WithDefault(message: String = "default") : Exception(message)

    @Test
    fun testStackTraceRecoveredWithCustomMessage() = runTest {
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw WithDefault("custom")
            }
        } catch (e: WithDefault) {
            assertEquals("custom", e.message)
            val cause = e.cause
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
            @Suppress("ControlFlowWithEmptyBody")
            for (unit in result) {
                // Iterator has a special code path
            }
        }.exceptionOrNull() ?: error("Expected to fail")
        assertIs<WrongMessageException>(ex)
        assertEquals("Token OK", ex.message)
    }
}
