package kotlinx.coroutines.experimental

import org.junit.Test
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.EmptyCoroutineContext
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED

class CancellableContinuationImplTest {
    @Test
    fun testIdempotentSelectResume() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resume(value: String) {
                check(value === "OK")
                resumed = true
            }
            override fun resumeWithException(exception: Throwable) { error("Should not happen") }
        }
        val c = CancellableContinuationImpl<String>(delegate, false)
        check(!c.isSelected)
        check(!c.isActive)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(c.isActive)
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        val token = c.tryResume("OK", "RESUME") ?: error("Failed")
        check(c.isSelected)
        check(!c.isActive)
        check(null == c.tryResume("FAIL"))
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(token === c.tryResume("OK", "RESUME"))
        check(c.getResult() === COROUTINE_SUSPENDED)
        check(!resumed)
        c.completeResume(token)
        check(resumed)
        check(c.isSelected)
        check(!c.isActive)
        check(null == c.tryResume("FAIL"))
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(token === c.tryResume("OK", "RESUME"))
        check(c.getResult() === "OK")
    }

    @Test
    fun testIdempotentSelectCancel() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resume(value: String) { error("Should not happen") }
            override fun resumeWithException(exception: Throwable) {
                check(exception is CancellationException)
                resumed = true
            }
        }
        val c = CancellableContinuationImpl<String>(delegate, false)
        check(!c.isSelected)
        check(!c.isActive)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(c.isActive)
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(c.getResult() === COROUTINE_SUSPENDED)
        check(!resumed)
        c.cancel()
        check(resumed)
        check(c.isSelected)
        check(!c.isActive)
        check(null == c.tryResume("FAIL"))
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(null === c.tryResume("OK", "RESUME"))
    }
}