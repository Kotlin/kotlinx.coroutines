package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class OnCompletionInterceptedReleaseTest : TestBase() {
    @Test
    fun testLeak() = runTest {
        expect(1)
        var cont: Continuation<Unit>? = null
        val interceptor = CountingInterceptor()
        val job = launch(interceptor, start = CoroutineStart.UNDISPATCHED) {
            emptyFlow<Int>()
                .onCompletion { emit(1) }
                .collect { value ->
                    expect(2)
                    assertEquals(1, value)
                    suspendCoroutine { cont = it }
                }
        }
        cont!!.resume(Unit)
        assertTrue(job.isCompleted)
        assertEquals(interceptor.intercepted, interceptor.released)
        finish(3)
    }

    class CountingInterceptor : AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
        var intercepted = 0
        var released = 0
        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
            intercepted++
            return Continuation(continuation.context) { continuation.resumeWith(it) }
        }

        override fun releaseInterceptedContinuation(continuation: Continuation<*>) {
            released++
        }
    }
}