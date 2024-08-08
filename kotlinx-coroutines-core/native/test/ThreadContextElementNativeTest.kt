package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class ThreadContextElementNativeTest : TestBase() {
    class JobCaptor(val capturees: ArrayList<Job> = ArrayList()) : ThreadContextElement<Unit> {

        companion object Key : CoroutineContext.Key<MyElement>

        override val key: CoroutineContext.Key<*> get() = Key

        override fun updateThreadContext(context: CoroutineContext) {
            capturees.add(context.job)
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
        }
    }

    @Test
    fun testWithContextJobAccess() = runTest {
        val captor = JobCaptor()
        val manuallyCaptured = ArrayList<Job>()
        runBlocking(captor) {
            manuallyCaptured += coroutineContext.job
            withContext(CoroutineName("undispatched")) {
                manuallyCaptured += coroutineContext.job
                withContext(Dispatchers.IO) {
                    manuallyCaptured += coroutineContext.job
                }
                // Context restored, captured again
                manuallyCaptured += coroutineContext.job
            }
            // Context restored, captured again
            manuallyCaptured += coroutineContext.job
        }

        assertEquals(manuallyCaptured, captor.capturees)
    }
}

