@file:Suppress("DeferredResultUnused")

package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.emptyFlow
import kotlinx.coroutines.flow.flowOn
import org.junit.Rule
import org.junit.rules.*
import kotlin.coroutines.Continuation
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.coroutines.startCoroutine
import kotlin.test.*

class FailFastOnStartTest : TestBase() {

    @Rule
    @JvmField
    val timeout: Timeout = Timeout.seconds(5)

    @Test
    fun testLaunch() = runTest {
        assertFailsWithMainException {
            launch(Dispatchers.Main) {}
        }
    }

    @Test
    fun testLaunchLazy() = runTest {
        assertFailsWithMainException {
            val job = launch(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
            job.join()
        }
    }

    @Test
    fun testLaunchUndispatched() = runTest {
        assertFailsWithMainException {
            launch(Dispatchers.Main, start = CoroutineStart.UNDISPATCHED) {
                yield()
                fail()
            }
        }
    }

    @Test
    fun testAsync() = runTest {
        assertFailsWithMainException {
            async(Dispatchers.Main) {}
        }
    }

    @Test
    fun testAsyncLazy() = runTest {
        assertFailsWithMainException {
            val job = async(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
            job.await()
        }
    }

    @Test
    fun testAsyncAtomic() = runTest {
        assertFailsWithMainException {
            async(Dispatchers.Main, start = CoroutineStart.ATOMIC) { expectUnreached() }
        }
    }

    @Test
    fun testAsyncAtomicCancellation() = runTest {
        val parent = Job()
        assertFailsWithMainException {
            async(
                Dispatchers.Main + parent,
                start = CoroutineStart.ATOMIC
            ) { expectUnreached() }
        }
        assertFalse(parent.isActive)
        assertTrue(parent.isCancelled)
        assertTrue(parent.isCompleted)
        assertTrue(parent.children.toList().isEmpty())
    }

    @Test
    fun testWithContext() = runTest {
        assertFailsWithMainException {
            withContext(Dispatchers.Main) {
                fail()
            }
        }
    }

    @Test
    fun testProduce() = runTest {
        assertFailsWithMainException {
            produce<Int>(Dispatchers.Main) { fail() }
        }
    }

    @Test
    fun testActor() = runTest {
        assertFailsWithMainException {
            actor<Int>(Dispatchers.Main) { fail() }
        }
    }

    @Test
    fun testActorLazy() = runTest {
        assertFailsWithMainException {
            val actor = actor<Int>(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
            actor.send(1)
        }
    }

    private fun mainException(e: Throwable): Boolean {
        return e is IllegalStateException && e.message?.contains("Module with the Main dispatcher is missing") ?: false
    }

    private suspend fun assertFailsWithMainException(block: suspend CoroutineScope.() -> Any?) {
        // Whatever failures happen in coroutines due to a missing dispatcher, they should get propagated to the parent.
        // `async` is the parent, and `supervisorScope` ensures that's where the propagation stops.
        supervisorScope {
            val result = async {
                block()
            }
            val e = assertFailsWith<IllegalStateException> {
                result.await()
            }
            assertTrue(mainException(e), "$e")
        }
    }

    @Test
    fun testProduceNonChild() = runTest {
        assertFailsWithMainException {
            produce<Int>(Job() + Dispatchers.Main) { fail() }
        }
    }

    @Test
    fun testFlowOnCompletes() = runTest {
        assertFailsWithMainException {
            emptyFlow<Int>().flowOn(Dispatchers.Main).collect { fail() }
        }
    }
}
