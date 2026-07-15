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
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.startCoroutine
import kotlin.test.*

class FailFastOnStartTest : TestBase() {

    @Rule
    @JvmField
    val timeout: Timeout = Timeout.seconds(5)

    val brokenDispatcher = object: CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            throw TestException("Dispatcher refuses to execute code")
        }
    }

    @Test
    fun testLaunch() = runTest(expected = ::isTestException) {
        launch(brokenDispatcher) {}
    }

    @Test
    fun testLaunchLazy() = runTest(expected = ::isTestException) {
        val job = launch(brokenDispatcher, start = CoroutineStart.LAZY) { fail() }
        job.join()
    }

    @Test
    fun testLaunchUndispatched() = runTest(expected = ::isTestException) {
        launch(brokenDispatcher, start = CoroutineStart.UNDISPATCHED) {
            yield()
            fail()
        }
    }

    @Test
    fun testAsync() = runTest(expected = ::isTestException) {
        async(brokenDispatcher) {}
    }

    @Test
    fun testAsyncLazy() = runTest(expected = ::isTestException) {
        val job = async(brokenDispatcher, start = CoroutineStart.LAZY) { fail() }
        job.await()
    }

    @Test
    fun testWithContext() = runTest(expected = ::isTestException) {
        withContext(brokenDispatcher) {
            fail()
        }
    }

    @Test
    fun testProduce() = runTest(expected = ::isTestException) {
        produce<Int>(brokenDispatcher) { fail() }
    }

    @Test
    fun testActor() = runTest(expected = ::isTestException) {
        actor<Int>(brokenDispatcher) { fail() }
    }

    @Test
    fun testActorLazy() = runTest(expected = ::isTestException) {
        val actor = actor<Int>(brokenDispatcher, start = CoroutineStart.LAZY) { fail() }
        actor.send(1)
    }

    @Test
    fun testProduceNonChild() = runTest(expected = ::isTestException) {
        produce<Int>(Job() + brokenDispatcher) { fail() }
    }

    @Test
    fun testAsyncNonChild() = runTest(expected = ::isTestException) {
        async<Int>(Job() + brokenDispatcher) { fail() }
    }

    @Test
    fun testFlowOn() {
        // See #4142, this test ensures that `coroutineScope { produce(failingDispatcher, ATOMIC) }`
        // rethrows an exception. It does not help with the completion of such a coroutine though.
        // `suspend {}` + start coroutine with custom `completion` to avoid waiting for test completion
        expect(1)
        val caller = suspend {
            try {
                emptyFlow<Int>().flowOn(brokenDispatcher).collect { fail() }
            } catch (e: Throwable) {
                assertTrue(isTestException(e))
                expect(2)
            }
        }

        caller.startCoroutine(Continuation(EmptyCoroutineContext) {
            finish(3)
        })
    }

    private fun isTestException(e: Throwable): Boolean =
        e is TestException
}
