package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class DispatcherNeverRunsReproducerTest : TestBase() {
    
    @Test
    fun testPerpetuallyBusyDispatcherWithCancellation() = runBlocking {
        expect(1)
        val perpetuallyBusyDispatcher = object: CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                // do nothing - never runs the block
            }
        }
        
        try {
            coroutineScope {
                val job = launch(perpetuallyBusyDispatcher) {
                    expectUnreached() // should never execute because cancelled before dispatch runs
                }
                expect(2)
                cancel() // cancel the scope
                expect(3)
                job.join() // should complete with cancellation, not hang
            }
        } catch (e: CancellationException) {
            // Expected - scope was cancelled
            finish(4)
        }
    }
    
    @Test
    fun testWithContextOnBusyDispatcherTimesOut() = runBlocking {
        expect(1)
        val perpetuallyBusyDispatcher = object: CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                // do nothing
            }
        }
        
        try {
            withTimeout(100) {
                expect(2)
                withContext(perpetuallyBusyDispatcher) {
                    expectUnreached() // should not execute
                }
            }
            expectUnreached()
        } catch (e: TimeoutCancellationException) {
            // Expected - should timeout
            finish(3)
        }
    }
    
    @Test
    fun testUndispatchedWithContextGuaranteesCorrectDispatcher() = runBlocking {
        val mainThread = Thread.currentThread()
        val ioScope = CoroutineScope(Dispatchers.IO + SupervisorJob())
        expect(1)
        
        suspend fun doSomeIo(): String = withContext(Dispatchers.IO) {
            // This code MUST run on IO thread, not Main
            assertNotSame(mainThread, Thread.currentThread(), "Should be on IO dispatcher, not main thread")
            expect(3)
            "OK"
        }
        
        // Start on Main thread but with UNDISPATCHED
        ioScope.launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            // Even though we're UNDISPATCHED and ioScope uses Dispatchers.IO,
            // withContext(Dispatchers.IO) inside doSomeIo should still dispatch
            // to ensure it runs on IO thread
            val result = doSomeIo()
            expect(4)
            assertEquals("OK", result)
        }.join()
        
        finish(5)
    }
}
