package kotlinx.coroutines.experimental

import kotlin.test.*

class CommonAtomicCancellationTest : TestBase() {
    @Test
    fun testCancellableLaunch() = runBlocking {
        expect(1)
        val job = launch(coroutineContext) {
            expectUnreached() // will get cancelled before start
        }
        expect(2)
        job.cancel()
        finish(3)
    }

    @Test
    fun testAtomicLaunch() = runBlocking {
        expect(1)
        val job = launch(coroutineContext, start = CoroutineStart.ATOMIC) {
            finish(4) // will execute even after it was cancelled
        }
        expect(2)
        job.cancel()
        expect(3)
    }

    @Test
    fun testDeferredAwaitCancellable() = runBlocking {
        expect(1)
        val deferred = async(coroutineContext) { // deferred, not yet complete
            expect(4)
            "OK"
        }
        assertEquals(false, deferred.isCompleted)
        var job: Job? = null
        launch(coroutineContext) { // will cancel job as soon as deferred completes
            expect(5)
            assertEquals(true, deferred.isCompleted)
            job!!.cancel()
        }
        job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                deferred.await() // suspends
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when job suspends
        yield() // to deferred & canceller
        expect(6)
    }

    @Test
    fun testJobJoinCancellable() = runBlocking {
        expect(1)
        val jobToJoin = launch(coroutineContext) { // not yet complete
            expect(4)
        }
        assertEquals(false, jobToJoin.isCompleted)
        var job: Job? = null
        launch(coroutineContext) { // will cancel job as soon as jobToJoin completes
            expect(5)
            assertEquals(true, jobToJoin.isCompleted)
            job!!.cancel()
        }
        job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                jobToJoin.join() // suspends
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when job suspends
        yield() // to jobToJoin & canceller
        expect(6)
    }
}