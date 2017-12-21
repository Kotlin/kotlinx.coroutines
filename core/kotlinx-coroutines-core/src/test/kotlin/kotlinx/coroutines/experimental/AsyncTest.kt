package kotlinx.coroutines.experimental

import kotlin.test.*

class AsyncTest : TestBase() {
    // This must be a common test but it fails on JS because of KT-21961
    @Test
    fun testAsyncWithFinally() = runTest {
        expect(1)
        val d = async<String>(coroutineContext) {
            expect(3)
            try {
                yield() // to main, will cancel
            } finally {
                expect(6) // will go there on await
                return@async "Fail" // result will not override cancellation
            }
            expectUnreached()
            "Fail2"
        }
        expect(2)
        yield() // to async
        expect(4)
        check(d.isActive && !d.isCompleted && !d.isCompletedExceptionally && !d.isCancelled)
        check(d.cancel())
        check(!d.isActive && !d.isCompleted && !d.isCompletedExceptionally && d.isCancelled)
        check(!d.cancel()) // second attempt returns false
        check(!d.isActive && !d.isCompleted && !d.isCompletedExceptionally && d.isCancelled)
        expect(5)
        try {
            d.await() // awaits
            expectUnreached() // does not complete normally
        } catch (e: Throwable) {
            expect(7)
            check(e is CancellationException)
        }
        check(!d.isActive && d.isCompleted && d.isCompletedExceptionally && d.isCancelled)
        finish(8)
    }
}