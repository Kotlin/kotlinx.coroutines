package kotlinx.coroutines.experimental

import org.junit.Test

class LaunchLazyTest : TestBase() {
    @Test
    fun testLaunchAndYieldJoin() = runBlocking {
        expect(1)
        val job = launch(context, start = false) {
            expect(4)
            yield() // does nothing -- main waits
            expect(5)
        }
        expect(2)
        yield() // does nothing, was not started yet
        expect(3)
        check(!job.isActive && !job.isCompleted)
        job.join()
        check(!job.isActive && job.isCompleted)
        finish(6)
    }

    @Test
    fun testStart() = runBlocking {
        expect(1)
        val job = launch(context, start = false) {
            expect(5)
            yield() // yields back to main
            expect(7)
        }
        expect(2)
        yield() // does nothing, was not started yet
        expect(3)
        check(!job.isActive && !job.isCompleted)
        check(job.start())
        check(job.isActive && !job.isCompleted)
        check(!job.start()) // start again -- does nothing
        check(job.isActive && !job.isCompleted)
        expect(4)
        yield() // now yield to started coroutine
        expect(6)
        check(job.isActive && !job.isCompleted)
        yield() // yield again
        check(!job.isActive && job.isCompleted) // it completes this time
        expect(8)
        job.join() // immediately returns
        finish(9)
    }
}
