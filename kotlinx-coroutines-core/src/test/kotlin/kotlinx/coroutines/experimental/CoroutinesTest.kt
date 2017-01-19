package kotlinx.coroutines.experimental

import org.junit.After
import org.junit.Test
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger

class CoroutinesTest {
    var actionIndex = AtomicInteger()
    var finished = AtomicBoolean()

    fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex"}
    }

    fun finish(index: Int) {
        expect(index)
        finished.set(true)
    }

    @After
    fun onCompletion() {
        check(finished.get()) { "Expecting that 'finish(...)' was invoked, but it was not" }
    }

    @Test
    fun testSimple() = runEventLoop {
        expect(1)
        finish(2)
    }

    @Test
    fun testYield() = runEventLoop {
        expect(1)
        yield() // effectively does nothing, as we don't have other coroutines
        finish(2)
    }

    @Test
    fun testLaunchHereAndYield() = runEventLoop {
        expect(1)
        val job = launch(Here) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3)
        job.join()
        finish(5)
    }
}