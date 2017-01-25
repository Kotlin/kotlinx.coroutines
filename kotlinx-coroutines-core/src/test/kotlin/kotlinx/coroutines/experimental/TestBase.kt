package kotlinx.coroutines.experimental

import org.junit.After
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference

open class TestBase {
    var actionIndex = AtomicInteger()
    var finished = AtomicBoolean()
    var error = AtomicReference<Throwable>()

    fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    fun expectUnreached() {
        throw IllegalStateException("Should not be reached").also { error.compareAndSet(null, it) }
    }

    fun finish(index: Int) {
        expect(index)
        finished.set(true)
    }

    @After
    fun onCompletion() {
        error.get()?.let { throw it }
        check(finished.get()) { "Expecting that 'finish(...)' was invoked, but it was not" }
    }

}