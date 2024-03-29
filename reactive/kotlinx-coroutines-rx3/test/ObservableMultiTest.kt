package kotlinx.coroutines.rx3

import kotlinx.coroutines.testing.*
import io.reactivex.rxjava3.core.*
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import java.io.*
import kotlin.test.*

/**
 * Test emitting multiple values with [rxObservable].
 */
class ObservableMultiTest : TestBase() {
    @Test
    fun testNumbers() {
        val n = 100 * stressTestMultiplier
        val observable = rxObservable {
            repeat(n) { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }


    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable {
            newCoroutineContext(coroutineContext)
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(Dispatchers.Default) {
                    val i = it
                    send(i)
                }
            }
            jobs.forEach { it.join() }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals(n, list.size)
            assertEquals((0 until n).toList(), list.sorted())
        }
    }

    @Test
    fun testConcurrentStressOnSend() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable<Int> {
            newCoroutineContext(coroutineContext)
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(Dispatchers.Default) {
                    val i = it
                    select<Unit> {
                        onSend(i) {}
                    }
                }
            }
            jobs.forEach { it.join() }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals(n, list.size)
            assertEquals((0 until n).toList(), list.sorted())
        }
    }

    @Test
    fun testIteratorResendUnconfined() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable(Dispatchers.Unconfined) {
            Observable.range(0, n).collect { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testIteratorResendPool() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable {
            Observable.range(0, n).collect { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val observable = rxObservable {
            send("O")
            throw IOException("K")
        }
        val single = rxSingle {
            var result = ""
            try {
                observable.collect { result += it }
            } catch(e: IOException) {
                result += e.message
            }
            result
        }
        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }
}
