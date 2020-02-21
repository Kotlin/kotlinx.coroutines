package kotlinx.coroutines.javafx

import javafx.beans.property.SimpleIntegerProperty
import kotlinx.coroutines.TestBase
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.Before
import org.junit.Test
import kotlin.test.*


class JavaFxObservableAsFlowTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-", "InvokeLaterDispatcher")
    }

    @Test
    fun testFlowOrder() = runTest {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return@runTest // ignore test in headless environments
        }

        val integerProperty = SimpleIntegerProperty(0)
        val n = 1000
        val flow = integerProperty.asFlow().takeWhile { j -> j != n }
        newSingleThreadContext("setter").use { pool ->
            launch(pool) {
                for (i in 1..n) {
                    launch(Dispatchers.JavaFx) {
                        integerProperty.set(i)
                    }
                }
            }
            var i = -1
            flow.collect { j ->
                assertTrue(i < (j as Int), "Elements are neither repeated nor shuffled")
                i = j
            }
        }
    }

    @Test
    fun testConflation() = runTest {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return@runTest // ignore test in headless environments
        }

        withContext(Dispatchers.JavaFx) {
            val END_MARKER = -1
            val integerProperty = SimpleIntegerProperty(0)
            val flow = integerProperty.asFlow().takeWhile { j -> j != END_MARKER }
            launch {
                yield() // to subscribe to [integerProperty]
                yield() // send 0
                integerProperty.set(1)
                expect(3)
                yield() // send 1
                expect(5)
                integerProperty.set(2)
                for (i in (-100..-2)) {
                    integerProperty.set(i) // should be skipped due to conflation
                }
                integerProperty.set(3)
                expect(6)
                yield() // send 2 and 3
                integerProperty.set(-1)
            }
            expect(1)
            flow.collect { i ->
                when (i) {
                    0 -> expect(2)
                    1 -> expect(4)
                    2 -> expect(7)
                    3 -> expect(8)
                    else -> fail("i is $i")
                }
            }
            finish(9)
        }
    }

}
