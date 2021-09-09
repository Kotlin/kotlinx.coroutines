package kotlinx.coroutines.javafx

import javafx.beans.property.SimpleIntegerProperty
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.first
import org.junit.*

class JavaFxStressTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-", "InvokeLaterDispatcher")
    }

    @get:Rule
    val pool = ExecutorRule(1)

    @Test
    fun testCancellationRace() = runTest {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return@runTest // ignore test in headless environments
        }

        val integerProperty = SimpleIntegerProperty(0)
        val flow = integerProperty.asFlow()
        var i = 1
        val n = 1000 * stressTestMultiplier
        repeat (n) {
            launch(pool) {
                flow.first()
            }
            withContext(Dispatchers.JavaFx) {
                integerProperty.set(i)
            }
            i += 1
        }
    }
}