package kotlinx.coroutines.javafx

import javafx.beans.property.SimpleIntegerProperty
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.first
import org.junit.Before
import org.junit.Test

class JavaFxStressTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-", "InvokeLaterDispatcher")
    }

    @Test
    fun cancellationRaceStressTest() = runTest {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return@runTest // ignore test in headless environments
        }

        val integerProperty = SimpleIntegerProperty(0)
        val flow = integerProperty.asFlow()
        var i = 1
        val n = 1000 * stressTestMultiplier
        newSingleThreadContext("collector").use { pool ->
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
}