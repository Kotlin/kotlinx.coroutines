package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.test.Test
import kotlin.test.assertTrue

class NestedLaunchesTest {
    private var reached: Boolean = false

    private fun CoroutineScope.launchInContext(context: CoroutineContext) {
        launch(context) {
            reached = true
        }
    }
    private val dispatcher = Dispatchers.Main + CoroutineExceptionHandler { _, e -> e.printStackTrace() }

    @Test
    fun testShouldNotThrowTce() {
        runBlocking {
            CoroutineScope(dispatcher).launch(dispatcher) {
                launchInContext(this.coroutineContext)
            }

            assertTrue(reached)
        }
    }
}
