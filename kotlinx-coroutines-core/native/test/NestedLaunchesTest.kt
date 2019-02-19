package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.test.Test
import kotlin.test.assertTrue

class NestedLaunchesTest {
    private object Dispatcher : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean = true
        override fun dispatch(context: CoroutineContext, block: Runnable) { block.run() }
    }
    
    private var reached: Boolean = false

    private fun CoroutineScope.launchInContext(context: CoroutineContext) {
        launch(context) {
            reached = true
        }
    }
    private val dispatcher = Dispatcher + CoroutineExceptionHandler { _, e -> e.printStackTrace() }

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
