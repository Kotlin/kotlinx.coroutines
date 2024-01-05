package ordered.tests

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.Test
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.annotation.*
import org.robolectric.shadows.*
import kotlin.test.*


class InitMainDispatcherBeforeRobolectricTestRunner(testClass: Class<*>) : RobolectricTestRunner(testClass) {

    init {
        kotlin.runCatching {
            // touch Main, watch it burn
            GlobalScope.launch(Dispatchers.Main + CoroutineExceptionHandler { _, _ -> }) {  }
        }
    }
}

@Config(manifest = Config.NONE, sdk = [28])
@RunWith(InitMainDispatcherBeforeRobolectricTestRunner::class)
@LooperMode(LooperMode.Mode.LEGACY)
class CustomizedRobolectricTest : TestBase() {
    @Test
    fun testComponent()  {
        // Note that main is not set at all
        val component = TestComponent()
        checkComponent(component)
    }

    @Test
    fun testComponentAfterReset()  {
        // Note that main is not set at all
        val component = TestComponent()
        Dispatchers.setMain(Dispatchers.Unconfined)
        Dispatchers.resetMain()
        checkComponent(component)
    }


    private fun checkComponent(component: TestComponent) {
        val mainLooper = ShadowLooper.getShadowMainLooper()
        mainLooper.pause()
        component.launchSomething()
        assertFalse(component.launchCompleted)
        mainLooper.unPause()
        assertTrue(component.launchCompleted)
    }
}
