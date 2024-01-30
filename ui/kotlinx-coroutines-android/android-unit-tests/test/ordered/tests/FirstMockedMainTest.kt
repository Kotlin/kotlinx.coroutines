package ordered.tests

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.*
import org.junit.Test
import java.lang.IllegalStateException
import kotlin.test.*

open class FirstMockedMainTest : TestBase() {

    @Before
    fun setUp() {
        Dispatchers.setMain(Dispatchers.Unconfined)
    }

    @After
    fun tearDown() {
        Dispatchers.resetMain()
    }

    @Test
    fun testComponent() {
        val component = TestComponent()
        component.launchSomething()
        assertTrue(component.launchCompleted)
    }

    @Test
    fun testFailureWhenReset() {
        Dispatchers.resetMain()
        val component = TestComponent()
        try {
            component.launchSomething()
            throw component.caughtException
        } catch (e: IllegalStateException) {
            assertTrue(e.message!!.contains("Dispatchers.setMain from kotlinx-coroutines-test"))
        }
    }
}
