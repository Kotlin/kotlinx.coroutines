package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*
import kotlin.test.*

/** These are tests that we want to fail. They are here so that, when the issue is fixed, their failure indicates that
 * everything is better now. */
class FailingTests {

    private var tearDownEntered = false

    @BeforeTest
    fun setUp() {
        Dispatchers.setMain(StandardTestDispatcher())
    }

    @AfterTest
    fun tearDown() {
        Dispatchers.resetMain()
        tearDownEntered = true
    }

    /** [TestDispatchersTest.testMainMocking]. */
    @Test
    fun testAfterTestIsConcurrent() = runTest {
        try {
            val mainAtStart = TestMainDispatcher.currentTestDispatcher ?: return@runTest
            withContext(Dispatchers.Default) {
                // context switch
            }
            assertNotSame(mainAtStart, TestMainDispatcher.currentTestDispatcher!!)
        } finally {
            assertTrue(tearDownEntered)
        }
    }
}
