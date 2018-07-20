package kotlinx.coroutines.experimental.slf4j

import kotlinx.coroutines.experimental.*
import org.junit.After
import org.junit.Before
import org.junit.Test
import org.slf4j.MDC
import kotlin.test.assertEquals
import kotlin.test.assertNull

class MDCContextTest : TestBase() {

    @Before
    fun setUp() {
        MDC.clear()
    }

    @After
    fun tearDown() {
        MDC.clear()
    }

    @Test
    fun mdcContextIsNotPassedByDefaultBetweenCoRoutines() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")

        launch {
            val mdcValue = MDC.get("myKey")
            check(mdcValue == null)
            expect(2)
        }.join()

        expect(3)

        finish(4)
    }

    @Test
    fun mdcContextCanBePassedBetweenCoRoutines() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")

        launch(MDCContext(DefaultDispatcher)) {
            val mdcValue = MDC.get("myKey")
            check(mdcValue == "myValue")
            expect(2)
        }.join()

        expect(3)

        finish(4)
    }

    @Test
    fun mdcContextNotNeededWhileOnMainThread() {
        MDC.put("myKey", "myValue")

        runBlocking {
            val mdcValue = MDC.get("myKey")

            assertEquals(mdcValue, "myValue")
        }
    }

    @Test
    fun mdcContextNeededWithOtherContext() {
        MDC.put("myKey", "myValue")

        runBlocking(MDCContext(DefaultDispatcher)) {
            val mdcValue = MDC.get("myKey")

            assertEquals(mdcValue, "myValue")
        }
    }

    @Test
    fun mdcContextMayBeEmpty() {
        runBlocking(MDCContext(DefaultDispatcher)) {
            val mdcValue = MDC.get("myKey")

            assertNull(mdcValue)
        }
    }
}