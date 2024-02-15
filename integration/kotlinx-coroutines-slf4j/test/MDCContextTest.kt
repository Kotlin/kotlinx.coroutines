package kotlinx.coroutines.slf4j

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.slf4j.*
import kotlin.coroutines.*
import kotlin.test.*

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
    fun testContextIsNotPassedByDefaultBetweenCoroutines() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")
        // Standalone launch
        GlobalScope.launch {
            assertNull(MDC.get("myKey"))
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testContextCanBePassedBetweenCoroutines() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")
        // Scoped launch with MDCContext element
        launch(MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
            expect(2)
        }.join()

        finish(3)
    }

    @Test
    fun testContextInheritance() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")
        withContext(MDCContext()) {
            MDC.put("myKey", "myValue2")
            // Scoped launch with inherited MDContext element
            launch(Dispatchers.Default) {
                assertEquals("myValue", MDC.get("myKey"))
                expect(2)
            }.join()

            finish(3)
        }
        assertEquals("myValue", MDC.get("myKey"))
    }

    @Test
    fun testContextPassedWhileOnMainThread() {
        MDC.put("myKey", "myValue")
        // No MDCContext element
        runBlocking {
            assertEquals("myValue", MDC.get("myKey"))
        }
    }

    @Test
    fun testContextCanBePassedWhileOnMainThread() {
        MDC.put("myKey", "myValue")
        runBlocking(MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
        }
    }

    @Test
    fun testContextNeededWithOtherContext() {
        MDC.put("myKey", "myValue")
        runBlocking(MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
        }
    }

    @Test
    fun testContextMayBeEmpty() {
        runBlocking(MDCContext()) {
            assertNull(MDC.get("myKey"))
        }
    }

    @Test
    fun testContextWithContext() = runTest {
        MDC.put("myKey", "myValue")
        val mainDispatcher = kotlin.coroutines.coroutineContext[ContinuationInterceptor]!!
        withContext(Dispatchers.Default + MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
            assertEquals("myValue", coroutineContext[MDCContext]?.contextMap?.get("myKey"))
            withContext(mainDispatcher) {
                assertEquals("myValue", MDC.get("myKey"))
            }
        }
    }

    /** Tests that the initially captured MDC context gets restored after suspension. */
    @Test
    fun testSuspensionsUndoingMdcContextUpdates() = runTest {
        MDC.put("a", "b")
        withContext(MDCContext()) {
            MDC.put("key", "value")
            assertEquals("b", MDC.get("a"))
            yield()
            assertNull(MDC.get("key"))
            assertEquals("b", MDC.get("a"))
        }
    }

    /** Tests capturing and restoring the MDC context. */
    @Test
    fun testRestoringMdcContext() = runTest {
        MDC.put("a", "b")
        val contextMap = withContext(MDCContext()) {
            MDC.put("key", "value")
            assertEquals("b", MDC.get("a"))
            withContext(MDCContext()) {
                assertEquals("value", MDC.get("key"))
                MDC.put("key2", "value2")
                assertEquals("value2", MDC.get("key2"))
                withContext(MDCContext()) {
                    yield()
                    MDC.getCopyOfContextMap()
                }
            }
        }
        MDC.setContextMap(contextMap)
        assertEquals("value2", MDC.get("key2"))
        assertEquals("value", MDC.get("key"))
        assertEquals("b", MDC.get("a"))
    }
}
