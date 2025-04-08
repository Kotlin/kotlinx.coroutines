package kotlinx.coroutines

import kotlinx.coroutines.internal.CommonThreadLocal
import kotlinx.coroutines.internal.Symbol
import kotlinx.coroutines.internal.commonThreadLocal
import kotlinx.coroutines.testing.*
import kotlin.coroutines.coroutineContext
import kotlin.test.*

@Suppress("RedundantAsync")
class ThreadLocalTest : TestBase() {
    private val stringThreadLocal = commonThreadLocal<String?>(Symbol("ThreadLocalTest#stringThreadLocal"))
    private val intThreadLocal = commonThreadLocal<Int?>(Symbol("ThreadLocalTest#intThreadLocal"))
    private val executor = newFixedThreadPoolContext(1, "threadLocalTest")

    @AfterTest
    fun tearDown() {
        executor.close()
    }

    @Test
    fun testThreadLocal() = runTest {
        assertNull(stringThreadLocal.get())
        assertFalse(stringThreadLocal.isPresent())
        val deferred = async(Dispatchers.Default + stringThreadLocal.asCtxElement("value")) {
            assertEquals("value", stringThreadLocal.get())
            assertTrue(stringThreadLocal.isPresent())
            withContext(executor) {
                assertTrue(stringThreadLocal.isPresent())
                assertFailsWith<IllegalStateException> { intThreadLocal.ensurePresent() }
                assertEquals("value", stringThreadLocal.get())
            }
            assertTrue(stringThreadLocal.isPresent())
            assertEquals("value", stringThreadLocal.get())
        }

        assertNull(stringThreadLocal.get())
        deferred.await()
        assertNull(stringThreadLocal.get())
        assertFalse(stringThreadLocal.isPresent())
    }

    @Test
    fun testThreadLocalInitialValue() = runTest {
        intThreadLocal.set(42)
        assertFalse(intThreadLocal.isPresent())
        val deferred = async(Dispatchers.Default + intThreadLocal.asCtxElement(239)) {
            assertEquals(239, intThreadLocal.get())
            withContext(executor) {
                intThreadLocal.ensurePresent()
                assertEquals(239, intThreadLocal.get())
            }
            assertEquals(239, intThreadLocal.get())
        }

        deferred.await()
        assertEquals(42, intThreadLocal.get())
    }

    @Test
    fun testMultipleThreadLocals() = runTest {
        stringThreadLocal.set("test")
        intThreadLocal.set(314)

        val deferred = async(Dispatchers.Default
                + intThreadLocal.asCtxElement(value = 239) + stringThreadLocal.asCtxElement(value = "pew")) {
            assertEquals(239, intThreadLocal.get())
            assertEquals("pew", stringThreadLocal.get())

            withContext(executor) {
                assertEquals(239, intThreadLocal.get())
                assertEquals("pew", stringThreadLocal.get())
                intThreadLocal.ensurePresent()
                stringThreadLocal.ensurePresent()
            }

            assertEquals(239, intThreadLocal.get())
            assertEquals("pew", stringThreadLocal.get())
        }

        deferred.await()
        assertEquals(314, intThreadLocal.get())
        assertEquals("test", stringThreadLocal.get())
    }

    @Test
    fun testConflictingThreadLocals() = runTest {
        intThreadLocal.set(42)

        val deferred = GlobalScope.async(intThreadLocal.asCtxElement(1)) {
            assertEquals(1, intThreadLocal.get())

            withContext(executor + intThreadLocal.asCtxElement(42)) {
                assertEquals(42, intThreadLocal.get())
            }

            assertEquals(1, intThreadLocal.get())

            val deferred = async(intThreadLocal.asCtxElement(53)) {
                assertEquals(53, intThreadLocal.get())
            }

            deferred.await()
            assertEquals(1, intThreadLocal.get())

            val deferred2 = GlobalScope.async(executor) {
                assertNull(intThreadLocal.get())
            }

            deferred2.await()
            assertEquals(1, intThreadLocal.get())
        }

        deferred.await()
        assertEquals(42, intThreadLocal.get())
    }

    @Test
    fun testWritesLostOnSuspensions() = runTest {
        withContext(intThreadLocal.asCtxElement(1)) {
            assertEquals(1, intThreadLocal.get())
            intThreadLocal.set(5)
            yield()
            assertEquals(1, intThreadLocal.get())
        }
    }

    @Test
    fun testThreadLocalModification() = runTest {
        stringThreadLocal.set("main")

        val deferred = async(Dispatchers.Default
                + stringThreadLocal.asCtxElement("initial")) {
            assertEquals("initial", stringThreadLocal.get())

            stringThreadLocal.set("overridden") // <- this value is not reflected in the context, so it's not restored

            withContext(executor + stringThreadLocal.asCtxElement("ctx")) {
                assertEquals("ctx", stringThreadLocal.get())
            }

            val deferred = async(stringThreadLocal.asCtxElement("async")) {
                assertEquals("async", stringThreadLocal.get())
            }

            deferred.await()
            assertEquals("initial", stringThreadLocal.get()) // <- not restored
        }

        deferred.await()
        assertFalse(stringThreadLocal.isPresent())
        assertEquals("main", stringThreadLocal.get())
    }



    private data class Counter(var cnt: Int)
    private val myCounterLocal = commonThreadLocal<Counter>(Symbol("ThreadLocalTest#myCounterLocal"))

    @Test
    fun testThreadLocalModificationMutableBox() = runTest {
        myCounterLocal.set(Counter(42))

        val deferred = async(Dispatchers.Default
                + myCounterLocal.asCtxElement(Counter(0))) {
            assertEquals(0, myCounterLocal.get().cnt)

            // Mutate
            myCounterLocal.get().cnt = 71

            withContext(executor + myCounterLocal.asCtxElement(Counter(-1))) {
                assertEquals(-1, myCounterLocal.get().cnt)
                ++myCounterLocal.get().cnt
            }

            val deferred = async(myCounterLocal.asCtxElement(Counter(31))) {
                assertEquals(31, myCounterLocal.get().cnt)
                ++myCounterLocal.get().cnt
            }

            deferred.await()
            assertEquals(71, myCounterLocal.get().cnt)
        }

        deferred.await()
        assertEquals(42, myCounterLocal.get().cnt)
    }

    @Test
    fun testWithContext() = runTest {
        expect(1)
        newSingleThreadContext("withContext").use {
            val data = 42
            GlobalScope.async(Dispatchers.Default + intThreadLocal.asCtxElement(42)) {

                assertEquals(data, intThreadLocal.get())
                expect(2)

                GlobalScope.async(it + intThreadLocal.asCtxElement(31)) {
                    assertEquals(31, intThreadLocal.get())
                    expect(3)
                }.await()

                withContext(it + intThreadLocal.asCtxElement(2)) {
                    assertEquals(2, intThreadLocal.get())
                    expect(4)
                }

                GlobalScope.async(it) {
                    assertNull(intThreadLocal.get())
                    expect(5)
                }.await()

                expect(6)
            }.await()
        }

        finish(7)
    }

    @Test
    fun testScope() = runTest {
        intThreadLocal.set(42)
        newSingleThreadContext("testScope").use {
            GlobalScope.async(it) {
                assertNull(intThreadLocal.get())
            }.await()

            GlobalScope.async(it + intThreadLocal.asCtxElement()) {
                assertEquals(42, intThreadLocal.get())
            }.await()
        }
    }

    @Test
    fun testMissingThreadLocal() = runTest {
        assertFailsWith<IllegalStateException> { stringThreadLocal.ensurePresent() }
        assertFailsWith<IllegalStateException> { intThreadLocal.ensurePresent() }
    }
}

internal suspend inline fun CommonThreadLocal<*>.isPresent(): Boolean =
    coroutineContext[CommonThreadLocalKey(this)] !== null

internal suspend inline fun CommonThreadLocal<*>.ensurePresent(): Unit =
    check(isPresent()) { "ThreadLocal $this is missing from context $coroutineContext" }
