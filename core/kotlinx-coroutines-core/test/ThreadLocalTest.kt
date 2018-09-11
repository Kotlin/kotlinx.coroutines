/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.*
import org.junit.Test
import kotlin.test.*

@Suppress("RedundantAsync")
class ThreadLocalTest : TestBase() {
    private val stringThreadLocal = ThreadLocal<String?>()
    private val intThreadLocal = ThreadLocal<Int?>()
    private val executor = newFixedThreadPoolContext(1, "threadLocalTest")

    @After
    fun tearDown() {
        executor.close()
    }

    @Test
    fun testThreadLocal() = runTest {
        assertNull(stringThreadLocal.get())
        val deferred = async(Dispatchers.Default + stringThreadLocal.asContextElement("value")) {
            assertEquals("value", stringThreadLocal.get())
            withContext(executor) {
                assertEquals("value", stringThreadLocal.get())
            }
            assertEquals("value", stringThreadLocal.get())
        }

        assertNull(stringThreadLocal.get())
        deferred.await()
        assertNull(stringThreadLocal.get())
    }

    @Test
    fun testThreadLocalInitialValue() = runTest {
        intThreadLocal.set(42)
        val deferred = async(Dispatchers.Default + intThreadLocal.asContextElement(239)) {
            assertEquals(239, intThreadLocal.get())
            withContext(executor) {
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
                + intThreadLocal.asContextElement(value = 239) + stringThreadLocal.asContextElement(value = "pew")) {
            assertEquals(239, intThreadLocal.get())
            assertEquals("pew", stringThreadLocal.get())

            withContext(executor) {
                assertEquals(239, intThreadLocal.get())
                assertEquals("pew", stringThreadLocal.get())
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

        val deferred = GlobalScope.async(intThreadLocal.asContextElement(1)) {
            assertEquals(1, intThreadLocal.get())

            withContext(executor + intThreadLocal.asContextElement(42)) {
                assertEquals(42, intThreadLocal.get())
            }

            assertEquals(1, intThreadLocal.get())

            val deferred = GlobalScope.async(coroutineContext + intThreadLocal.asContextElement(53)) {
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
    fun testThreadLocalModification() = runTest {
        stringThreadLocal.set("main")

        val deferred = async(Dispatchers.Default
                + stringThreadLocal.asContextElement("initial")) {
            assertEquals("initial", stringThreadLocal.get())

            stringThreadLocal.set("overridden") // <- this value is not reflected in the context, so it's not restored

            withContext(executor + stringThreadLocal.asContextElement("ctx")) {
                assertEquals("ctx", stringThreadLocal.get())
            }

            val deferred = async(coroutineContext + stringThreadLocal.asContextElement("async")) {
                assertEquals("async", stringThreadLocal.get())
            }

            deferred.await()
            assertEquals("initial", stringThreadLocal.get()) // <- not restored
        }

        deferred.await()
        assertEquals("main", stringThreadLocal.get())
    }



    private data class Counter(var cnt: Int)
    private val myCounterLocal = ThreadLocal<Counter>()

    @Test
    fun testThreadLocalModificationMutableBox() = runTest {
        myCounterLocal.set(Counter(42))

        val deferred = async(Dispatchers.Default
                + myCounterLocal.asContextElement(Counter(0))) {
            assertEquals(0, myCounterLocal.get().cnt)

            // Mutate
            myCounterLocal.get().cnt = 71

            withContext(executor + myCounterLocal.asContextElement(Counter(-1))) {
                assertEquals(-1, myCounterLocal.get().cnt)
                ++myCounterLocal.get().cnt
            }

            val deferred = async(coroutineContext + myCounterLocal.asContextElement(Counter(31))) {
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
            GlobalScope.async(Dispatchers.Default + intThreadLocal.asContextElement(42)) {

                assertSame(data, intThreadLocal.get())
                expect(2)

                GlobalScope.async(it + intThreadLocal.asContextElement(31)) {
                    assertEquals(31, intThreadLocal.get())
                    expect(3)
                }.await()

                withContext(it + intThreadLocal.asContextElement(2)) {
                    assertSame(2, intThreadLocal.get())
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
        val mainThread = Thread.currentThread()
        GlobalScope.async {
          assertNull(intThreadLocal.get())
            assertNotSame(mainThread, Thread.currentThread())
        }.await()

        GlobalScope.async(intThreadLocal.asContextElement()) {
            assertEquals(42, intThreadLocal.get())
            assertNotSame(mainThread, Thread.currentThread())
        }.await()
    }
}
