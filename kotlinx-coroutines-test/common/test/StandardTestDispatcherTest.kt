/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class StandardTestDispatcherTest: OrderedExecutionTestBase() {

    private val scope = TestScope(StandardTestDispatcher())

    @BeforeTest
    fun init() {
        scope.asSpecificImplementation().enter()
    }

    @AfterTest
    fun cleanup() {
        scope.runCurrent()
        assertEquals(listOf(), scope.asSpecificImplementation().leave())
    }

    /** Tests that the [StandardTestDispatcher] follows an execution order similar to `runBlocking`. */
    @Test
    fun testFlowsNotSkippingValues() = scope.launch {
        // https://github.com/Kotlin/kotlinx.coroutines/issues/1626#issuecomment-554632852
        val list = flowOf(1).onStart { emit(0) }
            .combine(flowOf("A")) { int, str -> "$str$int" }
            .toList()
        assertEquals(list, listOf("A0", "A1"))
    }.void()

    /** Tests that each [launch] gets dispatched. */
    @Test
    fun testLaunchDispatched() = scope.launch {
        expect(1)
        launch {
            expect(3)
        }
        finish(2)
    }.void()

    /** Tests that dispatching is done in a predictable order and [yield] puts this task at the end of the queue. */
    @Test
    fun testYield() = scope.launch {
        expect(1)
        scope.launch {
            expect(3)
            yield()
            expect(6)
        }
        scope.launch {
            expect(4)
            yield()
            finish(7)
        }
        expect(2)
        yield()
        expect(5)
    }.void()

    /** Tests that the [TestCoroutineScheduler] used for [Dispatchers.Main] gets used by default. */
    @Test
    fun testSchedulerReuse() {
        val dispatcher1 = StandardTestDispatcher()
        Dispatchers.setMain(dispatcher1)
        try {
            val dispatcher2 = StandardTestDispatcher()
            assertSame(dispatcher1.scheduler, dispatcher2.scheduler)
        } finally {
            Dispatchers.resetMain()
        }
    }

}
