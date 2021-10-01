/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.coroutines.*
import kotlin.test.*

class TestDispatchersTest {
    private val actionIndex = atomic(0)
    private val finished = atomic(false)

    private fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        println("expect($index), wasIndex=$wasIndex")
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    private fun finish(index: Int) {
        expect(index)
        check(!finished.getAndSet(true)) { "Should call 'finish(...)' at most once" }
    }

    @BeforeTest
    fun setUp() {
        Dispatchers.resetMain()
    }

    @Test
    fun testSelfSet() {
        assertFailsWith<IllegalArgumentException> { Dispatchers.setMain(Dispatchers.Main) }
    }

    @Test
    fun testImmediateDispatcher() = runBlockingTest {
        Dispatchers.setMain(ImmediateDispatcher())
        expect(1)
        withContext(Dispatchers.Main) {
            expect(3)
        }

        Dispatchers.setMain(RegularDispatcher())
        withContext(Dispatchers.Main) {
            expect(6)
        }

        finish(7)
    }

    private inner class ImmediateDispatcher : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean {
            expect(2)
            return false
        }

        override fun dispatch(context: CoroutineContext, block: Runnable) = throw RuntimeException("Shouldn't be reached")
    }

    private inner class RegularDispatcher : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean {
            expect(4)
            return true
        }

        override fun dispatch(context: CoroutineContext, block: Runnable) {
            expect(5)
            block.run()
        }
    }
}
