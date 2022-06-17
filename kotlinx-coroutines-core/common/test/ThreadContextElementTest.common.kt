/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class ThreadContextElementCommonTest : TestBase() {

    interface TestThreadContextElement : ThreadContextElement<Int> {
        companion object Key : CoroutineContext.Key<TestThreadContextElement>
    }

    @Test
    fun updatesAndRestores() = runTest {
        expect(1)
        var update = 0
        var restore = 0
        val threadContextElement = object : TestThreadContextElement {
            override fun updateThreadContext(context: CoroutineContext): Int {
                update++
                return 0
            }

            override fun restoreThreadContext(context: CoroutineContext, oldState: Int) {
                restore++
            }

            override val key: CoroutineContext.Key<*>
                get() = TestThreadContextElement.Key
        }
        launch(Dispatchers.Unconfined + threadContextElement) {
            assertEquals(1, update)
            assertEquals(0, restore)
        }
        assertEquals(1, update)
        assertEquals(1, restore)
        finish(2)
    }

    class TestThreadContextIntElement(
        val update: () -> Int,
        val restore: (Int) -> Unit
    ) : TestThreadContextElement {
        override val key: CoroutineContext.Key<*>
            get() = TestThreadContextElement.Key

        override fun updateThreadContext(context: CoroutineContext): Int {
            return update()
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: Int) {
            restore(oldState)
        }
    }

    @Test
    fun twoCoroutinesUpdateAndRestore() = runTest {
        expect(1)
        var state = 0

        var updateA = 0
        var restoreA = 0
        var updateB = 0
        var restoreB = 0

        val lock = Job()
        println("Launch A")
        val jobA = launch(Dispatchers.Unconfined + TestThreadContextIntElement(
            update = {
                updateA++
                state = 10; 0
            },
            restore = {
                restoreA++
                state = it
            }
        )) {
            println("A started")
            assertEquals(1, updateA)
            assertEquals(10, state)
            println("A lock reached")
            lock.join()
            assertEquals(1, restoreA)
            assertEquals(1, updateB)
            assertEquals(1, restoreB)
            assertEquals(2, updateA)
            println("A resumed")
            assertEquals(10, state)
            println("A completes")
        }

        println("Launch B")
        launch(Dispatchers.Unconfined + TestThreadContextIntElement(
            update = {
                updateB++
                state = 20; 0
            },
            restore = {
                restoreB++
                state = it
            }
        )) {
            println("B started")
            assertEquals(1, updateB)
            assertEquals(20, state)
            println("B lock complete")
            lock.complete()
            println("B wait join A")
            jobA.join()
            assertEquals(2, updateB)
            assertEquals(1, restoreB)
            assertEquals(2, updateA)
            assertEquals(2, restoreA)
            println("B resumed")
            assertEquals(20, state)
            println("B completes")
        }

        println("All complete")
        assertEquals(0, state)

        finish(2)
    }
}
