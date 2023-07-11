/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class UnconfinedTestDispatcherTest {

    @Test
    fun reproducer1742() {
        class ObservableValue<T>(initial: T) {
            var value: T = initial
                private set

            private val listeners = mutableListOf<(T) -> Unit>()

            fun set(value: T) {
                this.value = value
                listeners.forEach { it(value) }
            }

            fun addListener(listener: (T) -> Unit) {
                listeners.add(listener)
            }

            fun removeListener(listener: (T) -> Unit) {
                listeners.remove(listener)
            }
        }

        fun <T> ObservableValue<T>.observe(): Flow<T> =
            callbackFlow {
                val listener = { value: T ->
                    if (!isClosedForSend) {
                        trySend(value)
                    }
                }
                addListener(listener)
                listener(value)
                awaitClose { removeListener(listener) }
            }

        val intProvider = ObservableValue(0)
        val stringProvider = ObservableValue("")
        var data = Pair(0, "")
        val scope = CoroutineScope(UnconfinedTestDispatcher())
        scope.launch {
            combine(
                intProvider.observe(),
                stringProvider.observe()
            ) { intValue, stringValue -> Pair(intValue, stringValue) }
                .collect { pair ->
                    data = pair
                }
        }

        intProvider.set(1)
        stringProvider.set("3")
        intProvider.set(2)
        intProvider.set(3)

        scope.cancel()
        assertEquals(Pair(3, "3"), data)
    }

    @Test
    fun reproducer2082() = runTest {
        val subject1 = MutableStateFlow(1)
        val subject2 = MutableStateFlow("a")
        val values = mutableListOf<Pair<Int, String>>()

        val job = launch(UnconfinedTestDispatcher(testScheduler)) {
            combine(subject1, subject2) { intVal, strVal -> intVal to strVal }
                .collect {
                    delay(10000)
                    values += it
                }
        }

        subject1.value = 2
        delay(10000)
        subject2.value = "b"
        delay(10000)

        subject1.value = 3
        delay(10000)
        subject2.value = "c"
        delay(10000)
        delay(10000)
        delay(1)

        job.cancel()

        assertEquals(listOf(Pair(1, "a"), Pair(2, "a"), Pair(2, "b"), Pair(3, "b"), Pair(3, "c")), values)
    }

    @Test
    fun reproducer2405() = createTestResult {
        val dispatcher = UnconfinedTestDispatcher()
        var collectedError = false
        withContext(dispatcher) {
            flow { emit(1) }
                .combine(
                    flow<String> { throw IllegalArgumentException() }
                ) { int, string -> int.toString() + string }
                .catch { emit("error") }
                .collect {
                    assertEquals("error", it)
                    collectedError = true
                }
        }
        assertTrue(collectedError)
    }

    /** An example from the [UnconfinedTestDispatcher] documentation. */
    @Test
    fun testUnconfinedDispatcher() = runTest {
        val values = mutableListOf<Int>()
        val stateFlow = MutableStateFlow(0)
        val job = launch(UnconfinedTestDispatcher(testScheduler)) {
            stateFlow.collect {
                values.add(it)
            }
        }
        stateFlow.value = 1
        stateFlow.value = 2
        stateFlow.value = 3
        job.cancel()
        assertEquals(listOf(0, 1, 2, 3), values)
    }

    /** Tests that child coroutines are eagerly entered. */
    @Test
    fun testEagerlyEnteringChildCoroutines() = runTest(UnconfinedTestDispatcher()) {
        var entered = false
        val deferred = CompletableDeferred<Unit>()
        var completed = false
        launch {
            entered = true
            deferred.await()
            completed = true
        }
        assertTrue(entered) // `entered = true` already executed.
        assertFalse(completed) // however, the child coroutine then suspended, so it is enqueued.
        deferred.complete(Unit) // resume the coroutine.
        assertTrue(completed) // now the child coroutine is immediately completed.
    }

    /** Tests that the [TestCoroutineScheduler] used for [Dispatchers.Main] gets used by default. */
    @Test
    fun testSchedulerReuse() {
        val dispatcher1 = StandardTestDispatcher()
        Dispatchers.setMain(dispatcher1)
        try {
            val dispatcher2 = UnconfinedTestDispatcher()
            assertSame(dispatcher1.scheduler, dispatcher2.scheduler)
        } finally {
            Dispatchers.resetMain()
        }
    }

}
