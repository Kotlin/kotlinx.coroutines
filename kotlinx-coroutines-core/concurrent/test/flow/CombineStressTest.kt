/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class CombineStressTest : TestBase() {

    @Test
    fun testCancellation() = runTest {
        withContext(Dispatchers.Default + CoroutineExceptionHandler { _, _ -> expectUnreached() }) {
            flow {
                expect(1)
                repeat(1_000 * stressTestMultiplier) {
                    emit(it)
                }
            }.flatMapLatest {
                combine(flowOf(it), flowOf(it)) { arr -> arr[0] }
            }.collect()
            finish(2)
            reset()
        }
    }

    @Test
    fun testFailure() = runTest {
        val innerIterations = 100 * stressTestMultiplierSqrt
        val outerIterations = 10 * stressTestMultiplierSqrt
        withContext(Dispatchers.Default + CoroutineExceptionHandler { _, _ -> expectUnreached() }) {
            repeat(outerIterations) {
                try {
                    flow {
                        expect(1)
                        repeat(innerIterations) {
                            emit(it)
                        }
                    }.flatMapLatest {
                        combine(flowOf(it), flowOf(it)) { arr -> arr[0] }
                    }.onEach {
                        if (it >= innerIterations / 2) throw TestException()
                    }.collect()
                } catch (e: TestException) {
                    expect(2)
                }
                finish(3)
                reset()
            }
        }
    }
}
