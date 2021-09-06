/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.atomic.*
import kotlin.test.*

@RunWith(Parameterized::class)
class LimitedParallelismStressTest(private val targetParallelism: Int) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(1, 2, 3, 4).map { arrayOf(it) }
    }

    @get:Rule
    val executor = ExecutorRule(targetParallelism * 2)
    private val iterations = 100_000 * stressTestMultiplier

    private val parallelism = AtomicInteger(0)

    private fun checkParallelism() {
        val value = parallelism.incrementAndGet()
        assertTrue { value <= targetParallelism }
        parallelism.decrementAndGet()
    }

    @Test
    fun testLimited() = runTest {
        val view = executor.limitedParallelism(targetParallelism)
        repeat(iterations) {
            launch(view) {
                checkParallelism()
            }
        }
    }

    @Test
    fun testUnconfined() = runTest {
        val view = Dispatchers.Unconfined.limitedParallelism(targetParallelism)
        repeat(iterations) {
            launch(executor) {
                withContext(view) {
                    checkParallelism()
                }
            }
        }
    }
}
