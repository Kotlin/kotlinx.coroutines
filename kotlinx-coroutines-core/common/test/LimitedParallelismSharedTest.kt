/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class LimitedParallelismSharedTest : TestBase() {

    @Test
    fun testLimitedDefault() = runTest {
        // Test that evaluates the very basic completion of tasks in limited dispatcher
        // for all supported platforms.
        // For more specific and concurrent tests, see 'concurrent' package.
        val view = Dispatchers.Default.limitedParallelism(1)
        val view2 = Dispatchers.Default.limitedParallelism(1)
        val j1 = launch(view) {
            while (true) {
                yield()
            }
        }
        val j2 = launch(view2) { j1.cancel() }
        joinAll(j1, j2)
    }

    @Test
    fun testParallelismSpec() {
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(0) }
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(-1) }
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(Int.MIN_VALUE) }
        Dispatchers.Default.limitedParallelism(Int.MAX_VALUE)
    }
}
