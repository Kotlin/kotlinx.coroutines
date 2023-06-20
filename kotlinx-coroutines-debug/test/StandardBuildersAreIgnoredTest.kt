/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug

import org.junit.Test
import kotlin.test.*

class StandardBuildersAreIgnoredTest : DebugTestBase() {

    @Test
    fun testBuildersAreMissingFromDump() = runTest {
        val fromSequence = sequence {
            while (true) {
                yield(1)
            }
        }.iterator()

        val fromIterator = iterator {
            while (true) {
                yield(1)
            }
        }
        // Start coroutines
        fromIterator.hasNext()
        fromSequence.hasNext()

        val coroutines = DebugProbes.dumpCoroutinesInfo()
        assertEquals(1, coroutines.size)
    }
}
