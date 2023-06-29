/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug

import org.junit.Test
import kotlin.test.*

class StandardBuildersDebugTest : DebugTestBase() {

    @Test
    fun testBuildersAreMissingFromDumpByDefault() = runTest {
        val (b1, b2) = createBuilders()

        val coroutines = DebugProbes.dumpCoroutinesInfo()
        assertEquals(1, coroutines.size)
        assertTrue { b1.hasNext() && b2.hasNext() } // Don't let GC collect our coroutines until the test is complete
    }

    @Test
    fun testBuildersCanBeEnabled() = runTest {
        try {
            DebugProbes.ignoreCoroutinesWithEmptyContext = false
            val (b1, b2) = createBuilders()
            val coroutines = DebugProbes.dumpCoroutinesInfo()
            assertEquals(3, coroutines.size)
            assertTrue { b1.hasNext() && b2.hasNext() } // Don't let GC collect our coroutines until the test is complete
        } finally {
            DebugProbes.ignoreCoroutinesWithEmptyContext = true
        }
    }

    private fun createBuilders(): Pair<Iterator<Int>, Iterator<Int>> {
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
        return fromSequence to fromIterator
    }
}
