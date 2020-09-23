/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import junit.framework.Assert.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.*
import kotlin.concurrent.*

class ConcurrentWeakMapCollectionStressTest : TestBase() {
    private data class Key(val i: Int)
    private val nElements = 100_000 * stressTestMultiplier
    private val size = 100_000
    
    @Test
    fun testCollected() {
        // use very big arrays as values, we'll need a queue and a cleaner thread to handle them
        val m = ConcurrentWeakMap<Key, ByteArray>(weakRefQueue = true)
        val cleaner = thread(name = "ConcurrentWeakMapCollectionStressTest-Cleaner") {
            m.runWeakRefQueueCleaningLoopUntilInterrupted()
        }
        for (i in 1..nElements) {
            m.put(Key(i), ByteArray(size))
        }
        assertTrue(m.size < nElements) // some of it was collected for sure
        cleaner.interrupt()
        cleaner.join()
    }
}