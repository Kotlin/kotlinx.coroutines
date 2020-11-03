/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import kotlin.concurrent.*
import kotlin.test.*

/**
 * Concurrent test for [ConcurrentWeakMap] that tests put/get/remove from concurrent threads and is
 * arranged so that concurrent rehashing is also happening.
 */
class ConcurrentWeakMapOperationStressTest : TestBase() {
    private val nThreads = 10
    private val batchSize = 1000
    private val nSeconds = 3 * stressTestMultiplier

    private val count = atomic(0L)
    private val stop = atomic(false)

    private data class Key(val i: Long)

    @Test
    fun testOperations() {
        // We don't create queue here, because concurrent operations are enough to make it clean itself
        val m = ConcurrentWeakMap<Key, Long>()
        val threads = Array(nThreads) { index ->
            thread(start = false, name = "ConcurrentWeakMapOperationStressTest-$index") {
                var generationOffset = 0L
                while (!stop.value) {
                    val kvs = (generationOffset + batchSize * index until generationOffset + batchSize * (index + 1))
                        .associateBy({ Key(it) }, {  it * it })
                    generationOffset += batchSize * nThreads
                    for ((k, v) in kvs) {
                        assertEquals(null, m.put(k, v))
                    }
                    for ((k, v) in kvs) {
                        assertEquals(v, m[k])
                    }
                    for ((k, v) in kvs) {
                        assertEquals(v, m.remove(k))
                    }
                    for ((k, v) in kvs) {
                        assertEquals(null, m.get(k))
                    }
                    count.incrementAndGet()
                }
            }
        }
        val uncaughtExceptionHandler = Thread.UncaughtExceptionHandler { t, ex ->
            ex.printStackTrace()
            error("Error in thread $t", ex)
        }
        threads.forEach { it.uncaughtExceptionHandler = uncaughtExceptionHandler }
        threads.forEach { it.start() }
        var lastCount = -1L
        for (sec in 1..nSeconds) {
            Thread.sleep(1000)
            val count = count.value
            println("$sec: done $count batches")
            assertTrue(count > lastCount) // ensure progress
            lastCount = count
        }
        stop.value = true
        threads.forEach { it.join() }
        assertEquals(0, m.size)
    }
}