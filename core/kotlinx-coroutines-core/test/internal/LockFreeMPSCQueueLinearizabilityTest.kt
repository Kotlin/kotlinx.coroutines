/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.internal

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.*
import kotlin.test.*

@OpGroupConfigs(OpGroupConfig(name = "consumer", nonParallel = true))
@Param(name = "value", gen = IntGen::class, conf = "1:3")
class LockFreeMPSCQueueLinearizabilityTest : TestBase() {
    private lateinit var q: LockFreeMPSCQueue<Int>

    @Reset
    fun resetQueue() {
        q = LockFreeMPSCQueue()
    }

    @Operation
    fun close() = q.close()

    @Operation
    fun addLast(@Param(name = "value") value: Int) = q.addLast(value)

    /**
     * Note, that removeFirstOrNull is not linearizable w.r.t. to addLast, so here
     * we test only linearizability of close.
     */
//    @Operation(group = "consumer")
//    fun removeFirstOrNull() = q.removeFirstOrNull()

    @Test
    fun testLinearizability() {
        val options = StressOptions()
            .iterations(100 * stressTestMultiplierSqrt)
            .invocationsPerIteration(1000 * stressTestMultiplierSqrt)
            .addThread(1, 3)
            .addThread(1, 3)
            .addThread(1, 3)
        LinChecker.check(LockFreeMPSCQueueLinearizabilityTest::class.java, options)
    }
}