/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.linearizability

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.strategy.stress.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.test.*

internal data class Snapshot(val elements: List<Int>, val isClosed: Boolean) {
    constructor(q: LockFreeTaskQueue<Int>) : this(q.map { it }, q.isClosed())
}

@OpGroupConfig.OpGroupConfigs(OpGroupConfig(name = "consumer", nonParallel = true))
@Param(name = "value", gen = IntGen::class, conf = "1:3")
class SCLockFreeTaskQueueLCStressTest : LockFreeTaskQueueLCTestBase() {
    private val q: LockFreeTaskQueue<Int> = LockFreeTaskQueue(singleConsumer = true)

    @Operation
    fun close() = q.close()

    @Operation
    fun addLast(@Param(name = "value") value: Int) = q.addLast(value)

    /**
     * Note that removeFirstOrNull is not linearizable w.r.t. to addLast, so here
     * we test only linearizability of close.
     */
//    @Operation(group = "consumer")
//    fun removeFirstOrNull() = q.removeFirstOrNull()

    @Test
    fun testSC() = linTest()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as SCLockFreeTaskQueueLCStressTest

        return Snapshot(q) == Snapshot(other.q)
    }

    override fun hashCode(): Int = Snapshot(q).hashCode()
}

@Param(name = "value", gen = IntGen::class, conf = "1:3")
class MCLockFreeTaskQueueLCStressTest : LockFreeTaskQueueLCTestBase() {
    private val q: LockFreeTaskQueue<Int> = LockFreeTaskQueue(singleConsumer = false)

    @Operation
    fun close() = q.close()

    @Operation
    fun addLast(@Param(name = "value") value: Int) = q.addLast(value)

    /**
     * Note that removeFirstOrNull is not linearizable w.r.t. to addLast, so here
     * we test only linearizability of close.
     */
//    @Operation(group = "consumer")
//    fun removeFirstOrNull() = q.removeFirstOrNull()

    @Test
    fun testMC() = linTest()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as MCLockFreeTaskQueueLCStressTest

        return Snapshot(q) == Snapshot(other.q)
    }

    override fun hashCode(): Int = Snapshot(q).hashCode()
}

open class LockFreeTaskQueueLCTestBase : TestBase() {
    fun linTest() {
        val options = StressOptions()
            .iterations(100 * stressTestMultiplierSqrt)
            .invocationsPerIteration(1000 * stressTestMultiplierSqrt)
            .threads(2)
        LinChecker.check(this::class.java, options)
    }
}