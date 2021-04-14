/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.collections.ArrayList
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class SharedFlowStressTest : TestBase() {
    private val nProducers = 5
    private val nConsumers = 3
    private val nSeconds = 3 * stressTestMultiplier

    private lateinit var sf: MutableSharedFlow<Long>
    private lateinit var view: SharedFlow<Long>

    @get:Rule
    val producerDispatcher = ExecutorRule(nProducers)
    @get:Rule
    val consumerDispatcher = ExecutorRule(nConsumers)

    private val totalProduced = atomic(0L)
    private val totalConsumed = atomic(0L)

    @Test
    fun testStressReplay1() =
        testStress(1, 0)

    @Test
    fun testStressReplay1ExtraBuffer1() =
        testStress(1, 1)

    @Test
    fun testStressReplay2ExtraBuffer1() =
        testStress(2, 1)

    private fun testStress(replay: Int, extraBufferCapacity: Int) = runTest {
        sf = MutableSharedFlow(replay, extraBufferCapacity)
        view = sf.asSharedFlow()
        val jobs = ArrayList<Job>()
        jobs += List(nProducers) { producerIndex ->
            launch(producerDispatcher) {
                var cur = producerIndex.toLong()
                while (isActive) {
                    sf.emit(cur)
                    totalProduced.incrementAndGet()
                    cur += nProducers
                }
            }
        }
        jobs += List(nConsumers) { consumerIndex ->
            launch(consumerDispatcher) {
                while (isActive) {
                    view
                        .dropWhile { it % nConsumers != consumerIndex.toLong() }
                        .take(1)
                        .collect {
                            check(it % nConsumers == consumerIndex.toLong())
                            totalConsumed.incrementAndGet()
                        }
                }
            }
        }
        var lastProduced = 0L
        var lastConsumed = 0L
        for (sec in 1..nSeconds) {
            delay(1.seconds)
            val produced = totalProduced.value
            val consumed = totalConsumed.value
            println("$sec sec: produced = $produced; consumed = $consumed")
            assertNotEquals(lastProduced, produced)
            assertNotEquals(lastConsumed, consumed)
            lastProduced = produced
            lastConsumed = consumed
        }
        jobs.forEach { it.cancel() }
        jobs.forEach { it.join() }
        println("total: produced = ${totalProduced.value}; consumed = ${totalConsumed.value}")
    }
}