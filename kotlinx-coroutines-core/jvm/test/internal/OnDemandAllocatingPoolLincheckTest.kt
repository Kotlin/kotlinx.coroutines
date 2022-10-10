/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*

/**
 * Test that:
 * * All elements allocated in [OnDemandAllocatingPool] get returned when [close] is invoked.
 * * After reaching the maximum capacity, new elements are not added.
 * * After [close] is invoked, [OnDemandAllocatingPool.allocate] returns `false`.
 * * [OnDemandAllocatingPool.close] will return an empty list after the first invocation.
 */
abstract class OnDemandAllocatingPoolLincheckTest(maxCapacity: Int) : AbstractLincheckTest() {
    private val counter = atomic(0)
    private val pool = OnDemandAllocatingPool(maxCapacity = maxCapacity, create = {
        counter.getAndIncrement()
    })

    @Operation
    fun allocate(): Boolean = pool.allocate()

    @Operation
    fun close(): String = pool.close().sorted().toString()

    override fun extractState(): Any = pool.stateRepresentation()
}

abstract class OnDemandAllocatingSequentialPool(private val maxCapacity: Int) {
    var closed = false
    var elements = 0

    fun allocate() = if (closed) {
        false
    } else {
        if (elements < maxCapacity) {
            elements++
        }
        true
    }

    fun close(): String = if (closed) {
        emptyList()
    } else {
        closed = true
        (0 until elements)
    }.sorted().toString()
}

class OnDemandAllocatingPool3LincheckTest : OnDemandAllocatingPoolLincheckTest(3) {
    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        this.sequentialSpecification(OnDemandAllocatingSequentialPool3::class.java)
}

class OnDemandAllocatingSequentialPool3 : OnDemandAllocatingSequentialPool(3)
