/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.linearizability

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.SegmentBasedQueue
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.*

@Param(name = "value", gen = IntGen::class, conf = "1:5")
class SegmentQueueLCStressTest : VerifierState() {
    private val q = SegmentBasedQueue<Int>()

    @Operation
    fun add(@Param(name = "value") value: Int) {
        q.enqueue(value)
    }

    @Operation
    fun poll(): Int? = q.dequeue()

    override fun extractState(): Any {
        val elements = ArrayList<Int>()
        while (true) {
            val x = q.dequeue() ?: break
            elements.add(x)
        }

        return elements
    }

    @Test
    fun test() = LCStressOptionsDefault().check(this::class)
}