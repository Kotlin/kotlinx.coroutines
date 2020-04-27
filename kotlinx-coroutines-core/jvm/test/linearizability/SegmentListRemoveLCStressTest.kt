/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.linearizability

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.*


class SegmentListRemoveLCStressTest : VerifierState() {
    private val q = SegmentBasedQueue<Int>()
    private val segments: Array<OneElementSegment<Int>>

    init {
        segments = (0..5).map { q.enqueue(it)!! }.toTypedArray()
        q.enqueue(6)
    }

    @Operation
    fun removeSegment(@Param(gen = IntGen::class, conf = "1:5") index: Int) {
        segments[index].removeSegment()
    }

    override fun extractState() = segments.map { it.logicallyRemoved }

    @Validate
    fun checkAllRemoved() {
        q.checkHeadPrevIsCleaned()
        q.checkAllSegmentsAreNotLogicallyRemoved()
    }

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .actorsAfter(0)
        .check(this::class)
}