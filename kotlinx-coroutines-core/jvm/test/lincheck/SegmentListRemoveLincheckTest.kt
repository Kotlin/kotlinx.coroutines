/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*

class SegmentListRemoveLincheckTest : AbstractLincheckTest() {
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

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O = this
        .actorsBefore(0).actorsAfter(0)

    override fun extractState() = segments.map { it.logicallyRemoved }

    @Validate
    fun checkAllRemoved() {
        q.checkHeadPrevIsCleaned()
        q.checkAllSegmentsAreNotLogicallyRemoved()
    }

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}