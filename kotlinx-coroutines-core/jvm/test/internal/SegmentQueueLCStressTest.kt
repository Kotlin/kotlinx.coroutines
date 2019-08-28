/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import com.devexperts.dxlab.lincheck.LinChecker
import com.devexperts.dxlab.lincheck.annotations.Operation
import com.devexperts.dxlab.lincheck.annotations.Param
import com.devexperts.dxlab.lincheck.paramgen.IntGen
import com.devexperts.dxlab.lincheck.strategy.stress.StressCTest
import org.junit.Test

@StressCTest
class SegmentQueueLCStressTest {
    private val q = SegmentBasedQueue<Int>()

    @Operation
    fun add(@Param(gen = IntGen::class) x: Int) {
        q.enqueue(x)
    }

    @Operation
    fun poll(): Int? = q.dequeue()

    @Test
    fun test() {
        LinChecker.check(SegmentQueueLCStressTest::class.java)
    }
}