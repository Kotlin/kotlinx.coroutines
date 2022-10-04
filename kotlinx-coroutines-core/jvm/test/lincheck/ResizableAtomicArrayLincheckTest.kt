/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.paramgen.*

@Param(name = "index", gen = IntGen::class, conf = "0:4")
@Param(name = "value", gen = IntGen::class, conf = "1:5")
@OpGroupConfig(name = "sync", nonParallel = true)
class ResizableAtomicArrayLincheckTest : AbstractLincheckTest() {
    private val a = ResizableAtomicArray<Int>(2)

    @Operation
    fun get(@Param(name = "index") index: Int): Int? = a[index]

    @Operation(group = "sync")
    fun set(@Param(name = "index") index: Int, @Param(name = "value") value: Int) {
        a.setSynchronized(index, value)
    }

    override fun extractState() = (0..4).map { a[it] }
}