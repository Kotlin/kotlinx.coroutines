/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")
package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*

class MutexLincheckTest : AbstractLincheckTest() {
    private val mutex = Mutex()

    @Operation
    fun tryLock() = mutex.tryLock()

    @Operation(promptCancellation = true)
    suspend fun lock() = mutex.lock()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun unlock() = mutex.unlock()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()

    override fun extractState() = mutex.isLocked
}