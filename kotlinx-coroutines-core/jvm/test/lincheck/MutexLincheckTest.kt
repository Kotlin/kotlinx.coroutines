/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")
package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*

@Param(name = "owner", gen = IntGen::class, conf = "0:2")
class MutexLincheckTest : AbstractLincheckTest() {
    private val mutex = Mutex()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun tryLock(@Param(name = "owner") owner: Int) = mutex.tryLock(owner.asOwnerOrNull)

    // TODO: `lock()` with non-null owner is non-linearizable
    @Operation(promptCancellation = true)
    suspend fun lock() = mutex.lock(null)

    // TODO: `onLock` with non-null owner is non-linearizable
    // onLock may suspend in case of clause re-registration.
    @Operation(allowExtraSuspension = true, promptCancellation = true)
    suspend fun onLock() = select<Unit> { mutex.onLock(null) {} }

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun unlock(@Param(name = "owner") owner: Int) = mutex.unlock(owner.asOwnerOrNull)

    @Operation
    fun isLocked() = mutex.isLocked

    @Operation
    fun holdsLock(@Param(name = "owner") owner: Int) = mutex.holdsLock(owner)

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)

    // state[i] == true <=> mutex.holdsLock(i) with the only exception for 0 that specifies `null`.
    override fun extractState() = (1..2).map { mutex.holdsLock(it) } + mutex.isLocked

    private val Int.asOwnerOrNull get() = if (this == 0) null else this
}
