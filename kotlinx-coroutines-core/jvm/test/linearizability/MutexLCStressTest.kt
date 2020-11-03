/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")
package kotlinx.coroutines.linearizability

import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.*

class MutexLCStressTest : VerifierState() {
    private val mutex = Mutex()

    @Operation
    fun tryLock() = mutex.tryLock()

    @Operation
    suspend fun lock() = mutex.lock()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun unlock() = mutex.unlock()

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .check(this::class)

    override fun extractState() = mutex.isLocked
}