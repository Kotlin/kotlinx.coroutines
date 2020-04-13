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

abstract class SemaphoreLCStressTestBase(permits: Int) : VerifierState() {
    private val semaphore = Semaphore(permits)

    @Operation
    fun tryAcquire() = semaphore.tryAcquire()

    @Operation
    suspend fun acquire() = semaphore.acquire()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun release() = semaphore.release()

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .check(this::class)

    override fun extractState() = semaphore.availablePermits
}

class Semaphore1LCStressTest : SemaphoreLCStressTestBase(1)
class Semaphore2LCStressTest : SemaphoreLCStressTestBase(2)