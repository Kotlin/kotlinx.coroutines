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

abstract class SemaphoreLincheckTestBase(permits: Int) : AbstractLincheckTest() {
    private val semaphore = SemaphoreImpl(permits = permits, acquiredPermits = 0)

    @Operation
    fun tryAcquire() = semaphore.tryAcquire()

    @Operation(promptCancellation = true, allowExtraSuspension = true)
    suspend fun acquire() = semaphore.acquire()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun release() = semaphore.release()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)

    override fun extractState() = semaphore.availablePermits

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class Semaphore1LincheckTest : SemaphoreLincheckTestBase(1)
class Semaphore2LincheckTest : SemaphoreLincheckTestBase(2)
