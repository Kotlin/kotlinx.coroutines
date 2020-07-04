/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")
package kotlinx.coroutines.linearizability

import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.*
import kotlin.reflect.*

abstract class SemaphoreLCStressTestBase(semaphore: Semaphore, val seqSpec: KClass<*>) {
    private val s = semaphore

    @Operation
    fun tryAcquire() = s.tryAcquire()

    @Operation
    suspend fun acquire() = s.acquire()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun release() = s.release()

    @Test
    fun test() = LCStressOptionsDefault()
        .actorsBefore(0)
        .sequentialSpecification(seqSpec.java)
        .check(this::class)
}

open class SemaphoreSequential(val permits: Int, val boundMaxPermits: Boolean) : VerifierState() {
    private var availablePermits = permits
    private val waiters = ArrayList<CancellableContinuation<Unit>>()

    fun tryAcquire(): Boolean {
        if (availablePermits <= 0) return false
        availablePermits--
        return true
    }

    suspend fun acquire() {
        if (tryAcquire()) return
        availablePermits--
        suspendAtomicCancellableCoroutine<Unit> { cont ->
            waiters.add(cont)
        }
    }

    fun release() {
        while (true) {
            check(availablePermits < permits || !boundMaxPermits)
            availablePermits++
            if (availablePermits > 0) return
            val w = waiters.removeAt(0)
            if (w.tryResume0(Unit)) return
        }
    }

    override fun extractState() = availablePermits.coerceAtLeast(0)
}

class SemaphoreSequential1 : SemaphoreSequential(1, true)
class Semaphore1LCStressTest : SemaphoreLCStressTestBase(Semaphore(1), SemaphoreSequential1::class)

class SemaphoreSequential2 : SemaphoreSequential(2, true)
class Semaphore2LCStressTest : SemaphoreLCStressTestBase(Semaphore(2), SemaphoreSequential2::class)

private fun <T> CancellableContinuation<T>.tryResume0(value: T): Boolean {
    val token = tryResume(value) ?: return false
    completeResume(token)
    return true
}