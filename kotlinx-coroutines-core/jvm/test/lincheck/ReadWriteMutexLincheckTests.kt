/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import kotlinx.coroutines.sync.ReadWriteMutexImpl.WriteUnlockPolicy.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import org.jetbrains.kotlinx.lincheck.verifier.*

class ReadWriteMutexLincheckTest : AbstractLincheckTest() {
    private val m = ReadWriteMutexImpl()
    private val readLockAcquired = IntArray(6)
    private val writeLockAcquired = BooleanArray(6)

    @Operation(allowExtraSuspension = true, promptCancellation = false)
    suspend fun readLock(@Param(gen = ThreadIdGen::class) threadId: Int) {
        m.readLock()
        readLockAcquired[threadId]++
    }

    @Operation
    fun readUnlock(@Param(gen = ThreadIdGen::class) threadId: Int): Boolean {
        if (readLockAcquired[threadId] == 0) return false
        m.readUnlock()
        readLockAcquired[threadId]--
        return true
    }

    @Operation(allowExtraSuspension = true, promptCancellation = false)
    suspend fun writeLock(@Param(gen = ThreadIdGen::class) threadId: Int) {
        m.writeLock()
        assert(!writeLockAcquired[threadId]) {
            "The mutex is not reentrant, this `writeLock()` invocation had to suspend"
        }
        writeLockAcquired[threadId] = true
    }

    @Operation
    fun writeUnlock(@Param(gen = ThreadIdGen::class) threadId: Int, prioritizeWriters: Boolean): Boolean {
        if (!writeLockAcquired[threadId]) return false
        m.writeUnlock(if (prioritizeWriters) PRIORITIZE_WRITERS else PRIORITIZE_READERS)
        writeLockAcquired[threadId] = false
        return true
    }

    @StateRepresentation
    fun stateRepresentation() = m.stateRepresentation

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean) =
        actorsBefore(0)
        .actorsAfter(0)
        .sequentialSpecification(ReadWriteMutexLincheckTestSequential::class.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class ReadWriteMutexLincheckTestSequential : VerifierState() {
    private val m = ReadWriteMutexSequential()
    private val readLockAcquired = IntArray(6)
    private val writeLockAcquired = BooleanArray(6)

    fun tryReadLock(threadId: Int): Boolean =
        m.tryReadLock().also { success ->
            if (success) readLockAcquired[threadId]++
        }

    suspend fun readLock(threadId: Int) {
        m.readLock()
        readLockAcquired[threadId]++
    }

    fun readUnlock(threadId: Int): Boolean {
        if (readLockAcquired[threadId] == 0) return false
        m.readUnlock()
        readLockAcquired[threadId]--
        return true
    }

    fun tryWriteLock(threadId: Int): Boolean =
        m.tryWriteLock().also { success ->
            if (success) writeLockAcquired[threadId] = true
        }

    suspend fun writeLock(threadId: Int) {
        m.writeLock()
        writeLockAcquired[threadId] = true
    }

    fun writeUnlock(threadId: Int, prioritizeWriters: Boolean): Boolean {
        if (!writeLockAcquired[threadId]) return false
        m.writeUnlock(prioritizeWriters)
        writeLockAcquired[threadId] = false
        return true
    }

    override fun extractState() =
        "mutex=${m.state},rlaPerThread=${readLockAcquired.contentToString()},wlaPerThread=${writeLockAcquired.contentToString()}"
}

internal class ReadWriteMutexSequential {
    private var ar = 0
    private var wla = false
    private val wr = ArrayList<CancellableContinuation<Unit>>()
    private val ww = ArrayList<CancellableContinuation<Unit>>()

    fun tryReadLock(): Boolean {
        if (wla || ww.isNotEmpty()) return false
        ar++
        return true
    }

    suspend fun readLock() {
        if (wla || ww.isNotEmpty()) {
            suspendCancellableCoroutine<Unit> { cont ->
                wr += cont
                cont.invokeOnCancellation { wr -= cont }
            }
        } else {
            ar++
        }
    }

    fun readUnlock() {
        ar--
        if (ar == 0 && ww.isNotEmpty()) {
            wla = true
            val w = ww.removeAt(0)
            w.resume(Unit) { writeUnlock(true) }
        }
    }

    fun tryWriteLock(): Boolean {
        if (wla || ar > 0) return false
        wla = true
        return true
    }

    suspend fun writeLock() {
        if (wla || ar > 0) {
            suspendCancellableCoroutine<Unit> { cont ->
                ww += cont
                cont.invokeOnCancellation {
                    ww -= cont
                    if (!wla && ww.isEmpty()) {
                        ar += wr.size
                        wr.forEach { it.resume(Unit) { readUnlock() } }
                        wr.clear()
                    }
                }
            }
        } else {
            wla = true
        }
    }

    fun writeUnlock(prioritizeWriters: Boolean) {
        if (ww.isNotEmpty() && prioritizeWriters) {
            val w = ww.removeAt(0)
            w.resume(Unit) { writeUnlock(prioritizeWriters) }
        } else {
            wla = false
            ar = wr.size
            wr.forEach { it.resume(Unit) { readUnlock() } }
            wr.clear()
        }
    }

    val state get() = "ar=$ar,wla=$wla,wr=${wr.size},ww=${ww.size}"
}

// This is an additional test to check the [ReadWriteMutex] synchronization contract.
internal class ReadWriteMutexCounterLincheckTest : AbstractLincheckTest() {
    private val m = ReadWriteMutexImpl()
    private var c = 0

    @Operation(allowExtraSuspension = true, promptCancellation = false)
    suspend fun inc(): Int = m.write { c++ }

    @Operation(allowExtraSuspension = true, promptCancellation = false)
    suspend fun get(): Int = m.read { c }

    @StateRepresentation
    fun stateRepresentation(): String = "$c + ${m.stateRepresentation}"

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)
        .actorsAfter(0)
        .sequentialSpecification(ReadWriteMutexCounterSequential::class.java)
}

@Suppress("RedundantSuspendModifier")
class ReadWriteMutexCounterSequential : VerifierState() {
    private var c = 0

    fun incViaTryLock() = c++
    suspend fun inc() = c++
    suspend fun get() = c

    override fun extractState() = c
}