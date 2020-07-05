/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.common.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import java.util.concurrent.Semaphore
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.*

@Warmup(iterations = 3, time = 500, timeUnit = TimeUnit.MICROSECONDS)
@Measurement(iterations = 5, time = 500, timeUnit = TimeUnit.MICROSECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class SemaphoreJVMBenchmark {
    @Param
    private var algo: SemaAlgo = SemaAlgo.`ASYNC + SIMPLE`

    @Param("1", "2", "4", "8")
    private var maxPermits: Int = 0

    @Param("1", "2", "4", "8") // local machine
//    @Param("1", "2", "4", "8", "16", "32", "64", "128") // dasquad
    private var parallelism: Int = 0

    @Benchmark
    fun semaphore() {
        val n = BATCH_SIZE / parallelism
        val semaphore = algo.create(maxPermits)
        val threads = ArrayList<Thread>(parallelism)
        repeat(parallelism) {
            threads += thread {
                repeat(n) {
                    semaphore.acquire()
                    doGeomDistrWork(WORK_INSIDE)
                    semaphore.release()
                    doGeomDistrWork(WORK_OUTSIDE)
                }
            }
        }
        threads.forEach { it.join() }
    }
}

private const val WORK_INSIDE = 80
private const val WORK_OUTSIDE = 40
private const val BATCH_SIZE = 1000000

enum class SemaAlgo(val create: (Int) -> Sema) {
    `Java ReentrantLock`({p -> SemaReentrantLock(p)}),
    `Java Semaphore`({p -> SemaJVM(p)}),
    `SYNC + SIMPLE`({p -> SemaSQS_Sync_Simple(p)}),
    `ASYNC + SIMPLE`({p -> SemaSQS_Async_Simple(p)}),
    `SYNC + SMART`({p -> SemaSQS_Sync_Smart(p)}),
    `ASYNC + SMART`({p -> SemaSQS_Async_Smart(p)})
}

interface Sema {
    fun acquire()
    fun release()
}

class SemaReentrantLock(permits: Int) : Sema {
    val l = ReentrantLock(true)
    override fun acquire() = l.lock()
    override fun release() = l.unlock()
}

class SemaJVM(permits: Int) : Sema {
    val s = Semaphore(permits, true)
    override fun acquire() = s.acquire()
    override fun release() = s.release()
}

class SemaSQS_Async_Simple(permits: Int): SegmentQueueSynchronizerJVM<Unit>(), Sema {
    override val resumeMode get() = ResumeMode.ASYNC
    override val cancellationMode: CancellationMode get() = CancellationMode.SIMPLE

    private val _availablePermits = atomic(permits)

    override fun acquire() {
        val p = _availablePermits.getAndDecrement()
        if (p > 0) return
        suspendCurThread()
    }

    override fun release() {
        while (true) {
            val p = _availablePermits.getAndIncrement()
            if (p >= 0) return
            if (resume(Unit)) return
        }
    }
}

class SemaSQS_Async_Smart(permits: Int): SegmentQueueSynchronizerJVM<Unit>(), Sema {
    override val resumeMode get() = ResumeMode.ASYNC
    override val cancellationMode: CancellationMode get() = CancellationMode.SMART_SYNC

    private val _availablePermits = atomic(permits)

    override fun acquire() {
        val p = _availablePermits.getAndDecrement()
        if (p > 0) return
        suspendCurThread()
    }

    override fun release() {
        val p = _availablePermits.getAndIncrement()
        if (p >= 0) return
        resume(Unit)
    }

    override fun onCancellation(): Boolean {
        val p = _availablePermits.getAndIncrement()
        return p < 0
    }
}

class SemaSQS_Sync_Smart(permits: Int): SegmentQueueSynchronizerJVM<Unit>(), Sema {
    override val resumeMode get() = ResumeMode.SYNC
    override val cancellationMode: CancellationMode get() = CancellationMode.SMART_SYNC

    private val _availablePermits = atomic(permits)

    override fun acquire() {
        while (true) {
            val p = _availablePermits.getAndDecrement()
            if (p > 0) return
            suspendCurThread() ?: continue
            return
        }
    }

    override fun release() {
        while (true) {
            val p = _availablePermits.getAndIncrement()
            if (p >= 0) return
            if (resume(Unit)) return
        }
    }

    override fun onCancellation(): Boolean {
        val p = _availablePermits.getAndIncrement()
        return p < 0
    }

    override fun returnValue(value: Unit) {
        release()
    }
}

class SemaSQS_Sync_Simple(permits: Int): SegmentQueueSynchronizerJVM<Unit>(), Sema {
    override val resumeMode get() = ResumeMode.SYNC
    override val cancellationMode: CancellationMode get() = CancellationMode.SIMPLE

    private val _availablePermits = atomic(permits)

    override fun acquire() {
        while (true) {
            val p = _availablePermits.getAndDecrement()
            if (p > 0) return
            suspendCurThread() ?: continue
            return
        }
    }

    override fun release() {
        while (true) {
            val p = _availablePermits.getAndIncrement()
            if (p >= 0) return
            if (resume(Unit)) return
        }
    }
}