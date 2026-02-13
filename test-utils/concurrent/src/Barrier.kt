@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlin.time.*

/**
 * Single-use barrier that blocks all participants until they all arrive.
 *
 * Adapted from kotlinx-atomicfu
 * https://github.com/Kotlin/kotlinx-atomicfu/blob/d09c2b07cd16b0b273bd94edaa4929acd2ec42bc/atomicfu/src/concurrentTest/kotlin/kotlinx/atomicfu/locks/BarrierTest.kt#L60
 */
class Barrier(private val parties: Int) {
    init {
        require(parties > 1)
    }

    private val count = atomic(0)
    private val waiters = atomicArrayOfNulls<Any?>(parties - 1)

    fun await() {
        val myIndex = count.getAndIncrement()
        check(myIndex < parties) {
            "No more than $parties threads can call await() throughout the lifetime of the barrier($parties)."
        }
        if (myIndex == parties - 1) {
            wakeUpEveryone()
            return
        }
        // else myIndex < parties - 1, enqueue and park
        val currentThread = ParkingSupport.currentThreadHandle()
        while (true) {
            val waiter = waiters[myIndex].value
            when {
                waiter === null -> waiters[myIndex].compareAndSet(waiter, currentThread)
                waiter is ParkingHandle -> ParkingSupport.park(Duration.INFINITE)
                waiter === FINISHED -> return
                else -> error("Unreachable")
            }
        }
    }

    fun checkTriggeredAndAllWokenUp() {
        for (i in 0..<parties - 1) {
            val waiter = waiters[i].value
            check(waiter === FINISHED) { "Thread #$i either never awaited or is still awaiting" }
        }
    }

    private fun wakeUpEveryone() {
        for (i in 0..<parties - 1) {
            while (true) {
                val waiter = waiters[i].value
                if (waiters[i].compareAndSet(waiter, FINISHED)) {
                    if (waiter is ParkingHandle) {
                        ParkingSupport.unpark(waiter)
                    } else {
                        check(waiter === null) { "Inconsistent state: expected null, got $waiter in the cell $i" }
                    }
                    break
                }
            }
        }
    }
}

private val FINISHED = Any()
