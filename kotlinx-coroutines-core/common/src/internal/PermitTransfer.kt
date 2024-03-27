package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlin.jvm.*

@JvmField
internal val PERMIT_ACQUIRE_PARK_NS = systemProp(
    "kotlinx.coroutines.permit.acquire.ns", 250L * 1000 * 1000 // 250ms
)

internal class PermitTransferStatus {
    private val status = atomic(false)
    fun check(): Boolean = status.value
    fun complete(): Boolean = status.compareAndSet(false, true)
}

internal expect class PermitTransfer constructor() {
    /**
     * [releasePermit] may throw
     */
    fun releaseFun(releasePermit: () -> Unit): () -> Unit

    /**
     * [tryAllocatePermit] and [deallocatePermit] must not throw
     */
    fun acquire(tryAllocatePermit: () -> Boolean, deallocatePermit: () -> Unit)
}

internal class BusyPermitTransfer {
    private val status = PermitTransferStatus()

    fun releaseFun(releasePermit: () -> Unit): () -> Unit = {
        if (status.complete()) {
            releasePermit()
        }
    }

    fun acquire(tryAllocatePermit: () -> Boolean, deallocatePermit: () -> Unit) {
        while (true) {
            if (status.check()) {
                return
            }
            if (tryAllocatePermit()) {
                if (!status.complete()) { // race: transfer was completed first by releaseFun
                    deallocatePermit()
                }
                return
            }
        }
    }
}