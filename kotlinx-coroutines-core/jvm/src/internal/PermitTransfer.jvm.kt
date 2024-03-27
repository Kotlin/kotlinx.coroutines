package kotlinx.coroutines.internal

import java.util.concurrent.locks.*

internal actual class PermitTransfer {
    private val status = PermitTransferStatus()

    public actual fun releaseFun(releasePermit: () -> Unit): () -> Unit {
        val blockedThread = Thread.currentThread()
        return {
            if (status.complete()) {
                try {
                    releasePermit()
                } finally {
                    LockSupport.unpark(blockedThread)
                }
            }
        }
    }

    public actual fun acquire(tryAllocatePermit: () -> Boolean, deallocatePermit: () -> Unit) {
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
            LockSupport.parkNanos(
                PERMIT_ACQUIRE_PARK_NS // todo: not sure if it's needed at all, I mean that it is < Long.MAX_VALUE, but at least this way it's safer
            )
        }
    }
}