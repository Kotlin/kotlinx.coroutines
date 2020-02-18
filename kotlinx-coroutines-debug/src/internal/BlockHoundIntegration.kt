@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
package kotlinx.coroutines.debug.internal

import reactor.blockhound.BlockHound
import kotlinx.coroutines.scheduling.*

internal object BlockHoundIntegration {

    init {
        BlockHound.builder()
            .addDynamicThreadPredicate { isSchedulerWorker(it) }
            .nonBlockingThreadPredicate { p -> p.or { thread -> enabled && mayNotBlock(thread) } }
            .install()
    }

    @Volatile
    private var enabled = false

    fun install() {
        enabled = true
    }

    fun uninstall() {
        enabled = false
    }

}
