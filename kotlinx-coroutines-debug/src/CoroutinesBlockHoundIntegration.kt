@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
package kotlinx.coroutines.debug

import reactor.blockhound.BlockHound
import kotlinx.coroutines.scheduling.*
import reactor.blockhound.integration.*

@Suppress("UNUSED")
public class CoroutinesBlockHoundIntegration: BlockHoundIntegration {

    override fun applyTo(builder: BlockHound.Builder) {
        builder.addDynamicThreadPredicate { isSchedulerWorker(it) }
        builder.nonBlockingThreadPredicate { p -> p.or { mayNotBlock(it) } }
    }

}
