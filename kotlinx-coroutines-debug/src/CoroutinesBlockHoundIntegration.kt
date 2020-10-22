@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.debug

import kotlinx.coroutines.scheduling.*
import reactor.blockhound.*
import reactor.blockhound.integration.*

@Suppress("UNUSED")
public class CoroutinesBlockHoundIntegration : BlockHoundIntegration {

    override fun applyTo(builder: BlockHound.Builder): Unit = with(builder) {
        allowBlockingCallsInside("kotlinx.coroutines.channels.AbstractSendChannel", "sendSuspend")
        // these classes use a lock internally
        for (method in listOf(
            "pollInternal", "isEmpty", "isFull", "isClosedForReceive", "offerInternal", "offerSelectInternal",
            "enqueueSend", "pollInternal", "pollSelectInternal", "enqueueReceiveInternal", "onCancelIdempotent" ))
        {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ArrayChannel", method)
        }
        for (method in listOf("offerInternal", "offerSelectInternal", "updateHead")) {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ArrayBroadcastChannel", method)
        }
        for (method in listOf("checkOffer", "pollInternal", "pollSelectInternal")) {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ArrayBroadcastChannel\$Subscriber", method)
        }
        for (method in listOf("offerInternal", "offerSelectInternal", "pollInternal", "pollSelectInternal",
            "onCancelIdempotent"))
        {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ConflatedChannel", method)
        }
        // should be safe; used for sending tasks to a thread pool
        allowBlockingCallsInside("java.util.concurrent.ScheduledThreadPoolExecutor", "execute")
        addDynamicThreadPredicate { isSchedulerWorker(it) }
        nonBlockingThreadPredicate { p -> p.or { mayNotBlock(it) } }
    }

}
