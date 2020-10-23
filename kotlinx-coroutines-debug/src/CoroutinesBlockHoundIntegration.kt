@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.debug

import kotlinx.coroutines.scheduling.*
import reactor.blockhound.*
import reactor.blockhound.integration.*

@Suppress("UNUSED")
public class CoroutinesBlockHoundIntegration : BlockHoundIntegration {

    override fun applyTo(builder: BlockHound.Builder): Unit = with(builder) {
        // These classes use a lock internally, but should be safe to use.
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
        allowBlockingCallsInside("kotlinx.coroutines.channels.AbstractSendChannel", "sendSuspend")
        /* This method may block as part of its implementation, but is probably safe. We need to whitelist it so that
        it is possible to enqueue coroutines in contexts that use thread pools from other coroutines in a way that's not
        considered blocking. */
        allowBlockingCallsInside("java.util.concurrent.ScheduledThreadPoolExecutor", "execute")
        /* These files have fields that invoke service loaders. They are manually whitelisted; another approach could be
        to whitelist the operations performed by service loaders, as they can generally be considered safe. This was not
        done here because ServiceLoader has a large API surface, with some methods being hidden as implementation
        details (in particular, the implementation of its iterator is completely opaque). Relying on particular names
        being used in ServiceLoader's implementation would be brittle. */
        allowBlockingCallsInside("kotlinx.coroutines.reactive.ReactiveFlowKt", "<clinit>")
        allowBlockingCallsInside("kotlinx.coroutines.CoroutineExceptionHandlerImplKt", "<clinit>")
        /* These methods are from the reflection API. The API is big, so surely some other blocking calls will show up,
        but with these rules in place, at least some simple examples pass without problems. */
        allowBlockingCallsInside("kotlin.reflect.jvm.internal.impl.builtins.jvm.JvmBuiltInsPackageFragmentProvider", "findPackage")
        allowBlockingCallsInside("kotlin.reflect.jvm.internal.impl.resolve.OverridingUtil", "<clinit>")
        /* The predicates that define that BlockHound should only report blocking calls from threads that are part of
        the coroutine thread pool and currently execute a CPU-bound coroutine computation. */
        addDynamicThreadPredicate { isSchedulerWorker(it) }
        nonBlockingThreadPredicate { p -> p.or { mayNotBlock(it) } }
    }

}
