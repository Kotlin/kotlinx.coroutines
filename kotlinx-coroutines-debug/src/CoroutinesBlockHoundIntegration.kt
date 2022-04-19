/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.debug

import kotlinx.coroutines.scheduling.*
import reactor.blockhound.*
import reactor.blockhound.integration.*

public class CoroutinesBlockHoundIntegration : BlockHoundIntegration {

    override fun applyTo(builder: BlockHound.Builder): Unit = with(builder) {
        allowBlockingCallsInPrimitiveImplementations()
        allowBlockingWhenEnqueuingTasks()
        allowServiceLoaderInvocationsOnInit()
        allowBlockingCallsInReflectionImpl()
        allowBlockingCallsInDebugProbes()
        allowBlockingCallsInWorkQueue()
        // Stacktrace recovery cache is guarded by lock
        allowBlockingCallsInside("kotlinx.coroutines.internal.ExceptionsConstructorKt", "tryCopyException")
        /* The predicates that define that BlockHound should only report blocking calls from threads that are part of
        the coroutine thread pool and currently execute a CPU-bound coroutine computation. */
        addDynamicThreadPredicate { isSchedulerWorker(it) }
        nonBlockingThreadPredicate { p -> p.or { mayNotBlock(it) } }
    }

    /**
     * Allows blocking calls in various coroutine structures, such as flows and channels.
     *
     * They use locks in implementations, though only for protecting short pieces of fast and well-understood code, so
     * locking in such places doesn't affect the program liveness.
     */
    private fun BlockHound.Builder.allowBlockingCallsInPrimitiveImplementations() {
        allowBlockingCallsInJobSupport()
        allowBlockingCallsInThreadSafeHeap()
        allowBlockingCallsInFlow()
        allowBlockingCallsInChannels()
    }

    /**
     * Allows blocking inside [kotlinx.coroutines.JobSupport].
     */
    private fun BlockHound.Builder.allowBlockingCallsInJobSupport() {
        for (method in listOf("finalizeFinishingState", "invokeOnCompletion", "makeCancelling",
            "tryMakeCompleting"))
        {
            allowBlockingCallsInside("kotlinx.coroutines.JobSupport", method)
        }
    }

    /**
     * Allow blocking calls inside [kotlinx.coroutines.debug.internal.DebugProbesImpl].
     */
    private fun BlockHound.Builder.allowBlockingCallsInDebugProbes() {
        for (method in listOf("install", "uninstall", "hierarchyToString", "dumpCoroutinesInfo", "dumpDebuggerInfo",
            "dumpCoroutinesSynchronized", "updateRunningState", "updateState"))
        {
            allowBlockingCallsInside("kotlinx.coroutines.debug.internal.DebugProbesImpl", method)
        }
    }

    /**
     * Allow blocking calls inside [kotlinx.coroutines.scheduling.WorkQueue]
     */
    private fun BlockHound.Builder.allowBlockingCallsInWorkQueue() {
        /** uses [Thread.yield] in a benign way. */
        allowBlockingCallsInside("kotlinx.coroutines.scheduling.WorkQueue", "addLast")
    }

    /**
     * Allows blocking inside [kotlinx.coroutines.internal.ThreadSafeHeap].
     */
    private fun BlockHound.Builder.allowBlockingCallsInThreadSafeHeap() {
        for (method in listOf("clear", "peek", "removeFirstOrNull", "addLast")) {
            allowBlockingCallsInside("kotlinx.coroutines.internal.ThreadSafeHeap", method)
        }
        // [addLastIf] is only used in [EventLoop.common]. Users of [removeFirstIf]:
        allowBlockingCallsInside("kotlinx.coroutines.test.TestCoroutineDispatcher", "doActionsUntil")
        allowBlockingCallsInside("kotlinx.coroutines.test.TestCoroutineContext", "triggerActions")
    }

    private fun BlockHound.Builder.allowBlockingCallsInFlow() {
        allowBlockingCallsInsideStateFlow()
        allowBlockingCallsInsideSharedFlow()
    }

    /**
     * Allows blocking inside the implementation of [kotlinx.coroutines.flow.StateFlow].
     */
    private fun BlockHound.Builder.allowBlockingCallsInsideStateFlow() {
        allowBlockingCallsInside("kotlinx.coroutines.flow.StateFlowImpl", "updateState")
    }

    /**
     * Allows blocking inside the implementation of [kotlinx.coroutines.flow.SharedFlow].
     */
    private fun BlockHound.Builder.allowBlockingCallsInsideSharedFlow() {
        for (method in listOf("emitSuspend", "awaitValue", "getReplayCache", "tryEmit", "cancelEmitter",
            "tryTakeValue", "resetReplayCache"))
        {
            allowBlockingCallsInside("kotlinx.coroutines.flow.SharedFlowImpl", method)
        }
        for (method in listOf("getSubscriptionCount", "allocateSlot", "freeSlot")) {
            allowBlockingCallsInside("kotlinx.coroutines.flow.internal.AbstractSharedFlow", method)
        }
    }

    private fun BlockHound.Builder.allowBlockingCallsInChannels() {
        allowBlockingCallsInArrayChannel()
        allowBlockingCallsInBroadcastChannel()
        allowBlockingCallsInConflatedChannel()
    }

    /**
     * Allows blocking inside [kotlinx.coroutines.channels.ArrayChannel].
     */
    private fun BlockHound.Builder.allowBlockingCallsInArrayChannel() {
        for (method in listOf(
            "pollInternal", "isEmpty", "isFull", "isClosedForReceive", "offerInternal", "offerSelectInternal",
            "enqueueSend", "pollSelectInternal", "enqueueReceiveInternal", "onCancelIdempotent"))
        {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ArrayChannel", method)
        }
    }

    /**
     * Allows blocking inside [kotlinx.coroutines.channels.ArrayBroadcastChannel].
     */
    private fun BlockHound.Builder.allowBlockingCallsInBroadcastChannel() {
        for (method in listOf("offerInternal", "offerSelectInternal", "updateHead")) {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ArrayBroadcastChannel", method)
        }
        for (method in listOf("checkOffer", "pollInternal", "pollSelectInternal")) {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ArrayBroadcastChannel\$Subscriber", method)
        }
    }

    /**
     * Allows blocking inside [kotlinx.coroutines.channels.ConflatedChannel].
     */
    private fun BlockHound.Builder.allowBlockingCallsInConflatedChannel() {
        for (method in listOf("offerInternal", "offerSelectInternal", "pollInternal", "pollSelectInternal",
            "onCancelIdempotent", "isEmpty", "enqueueReceiveInternal"))
        {
            allowBlockingCallsInside("kotlinx.coroutines.channels.ConflatedChannel", method)
        }
    }

    /**
     * Allows blocking when enqueuing tasks into a thread pool.
     *
     * Without this, the following code breaks:
     * ```
     * withContext(Dispatchers.Default) {
     *     withContext(newSingleThreadContext("singleThreadedContext")) {
     *     }
     * }
     * ```
     */
    private fun BlockHound.Builder.allowBlockingWhenEnqueuingTasks() {
        /* This method may block as part of its implementation, but is probably safe. */
        allowBlockingCallsInside("java.util.concurrent.ScheduledThreadPoolExecutor", "execute")
    }

    /**
     * Allows instances of [java.util.ServiceLoader] being called.
     *
     * Each instance is listed separately; another approach could be to generally allow the operations performed by
     * service loaders, as they can generally be considered safe. This was not done here because ServiceLoader has a
     * large API surface, with some methods being hidden as implementation details (in particular, the implementation of
     * its iterator is completely opaque). Relying on particular names being used in ServiceLoader's implementation
     * would be brittle, so here we only provide clearance rules for some specific instances.
     */
    private fun BlockHound.Builder.allowServiceLoaderInvocationsOnInit() {
        allowBlockingCallsInside("kotlinx.coroutines.reactive.ReactiveFlowKt", "<clinit>")
        allowBlockingCallsInside("kotlinx.coroutines.CoroutineExceptionHandlerImplKt", "<clinit>")
        // not part of the coroutines library, but it would be nice if reflection also wasn't considered blocking
        allowBlockingCallsInside("kotlin.reflect.jvm.internal.impl.resolve.OverridingUtil", "<clinit>")
    }

    /**
     * Allows some blocking calls from the reflection API.
     *
     * The API is big, so surely some other blocking calls will show up, but with these rules in place, at least some
     * simple examples work without problems.
     */
    private fun BlockHound.Builder.allowBlockingCallsInReflectionImpl() {
        allowBlockingCallsInside("kotlin.reflect.jvm.internal.impl.builtins.jvm.JvmBuiltInsPackageFragmentProvider", "findPackage")
    }

}
