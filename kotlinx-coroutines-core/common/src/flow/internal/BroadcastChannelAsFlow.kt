package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*

/**
 * Accumulator for pending `onStart` callbacks when consuming a [BroadcastChannel] as a Flow.
 *
 * `BroadcastChannel.openSubscription()` must be called before values sent to the `BroadcastChannel`
 * will be forwarded to the [ReceiveChannel].  That subscription should only be made upon collection of the Flow,
 * so it is necessary to wait until that point to invoke any `onStart` callbacks.
 *
 * @param source The source `BroadcastChannel`
 * @param startAction The callback to be executed after subscription but before `emitAll()`
 */
internal class BroadcastChannelAsFlow<T>(
    private val source: BroadcastChannel<T>,
    private val startAction: suspend FlowCollector<T>.() -> Unit = {}
) : Flow<T> {

    fun update(
        action: suspend FlowCollector<T>.() -> Unit
    ): BroadcastChannelAsFlow<T> = BroadcastChannelAsFlow(source) {
        // new or upstream actions are invoked before old/downstream ones
        action()
        startAction()
    }

    override suspend fun collect(collector: FlowCollector<T>) {
        // open the ReceiveChannel before invoking the actions so that any sent values will be received
        val channel = source.openSubscription()
        collector.startAction()
        collector.emitAll(channel)
    }
}
