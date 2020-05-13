package kotlinx.coroutines.flow

import kotlinx.coroutines.Job
import kotlinx.coroutines.channels.TickerMode
import kotlinx.coroutines.channels.ticker
import java.util.*
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

/**
 * Creates a flow that produces the first item after the given initial delay and subsequent items with the
 * given delay between them.
 *
 * The resulting flow is a callback flow, which basically listens @see [Timer.schedule]
 *
 * This Flow stops producing elements immediately after [Job.cancel] invocation.
 *
 * @param delayMillis delay between each element in milliseconds.
 * @param initialDelayMillis delay after which the first element will be produced (it is equal to [delayMillis] by default) in milliseconds.
 * @param context context of the producing coroutine.
 * @param mode specifies behavior when elements are not received ([FIXED_PERIOD][TickerMode.FIXED_PERIOD] by default).
 */
public fun tickerFlow(
        delayMillis: Long,
        initialDelayMillis: Long = delayMillis,
        context: CoroutineContext = EmptyCoroutineContext,
        mode: TickerMode = TickerMode.FIXED_PERIOD
): Flow<Unit> {
    require(delayMillis > 0)
    return ticker(delayMillis, initialDelayMillis, context, mode).receiveAsFlow()
}