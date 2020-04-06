package kotlinx.coroutines.flow

import kotlinx.coroutines.Job
import kotlinx.coroutines.channels.awaitClose
import java.util.*
import kotlin.concurrent.schedule

/**
 * Creates a flow that produces the first item after the given initial delay and subsequent items with the
 * given delay between them.
 *
 * The resulting flow is a callback flow, which basically listens @see [Timer.schedule]
 *
 * This Flow stops producing elements immediately after [Job.cancel] invocation.
 *
 * @param period period between each element in milliseconds.
 * @param initialDelay delay after which the first element will be produced (it is equal to [period] by default) in milliseconds.
 */
public fun tickerFlow(
        period: Long,
        initialDelay: Long = period
): Flow<Unit> = callbackFlow {
    require(period > 0)
    require(initialDelay > -1)

    val timer = Timer()
    timer.schedule(initialDelay, period) {
        offer(Unit)
    }

    awaitClose { timer.cancel() }
}

