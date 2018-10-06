package kotlinx.coroutines.androidx.lifecycle

import androidx.lifecycle.GenericLifecycleObserver
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.Lifecycle.Event.*
import androidx.lifecycle.LifecycleOwner
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Dispatchers
import kotlinx.coroutines.experimental.Job
import java.util.concurrent.ConcurrentHashMap

/**
 * Creates a [Job] that will be cancelled when the [Lifecycle] encounters [cancelEvent]
 * (which defaults to [ON_DESTROY]).
 *
 * Note that [cancelEvent] supports only "**down**" events. That means that only [ON_PAUSE],
 * [ON_STOP] and [ON_DESTROY] are supported.
 *
 * If the [Lifecycle] is already destroyed, then the returned [Job] comes already cancelled.
 */
fun Lifecycle.createJob(cancelEvent: Lifecycle.Event = ON_DESTROY): Job {
    require(cancelEvent in allowedCancelEvents) { "$cancelEvent is forbidden for createJob(…)." }
    return Job().also { job ->
        if (currentState == Lifecycle.State.DESTROYED) job.cancel()
        else addObserver(object : GenericLifecycleObserver {
            override fun onStateChanged(source: LifecycleOwner?, event: Lifecycle.Event) {
                if (event == cancelEvent) {
                    removeObserver(this)
                    job.cancel()
                }
            }
        })
    }
}

private val allowedCancelEvents = arrayOf(ON_PAUSE, ON_STOP, ON_DESTROY)
private val lifecycleJobs = ConcurrentHashMap<Lifecycle, Job>()

val Lifecycle.job: Job
    get() = lifecycleJobs[this] ?: createJob().also {
        if (it.isActive) {
            lifecycleJobs[this] = it
            it.invokeOnCompletion { _ -> lifecycleJobs -= this }
        }
    }
private val lifecycleCoroutineScopes = ConcurrentHashMap<Lifecycle, CoroutineScope>()

val Lifecycle.coroutineScope: CoroutineScope
    get() = lifecycleCoroutineScopes[this] ?: job.let { job ->
        val newScope = CoroutineScope(job + Dispatchers.Main)
        if (job.isActive) {
            lifecycleCoroutineScopes[this] = newScope
            job.invokeOnCompletion { _ -> lifecycleCoroutineScopes -= this }
        }
        newScope
    }

inline val LifecycleOwner.coroutineScope get() = lifecycle.coroutineScope

fun Lifecycle.createScope(cancelEvent: Lifecycle.Event): CoroutineScope {
    return CoroutineScope(createJob(cancelEvent) + Dispatchers.Main)
}
