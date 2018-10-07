package kotlinx.coroutines.experimental.androidx.lifecycle

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

/**
 * Returns a [Job] that will be cancelled as soon as the [Lifecycle] reaches
 * [Lifecycle.State.DESTROYED] state.
 *
 * Note that this value is cached until the Lifecycle reaches the destroyed state.
 *
 * You can use this job for custom [CoroutineScope]s, or as a parent [Job].
 */
val Lifecycle.job: Job
    get() = lifecycleJobs[this] ?: createJob().also {
        if (it.isActive) {
            lifecycleJobs[this] = it
            it.invokeOnCompletion { _ -> lifecycleJobs -= this }
        }
    }
private val lifecycleCoroutineScopes = ConcurrentHashMap<Lifecycle, CoroutineScope>()

/**
 * Returns a [CoroutineScope] that uses [Dispatchers.Main] by default, and that is cancelled when
 * the [Lifecycle] reaches [Lifecycle.State.DESTROYED] state.
 *
 * Note that this value is cached until the Lifecycle reaches the destroyed state.
 */
val Lifecycle.coroutineScope: CoroutineScope
    get() = lifecycleCoroutineScopes[this] ?: job.let { job ->
        val newScope = CoroutineScope(job + Dispatchers.Main)
        if (job.isActive) {
            lifecycleCoroutineScopes[this] = newScope
            job.invokeOnCompletion { _ -> lifecycleCoroutineScopes -= this }
        }
        newScope
    }

/**
 * Calls [Lifecycle.coroutineScope] for the [Lifecycle] of this [LifecycleOwner].
 *
 * This is an inline property, just there for convenient usage from any [LifecycleOwner],
 * like FragmentActivity, AppCompatActivity, Fragment and LifecycleService.
 */
inline val LifecycleOwner.coroutineScope get() = lifecycle.coroutineScope

/**
 * Returns a [CoroutineScope] that uses [Dispatchers.Main] by default, and that is cancelled when
 * the [Lifecycle] encounters the passed [cancelEvent].
 */
fun Lifecycle.createScope(cancelEvent: Lifecycle.Event): CoroutineScope {
    if (cancelEvent == ON_DESTROY) return coroutineScope
    return CoroutineScope(createJob(cancelEvent) + Dispatchers.Main)
}
