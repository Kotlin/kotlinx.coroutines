package kotlinx.coroutines.experimental.androidx.lifecycle

import androidx.lifecycle.GenericLifecycleObserver
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.Lifecycle.State.DESTROYED
import androidx.lifecycle.Lifecycle.State.INITIALIZED
import androidx.lifecycle.LifecycleOwner
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Dispatchers
import kotlinx.coroutines.experimental.Job
import java.util.concurrent.ConcurrentHashMap

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
 * Returns a [CoroutineScope] that uses [Dispatchers.Main] by default, and that will be cancelled as
 * soon as this [Lifecycle] [currentState][Lifecycle.getCurrentState] is no longer
 * [at least][Lifecycle.State.isAtLeast] the passed [activeWhile] state.
 *
 * **Beware**: if the current state is lower than the passed [activeWhile] state, you'll get an
 * already cancelled scope.
 */
fun Lifecycle.createScope(activeWhile: Lifecycle.State): CoroutineScope {
    if (activeWhile == DESTROYED) return coroutineScope
    return CoroutineScope(createJob(activeWhile) + Dispatchers.Main)
}

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

/**
 * Creates a [Job] that will be cancelled as soon as this [Lifecycle]
 * [currentState][Lifecycle.getCurrentState] is no longer [at least][Lifecycle.State.isAtLeast] the
 * passed [activeWhile] state.
 *
 * **Beware**: if the current state is lower than the passed [activeWhile] state, you'll get an
 * already cancelled job.
 */
fun Lifecycle.createJob(activeWhile: Lifecycle.State = INITIALIZED): Job {
    require(activeWhile != Lifecycle.State.DESTROYED) {
        "DESTROYED is a terminal state that is forbidden for createJob(…), to avoid leaks."
    }
    return Job().also { job ->
        if (!currentState.isAtLeast(activeWhile)) job.cancel()
        else addObserver(object : GenericLifecycleObserver {
            override fun onStateChanged(source: LifecycleOwner?, event: Lifecycle.Event) {
                if (!currentState.isAtLeast(activeWhile)) {
                    removeObserver(this)
                    job.cancel()
                }
            }
        })
    }
}

private val lifecycleJobs = ConcurrentHashMap<Lifecycle, Job>()
private val lifecycleCoroutineScopes = ConcurrentHashMap<Lifecycle, CoroutineScope>()
