package kotlinx.coroutines.androidx.lifecycle

import androidx.lifecycle.GenericLifecycleObserver
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.Lifecycle.State.INITIALIZED
import androidx.lifecycle.LifecycleOwner
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.SupervisorJob

/**
 * Returns a [CoroutineScope] that uses [Dispatchers.Main] by default, and that will be cancelled as
 * soon as this [Lifecycle] [currentState][Lifecycle.getCurrentState] is no longer
 * [at least][Lifecycle.State.isAtLeast] the passed [activeWhile] state.
 *
 * **Beware**: if the current state is lower than the passed [activeWhile] state, you'll get an
 * already cancelled scope.
 */
fun Lifecycle.createScope(activeWhile: Lifecycle.State): CoroutineScope {
    return CoroutineScope(createJob(activeWhile) + Dispatchers.Main)
}

/**
 * Creates a [SupervisorJob] that will be cancelled as soon as this [Lifecycle]
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
    return SupervisorJob().also { job ->
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
