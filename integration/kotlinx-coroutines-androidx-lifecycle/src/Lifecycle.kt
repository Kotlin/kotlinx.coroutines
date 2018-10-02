package kotlinx.coroutines.experimental.guava

import androidx.lifecycle.GenericLifecycleObserver
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.Lifecycle.Event.ON_DESTROY
import androidx.lifecycle.LifecycleOwner
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Dispatchers
import kotlinx.coroutines.experimental.Job

fun Lifecycle.createJob(cancelEvent: Lifecycle.Event = ON_DESTROY): Job = Job().also { job ->
    addObserver(object : GenericLifecycleObserver {
        override fun onStateChanged(source: LifecycleOwner?, event: Lifecycle.Event) {
            if (event == cancelEvent) {
                removeObserver(this)
                job.cancel()
            }
        }
    })
}

private val lifecycleJobs = mutableMapOf<Lifecycle, Job>()

val Lifecycle.job: Job
    get() = lifecycleJobs[this] ?: createJob().also {
        lifecycleJobs[this] = it
        it.invokeOnCompletion { _ -> lifecycleJobs -= this }
    }
private val lifecycleCoroutineScopes = mutableMapOf<Lifecycle, CoroutineScope>()

val Lifecycle.coroutineScope: CoroutineScope
    get() = lifecycleCoroutineScopes[this] ?: createJob().let {
        val newScope = CoroutineScope(it + Dispatchers.Main)
        lifecycleCoroutineScopes[this] = newScope
        it.invokeOnCompletion { _ -> lifecycleCoroutineScopes -= this }
        newScope
    }

inline val LifecycleOwner.coroutineScope get() = lifecycle.coroutineScope

fun Lifecycle.createScope(cancelEvent: Lifecycle.Event): CoroutineScope {
    return CoroutineScope(createJob(cancelEvent) + Dispatchers.Main)
}
