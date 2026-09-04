package kotlinx.coroutines.external

import kotlinx.coroutines.debug.internal.AbstractStaticDebugProbes
import kotlin.coroutines.*

object ExternalStaticDebugProbes: AbstractStaticDebugProbes() {
    override fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> {
        return super.probeCoroutineCreated(completion)
    }
}