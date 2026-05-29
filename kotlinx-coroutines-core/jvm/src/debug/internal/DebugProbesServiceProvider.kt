package kotlinx.coroutines.debug.internal

import java.lang.System
import kotlin.coroutines.Continuation
import kotlin.coroutines.jvm.DebugProbes

@OptIn(ExperimentalStdlibApi::class)
internal class DebugProbesServiceProvider : DebugProbes {
    init {
        AgentInstallationType.isInstalledStatically = true
        DebugProbesImpl.enableCreationStackTraces = System.getProperty("kotlinx.coroutines.debug.enable.creation.stack.trace")?.toBooleanStrictOrNull() == true
        DebugProbesImpl.install()
    }

    override fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> {
        return DebugProbesImpl.probeCoroutineCreated(completion)
    }

    override fun probeCoroutineResumed(frame: Continuation<*>) {
        DebugProbesImpl.probeCoroutineResumed(frame)
    }

    override fun probeCoroutineSuspended(frame: Continuation<*>) {
        DebugProbesImpl.probeCoroutineSuspended(frame)
    }
}
