package kotlinx.coroutines.debug.internal

import kotlinx.coroutines.*
import java.io.*
import kotlin.coroutines.*

/**
 * Allows to statically install 'Debug Probes' at the known location
 * (kotlinx.coroutines.external.ExternalStaticDebugProbes).
 *
 * **Discussion**
 *
 * There are three methods of installing/engaging coroutines 'Debug Probes'
 *
 * 1) Dynamic Attach (using the 'kotlinx-coroutines-debug' module)
 *  This uses runtime byte-code alteration to replace the 'Debug Probes' straight from the kotlin-stdlib
 *
 * 2) Static Attach using an Agent
 *  This uses a java agent to replace the 'Debug Probes' from the kotlin-stdlib statically
 *
 * 3) ExternalStaticDebugProbes
 *  The kotlin-stdlib compiled against a class at
 *  `kotlinx.coroutines.external.ExternalStaticDebugProbes` which is not available at runtime, by default.
 *  If a class at this location is present, then the kotlin-stdlib will call into it.
 *
 *  ```kotlin
 *  package kotlinx.coroutines.external
 *  object ExternalStaticDebugProbes: AbstractStaticDebugProbes() {
 *      override fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> {
 *          // intercept
 *          // ...
 *
 *          // forward to debugger machinery
 *          return super.probeCoroutineCreated(completion)
 *      }
 *  }
 *  ```
 */
@Suppress("unused")
@DelicateCoroutinesApi
@ExperimentalCoroutinesApi
abstract class AbstractStaticDebugProbes {
    init {
        require(javaClass.name == "kotlinx.coroutines.external.ExternalStaticDebugProbes")
        AgentInstallationType.isInstalledStatically = true
        DebugProbesImpl.install()
    }

    open fun probeCoroutineResumed(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineResumed(frame)

    open fun probeCoroutineSuspended(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineSuspended(frame)

    open fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> =
        DebugProbesImpl.probeCoroutineCreated(completion)

    fun dumpCoroutines(out: PrintStream) {
        DebugProbesImpl.dumpCoroutines(out)
    }
}