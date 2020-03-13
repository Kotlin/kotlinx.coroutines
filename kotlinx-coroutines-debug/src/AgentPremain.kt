/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import net.bytebuddy.agent.*
import sun.misc.*
import java.lang.instrument.*

@Suppress("unused")
internal object AgentPremain {

    private val enableCreationStackTraces =
        System.getProperty("kotlinx.coroutines.debug.enable.creation.stack.trace")?.toBoolean()
            ?: DebugProbes.enableCreationStackTraces

    @JvmStatic
    public fun premain(args: String?, instrumentation: Instrumentation) {
        Installer.premain(args, instrumentation)
        DebugProbes.enableCreationStackTraces = enableCreationStackTraces
        DebugProbes.install()
        installSignalHandler()
    }

    private fun installSignalHandler() {
        try {
            Signal.handle(Signal("TRAP")) { // kill -5
                if (DebugProbes.isInstalled) {
                    // Case with 'isInstalled' changed between this check-and-act is not considered
                    // a real debug probes use-case, thus is not guarded against.
                    DebugProbes.dumpCoroutines()
                } else {
                    println("""Cannot perform coroutines dump, debug probes are disabled""")
                }
            }
        } catch (t: Throwable) {
            System.err.println("Failed to install signal handler: $t")
        }
    }
}
