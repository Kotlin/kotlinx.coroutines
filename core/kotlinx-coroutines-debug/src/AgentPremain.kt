/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import net.bytebuddy.agent.*
import sun.misc.*
import java.lang.instrument.*

@Suppress("unused")
internal object AgentPremain {

    @JvmStatic
    public fun premain(args: String?, instrumentation: Instrumentation) {
        Installer.premain(args, instrumentation)
        DebugProbes.install()
        installSignalHandler()
    }

    private fun installSignalHandler() {
        Signal.handle(Signal("TRAP") ) { // kill -5
            DebugProbes.dumpCoroutines()
        }
    }
}
