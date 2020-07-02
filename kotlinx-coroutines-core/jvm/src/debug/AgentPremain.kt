/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import kotlinx.coroutines.debug.internal.DebugProbesImpl
import sun.misc.*
import java.lang.instrument.*
import java.lang.instrument.ClassFileTransformer
import java.security.*
import android.annotation.*

/*
 * This class is loaded if and only if kotlinx-coroutines-core was used as -javaagent argument,
 * but Android complains anyway (java.lang.instrument.*), so we suppress all lint checks here
 */
@Suppress("unused")
@SuppressLint("all")
internal object AgentPremain {

    public var isInstalledStatically = false

    private val enableCreationStackTraces =
        System.getProperty("kotlinx.coroutines.debug.enable.creation.stack.trace")?.toBoolean()
            ?: DebugProbesImpl.enableCreationStackTraces

    @JvmStatic
    public fun premain(args: String?, instrumentation: Instrumentation) {
        isInstalledStatically = true
        instrumentation.addTransformer(DebugProbesTransformer)
        DebugProbesImpl.enableCreationStackTraces = enableCreationStackTraces
        DebugProbesImpl.install()
        installSignalHandler()
    }

    internal object DebugProbesTransformer : ClassFileTransformer {
        override fun transform(
            loader: ClassLoader,
            className: String,
            classBeingRedefined: Class<*>?,
            protectionDomain: ProtectionDomain,
            classfileBuffer: ByteArray?
        ): ByteArray? {
            if (className != "kotlin/coroutines/jvm/internal/DebugProbesKt") {
               return null
            }
            /*
             * DebugProbesKt.bin contains `kotlin.coroutines.jvm.internal.DebugProbesKt` class
             * with method bodies that delegate all calls directly to their counterparts in
             * kotlinx.coroutines.debug.DebugProbesImpl. This is done to avoid classfile patching
             * on the fly (-> get rid of ASM dependency).
             * You can verify its content either by using javap on it or looking at out integration test module.
             */
            isInstalledStatically = true
            return loader.getResourceAsStream("DebugProbesKt.bin").readBytes()
        }
    }

    private fun installSignalHandler() {
        try {
            Signal.handle(Signal("TRAP")) { // kill -5
                if (DebugProbesImpl.isInstalled) {
                    // Case with 'isInstalled' changed between this check-and-act is not considered
                    // a real debug probes use-case, thus is not guarded against.
                    DebugProbesImpl.dumpCoroutines(System.out)
                } else {
                    println("Cannot perform coroutines dump, debug probes are disabled")
                }
            }
        } catch (t: Throwable) {
            // Do nothing, signal cannot be installed, e.g. because we are on Windows
        }
    }
}
