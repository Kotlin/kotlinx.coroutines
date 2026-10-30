package kotlinx.coroutines.debug.internal

import android.annotation.*
import org.codehaus.mojo.animal_sniffer.*
import sun.misc.*
import java.lang.instrument.*
import java.lang.instrument.ClassFileTransformer
import java.security.*

/*
 * This class is loaded if and only if kotlinx-coroutines-core was used as -javaagent argument,
 * but Android complains anyway (java.lang.instrument.*), so we suppress all lint checks here
 */
@SuppressLint("all")
@IgnoreJRERequirement // Never touched on Android
internal object AgentPremain {
    private val enableCreationStackTraces = try {
        System.getProperty("kotlinx.coroutines.debug.enable.creation.stack.trace")?.toBoolean()!!
    } catch (_: Throwable) {
        DebugProbesImpl.enableCreationStackTraces
    }

    @JvmStatic
    fun premain(args: String?, instrumentation: Instrumentation) {
        AgentInstallationType.isInstalledStatically = true
        instrumentation.addTransformer(DebugProbesTransformer)
        DebugProbesImpl.enableCreationStackTraces = enableCreationStackTraces
        DebugProbesImpl.install()
        installSignalHandler()
    }

    internal object DebugProbesTransformer : ClassFileTransformer {
        override fun transform(
            loader: ClassLoader?,
            className: String,
            classBeingRedefined: Class<*>?,
            protectionDomain: ProtectionDomain,
            classfileBuffer: ByteArray?
        ): ByteArray? {
            if (loader == null || className != "kotlin/coroutines/jvm/internal/DebugProbesKt") {
               return null
            }
            /*
             * DebugProbesKt.bin contains `kotlin.coroutines.jvm.internal.DebugProbesKt` class
             * with method bodies that delegate all calls directly to their counterparts in
             * kotlinx.coroutines.debug.DebugProbesImpl. This is done to avoid classfile patching
             * on the fly (-> get rid of ASM dependency).
             * You can verify its content either by using javap on it or looking at out integration test module.
             */
            AgentInstallationType.isInstalledStatically = true
            val debugProbesResource = loader.getResourceAsStream("DebugProbesKt.bin")
                ?: error("Could not find DebugProbesKt.bin in the jar resources")
            return debugProbesResource.readBytes()
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
        } catch (_: Throwable) {
            // Do nothing, signal cannot be installed, e.g. because we are on Windows
        }
    }
}
