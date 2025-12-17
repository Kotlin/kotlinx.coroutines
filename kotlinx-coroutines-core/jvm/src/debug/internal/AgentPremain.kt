package kotlinx.coroutines.debug.internal

import android.annotation.*
import org.codehaus.mojo.animal_sniffer.*
import sun.misc.*
import java.lang.IllegalStateException
import java.lang.instrument.*
import java.lang.instrument.ClassFileTransformer
import java.security.*

/*
 * This class is loaded if and only if kotlinx-coroutines-core was used as -javaagent argument,
 * but Android complains anyway (java.lang.instrument.*), so we suppress all lint checks here
 */
@Suppress("unused")
@SuppressLint("all")
@IgnoreJRERequirement // Never touched on Android
internal object AgentPremain {

    // This should be the first property to ensure the check happens first! Add new properties only below!
    private val dummy = checkIfStdlibIsAvailable()

    /**
     * This check ensures that kotlin-stdlib classes are loaded by the time AgentPremain is initialized;
     * otherwise the debug session would fail with `java.lang.NoClassDefFoundError: kotlin/Result`.
     */
    private fun checkIfStdlibIsAvailable() {
        try {
            Result.success(42)
        } catch (t: Throwable) {
            throw IllegalStateException("kotlinx.coroutines debug agent failed to load.\n" +
                "Please ensure that the Kotlin standard library is present in the classpath.\n" +
                "Alternatively, you can disable kotlinx.coroutines debug agent by removing `-javaagent=/path/kotlinx-coroutines-core.jar` from your VM arguments.\n" +
                t.cause
            )
        }
    }

    private val enableCreationStackTraces = runCatching {
        System.getProperty("kotlinx.coroutines.debug.enable.creation.stack.trace")?.toBoolean()
    }.getOrNull() ?: DebugProbesImpl.enableCreationStackTraces

    @JvmStatic
    @Suppress("UNUSED_PARAMETER")
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
