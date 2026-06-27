@file:Suppress("unused")
package kotlinx.coroutines.debug

import net.bytebuddy.*
import net.bytebuddy.agent.*
import net.bytebuddy.dynamic.loading.*

/*
 * This class is used reflectively from kotlinx-coroutines-core when this module is present in the classpath.
 * It is a substitute for service loading.
 */
internal class ByteBuddyDynamicAttach : Function1<Boolean, Unit> {
    override fun invoke(value: Boolean) {
        if (value) attach() else detach()
    }

    private fun attach() {
        ByteBuddyAgent.install(ByteBuddyAgent.AttachmentProvider.ForEmulatedAttachment.INSTANCE)
        dynamicTypeWithProbes.load(targetClassLoader, ClassReloadingStrategy.fromInstalledAgent())
    }

    private fun detach() {
        dynamicTypeWithoutProbes.load(targetClassLoader, ClassReloadingStrategy.fromInstalledAgent())
    }
}

private val targetClassLoader = Class.forName(classNameToOverride).classLoader

private const val classNameToOverride = "kotlin.coroutines.jvm.internal.DebugProbesKt"

private val dynamicTypeWithProbes by lazy {
    val classWithProbes = Class.forName("kotlinx.coroutines.debug.internal.DebugProbesKt")
    ByteBuddy()
        .redefine(classWithProbes)
        .name(classNameToOverride)
        .make()
}

private val dynamicTypeWithoutProbes by lazy {
    val classWithoutProbes = Class.forName("kotlinx.coroutines.debug.NoOpProbesKt")
    ByteBuddy()
        .redefine(classWithoutProbes)
        .name(classNameToOverride)
        .make()
}
