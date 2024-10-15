package kotlinx.coroutines.debug.internal

/**
 * Object used to differentiate between agent installed statically or dynamically.
 * This is done in a separate object so [DebugProbesImpl] can check for static installation
 * without having to depend on [AgentPremain], which is not compatible with Android.
 * Otherwise, access to `AgentPremain.isInstalledStatically` triggers the load of its internal `ClassFileTransformer`
 * that is not available on Android.
 *
 * The entity (despite being internal) has usages in the following products
 * - Fleet (Reflection): FleetDebugProbes
 * - Android (Hard Coded, ignored for Leak Detection)
 * - IntelliJ (Suppress KotlinInternalInJava): CoroutineDumpState
 */
@PublishedApi
internal object AgentInstallationType {
    internal var isInstalledStatically = false
}
