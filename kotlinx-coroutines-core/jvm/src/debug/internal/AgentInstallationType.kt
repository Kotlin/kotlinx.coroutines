package kotlinx.coroutines.debug.internal

/**
 * Object used to differentiate between agent installed statically or dynamically.
 * This is done in a separate object so [DebugProbesImpl] can check for static installation
 * without having to depend on [kotlinx.coroutines.debug.AgentPremain], which is not compatible with Android.
 * Otherwise, access to `AgentPremain.isInstalledStatically` triggers the load of its internal `ClassFileTransformer`
 * that is not available on Android.
 */
internal object AgentInstallationType {
    internal var isInstalledStatically = false
}
