/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

/**
 * Object used to differentiate between agent installed statically or dinamically.
 * This is done in a separate object so [DebugProbesImpl] can check for static installation
 * without having to depend on [AgentPremain], which is not compatible with Android.
 */
internal object AgentInstallationType {
    internal var isInstalledStatically = false
}
