/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

// It is used in the main sources of native-mt branch
internal expect inline fun workerMain(block: () -> Unit)
