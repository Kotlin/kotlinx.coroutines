/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal actual fun initCurrentThread(): Thread = WorkerThread()

internal actual inline fun workerMain(block: () -> Unit) = block()