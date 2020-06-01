/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.native.concurrent.*

internal actual fun initCurrentThread(): Thread = WorkerThread()

internal actual fun Worker.toThread(): Thread = WorkerThread(this)
