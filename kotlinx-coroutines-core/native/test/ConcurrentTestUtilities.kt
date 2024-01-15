/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import platform.posix.*
import kotlin.native.concurrent.*

actual inline fun yieldThread() { sched_yield() }

actual fun currentThreadName(): String = Worker.current.name
