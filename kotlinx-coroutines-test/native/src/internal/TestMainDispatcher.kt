/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal
import kotlinx.coroutines.*

@Suppress("INVISIBLE_MEMBER")
internal actual fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher =
    when (val mainDispatcher = Main) {
        is TestMainDispatcher -> mainDispatcher
        else -> TestMainDispatcher(mainDispatcher).also { injectMain(it) }
    }
