/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.cinterop.*

internal actual inline fun workerMain(block: () -> Unit) {
    autoreleasepool {
        block()
    }
}
