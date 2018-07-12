/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

private var counter = 0

internal actual val Any.hexAddress: String
    get() {
        return "<not_implemented>" // :todo:
    }

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"
