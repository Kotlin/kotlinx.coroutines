/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

private var counter = 0

internal actual val Any.hexAddress: String
    get() {
        var result = this.asDynamic().__debug_counter
        if (jsTypeOf(result) !== "number") {
            result = ++counter
            this.asDynamic().__debug_counter = result

        }
        return (result as Int).toString()
    }

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"
