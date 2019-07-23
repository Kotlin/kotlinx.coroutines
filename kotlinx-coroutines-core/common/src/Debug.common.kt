/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal expect val DEBUG: Boolean
internal expect val Any.hexAddress: String
internal expect val Any.classSimpleName: String
internal expect fun assert(value: () -> Boolean)
