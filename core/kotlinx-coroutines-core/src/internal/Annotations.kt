/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias JvmName = kotlin.jvm.JvmName

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias JvmOverloads = kotlin.jvm.JvmOverloads

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias JvmMultifileClass = kotlin.jvm.JvmMultifileClass

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias JvmField = kotlin.jvm.JvmField

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias Volatile = kotlin.jvm.Volatile

internal actual annotation class JsName(actual val name: String)
