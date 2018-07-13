/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

@Target(AnnotationTarget.FILE, AnnotationTarget.FUNCTION)
internal actual annotation class JvmName(actual val name: String)

@Target(AnnotationTarget.CONSTRUCTOR, AnnotationTarget.FUNCTION)
internal actual annotation class JvmOverloads

@Target(AnnotationTarget.FILE)
internal actual annotation class JvmMultifileClass

internal actual annotation class JvmField

internal actual annotation class Volatile

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias JsName = kotlin.js.JsName

