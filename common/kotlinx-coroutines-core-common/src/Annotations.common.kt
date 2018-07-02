/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// NOTE: We are defining them in a special internalAnnotations package because they would break
// user code that uses kotlinx.coroutines library otherwise, see https://youtrack.jetbrains.com/issue/KT-23727
package kotlinx.coroutines.experimental.internalAnnotations

@Target(AnnotationTarget.FILE, AnnotationTarget.FUNCTION)
internal expect annotation class JvmName(val name: String)

@Target(AnnotationTarget.FILE)
internal expect annotation class JvmMultifileClass()

internal expect annotation class JvmField()

internal expect annotation class Volatile()

internal expect annotation class JsName(val name: String)
