/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

@OptionalExpectation
@UseExperimental(ExperimentalMultiplatform::class)
internal expect annotation class NativeThreadLocal()

internal expect class CommonThreadLocal<T>(supplier: () -> T) {
    fun get(): T
}
