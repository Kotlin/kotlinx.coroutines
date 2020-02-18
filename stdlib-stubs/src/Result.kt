/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlin

interface Result<out T> {
    public val value: T
    public val isSuccess: Boolean
    public val isFailure: Boolean
    public fun exceptionOrNull(): Throwable?
    public fun getOrNull(): T?
    public fun getOrThrow(): T
}
