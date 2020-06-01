/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.internal.*

@Suppress("ACTUAL_WITHOUT_EXPECT") // visibility different
internal actual typealias ShareableRefHolder = Any

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual fun ShareableRefHolder.disposeSharedRef() {}

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual fun <T> T.asShareable(): DisposableHandle where T : DisposableHandle, T : ShareableRefHolder = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun CoroutineDispatcher.asShareable(): CoroutineDispatcher = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T> Continuation<T>.asShareable() : Continuation<T> = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T> Continuation<T>.asLocal() : Continuation<T> = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T> Continuation<T>.asLocalOrNull() : Continuation<T>? = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual fun <T> Continuation<T>.asLocalOrNullIfNotUsed() : Continuation<T>? = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T> Continuation<T>.useLocal() : Continuation<T> = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T> Continuation<T>.shareableInterceptedResumeCancellableWith(result: Result<T>) {
    intercepted().resumeCancellableWith(result)
}

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T> Continuation<T>.shareableInterceptedResumeWith(result: Result<T>) {
    intercepted().resumeWith(result)
}

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun disposeContinuation(cont: () -> Continuation<*>) {}

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Save an entry on call stack
internal actual inline fun <T> CancellableContinuationImpl<T>.shareableResume(delegate: Continuation<T>, undispatched: Boolean) =
    resume(delegate, undispatched)

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun <T, R> (suspend (T) -> R).asShareable(): suspend (T) -> R = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Save an entry on call stack
internal actual inline fun isReuseSupportedInPlatform() = true

@InlineOnly
internal actual inline fun <T> ArrayList<T>.addOrUpdate(element: T, update: (ArrayList<T>) -> Unit) {
    add(element)
}

@InlineOnly
internal actual inline fun <T> ArrayList<T>.addOrUpdate(index: Int, element: T, update: (ArrayList<T>) -> Unit) {
    add(index, element)
}

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun Any.weakRef(): Any = this

@InlineOnly
@Suppress("NOTHING_TO_INLINE") // Should be NOP
internal actual inline fun Any?.unweakRef(): Any? = this
