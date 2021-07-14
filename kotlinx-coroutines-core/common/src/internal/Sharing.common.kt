/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

internal expect open class ShareableRefHolder()
internal expect fun ShareableRefHolder.disposeSharedRef()
internal expect fun <T> T.asShareable(): DisposableHandle where T : DisposableHandle, T : ShareableRefHolder
internal expect fun CoroutineDispatcher.asShareable(): CoroutineDispatcher
internal expect fun <T> Continuation<T>.asShareable() : Continuation<T>
internal expect fun <T> Continuation<T>.asLocal() : Continuation<T>
internal expect fun <T> Continuation<T>.asLocalOrNull() : Continuation<T>?
internal expect fun <T> Continuation<T>.asLocalOrNullIfNotUsed() : Continuation<T>?
internal expect fun <T> Continuation<T>.useLocal() : Continuation<T>
internal expect fun <T> Continuation<T>.shareableInterceptedResumeCancellableWith(result: Result<T>)
internal expect fun <T> Continuation<T>.shareableInterceptedResumeWith(result: Result<T>)
internal expect fun disposeContinuation(cont: () -> Continuation<*>)
internal expect fun <T> CancellableContinuationImpl<T>.shareableResume(delegate: Continuation<T>, undispatched: Boolean)

internal expect fun <T, R> (suspend (T) -> R).asShareable(): suspend (T) -> R

internal expect fun isReuseSupportedInPlatform(): Boolean
internal expect fun <T> ArrayList<T>.addOrUpdate(element: T, update: (ArrayList<T>) -> Unit)
internal expect fun <T> ArrayList<T>.addOrUpdate(index: Int, element: T, update: (ArrayList<T>) -> Unit)
internal expect fun Any.weakRef(): Any
internal expect fun Any?.unweakRef(): Any?
