/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

@PublishedApi internal const val MODE_ATOMIC_DEFAULT = 0 // schedule non-cancellable dispatch for suspendCoroutine
@PublishedApi internal const val MODE_CANCELLABLE = 1    // schedule cancellable dispatch for suspendCancellableCoroutine
@PublishedApi internal const val MODE_DIRECT = 2         // when the context is right just invoke the delegate continuation direct
@PublishedApi internal const val MODE_UNDISPATCHED = 3   // when the thread is right, but need to mark it with current coroutine

internal val Int.isCancellableMode get() = this == MODE_CANCELLABLE
internal val Int.isDispatchedMode get() = this == MODE_ATOMIC_DEFAULT || this == MODE_CANCELLABLE
