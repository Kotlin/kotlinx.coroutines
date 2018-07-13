/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.intrinsics

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Use this function to start coroutine in a cancellable way, so that it can be cancelled
 * while waiting to be dispatched.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <T> (suspend () -> T).startCoroutineCancellable(completion: Continuation<T>) =
    createCoroutineUnintercepted(completion).intercepted().resumeCancellable(Unit)

/**
 * Use this function to start coroutine in a cancellable way, so that it can be cancelled
 * while waiting to be dispatched.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <R, T> (suspend (R) -> T).startCoroutineCancellable(receiver: R, completion: Continuation<T>) =
    createCoroutineUnintercepted(receiver, completion).intercepted().resumeCancellable(Unit)
