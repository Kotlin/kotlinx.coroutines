/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 * It executes initial continuation of the coroutine _right here_ in the current call-frame
 * and let the coroutine resume in whatever thread that is used by the corresponding suspending function, without
 * mandating any specific threading policy.
 *
 * Note, that if you need your coroutine to be confined to a particular thread or a thread-pool after resumption,
 * but still want to execute it in the current call-frame until its first suspension, then you can use
 * an optional [CoroutineStart] parameter in coroutine builders like [launch] and [async] setting it to the
 * the value of [CoroutineStart.UNDISPATCHED].
 */
public object Unconfined : CoroutineDispatcher() {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = false
    override fun dispatch(context: CoroutineContext, block: Runnable) { throw UnsupportedOperationException() }
    override fun toString(): String = "Unconfined"
}
