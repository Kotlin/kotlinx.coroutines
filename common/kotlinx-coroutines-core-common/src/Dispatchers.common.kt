/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.*

/**
 * Groups various implementations of [CoroutineDispatcher].
 */
public object Dispatchers {
    /**
     * The default [CoroutineDispatcher] that is used by all standard builders like
     * [launch][CoroutineScope.launch], [async][CoroutineScope.async], etc
     * if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
     *
     * It is backed by a shared pool of threads on JVM.
     * You can set system property "`kotlinx.coroutines.scheduler`" (either no value or to the value of "`on`")
     * to use an experimental coroutine dispatcher that shares threads with [Dispatchers.IO] and thus can switch to
     * context without performing an actual thread context switch.
     */
    @JvmField
    public val Default: CoroutineDispatcher =
        createDefaultDispatcher()

    /**
     * A coroutine dispatcher that is not confined to any specific thread.
     * It executes initial continuation of the coroutine _immediately_ in the current call-frame
     * and lets the coroutine resume in whatever thread that is used by the corresponding suspending function, without
     * mandating any specific threading policy.
     * **Note: use with extreme caution, not for general code**.
     *
     * Note, that if you need your coroutine to be confined to a particular thread or a thread-pool after resumption,
     * but still want to execute it in the current call-frame until its first suspension, then you can use
     * an optional [CoroutineStart] parameter in coroutine builders like
     * [launch][CoroutineScope.launch] and [async][CoroutineScope.async] setting it to the
     * the value of [CoroutineStart.UNDISPATCHED].
     *
     * **Note: This is an experimental api.**
     * Semantics, order of execution, and particular implementation details of this dispatcher may change in the future.
     */
    @JvmField
    @ExperimentalCoroutinesApi
    public val Unconfined: CoroutineDispatcher =
        kotlinx.coroutines.experimental.Unconfined
}