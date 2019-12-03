/*
 * Copyright 2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext

/**
 * A global [CoroutineScope] not bound to any job.
 *
 * Global scope is used to launch top-level coroutines which are operating on the whole application lifetime
 * and are not cancelled prematurely.
 * Another use of the global scope is operators running in [Dispatchers.Unconfined], which don't have any job associated with them.
 *
 * Application code usually should use an application-defined [CoroutineScope]. Using
 * [async][CoroutineScope.async] or [launch][CoroutineScope.launch]
 * on the instance of [GlobalScope] is highly discouraged.
 *
 * Usage of this interface may look like this:
 *
 * ```
 * fun ReceiveChannel<Int>.sqrt(): ReceiveChannel<Double> = GlobalScope.produce(Dispatchers.Unconfined) {
 *     for (number in this) {
 *         send(Math.sqrt(number))
 *     }
 * }
 * ```
 */
public object GlobalScope : CoroutineScope {
    override val coroutineContext: CoroutineContext = createInitialContext()
}

internal expect fun createInitialContext(): CoroutineContext
