/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlin.coroutines.*

/**
 * Returns this.
 * Applying [flowOn][Flow.flowOn] operator to [StateFlow] has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying flowOn operator to StateFlow has no effect. See StateFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> StateFlow<T>.flowOn(context: CoroutineContext): Flow<T> = noImpl()

/**
 * Returns this.
 * Applying [conflate][Flow.conflate] operator to [StateFlow] has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying conflate operator to StateFlow has no effect. See StateFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> StateFlow<T>.conflate(): Flow<T> = noImpl()

/**
 * Returns this.
 * Applying [distinctUntilChanged][Flow.distinctUntilChanged] operator to [StateFlow] has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Applying distinctUntilChanged operator to StateFlow has no effect. See StateFlow documentation on Operator Fusion.",
    replaceWith = ReplaceWith("this")
)
public fun <T> StateFlow<T>.distinctUntilChanged(): Flow<T> = noImpl()
