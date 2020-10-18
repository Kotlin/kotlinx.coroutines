/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
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

//@Deprecated(
//    message = "isActive is resolved into the extension of outer CoroutineScope which is likely to be an error." +
//        "Use currentCoroutineContext().isActive or cancellable() operator instead " +
//        "or specify the receiver of isActive explicitly. " +
//        "Additionally, flow {} builder emissions are cancellable by default.",
//    level = DeprecationLevel.WARNING, // ERROR in 1.4
//    replaceWith = ReplaceWith("currentCoroutineContext().isActive")
//)
//public val FlowCollector<*>.isActive: Boolean
//    get() = noImpl()
//
//@Deprecated(
//    message = "cancel() is resolved into the extension of outer CoroutineScope which is likely to be an error." +
//        "Use currentCoroutineContext().cancel() instead or specify the receiver of cancel() explicitly",
//    level = DeprecationLevel.WARNING, // ERROR in 1.4
//    replaceWith = ReplaceWith("currentCoroutineContext().cancel(cause)")
//)
//public fun FlowCollector<*>.cancel(cause: CancellationException? = null): Unit = noImpl()
//
//@Deprecated(
//    message = "coroutineContext is resolved into the property of outer CoroutineScope which is likely to be an error." +
//        "Use currentCoroutineContext() instead or specify the receiver of coroutineContext explicitly",
//    level = DeprecationLevel.WARNING, // ERROR in 1.4
//    replaceWith = ReplaceWith("currentCoroutineContext()")
//)
//public val FlowCollector<*>.coroutineContext: CoroutineContext
//    get() = noImpl()