/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.reactivestreams.*

// Binary compatibility with Spring 5.2 RC
@Deprecated(
    message = "Replaced in favor of ReactiveFlow extension, please import kotlinx.coroutines.reactive.* instead of kotlinx.coroutines.reactive.FlowKt",
    level = DeprecationLevel.ERROR
)
@JvmName("asFlow")
public fun <T : Any> Publisher<T>.asFlowDeprecated(): Flow<T> = asFlow()

// Binary compatibility with Spring 5.2 RC
@Deprecated(
    message = "Replaced in favor of ReactiveFlow extension, please import kotlinx.coroutines.reactive.* instead of kotlinx.coroutines.reactive.FlowKt",
    level = DeprecationLevel.ERROR
)
@JvmName("asPublisher")
public fun <T : Any> Flow<T>.asPublisherDeprecated(): Publisher<T> = asPublisher()

@FlowPreview
@Deprecated(
    message = "batchSize parameter is deprecated, use .buffer() instead to control the backpressure",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("asFlow().buffer(batchSize)", imports = ["kotlinx.coroutines.flow.*"])
)
public fun <T : Any> Publisher<T>.asFlow(batchSize: Int): Flow<T> = asFlow().buffer(batchSize)