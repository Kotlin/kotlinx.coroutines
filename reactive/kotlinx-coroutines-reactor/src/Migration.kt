/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmName("FlowKt")

package kotlinx.coroutines.reactor

import kotlinx.coroutines.flow.*
import reactor.core.publisher.*

@Deprecated(
    message = "Replaced in favor of ReactiveFlow extension, please import kotlinx.coroutines.reactor.* instead of kotlinx.coroutines.reactor.FlowKt",
    level = DeprecationLevel.ERROR
)
@JvmName("asFlux")
public fun <T : Any> Flow<T>.asFluxDeprecated(): Flux<T> = asFlux()
