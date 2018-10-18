/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import reactor.core.publisher.Flux
import reactor.core.publisher.Mono

fun <T> checkMonoValue(
        mono: Mono<T>,
        checker: (T) -> Unit
) {
    val monoValue = mono.block()
    checker(monoValue)
}

fun checkErroneous(
        mono: Mono<*>,
        checker: (Throwable) -> Unit
) {
    try {
        mono.block()
        error("Should have failed")
    } catch (e: Throwable) {
        checker(e)
    }
}

fun <T> checkSingleValue(
        flux: Flux<T>,
        checker: (T) -> Unit
) {
    val singleValue = flux.toIterable().single()
    checker(singleValue)
}

fun checkErroneous(
        flux: Flux<*>,
        checker: (Throwable) -> Unit
) {
    val singleNotification = flux.materialize().toIterable().single()
    checker(singleNotification.throwable)
}
