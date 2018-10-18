/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*

fun <T> checkSingleValue(
    observable: Observable<T>,
    checker: (T) -> Unit
) {
    val singleValue = observable.blockingSingle()
    checker(singleValue)
}

fun checkErroneous(
        observable: Observable<*>,
        checker: (Throwable) -> Unit
) {
    val singleNotification = observable.materialize().blockingSingle()
    val error = singleNotification.error ?: error("Excepted error")
    checker(error)
}

fun <T> checkSingleValue(
    single: Single<T>,
    checker: (T) -> Unit
) {
    val singleValue = single.blockingGet()
    checker(singleValue)
}

fun checkErroneous(
    single: Single<*>,
    checker: (Throwable) -> Unit
) {
    try {
        single.blockingGet()
        error("Should have failed")
    } catch (e: Throwable) {
        checker(e)
    }
}

fun <T> checkMaybeValue(
        maybe: Maybe<T>,
        checker: (T?) -> Unit
) {
    val maybeValue = maybe.toFlowable().blockingIterable().firstOrNull()
    checker(maybeValue)
}

@Suppress("UNCHECKED_CAST")
fun checkErroneous(
    maybe: Maybe<*>,
    checker: (Throwable) -> Unit
) {
    try {
        (maybe as Maybe<Any>).blockingGet()
        error("Should have failed")
    } catch (e: Throwable) {
        checker(e)
    }
}

