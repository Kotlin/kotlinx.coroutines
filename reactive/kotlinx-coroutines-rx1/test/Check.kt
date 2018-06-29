/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import rx.Observable
import rx.Single

fun <T> checkSingleValue(
    observable: Observable<T>,
    checker: (T) -> Unit
) {
    val singleValue = observable.toBlocking().single()
    checker(singleValue)
}

fun checkErroneous(
        observable: Observable<*>,
        checker: (Throwable) -> Unit
) {
    val singleNotification = observable.materialize().toBlocking().single()
    checker(singleNotification.throwable)
}

fun <T> checkSingleValue(
    single: Single<T>,
    checker: (T) -> Unit
) {
    val singleValue = single.toBlocking().value()
    checker(singleValue)
}

fun checkErroneous(
    single: Single<*>,
    checker: (Throwable) -> Unit
) {
    try {
        single.toBlocking().value()
        error("Should have failed")
    } catch (e: Throwable) {
        checker(e)
    }
}

