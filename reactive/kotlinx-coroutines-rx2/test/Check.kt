package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.functions.Consumer
import io.reactivex.plugins.*

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

inline fun withExceptionHandler(noinline handler: (Throwable) -> Unit, block: () -> Unit) {
    val original = RxJavaPlugins.getErrorHandler()
    RxJavaPlugins.setErrorHandler { handler(it) }
    try {
        block()
    } finally {
        RxJavaPlugins.setErrorHandler(original)
    }
}