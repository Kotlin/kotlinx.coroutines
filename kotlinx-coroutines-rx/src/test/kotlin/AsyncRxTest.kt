package kotlinx.coroutines

import org.junit.Test
import rx.Observable
import java.util.concurrent.TimeUnit
import kotlin.test.assertEquals
import kotlin.test.fail

class AsyncRxTest {
    @Test
    fun testSingle() {
        val observable = asyncRx<String> {
            Observable.just("O").awaitSingle() + "K"
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val observable = asyncRx<String> {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }


    @Test
    fun testSingleException() {
        val observable = asyncRx<String> {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneousObservable(observable) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val observable = asyncRx<String> {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val observable = asyncRx<String> {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val observable = asyncRx<String> {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val observable = asyncRx<String> {
            error(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneousObservable(observable) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testApplyForEachAndWait() {
        val observable = asyncRx<String> {
            var result = ""

            Observable.just("O", "K").applyForEachAndAwait {
                result += it
            }

            result
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testApplyForEachAndWaitException() {
        val observable = asyncRx<String> {
            try {
                Observable.error<String>(RuntimeException("OK")).applyForEachAndAwait {
                    fail("Should not be here")
                }

                "Fail"
            } catch (e: RuntimeException) {
                e.message!!
            }
        }

        checkObservableWithSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    private fun checkErroneousObservable(
            observable: Observable<*>,
            checker: (Throwable) -> Unit
    ) {
        val singleNotification = observable.materialize().toBlocking().single()
        checker(singleNotification.throwable)
    }

    private fun <T> checkObservableWithSingleValue(
            observable: Observable<T>,
            checker: (T) -> Unit
    ) {
        val singleValue = observable.toBlocking().single()
        checker(singleValue)
    }
}
