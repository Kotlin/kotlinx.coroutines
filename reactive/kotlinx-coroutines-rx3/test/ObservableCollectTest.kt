package kotlinx.coroutines.rx3

import kotlinx.coroutines.testing.*
import io.reactivex.rxjava3.core.ObservableSource
import io.reactivex.rxjava3.disposables.*
import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class ObservableCollectTest: TestBase() {

    /** Tests the behavior of [collect] when the publisher raises an error. */
    @Test
    fun testObservableCollectThrowingObservable() = runTest {
        expect(1)
        var sum = 0
        try {
            rxObservable {
                for (i in 0..100) {
                    send(i)
                }
                throw TestException()
            }.collect {
                sum += it
            }
        } catch (e: TestException) {
            assertTrue(sum > 0)
            finish(2)
        }
    }

    @Test
    fun testObservableCollectThrowingAction() = runTest {
        expect(1)
        var sum = 0
        val expectedSum = 5
        try {
            var disposed = false
            ObservableSource<Int> { observer ->
                launch(Dispatchers.Default) {
                    observer.onSubscribe(object : Disposable {
                        override fun dispose() {
                            disposed = true
                            expect(expectedSum + 2)
                        }

                        override fun isDisposed(): Boolean = disposed
                    })
                    while (!disposed) {
                        observer.onNext(1)
                    }
                }
            }.collect {
                expect(sum + 2)
                sum += it
                if (sum == expectedSum) {
                    throw TestException()
                }
            }
        } catch (e: TestException) {
            assertEquals(expectedSum, sum)
            finish(expectedSum + 3)
        }
    }
}