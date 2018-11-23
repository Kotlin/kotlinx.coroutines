package kotlinx.coroutines.rx2

import io.reactivex.Observable
import kotlinx.coroutines.TestBase
import kotlinx.coroutines.ignoreLostThreads
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.scheduling.ExperimentalCoroutineDispatcher
import org.hamcrest.core.IsEqual
import org.junit.After
import org.junit.Assert
import org.junit.Before
import org.junit.Test

class DispatcherTest : TestBase() {

    lateinit var dispatcher: ExperimentalCoroutineDispatcher

    @Before
    fun setup() {
        ignoreLostThreads("RxCachedThreadScheduler-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
        dispatcher = ExperimentalCoroutineDispatcher(1, 1, 1, "TestDispatcher")
    }

    @After
    fun after() {
        dispatcher.close()
    }

    @Test
    fun testDispatcher() {
        val scheduler = dispatcher.asScheduler()

        lateinit var coroutineThread: Thread
        runBlocking(dispatcher) {
            coroutineThread = Thread.currentThread()
        }

        expect(1)
        Observable
                .create<String> {
                    expect(2)
                    val t1 = Thread.currentThread()
                    Assert.assertThat(t1, IsEqual(coroutineThread))
                    it.onNext("Message")
                    it.onComplete()
                }
                .subscribeOn(scheduler)
                .doOnNext {
                    expect(3)
                    val t2 = Thread.currentThread()
                    Assert.assertThat(t2, IsEqual(coroutineThread))
                }
                .blockingSubscribe {
                    expect(4)
                }
        finish(5)
    }
}
