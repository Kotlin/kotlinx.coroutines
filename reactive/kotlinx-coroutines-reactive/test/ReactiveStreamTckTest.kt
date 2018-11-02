/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.reactivestreams.*
import org.reactivestreams.tck.*
import org.testng.*
import org.testng.annotations.*


class ReactiveStreamTckTest {

    @Factory(dataProvider = "dispatchers")
    fun createTests(dispatcher: Dispatcher): Array<Any> {
        return arrayOf(ReactiveStreamTckTestSuite(dispatcher))
    }

    @DataProvider(name = "dispatchers")
    public fun dispatchers(): Array<Array<Any>> = Dispatcher.values().map { arrayOf<Any>(it) }.toTypedArray()


    public class ReactiveStreamTckTestSuite(
        private val dispatcher: Dispatcher
    ) : PublisherVerification<Long>(TestEnvironment(500, 500)) {

        private val scope = CoroutineScope(dispatcher.dispatcher + NonCancellable)

        override fun createPublisher(elements: Long): Publisher<Long> =
            scope.publish {
                for (i in 1..elements) send(i)
            }

        override fun createFailedPublisher(): Publisher<Long> =
            scope.publish {
                throw TestException()
            }

        @Test
        public override fun required_spec313_cancelMustMakeThePublisherEventuallyDropAllReferencesToTheSubscriber() {
            // This test fails on default dispatcher because it retains a reference to the last task
            // in the structure of  its GlobalQueue
            // So we skip it with the default dispatcher.
            // todo: remove it when CoroutinesScheduler is improved
            if (dispatcher == Dispatcher.DEFAULT) return
            super.required_spec313_cancelMustMakeThePublisherEventuallyDropAllReferencesToTheSubscriber()
        }

        @Test
        public override fun optional_spec105_emptyStreamMustTerminateBySignallingOnComplete() {
            throw SkipException("Skipped")
        }

        class TestException : Exception()
    }
}

enum class Dispatcher(val dispatcher: CoroutineDispatcher) {
    DEFAULT(Dispatchers.Default),
    UNCONFINED(Dispatchers.Unconfined)
}
