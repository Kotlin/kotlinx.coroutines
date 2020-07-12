/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.reactivestreams.*
import org.reactivestreams.tck.*
import org.testng.*
import org.testng.annotations.*


class ReactiveStreamTckTest : TestBase() {

    @Factory(dataProvider = "dispatchers")
    fun createTests(dispatcher: Dispatcher): Array<Any> {
        return arrayOf(ReactiveStreamTckTestSuite(dispatcher))
    }

    @DataProvider(name = "dispatchers")
    public fun dispatchers(): Array<Array<Any>> = Dispatcher.values().map { arrayOf<Any>(it) }.toTypedArray()


    public class ReactiveStreamTckTestSuite(
        private val dispatcher: Dispatcher
    ) : PublisherVerification<Long>(TestEnvironment(500, 500)) {

        override fun createPublisher(elements: Long): Publisher<Long> =
            publish(dispatcher.dispatcher) {
                for (i in 1..elements) send(i)
            }

        override fun createFailedPublisher(): Publisher<Long> =
            publish(dispatcher.dispatcher) {
                throw TestException()
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
