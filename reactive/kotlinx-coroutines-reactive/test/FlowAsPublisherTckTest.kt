/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.reactivestreams.*
import org.reactivestreams.tck.*
import org.testng.*
import org.testng.annotations.*


class FlowAsPublisherTckTest : TestBase() {

    @Factory(dataProvider = "dispatchers")
    fun createTests(dispatcher: Dispatcher): Array<Any> {
        return arrayOf(FlowAsPublisherTckTestSuite(dispatcher))
    }

    @DataProvider(name = "dispatchers")
    public fun dispatchers(): Array<Array<Any>> = Dispatcher.values().map { arrayOf<Any>(it) }.toTypedArray()


    public class FlowAsPublisherTckTestSuite(
        private val dispatcher: Dispatcher
    ) : PublisherVerification<Long>(TestEnvironment(500, 500)) {

        override fun createPublisher(elements: Long): Publisher<Long> =
            flow {
                for (i in 1..elements) emit(i)
            }.asPublisher(dispatcher.dispatcher)

        override fun createFailedPublisher(): Publisher<Long> =
            flow<Long> {
                throw TestException()
            }.asPublisher(dispatcher.dispatcher)

        @Test
        public override fun optional_spec104_mustSignalOnErrorWhenFails() {
            throw SkipException("Skipped")
        }

        @Test
        public override fun optional_spec105_emptyStreamMustTerminateBySignallingOnComplete() {
            throw SkipException("Skipped")
        }


        /**
         * Three required tests are skipped below. See discussion here:
         * https://github.com/Kotlin/kotlinx.coroutines/issues/3608#issuecomment-1415686018
         *
         * The short explanation is they don't make a lot of sense for a flow adapter
         * and no one would realistically rely on these behaviors.
         */

        @Test
        public override fun required_spec109_mayRejectCallsToSubscribeIfPublisherIsUnableOrUnwillingToServeThemRejectionMustTriggerOnErrorAfterOnSubscribe() {
            throw SkipException("Skipped")
        }

        @Test
        public override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
            throw SkipException("Skipped")
        }

        @Test
        public override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
            throw SkipException("Skipped")
        }

        class TestException : Exception()
    }
}
