/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import org.junit.*
import org.reactivestreams.*
import org.reactivestreams.example.unicast.*
import org.reactivestreams.tck.*

class RangePublisherTest : PublisherVerification<Int>(TestEnvironment(50, 50)) {

    override fun createPublisher(elements: Long): Publisher<Int> {
        return RangePublisher(1, elements.toInt()).asFlow().asPublisher()
    }

    override fun createFailedPublisher(): Publisher<Int>? {
        return null
    }

    @Ignore
    override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
    }
}

class RangePublisherWrappedTwiceTest : PublisherVerification<Int>(TestEnvironment(50, 50)) {

    override fun createPublisher(elements: Long): Publisher<Int> {
        return RangePublisher(1, elements.toInt()).asFlow().asPublisher().asFlow().asPublisher()
    }

    override fun createFailedPublisher(): Publisher<Int>? {
        return null
    }

    @Ignore
    override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
    }
}