/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.flow.*
import org.junit.*
import org.reactivestreams.*
import org.reactivestreams.example.unicast.*
import org.reactivestreams.tck.*

class RangePublisherBufferedTest :
    PublisherVerification<Int>(TestEnvironment(50, 50))
{
    override fun createPublisher(elements: Long): Publisher<Int> {
        return RangePublisher(1, elements.toInt()).asFlow().buffer(2).asPublisher()
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