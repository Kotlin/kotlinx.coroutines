/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import org.junit.*
import org.reactivestreams.example.unicast.AsyncIterablePublisher
import org.reactivestreams.Publisher
import org.reactivestreams.example.unicast.InfiniteIncrementNumberPublisher
import org.reactivestreams.tck.TestEnvironment
import java.util.concurrent.Executors
import java.util.concurrent.ExecutorService
import org.reactivestreams.tck.PublisherVerification
import org.testng.annotations.AfterClass
import org.testng.annotations.BeforeClass
import org.testng.annotations.Test

@Test
class UnboundedIntegerIncrementPublisherTest : PublisherVerification<Int>(TestEnvironment()) {

    private var e: ExecutorService? = null

    @BeforeClass
    internal fun before() {
        e = Executors.newFixedThreadPool(4)
    }

    @AfterClass
    internal fun after() {
        if (e != null) e!!.shutdown()
    }

    override fun createPublisher(elements: Long): Publisher<Int> {
        return InfiniteIncrementNumberPublisher(e!!).asFlow().asPublisher()
    }

    override fun createFailedPublisher(): Publisher<Int> {
        return AsyncIterablePublisher(object : Iterable<Int> {
            override fun iterator(): Iterator<Int> {
                throw RuntimeException("Error state signal!")
            }
        }, e!!)
    }

    override fun maxElementsFromPublisher(): Long {
        return super.publisherUnableToSignalOnComplete()
    }

    @Ignore
    override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
    }
}
