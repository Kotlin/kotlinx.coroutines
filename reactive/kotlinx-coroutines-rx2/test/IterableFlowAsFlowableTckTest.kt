/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.flow.*
import org.junit.*
import org.reactivestreams.*
import org.reactivestreams.tck.*

class IterableFlowAsFlowableTckTest : PublisherVerification<Long>(TestEnvironment()) {

    private fun generate(num: Long): Array<Long> {
        return Array(if (num >= Integer.MAX_VALUE) 1000000 else num.toInt()) { it.toLong() }
    }

    override fun createPublisher(elements: Long): Flowable<Long> {
        return generate(elements).asIterable().asFlow().asFlowable()
    }

    override fun createFailedPublisher(): Publisher<Long>? = null

    @Ignore
    override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
    }

    @Ignore
    override fun required_spec312_cancelMustMakeThePublisherToEventuallyStopSignaling() {
        //
    }
}
