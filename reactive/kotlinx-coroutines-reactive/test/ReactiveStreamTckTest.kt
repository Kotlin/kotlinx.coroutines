/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import org.reactivestreams.*
import org.reactivestreams.tck.*

@RunWith(Parameterized::class)
class ReactiveStreamTckTest(
    private val dispatcher: Dispatcher
) : PublisherVerification<Long>(TestEnvironment()) {

    enum class Dispatcher(val dispatcher: CoroutineDispatcher)  {
        DEFAULT(Dispatchers.Default),
        UNCONFINED(Dispatchers.Unconfined)
    }

    private val scope = CoroutineScope(dispatcher.dispatcher)

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = Dispatcher.values().map { arrayOf<Any>(it) }
    }

    override fun createPublisher(elements: Long): Publisher<Long> =
        scope.publish {
            for (i in 1..elements) send(i)
        }

    override fun createFailedPublisher(): Publisher<Long> =
        scope.publish {
            throw TestException()
        }

    @Before
    override fun setUp() {
        super.setUp()
    }

    @Test
    override fun required_spec306_afterSubscriptionIsCancelledRequestMustBeNops() {
        super.required_spec306_afterSubscriptionIsCancelledRequestMustBeNops()
    }

    @Test
    override fun required_spec303_mustNotAllowUnboundedRecursion() {
        super.required_spec303_mustNotAllowUnboundedRecursion()
    }

    @Test
    override fun required_spec107_mustNotEmitFurtherSignalsOnceOnCompleteHasBeenSignalled() {
        super.required_spec107_mustNotEmitFurtherSignalsOnceOnCompleteHasBeenSignalled()
    }

    @Test
    override fun required_spec109_mayRejectCallsToSubscribeIfPublisherIsUnableOrUnwillingToServeThemRejectionMustTriggerOnErrorAfterOnSubscribe() {
        super.required_spec109_mayRejectCallsToSubscribeIfPublisherIsUnableOrUnwillingToServeThemRejectionMustTriggerOnErrorAfterOnSubscribe()
    }

    @Test
    override fun required_spec302_mustAllowSynchronousRequestCallsFromOnNextAndOnSubscribe() {
        super.required_spec302_mustAllowSynchronousRequestCallsFromOnNextAndOnSubscribe()
    }

    @Test
    override fun required_spec313_cancelMustMakeThePublisherEventuallyDropAllReferencesToTheSubscriber() {
        // This test fails on default dispatcher because it retains a reference to the last task
        // in the structure of  its GlobalQueue
        // So we skip it with the default dispatcher.
        // todo: remove it when CoroutinesScheduler is improved
        if (dispatcher == Dispatcher.DEFAULT) return
        super.required_spec313_cancelMustMakeThePublisherEventuallyDropAllReferencesToTheSubscriber()
    }

    @Test
    override fun required_validate_boundedDepthOfOnNextAndRequestRecursion() {
        super.required_validate_boundedDepthOfOnNextAndRequestRecursion()
    }

    @Test
    override fun required_spec317_mustSupportAPendingElementCountUpToLongMaxValue() {
        super.required_spec317_mustSupportAPendingElementCountUpToLongMaxValue()
    }

    @Test
    override fun required_spec317_mustNotSignalOnErrorWhenPendingAboveLongMaxValue() {
        super.required_spec317_mustNotSignalOnErrorWhenPendingAboveLongMaxValue()
    }

    @Test
    override fun required_validate_maxElementsFromPublisher() {
        super.required_validate_maxElementsFromPublisher()
    }

    @Test
    @Ignore // This OPTIONAL requirement is not implemented, which is fine
    override fun optional_spec105_emptyStreamMustTerminateBySignallingOnComplete() {
        super.optional_spec105_emptyStreamMustTerminateBySignallingOnComplete()
    }

    @Test
    override fun required_spec105_mustSignalOnCompleteWhenFiniteStreamTerminates() {
        super.required_spec105_mustSignalOnCompleteWhenFiniteStreamTerminates()
    }

    @Test
    override fun optional_spec111_registeredSubscribersMustReceiveOnNextOrOnCompleteSignals() {
        super.optional_spec111_registeredSubscribersMustReceiveOnNextOrOnCompleteSignals()
    }

    @Test
    override fun required_spec102_maySignalLessThanRequestedAndTerminateSubscription() {
        super.required_spec102_maySignalLessThanRequestedAndTerminateSubscription()
    }

    @Test
    override fun required_createPublisher3MustProduceAStreamOfExactly3Elements() {
        super.required_createPublisher3MustProduceAStreamOfExactly3Elements()
    }

    @Test
    override fun optional_spec111_maySupportMultiSubscribe() {
        super.optional_spec111_maySupportMultiSubscribe()
    }

    @Test
    override fun stochastic_spec103_mustSignalOnMethodsSequentially() {
        super.stochastic_spec103_mustSignalOnMethodsSequentially()
    }

    @Test
    override fun required_spec307_afterSubscriptionIsCancelledAdditionalCancelationsMustBeNops() {
        super.required_spec307_afterSubscriptionIsCancelledAdditionalCancelationsMustBeNops()
    }

    @Test
    override fun required_createPublisher1MustProduceAStreamOfExactly1Element() {
        super.required_createPublisher1MustProduceAStreamOfExactly1Element()
    }

    @Test
    override fun optional_spec111_multicast_mustProduceTheSameElementsInTheSameSequenceToAllOfItsSubscribersWhenRequestingOneByOne() {
        super.optional_spec111_multicast_mustProduceTheSameElementsInTheSameSequenceToAllOfItsSubscribersWhenRequestingOneByOne()
    }

    @Test
    override fun optional_spec111_multicast_mustProduceTheSameElementsInTheSameSequenceToAllOfItsSubscribersWhenRequestingManyUpfront() {
        super.optional_spec111_multicast_mustProduceTheSameElementsInTheSameSequenceToAllOfItsSubscribersWhenRequestingManyUpfront()
    }

    @Test
    override fun required_spec309_requestNegativeNumberMustSignalIllegalArgumentException() {
        super.required_spec309_requestNegativeNumberMustSignalIllegalArgumentException()
    }

    @Test
    override fun required_spec312_cancelMustMakeThePublisherToEventuallyStopSignaling() {
        super.required_spec312_cancelMustMakeThePublisherToEventuallyStopSignaling()
    }

    @Test
    override fun required_spec317_mustSupportACumulativePendingElementCountUpToLongMaxValue() {
        super.required_spec317_mustSupportACumulativePendingElementCountUpToLongMaxValue()
    }

    @Test
    override fun optional_spec104_mustSignalOnErrorWhenFails() {
        super.optional_spec104_mustSignalOnErrorWhenFails()
    }

    @Test
    override fun required_spec309_requestZeroMustSignalIllegalArgumentException() {
        super.required_spec309_requestZeroMustSignalIllegalArgumentException()
    }

    @Test
    override fun optional_spec309_requestNegativeNumberMaySignalIllegalArgumentExceptionWithSpecificMessage() {
        super.optional_spec309_requestNegativeNumberMaySignalIllegalArgumentExceptionWithSpecificMessage()
    }

    @Test
    override fun required_spec109_subscribeThrowNPEOnNullSubscriber() {
        super.required_spec109_subscribeThrowNPEOnNullSubscriber()
    }

    @Test
    override fun optional_spec111_multicast_mustProduceTheSameElementsInTheSameSequenceToAllOfItsSubscribersWhenRequestingManyUpfrontAndCompleteAsExpected() {
        super.optional_spec111_multicast_mustProduceTheSameElementsInTheSameSequenceToAllOfItsSubscribersWhenRequestingManyUpfrontAndCompleteAsExpected()
    }

    @Test
    override fun required_spec101_subscriptionRequestMustResultInTheCorrectNumberOfProducedElements() {
        super.required_spec101_subscriptionRequestMustResultInTheCorrectNumberOfProducedElements()
    }

    @Test
    override fun required_spec109_mustIssueOnSubscribeForNonNullSubscriber() {
        super.required_spec109_mustIssueOnSubscribeForNonNullSubscriber()
    }

    class TestException : Exception()
}