/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused", "MemberVisibilityCanBePrivate")

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.RENDEZVOUS
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.selects.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import org.jetbrains.kotlinx.lincheck.verifier.*

class RendezvousChannelLincheckTest : ChannelLincheckTestBaseWithOnSend(
    c = Channel(RENDEZVOUS),
    sequentialSpecification = SequentialRendezvousChannel::class.java
)
class SequentialRendezvousChannel : SequentialIntChannelBase(RENDEZVOUS)

class Buffered1ChannelLincheckTest : ChannelLincheckTestBaseWithOnSend(
    c = Channel(1),
    sequentialSpecification = SequentialBuffered1Channel::class.java
)
class Buffered1BroadcastChannelLincheckTest : ChannelLincheckTestBase(
    c = ChannelViaBroadcast(BroadcastChannelImpl(1)),
    sequentialSpecification = SequentialBuffered1Channel::class.java,
    obstructionFree = false
)
class SequentialBuffered1Channel : SequentialIntChannelBase(1)

class Buffered2ChannelLincheckTest : ChannelLincheckTestBaseWithOnSend(
    c = Channel(2),
    sequentialSpecification = SequentialBuffered2Channel::class.java
)
class Buffered2BroadcastChannelLincheckTest : ChannelLincheckTestBase(
    c = ChannelViaBroadcast(BroadcastChannelImpl(2)),
    sequentialSpecification = SequentialBuffered2Channel::class.java,
    obstructionFree = false
)
class SequentialBuffered2Channel : SequentialIntChannelBase(2)

class UnlimitedChannelLincheckTest : ChannelLincheckTestBaseAll(
    c = Channel(UNLIMITED),
    sequentialSpecification = SequentialUnlimitedChannel::class.java
)
class SequentialUnlimitedChannel : SequentialIntChannelBase(UNLIMITED)

class ConflatedChannelLincheckTest : ChannelLincheckTestBaseAll(
    c = Channel(CONFLATED),
    sequentialSpecification = SequentialConflatedChannel::class.java,
    obstructionFree = false
)
class ConflatedBroadcastChannelLincheckTest : ChannelLincheckTestBaseAll(
    c = ChannelViaBroadcast(ConflatedBroadcastChannel()),
    sequentialSpecification = SequentialConflatedChannel::class.java,
    obstructionFree = false
)
class SequentialConflatedChannel : SequentialIntChannelBase(CONFLATED)

abstract class ChannelLincheckTestBaseAll(
    c: Channel<Int>,
    sequentialSpecification: Class<*>,
    obstructionFree: Boolean = true
) : ChannelLincheckTestBaseWithOnSend(c, sequentialSpecification, obstructionFree) {
    @Operation
    override fun trySend(value: Int) = super.trySend(value)
    @Operation
    override fun isClosedForReceive() = super.isClosedForReceive()
    @Operation
    override fun isEmpty() = super.isEmpty()
}

abstract class ChannelLincheckTestBaseWithOnSend(
    c: Channel<Int>,
    sequentialSpecification: Class<*>,
    obstructionFree: Boolean = true
) : ChannelLincheckTestBase(c, sequentialSpecification, obstructionFree) {
    @Operation(allowExtraSuspension = true, blocking = true)
    suspend fun sendViaSelect(@Param(name = "value") value: Int): Any = try {
        select<Unit> { c.onSend(value) {} }
    } catch (e: NumberedCancellationException) {
        e.testResult
    }
}

@Param.Params(
    Param(name = "value", gen = IntGen::class, conf = "1:9"),
    Param(name = "closeToken", gen = IntGen::class, conf = "1:9")
)
abstract class ChannelLincheckTestBase(
    protected val c: Channel<Int>,
    private val sequentialSpecification: Class<*>,
    private val obstructionFree: Boolean = true
) : AbstractLincheckTest() {

    @Operation(allowExtraSuspension = true, blocking = true)
    suspend fun send(@Param(name = "value") value: Int): Any = try {
        c.send(value)
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    // @Operation TODO: `trySend()` is not linearizable as it can fail due to postponed buffer expansion
    //            TODO: or make a rendezvous with `tryReceive`, which violates the sequential specification.
    open fun trySend(@Param(name = "value") value: Int): Any = c.trySend(value)
        .onSuccess { return true }
        .onFailure {
            return if (it is NumberedCancellationException) it.testResult
            else false
        }

    @Operation(allowExtraSuspension = true, blocking = true)
    suspend fun receive(): Any = try {
        c.receive()
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    @Operation(allowExtraSuspension = true, blocking = true)
    suspend fun receiveCatching(): Any = c.receiveCatching()
        .onSuccess { return it }
        .onClosed { e -> return (e as NumberedCancellationException).testResult }

    @Operation(blocking = true)
    fun tryReceive(): Any? =
        c.tryReceive()
            .onSuccess { return it }
            .onFailure { return if (it is NumberedCancellationException) it.testResult else null }

    @Operation(allowExtraSuspension = true, blocking = true)
    suspend fun receiveViaSelect(): Any = try {
        select<Int> { c.onReceive { it } }
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    @Operation(causesBlocking = true, blocking = true)
    fun close(@Param(name = "closeToken") token: Int): Boolean = c.close(NumberedCancellationException(token))

    @Operation(causesBlocking = true, blocking = true)
    fun cancel(@Param(name = "closeToken") token: Int) = c.cancel(NumberedCancellationException(token))

    // @Operation TODO non-linearizable in BufferedChannel
    open fun isClosedForReceive() = c.isClosedForReceive

    @Operation(blocking = true)
    fun isClosedForSend() = c.isClosedForSend

    // @Operation TODO non-linearizable in BufferedChannel
    open fun isEmpty() = c.isEmpty

    @StateRepresentation
    fun state() = (c as? BufferedChannel<*>)?.toStringDebug() ?: c.toString()

    @Validate
    fun validate() {
        (c as? BufferedChannel<*>)?.checkSegmentStructureInvariants()
    }

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean) =
        actorsBefore(0).sequentialSpecification(sequentialSpecification)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom(obstructionFree)
}

private class NumberedCancellationException(number: Int) : CancellationException() {
    val testResult = "Closed($number)"
}


abstract class SequentialIntChannelBase(private val capacity: Int) : VerifierState() {
    private val senders   = ArrayList<Pair<CancellableContinuation<Any>, Int>>()
    private val receivers = ArrayList<CancellableContinuation<Any>>()
    private val buffer = ArrayList<Int>()
    private var closedMessage: String? = null

    suspend fun send(x: Int): Any = when (val offerRes = trySend(x)) {
        true -> Unit
        false -> suspendCancellableCoroutine { cont ->
            senders.add(cont to x)
        }
        else -> offerRes
    }

    fun trySend(element: Int): Any {
        if (closedMessage !== null) return closedMessage!!
        if (capacity == CONFLATED) {
            if (resumeFirstReceiver(element)) return true
            buffer.clear()
            buffer.add(element)
            return true
        }
        if (resumeFirstReceiver(element)) return true
        if (buffer.size < capacity) {
            buffer.add(element)
            return true
        }
        return false
    }

    private fun resumeFirstReceiver(element: Int): Boolean {
        while (receivers.isNotEmpty()) {
            val r = receivers.removeAt(0)
            if (r.resume(element)) return true
        }
        return false
    }

    suspend fun receive(): Any = tryReceive() ?: suspendCancellableCoroutine { cont ->
        receivers.add(cont)
    }

    suspend fun receiveCatching() = receive()

    fun tryReceive(): Any? {
        if (buffer.isNotEmpty()) {
            val el = buffer.removeAt(0)
            resumeFirstSender().also {
                if (it !== null) buffer.add(it)
            }
            return el
        }
        resumeFirstSender()?.also { return it }
        if (closedMessage !== null) return closedMessage
        return null
    }

    private fun resumeFirstSender(): Int? {
        while (senders.isNotEmpty()) {
            val (s, el) = senders.removeAt(0)
            if (s.resume(Unit)) return el
        }
        return null
    }

    suspend fun sendViaSelect(element: Int) = send(element)
    suspend fun receiveViaSelect() = receive()

    fun close(token: Int): Boolean {
        if (closedMessage !== null) return false
        closedMessage = "Closed($token)"
        for (r in receivers) r.resume(closedMessage!!)
        receivers.clear()
        return true
    }

    fun cancel(token: Int) {
        close(token)
        for ((s, _) in senders) s.resume(closedMessage!!)
        senders.clear()
        buffer.clear()
    }

    fun isClosedForSend(): Boolean = closedMessage !== null
    fun isClosedForReceive(): Boolean = isClosedForSend() && buffer.isEmpty() && senders.isEmpty()

    fun isEmpty(): Boolean {
        if (closedMessage !== null) return false
        return buffer.isEmpty() && senders.isEmpty()
    }

    override fun extractState() = buffer to closedMessage
}

private fun <T> CancellableContinuation<T>.resume(res: T): Boolean {
    val token = tryResume(res) ?: return false
    completeResume(token)
    return true
}
