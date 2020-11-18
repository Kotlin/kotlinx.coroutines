/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

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
import org.jetbrains.kotlinx.lincheck.verifier.*

class RendezvousChannelLincheckTest : ChannelLincheckTestBase(
    c = Channel(RENDEZVOUS),
    sequentialSpecification = SequentialRendezvousChannel::class.java
)
class SequentialRendezvousChannel : SequentialIntChannelBase(RENDEZVOUS)

class Array1ChannelLincheckTest : ChannelLincheckTestBase(
    c = Channel(1),
    sequentialSpecification = SequentialArray1RendezvousChannel::class.java
)
class SequentialArray1RendezvousChannel : SequentialIntChannelBase(1)

class Array2ChannelLincheckTest : ChannelLincheckTestBase(
    c = Channel(2),
    sequentialSpecification = SequentialArray2RendezvousChannel::class.java
)
class SequentialArray2RendezvousChannel : SequentialIntChannelBase(2)

class UnlimitedChannelLincheckTest : ChannelLincheckTestBase(
    c = Channel(UNLIMITED),
    sequentialSpecification = SequentialUnlimitedChannel::class.java
)
class SequentialUnlimitedChannel : SequentialIntChannelBase(UNLIMITED)

class ConflatedChannelLincheckTest : ChannelLincheckTestBase(
    c = Channel(CONFLATED),
    sequentialSpecification = SequentialConflatedChannel::class.java
)
class SequentialConflatedChannel : SequentialIntChannelBase(CONFLATED)

@Param.Params(
    Param(name = "value", gen = IntGen::class, conf = "1:5"),
    Param(name = "closeToken", gen = IntGen::class, conf = "1:3")
)
abstract class ChannelLincheckTestBase(
    private val c: Channel<Int>,
    private val sequentialSpecification: Class<*>
) : AbstractLincheckTest() {
    @Operation(promptCancellation = true)
    suspend fun send(@Param(name = "value") value: Int): Any = try {
        c.send(value)
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    @Operation
    fun offer(@Param(name = "value") value: Int): Any = try {
        c.offer(value)
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    // TODO: this operation should be (and can be!) linearizable, but is not
    // @Operation
    suspend fun sendViaSelect(@Param(name = "value") value: Int): Any = try {
        select<Unit> { c.onSend(value) {} }
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    @Operation(promptCancellation = true)
    suspend fun receive(): Any = try {
        c.receive()
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    @Operation
    fun poll(): Any? = try {
        c.poll()
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    // TODO: this operation should be (and can be!) linearizable, but is not
    // @Operation
    suspend fun receiveViaSelect(): Any = try {
        select<Int> { c.onReceive { it } }
    } catch (e: NumberedCancellationException) {
        e.testResult
    }

    @Operation(causesBlocking = true)
    fun close(@Param(name = "closeToken") token: Int): Boolean = c.close(NumberedCancellationException(token))

    // TODO: this operation should be (and can be!) linearizable, but is not
    // @Operation
    fun cancel(@Param(name = "closeToken") token: Int) = c.cancel(NumberedCancellationException(token))

    // @Operation
    fun isClosedForReceive() = c.isClosedForReceive

    // @Operation
    fun isClosedForSend() = c.isClosedForSend

    // TODO: this operation should be (and can be!) linearizable, but is not
    // @Operation
    fun isEmpty() = c.isEmpty

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0).sequentialSpecification(sequentialSpecification)
}

private class NumberedCancellationException(number: Int) : CancellationException() {
    val testResult = "Closed($number)"
}


abstract class SequentialIntChannelBase(private val capacity: Int) : VerifierState() {
    private val senders   = ArrayList<Pair<CancellableContinuation<Any>, Int>>()
    private val receivers = ArrayList<CancellableContinuation<Any>>()
    private val buffer = ArrayList<Int>()
    private var closedMessage: String? = null

    suspend fun send(x: Int): Any = when (val offerRes = offer(x)) {
        true -> Unit
        false -> suspendCancellableCoroutine { cont ->
            senders.add(cont to x)
        }
        else -> offerRes
    }

    fun offer(element: Int): Any {
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

    suspend fun receive(): Any = poll() ?: suspendCancellableCoroutine { cont ->
        receivers.add(cont)
    }

    fun poll(): Any? {
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
        if (!close(token)) return
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