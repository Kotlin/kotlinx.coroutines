/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*

open class BroadcastChannelLincheckTestBase(
    private val c: BroadcastChannel<Int>
) : AbstractLincheckTest() {
    private val subs = arrayOfNulls<ReceiveChannel<Int>?>(10)

    @Operation(blocking = true)
    fun openSubscription(@Param(gen = ThreadIdGen::class) threadId: Int): Boolean =
        if (subs[threadId] === null) {
            subs[threadId] = c.openSubscription()
            true
        } else {
            false
        }

    @Operation(blocking = true)
    fun cancelSubscription(@Param(gen = ThreadIdGen::class) threadId: Int): Boolean =
        if (subs[threadId] !== null) {
            subs[threadId]!!.cancel()
            subs[threadId] = null
            true
        } else {
            false
        }

    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true, blocking = true)
    suspend fun send(element: Int) = c.send(element)

    @Operation(blocking = true)
    fun offer(element: Int) = c.offer(element)

    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true, blocking = true,
               handleExceptionsAsResult = [CancellationException::class])
    suspend fun receive(@Param(gen = ThreadIdGen::class) threadId: Int): Int? =
        subs[threadId]?.receive()

    @Operation(handleExceptionsAsResult = [CancellationException::class])
    fun poll(@Param(gen = ThreadIdGen::class) threadId: Int): Int? = subs[threadId]?.poll()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0).requireStateEquivalenceImplCheck(false)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        verboseTrace()

    override fun extractState() = c // inefficient but should work
}

class ConflatedBroadcastChannelLincheckTest : BroadcastChannelLincheckTestBase(
    c = ConflatedBroadcastChannel()
)