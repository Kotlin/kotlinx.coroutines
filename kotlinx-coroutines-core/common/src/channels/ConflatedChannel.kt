/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.selects.*
import kotlinx.coroutines.internal.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `offer` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [offer] always returns `true`.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 *
 * This implementation is fully lock-free.
 */
internal open class ConflatedChannel<E> : BufferedChannel<E>(Channel.UNLIMITED) {
    override suspend fun send(element: E) {
        offerConflated(element)
    }

    override fun offer(element: E): Boolean {
        offerConflated(element)
        return true
    }

    override fun close(cause: Throwable?): Boolean {
        return super.cancelImpl(cause)
    }

    override val onSend: SelectClause2<E, SendChannel<E>> get() = SelectClause2Impl(
            objForSelect = this,
            regFunc = ConflatedChannel<*>::onSendRegFunction as RegistrationFunction,
            processResFunc = ConflatedChannel<*>::onSendProcessResFunction as ProcessResultFunction
    )

    private fun onSendRegFunction(select: SelectInstance<*>, element: E) {
        offerConflated(element)
        select.selectInRegPhase(Unit)
    }

    private fun onSendProcessResFunction(ignoredElement: E, ignoredSelectResult: Any?): Any? = this
}
