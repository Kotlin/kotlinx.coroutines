/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * [TypedActor] is the base for all stateful actors, which can process only one [type][T] of messages.
 * [TypedActor] has well-defined lifecycle described in [ActorTraits].
 * [TypedActor.receive] method is used to declare a message handler, which is parametrized by [T]
 * to provide better compile-type safety.
 *
 * Example:
 * ```
 * class ExampleActor : TypedActor<String>() {
 *
 *   override suspend fun receive(string: String) = act {
 *     println("Received $string")
 *   }
 * }
 *
 * // Sender
 * exampleActor.send("foo")
 * ```
 *
 * @param T type of the message this actor can handle
 * @param context context in which actor's job will be launched
 * @param parent optional parent of actor's job
 * @param start start mode of actor's job
 * @param channelCapacity capacity of actor's mailbox aka maximum count of pending messages
 */
@Suppress("EXPOSED_SUPER_CLASS")
abstract class TypedActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : AbstractActor<T>(context, parent, start, channelCapacity) {


    /**
     * Sends the message to the actor, which later will be sequentially processed by [receive].
     * Sender is suspended, if actor's channel capacity is reached. This suspension is cancellable
     * and has semantics similar to [SendChannel.send]
     *
     * @throws ClosedSendChannelException if actor is [closed][close]
     */
    suspend fun send(message: T) {
        job.start()
        mailbox.send(message)
    }

    /**
     * Attempts to send message to the actor, which later will be sequentially processed by [receive].
     * Attempt is successful if actor's channel capacity restriction is not violated.
     * This method is intended to be used from synchronous callbacks with [Channel.UNLIMITED]
     *
     * @throws ClosedSendChannelException if actor is [closed][close]
     * @return `true` if offer was successful, false otherwise
     */
    fun offer(message: T): Boolean {
        job.start()
        return mailbox.offer(message)
    }

    /**
     * Handler, which handles all received messages.
     *
     * @throws ClassCastException if actor was casted to raw type and [send] was invoked with wrong type of the argument
     */
    protected abstract suspend fun receive(message: T)

    internal override suspend fun onMessage(message: T) {
        receive(message)
    }
}
