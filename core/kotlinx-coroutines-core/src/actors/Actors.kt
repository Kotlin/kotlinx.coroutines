/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*


/**
 * Creates a new [TypedActor] with given [block] as [message handler][TypedActor.receive]
 *
 * @param context context in which actor's job will be launched
 * @param parent optional parent of actor's job
 * @param start start mode of actor's job
 * @param channelCapacity capacity of actor's mailbox aka maximum count of pending messages
 * @param block actor's message handler
 */
public fun <T> actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: ActorTraits,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16, block: suspend TypedActor<T>.(T) -> Unit
): TypedActor<T> {
    return actor(context, parent.job, start, channelCapacity, block)
}

/**
 * Creates a new [TypedActor] with given [block] as [message handler][TypedActor.receive]
 *
 * @param context context in which actor's job will be launched
 * @param parent optional parent of actor's job
 * @param start start mode of actor's job
 * @param channelCapacity capacity of actor's mailbox aka maximum count of pending messages
 * @param block actor's message handler
 */
public fun <T> actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16, block: suspend TypedActor<T>.(T) -> Unit
): TypedActor<T> {
    return object : TypedActor<T>(context, parent, start, channelCapacity) {
        override suspend fun receive(message: T) {
            block(message)
        }
    }
}
