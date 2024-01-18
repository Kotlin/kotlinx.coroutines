@file:Suppress("unused", "UNUSED_PARAMETER")

package kotlinx.coroutines.debug.internal

import kotlin.coroutines.*

/*
 * Empty class used to replace installed agent in the end of debug session
 */
@JvmName("probeCoroutineResumed")
internal fun probeCoroutineResumedNoOp(frame: Continuation<*>) = Unit
@JvmName("probeCoroutineSuspended")
internal fun probeCoroutineSuspendedNoOp(frame: Continuation<*>) = Unit
@JvmName("probeCoroutineCreated")
internal fun <T> probeCoroutineCreatedNoOp(completion: kotlin.coroutines.Continuation<T>): kotlin.coroutines.Continuation<T> = completion
