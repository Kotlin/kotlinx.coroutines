/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.intrinsics

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * Use this function to restart coroutine directly from inside of [suspendCoroutine].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN", "UNCHECKED_CAST")
internal fun <T> (suspend () -> T).startCoroutineUndispatched(completion: Continuation<T>) {
    val value = try {
        startCoroutineUninterceptedOrReturn(completion)
    } catch (e: Throwable) {
        completion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED)
        completion.resume(value as T)
}

/**
 * Use this function to restart coroutine directly from inside of [suspendCoroutine].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN", "UNCHECKED_CAST")
internal fun <R, T> (suspend (R) -> T).startCoroutineUndispatched(receiver: R, completion: Continuation<T>) {
    val value = try {
        startCoroutineUninterceptedOrReturn(receiver, completion)
    } catch (e: Throwable) {
        completion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED)
        completion.resume(value as T)
}

/**
 * Starts the corresponding block as a coroutine with this coroutine start strategy.
 *
 * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
 * during construction. Second, it starts the coroutine using [startCoroutineUninterceptedOrReturn].
 *
 * This function shall be invoked at most once.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public fun <T> AbstractCoroutine<T>.startUndispatchedOrReturn(block: suspend () -> T): Any? {
    initParentJob()
    return undispatchedResult { block.startCoroutineUninterceptedOrReturn(this) }
}

/**
 * Starts the corresponding block with receiver as a coroutine with this coroutine start strategy.
 *
 * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
 * during construction. Second, it starts the coroutine using [startCoroutineUninterceptedOrReturn].
 *
 * This function shall be invoked at most once.
 * 
 * @suppress **This is unstable API and it is subject to change.**
 */
public fun <T, R> AbstractCoroutine<T>.startUndispatchedOrReturn(receiver: R, block: suspend R.() -> T): Any? {
    initParentJob()
    return undispatchedResult { block.startCoroutineUninterceptedOrReturn(receiver, this) }
}

private inline fun <T> AbstractCoroutine<T>.undispatchedResult(startBlock: () -> Any?): Any? {
    val result = try {
        startBlock()
    } catch (e: Throwable) {
        CompletedExceptionally(e)
    }
    return when {
        result == COROUTINE_SUSPENDED -> COROUTINE_SUSPENDED
        makeCompletingOnce(result, MODE_IGNORE) -> {
            if (result is CompletedExceptionally) throw result.exception else result
        }
        else -> COROUTINE_SUSPENDED
    }
}