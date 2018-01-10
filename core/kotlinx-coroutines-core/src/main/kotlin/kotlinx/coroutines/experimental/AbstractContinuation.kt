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

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
internal abstract class AbstractContinuation<in T>(
    public final override val delegate: Continuation<T>,
    public final override val resumeMode: Int
) : JobSupport(true), Continuation<T>, DispatchedTask<T> {
    private val _decision = atomic(UNDECIDED)

    /* decision state machine

        +-----------+   trySuspend   +-----------+
        | UNDECIDED | -------------> | SUSPENDED |
        +-----------+                +-----------+
              |
              | tryResume
              V
        +-----------+
        |  RESUMED  |
        +-----------+

        Note: both tryResume and trySuspend can be invoked at most once, first invocation wins
     */

    override fun takeState(): Any? = state

    private fun trySuspend(): Boolean {
        _decision.loop { decision ->
            when (decision) {
                UNDECIDED -> if (this._decision.compareAndSet(UNDECIDED, SUSPENDED)) return true
                RESUMED -> return false
                else -> error("Already suspended")
            }
        }
    }

    private fun tryResume(): Boolean {
        _decision.loop { decision ->
            when (decision) {
                UNDECIDED -> if (this._decision.compareAndSet(UNDECIDED, RESUMED)) return true
                SUSPENDED -> return false
                else -> error("Already resumed")
            }
        }
    }

    @PublishedApi
    internal fun getResult(): Any? {
        if (trySuspend()) return COROUTINE_SUSPENDED
        // otherwise, afterCompletion was already invoked & invoked tryResume, and the result is in the state
        val state = this.state
        if (state is CompletedExceptionally) throw state.exception
        return getSuccessfulResult(state)
    }

    override fun afterCompletion(state: Any?, mode: Int) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // otherwise, getResult has already commenced, i.e. completed later or in other thread
        dispatch(mode)
    }

    override fun resume(value: T) =
        resumeImpl(value, resumeMode)

    override fun resumeWithException(exception: Throwable) =
        resumeImpl(CompletedExceptionally(exception), resumeMode)

    protected fun resumeImpl(proposedUpdate: Any?, resumeMode: Int) {
        loopOnState { state ->
            when (state) {
                is Incomplete -> {
                    if (updateState(state, proposedUpdate, resumeMode)) return
                }
                is Cancelled -> {
                    // Ignore resumes in cancelled coroutines, but handle exception if a different one here
                    if (proposedUpdate is CompletedExceptionally && proposedUpdate.exception != state.exception)
                        handleException(proposedUpdate.exception)
                    return
                }
                else -> error("Already resumed, but got $proposedUpdate")
            }
        }
    }

    override fun handleException(exception: Throwable) {
        handleCoroutineException(context, exception)
    }
}