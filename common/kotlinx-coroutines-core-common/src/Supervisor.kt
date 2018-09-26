/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

/**
 * Creates a new _supervisor_ job object in an active state.
 * Children of a supervisor job can fail independently of each other.
 * 
 * A failure or cancellation of a child does not cause the supervisor job to fail and does not affect its other children,
 * so a supervisor can implement a custom policy for handling failures of its children:
 *
 * * A failure of a child job that was created using [launch][CoroutineScope.launch] can be handled via [CoroutineExceptionHandler] in the context.
 * * A failure of a child job that was created using [async][CoroutineScope.async] can be handled via [Deferred.await] on the resulting deferred value.
 *
 * If [parent] job is specified, then this supervisor job becomes a child job of its parent and is cancelled when its
 * parent fails or is cancelled. All this supervisor's children are cancelled in this case, too. The invocation of
 * of [cancel][Job.cancel] with exception (other than [CancellationException]) on this supervisor job also cancels parent.
 *
 * @param parent an optional parent job.
 */
@Suppress("FunctionName")
public fun SupervisorJob(parent: Job? = null) : Job = SupervisorJobImpl(parent)

/**
 * Creates new [CoroutineScope] with [SupervisorJob] and calls the specified suspend block with this scope.
 * The provided scope inherits its [coroutineContext][CoroutineScope.coroutineContext] from the outer scope, but overrides
 * context's [Job] with [SupervisorJob].
 *
 * A failure of a child does not cause this scope to fail and does not affect its other children,
 * so a custom policy for handling failures of its children can be implemented. See [SupervisorJob] for details.
 * A failure of the scope itself (exception thrown in the [block] or cancellation) fails the scope with all its children,
 * but does not cancel parent job.
 */
public suspend fun <R>  supervisorScope(block: suspend CoroutineScope.() -> R): R {
    // todo: optimize implementation to a single allocated object
    // todo: fix copy-and-paste with coroutineScope
    val owner = SupervisorCoroutine<R>(coroutineContext)
    owner.start(CoroutineStart.UNDISPATCHED, owner, block)
    owner.join()
    if (owner.isCancelled) {
        throw owner.getCancellationException().let { it.cause ?: it }
    }
    val state = owner.state
    if (state is CompletedExceptionally) {
        throw state.cause
    }
    @Suppress("UNCHECKED_CAST")
    return state as R

}

private class SupervisorJobImpl(parent: Job?) : JobSupport(true) {
    init { initParentJobInternal(parent) }
    override val cancelsParent: Boolean get() = true
    override val onCancelComplete get() = true
    override val handlesException: Boolean get() = false
    override fun childCancelled(cause: Throwable): Boolean = false
}

private class SupervisorCoroutine<R>(
    parentContext: CoroutineContext
) : AbstractCoroutine<R>(parentContext, true) {
    override val cancelsParent: Boolean get() = false
    override fun childCancelled(cause: Throwable): Boolean = false
}
