/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.internalAnnotations.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * A concrete implementation of [Job]. It is optionally a child to a parent job.
 * This job is cancelled when the parent is complete, but not vise-versa.
 *
 * This is an open class designed for extension by more specific classes that might augment the
 * state and mare store addition state information for completed jobs, like their result values.
 *
 * @param active when `true` the job is created in _active_ state, when `false` in _new_ state. See [Job] for details.
 * @suppress **This is unstable API and it is subject to change.**
 */
internal open class JobSupport constructor(active: Boolean) : Job, SelectClause0 {
    final override val key: CoroutineContext.Key<*> get() = Job

    /*
       === Internal states ===

       name       state class    public state  description
       ------     ------------   ------------  -----------
       EMPTY_N    EmptyNew     : New           no listeners
       EMPTY_A    EmptyActive  : Active        no listeners
       SINGLE     JobNode      : Active        a single listener
       SINGLE+    JobNode      : Active        a single listener + NodeList added as its next
       LIST_N     NodeList     : New           a list of listeners (promoted once, does not got back to EmptyNew)
       LIST_A     NodeList     : Active        a list of listeners (promoted once, does not got back to JobNode/EmptyActive)
       COMPLETING Finishing    : Completing    has a list of listeners (promoted once from LIST_*)
       CANCELLING Finishing    : Cancelling    has a list of listeners (promoted once from LIST_*)
       FINAL_C    Cancelled    : Cancelled     cancelled (final state)
       FINAL_F    Failed       : Completed     failed for other reason (final state)
       FINAL_R    <any>        : Completed     produced some result

       === Transitions ===

           New states      Active states       Inactive states

          +---------+       +---------+                          }
          | EMPTY_N | --+-> | EMPTY_A | ----+                    } Empty states
          +---------+   |   +---------+     |                    }
               |        |     |     ^       |    +----------+
               |        |     |     |       +--> |  FINAL_* |
               |        |     V     |       |    +----------+
               |        |   +---------+     |                    }
               |        |   | SINGLE  | ----+                    } JobNode states
               |        |   +---------+     |                    }
               |        |        |          |                    }
               |        |        V          |                    }
               |        |   +---------+     |                    }
               |        +-- | SINGLE+ | ----+                    }
               |            +---------+     |                    }
               |                 |          |
               V                 V          |
          +---------+       +---------+     |                    }
          | LIST_N  | ----> | LIST_A  | ----+                    } NodeList states
          +---------+       +---------+     |                    }
             |   |             |   |        |
             |   |    +--------+   |        |
             |   |    |            V        |
             |   |    |    +------------+   |   +------------+   }
             |   +-------> | COMPLETING | --+-- | CANCELLING |   } Finishing states
             |        |    +------------+       +------------+   }
             |        |         |                    ^
             |        |         |                    |
             +--------+---------+--------------------+


       This state machine and its transition matrix are optimized for the common case when job is created in active
       state (EMPTY_A) and at most one completion listener is added to it during its life-time.

       Note, that the actual `_state` variable can also be a reference to atomic operation descriptor `OpDescriptor`
     */

    // Note: use shared objects while we have no listeners
    private val _state = atomic<Any?>(if (active) EmptyActive else EmptyNew)

    @Volatile
    private var parentHandle: DisposableHandle? = null

    // ------------ initialization ------------

    /**
     * Initializes parent job.
     * It shall be invoked at most once after construction after all other initialization.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun initParentJobInternal(parent: Job?) {
        check(parentHandle == null)
        if (parent == null) {
            parentHandle = NonDisposableHandle
            return
        }
        parent.start() // make sure the parent is started
        @Suppress("DEPRECATION")
        val handle = parent.attachChild(this)
        parentHandle = handle
        // now check our state _after_ registering (see updateState order of actions)
        if (isCompleted) {
            handle.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    // ------------ state query ------------

    /**
     * Returns current state of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal val state: Any? get() {
        _state.loop { state -> // helper loop on state (complete in-progress atomic operations)
            if (state !is OpDescriptor) return state
            state.perform(this)
        }
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    private inline fun loopOnState(block: (Any?) -> Unit): Nothing {
        while (true) {
            block(state)
        }
    }

    public final override val isActive: Boolean get() {
        val state = this.state
        return state is Incomplete && state.isActive
    }

    public final override val isCompleted: Boolean get() = state !is Incomplete

    public final override val isCancelled: Boolean get() {
        val state = this.state
        return state is Cancelled || (state is Finishing && state.cancelled != null)
    }

    // ------------ state update ------------

    /**
     * Updates current [state] of this job. Returns `false` if current state is not equal to expected.
     * @suppress **This is unstable API and it is subject to change.**
     */
    private fun updateState(expect: Incomplete, proposedUpdate: Any?, mode: Int): Boolean {
        val update = coerceProposedUpdate(expect, proposedUpdate)
        if (!tryUpdateState(expect, update)) return false
        completeUpdateState(expect, update, mode)
        return true
    }

    // when Job is in Cancelling state, it can only be promoted to Cancelled state,
    // so if the proposed Update is not an appropriate Cancelled (preserving the cancellation cause),
    // then the corresponding Cancelled state is constructed.
    private fun coerceProposedUpdate(expect: Incomplete, proposedUpdate: Any?): Any? =
        if (expect is Finishing && expect.cancelled != null && !isCorrespondinglyCancelled(expect.cancelled, proposedUpdate))
            createCancelled(expect.cancelled, proposedUpdate) else proposedUpdate

    private fun isCorrespondinglyCancelled(cancelled: Cancelled, proposedUpdate: Any?): Boolean {
        if (proposedUpdate !is Cancelled) return false
        // NOTE: equality comparison of causes is performed here by design, see equals of JobCancellationException
        return proposedUpdate.cause == cancelled.cause || proposedUpdate.cause is JobCancellationException
    }

    private fun createCancelled(cancelled: Cancelled, proposedUpdate: Any?): Cancelled {
        if (proposedUpdate !is CompletedExceptionally) return cancelled // not exception -- just use original cancelled
        val exception = proposedUpdate.cause
        if (cancelled.cause == exception) return cancelled // that is the cancelled we need already!
        // todo: We need to rework this logic to keep original cancellation cause in the state and suppress other exceptions
        //       that could have occurred while coroutine is being cancelled.
        // Do not spam with JCE in suppressed exceptions
        if (cancelled.cause !is JobCancellationException) {
            exception.addSuppressedThrowable(cancelled.cause)
        }
        return Cancelled(this, exception)
    }

    /**
     * Tries to initiate update of the current [state] of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    private fun tryUpdateState(expect: Incomplete, update: Any?): Boolean  {
        require(update !is Incomplete) // only incomplete -> completed transition is allowed
        if (!_state.compareAndSet(expect, update)) return false
        // Unregister from parent job
        parentHandle?.let {
            it.dispose() // volatile read parentHandle _after_ state was updated
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
        return true // continues in completeUpdateState
    }

    /**
     * Completes update of the current [state] of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    private fun completeUpdateState(expect: Incomplete, update: Any?, mode: Int) {
        val exceptionally = update as? CompletedExceptionally
        // Do overridable processing before completion handlers

        /*
         * 1) Invoke onCancellationInternal: exception handling, parent/resource cancellation etc.
         * 2) Invoke completion handlers: .join(), callbacks etc. It's important to invoke them only AFTER exception handling, see #208
         * 3) Invoke onCompletionInternal: onNext(), timeout deregistration etc. I should be last so all callbacks observe consistent state
         *    of the job which doesn't depend on callback scheduling
         *
         * Only notify on cancellation once (expect.isCancelling)
         */
        if (!expect.isCancelling) onCancellationInternal(exceptionally)

        // Invoke completion handlers
        val cause = exceptionally?.cause
        if (expect is JobNode<*>) { // SINGLE/SINGLE+ state -- one completion handler (common case)
            try {
                expect.invoke(cause)
            } catch (ex: Throwable) {
                handleException(CompletionHandlerException("Exception in completion handler $expect for $this", ex))
            }
        } else {
            expect.list?.notifyCompletion(cause)
        }

        onCompletionInternal(update, mode)
    }

    private inline fun <reified T: JobNode<*>> notifyHandlers(list: NodeList, cause: Throwable?) {
        var exception: Throwable? = null
        list.forEach<T> { node ->
            try {
                node.invoke(cause)
            } catch (ex: Throwable) {
                exception?.apply { addSuppressedThrowable(ex) } ?: run {
                    exception =  CompletionHandlerException("Exception in completion handler $node for $this", ex)
                }
            }
        }
        exception?.let { handleException(it) }
    }

    private fun NodeList.notifyCompletion(cause: Throwable?) =
        notifyHandlers<JobNode<*>>(this, cause)

    private fun notifyCancellation(list: NodeList, cause: Throwable?) =
        notifyHandlers<JobCancellationNode<*>>(list, cause)

    public final override fun start(): Boolean {
        loopOnState { state ->
            when (startInternal(state)) {
                FALSE -> return false
                TRUE -> return true
            }
        }
    }

    // returns: RETRY/FALSE/TRUE:
    //   FALSE when not new,
    //   TRUE  when started
    //   RETRY when need to retry
    private fun startInternal(state: Any?): Int {
        when (state) {
            is Empty -> { // EMPTY_X state -- no completion handlers
                if (state.isActive) return FALSE // already active
                if (!_state.compareAndSet(state, EmptyActive)) return RETRY
                onStartInternal()
                return TRUE
            }
            is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                return state.tryMakeActive().also { result ->
                    if (result == TRUE) onStartInternal()
                }
            }
            else -> return FALSE // not a new state
        }
    }

    /**
     * Override to provide the actual [start] action.
     * This function is invoked exactly once when non-active coroutine is [started][start].
     */
    internal open fun onStartInternal() {}

    public final override fun getCancellationException(): CancellationException {
        val state = this.state
        return when {
            state is Finishing && state.cancelled != null ->
                state.cancelled.cause.toCancellationException("Job is being cancelled")
            state is Incomplete ->
                error("Job was not completed or cancelled yet: $this")
            state is CompletedExceptionally ->
                state.cause.toCancellationException("Job has failed")
            else -> JobCancellationException("Job has completed normally", null, this)
        }
    }

    private fun Throwable.toCancellationException(message: String): CancellationException =
        this as? CancellationException ?: JobCancellationException(message, this, this@JobSupport)

    /**
     * Returns the cause that signals the completion of this job -- it returns the original
     * [cancel] cause, [JobCancellationException] or **`null` if this job had completed normally**.
     * This function throws [IllegalStateException] when invoked for an job that has not [completed][isCompleted] nor
     * [isCancelled] yet.
     */
    protected fun getCompletionCause(): Throwable? {
        val state = this.state
        return when {
            state is Finishing && state.cancelled != null -> state.cancelled.cause
            state is Incomplete -> error("Job was not completed or cancelled yet")
            state is CompletedExceptionally -> state.cause
            else -> null
        }
    }

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        invokeOnCompletion(onCancelling = false, invokeImmediately = true, handler = handler)

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle =
        invokeOnCompletion(onCancelling = onCancelling, invokeImmediately = true, handler = handler)

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(onCancelling_: Boolean, handler: CompletionHandler): DisposableHandle =
        invokeOnCompletion(onCancelling = onCancelling_, invokeImmediately = true, handler = handler)

    // todo: non-final as a workaround for KT-21968, should be final in the future
    public override fun invokeOnCompletion(
        onCancelling: Boolean,
        invokeImmediately: Boolean,
        handler: CompletionHandler
    ): DisposableHandle {
        var nodeCache: JobNode<*>? = null
        loopOnState { state ->
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        // try move to SINGLE state
                        val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                        if (_state.compareAndSet(state, node)) return node
                    } else
                        promoteEmptyToNodeList(state) // that way we can add listener for non-active coroutine
                }
                is Incomplete -> {
                    val list = state.list
                    if (list == null) { // SINGLE/SINGLE+
                        promoteSingleToNodeList(state as JobNode<*>)
                    } else {
                        if (state is Finishing && state.cancelled != null && onCancelling) {
                            // installing cancellation handler on job that is being cancelled
                            if (invokeImmediately) handler(state.cancelled.cause)
                            return NonDisposableHandle
                        }
                        val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                        if (addLastAtomic(state, list, node)) return node
                    }
                }
                else -> { // is complete
                    // :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
                    // because we play type tricks on Kotlin/JS and handler is not necessarily a function there
                    if (invokeImmediately) handler.invokeIt((state as? CompletedExceptionally)?.cause)
                    return NonDisposableHandle
                }
            }
        }
    }

    private fun makeNode(handler: CompletionHandler, onCancelling: Boolean): JobNode<*> {
        return if (onCancelling)
            (handler as? JobCancellationNode<*>)?.also { require(it.job === this) }
                ?: InvokeOnCancellation(this, handler)
        else
            (handler as? JobNode<*>)?.also { require(it.job === this && it !is JobCancellationNode) }
                ?: InvokeOnCompletion(this, handler)
    }

    private fun addLastAtomic(expect: Any, list: NodeList, node: JobNode<*>) =
        list.addLastIf(node) { this.state === expect }

    private fun promoteEmptyToNodeList(state: Empty) {
        // try to promote it to list in new state
        _state.compareAndSet(state, NodeList(state.isActive))
    }

    private fun promoteSingleToNodeList(state: JobNode<*>) {
        // try to promote it to list (SINGLE+ state)
        state.addOneIfEmpty(NodeList(active = true))
        // it must be in SINGLE+ state or state has changed (node could have need removed from state)
        val list = state.nextNode // either our NodeList or somebody else won the race, updated state
        // just attempt converting it to list if state is still the same, then we'll continue lock-free loop
        _state.compareAndSet(state, list)
    }

    public final override suspend fun join() {
        if (!joinInternal()) { // fast-path no wait
            return suspendCoroutineOrReturn { cont ->
                cont.context.checkCompletion()
                Unit // do not suspend
            }
        }
        return joinSuspend() // slow-path wait
    }

    private fun joinInternal(): Boolean {
        loopOnState { state ->
            if (state !is Incomplete) return false // not active anymore (complete) -- no need to wait
            if (startInternal(state) >= 0) return true // wait unless need to retry
        }
    }

    private suspend fun joinSuspend() = suspendCancellableCoroutine<Unit> { cont ->
        // We have to invoke join() handler only on cancellation, on completion we will be resumed regularly without handlers
        cont.disposeOnCancellation(invokeOnCompletion(handler = ResumeOnCompletion(this, cont).asHandler))
    }

    public final override val onJoin: SelectClause0
        get() = this

    // registerSelectJoin
    public final override fun <R> registerSelectClause0(select: SelectInstance<R>, block: suspend () -> R) {
        // fast-path -- check state and select/return if needed
        loopOnState { state ->
            if (select.isSelected) return
            if (state !is Incomplete) {
                // already complete -- select result
                if (select.trySelect(null)) {
                    select.completion.context.checkCompletion() // always check for our completion
                    block.startCoroutineUndispatched(select.completion)
                }
                return
            }
            if (startInternal(state) == 0) {
                // slow-path -- register waiter for completion
                select.disposeOnSelect(invokeOnCompletion(handler = SelectJoinOnCompletion(this, select, block).asHandler))
                return
            }
        }
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun removeNode(node: JobNode<*>) {
        // remove logic depends on the state of the job
        loopOnState { state ->
            when (state) {
                is JobNode<*> -> { // SINGE/SINGLE+ state -- one completion handler
                    if (state !== node) return // a different job node --> we were already removed
                    // try remove and revert back to empty state
                    if (_state.compareAndSet(state, EmptyActive)) return
                }
                is Incomplete -> { // may have a list of completion handlers
                    // remove node from the list if there is a list
                    if (state.list != null) node.remove()
                    return
                }
                else -> return // it is complete and does not have any completion handlers
            }
        }
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open val onCancelMode: Int get() = ON_CANCEL_MAKE_CANCELLING

    public override fun cancel(cause: Throwable?): Boolean = when (onCancelMode) {
        ON_CANCEL_MAKE_CANCELLING -> makeCancelling(cause)
        ON_CANCEL_MAKE_COMPLETING -> makeCompletingOnCancel(cause)
        else -> error("Invalid onCancelMode $onCancelMode")
    }

    // we will be dispatching coroutine to process its cancellation exception, so there is no need for
    // an extra check for Job status in MODE_CANCELLABLE
    private fun updateStateCancelled(state: Incomplete, cause: Throwable?) =
        updateState(state, Cancelled(this, cause), mode = MODE_ATOMIC_DEFAULT)

    // transitions to Cancelling state
    private fun makeCancelling(cause: Throwable?): Boolean {
        loopOnState { state ->
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        promoteEmptyToNodeList(state) // this way can wrap it into Cancelling on next pass
                    } else {
                        // cancelling a non-started coroutine makes it immediately cancelled
                        // (and we have no listeners to notify which makes it very simple)
                        if (updateStateCancelled(state, cause)) return true
                    }
                }
                is JobNode<*> -> { // SINGLE/SINGLE+ state -- one completion handler
                    promoteSingleToNodeList(state)
                }
                is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                    if (state.isActive) {
                        if (tryMakeCancelling(state, state.list, cause)) return true
                    } else {
                        // cancelling a non-started coroutine makes it immediately cancelled
                        if (updateStateCancelled(state, cause))
                            return true
                    }
                }
                is Finishing -> { // Completing/Cancelling the job, may cancel
                    if (state.cancelled != null) return false // already cancelling
                    if (tryMakeCancelling(state, state.list, cause)) return true
                }
                else -> { // is inactive
                    return false
                }
            }
        }
    }

    // try make expected state in cancelling on the condition that we're still in this state
    private fun tryMakeCancelling(expect: Incomplete, list: NodeList, cause: Throwable?): Boolean {
        val cancelled = Cancelled(this, cause)
        if (!_state.compareAndSet(expect, Finishing(list, cancelled, false))) return false
        onFinishingInternal(cancelled)
        onCancellationInternal(cancelled)
        notifyCancellation(list, cause)
        return true
    }

    private fun makeCompletingOnCancel(cause: Throwable?): Boolean =
        makeCompleting(Cancelled(this, cause))

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun makeCompleting(proposedUpdate: Any?): Boolean =
        when (makeCompletingInternal(proposedUpdate, mode = MODE_ATOMIC_DEFAULT)) {
            COMPLETING_ALREADY_COMPLETING -> false
            else -> true
        }

    /**
     * Returns:
     * * `true` if state was updated to completed/cancelled;
     * * `false` if made completing or it is cancelling and is waiting for children.
     *
     * @throws IllegalStateException if job is already complete or completing
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun makeCompletingOnce(proposedUpdate: Any?, mode: Int): Boolean =
        when (makeCompletingInternal(proposedUpdate, mode)) {
            COMPLETING_COMPLETED -> true
            COMPLETING_WAITING_CHILDREN -> false
            else -> throw IllegalStateException("Job $this is already complete or completing, " +
                "but is being completed with $proposedUpdate", proposedUpdate.exceptionOrNull)
        }

    private fun makeCompletingInternal(proposedUpdate: Any?, mode: Int): Int {
        loopOnState { state ->
            if (state !is Incomplete)
                return COMPLETING_ALREADY_COMPLETING
            if (state is Finishing && state.completing)
                return COMPLETING_ALREADY_COMPLETING
            val child: ChildJob? = firstChild(state) ?: // or else complete immediately w/o children
            when {
                state !is Finishing && hasOnFinishingHandler(proposedUpdate) -> null // unless it has onFinishing handler
                updateState(state, proposedUpdate, mode) -> return COMPLETING_COMPLETED
                else -> return@loopOnState
            }
            val list = state.list ?: // must promote to list to correctly operate on child lists
            when (state) {
                is Empty -> {
                    promoteEmptyToNodeList(state)
                    return@loopOnState // retry
                }
                is JobNode<*> -> {
                    promoteSingleToNodeList(state)
                    return@loopOnState // retry
                }
                else -> error("Unexpected state with an empty list: $state")
            }
            // cancel all children in list on exceptional completion
            if (proposedUpdate is CompletedExceptionally)
                child?.cancelChildrenInternal(proposedUpdate.cause)
            // switch to completing state
            val cancelled = (state as? Finishing)?.cancelled ?: (proposedUpdate as? Cancelled)
            val completing = Finishing(list, cancelled, true)
            if (_state.compareAndSet(state, completing)) {
                if (state !is Finishing) onFinishingInternal(proposedUpdate)
                if (child != null && tryWaitForChild(child, proposedUpdate))
                    return COMPLETING_WAITING_CHILDREN
                if (updateState(completing, proposedUpdate, mode = MODE_ATOMIC_DEFAULT))
                    return COMPLETING_COMPLETED
            }
        }
    }

    private tailrec fun ChildJob.cancelChildrenInternal(cause: Throwable) {
        childJob.cancel(JobCancellationException("Child job was cancelled because of parent failure", cause, childJob))
        nextChild()?.cancelChildrenInternal(cause)
    }

    private val Any?.exceptionOrNull: Throwable?
        get() = (this as? CompletedExceptionally)?.cause

    private fun firstChild(state: Incomplete) =
        state as? ChildJob ?: state.list?.nextChild()

    // return false when there is no more incomplete children to wait
    private tailrec fun tryWaitForChild(child: ChildJob, proposedUpdate: Any?): Boolean {
        val handle = child.childJob.invokeOnCompletion(invokeImmediately = false,
            handler = ChildCompletion(this, child, proposedUpdate).asHandler)
        if (handle !== NonDisposableHandle) return true // child is not complete and we've started waiting for it
        val nextChild = child.nextChild() ?: return false
        return tryWaitForChild(nextChild, proposedUpdate)
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun continueCompleting(lastChild: ChildJob, proposedUpdate: Any?) {
        loopOnState { state ->
            if (state !is Finishing)
                throw IllegalStateException("Job $this is found in expected state while completing with $proposedUpdate", proposedUpdate.exceptionOrNull)
            // figure out if we need to wait for next child
            val waitChild = lastChild.nextChild()
            // try wait for next child
            if (waitChild != null && tryWaitForChild(waitChild, proposedUpdate)) return // waiting for next child
            // no more children to wait -- try update state
            if (updateState(state, proposedUpdate, MODE_ATOMIC_DEFAULT)) return
        }
    }

    private fun LockFreeLinkedListNode.nextChild(): ChildJob? {
        var cur = this
        while (cur.isRemoved) cur = cur.prevNode // rollback to prev non-removed (or list head)
        while (true) {
            cur = cur.nextNode
            if (cur.isRemoved) continue
            if (cur is ChildJob) return cur
            if (cur is NodeList) return null // checked all -- no more children
        }
    }

    public final override val children: Sequence<Job> get() = buildSequence {
        val state = this@JobSupport.state
        when (state) {
            is ChildJob -> yield(state.childJob)
            is Incomplete -> state.list?.let { list ->
                list.forEach<ChildJob> { yield(it.childJob) }
            }
        }
    }

    @Suppress("OverridingDeprecatedMember")
    public final override fun attachChild(child: Job): DisposableHandle =
        invokeOnCompletion(onCancelling = true, handler = ChildJob(this, child).asHandler)

    @Suppress("OverridingDeprecatedMember")
    public final override fun cancelChildren(cause: Throwable?) {
        this.cancelChildren(cause) // use extension function
    }

    /**
     * Override to process any exceptions that were encountered while invoking completion handlers
     * installed via [invokeOnCompletion].
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun handleException(exception: Throwable) {
        throw exception
    }

    /**
     * This function is invoked once when job is cancelled or is completed, similarly to [invokeOnCompletion] with
     * `onCancelling` set to `true`.
     * @param exceptionally not null when the the job was cancelled or completed exceptionally,
     *               null when it has completed normally.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun onCancellationInternal(exceptionally: CompletedExceptionally?) {}

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun hasOnFinishingHandler(update: Any?) = false

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun onFinishingInternal(update: Any?) {}

    /**
     * Override for post-completion actions that need to do something with the state.
     * @param mode completion mode.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun onCompletionInternal(state: Any?, mode: Int) {}

    // for nicer debugging
    public override fun toString(): String =
        "${nameString()}{${stateString()}}@$hexAddress"

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun nameString(): String = classSimpleName

    private fun stateString(): String {
        val state = this.state
        return when (state) {
            is Finishing -> buildString {
                if (state.cancelled != null) append("Cancelling")
                if (state.completing) append("Completing")
            }
            is Incomplete -> if (state.isActive) "Active" else "New"
            is Cancelled -> "Cancelled"
            is CompletedExceptionally -> "CompletedExceptionally"
            else -> "Completed"
        }
    }

    // Cancelling or Completing
    private class Finishing(
        override val list: NodeList,
        @JvmField val cancelled: Cancelled?, /* != null when cancelling */
        @JvmField val completing: Boolean /* true when completing */
    ) : Incomplete {
        override val isActive: Boolean get() = cancelled == null
    }

    private val Incomplete.isCancelling: Boolean
        get() = this is Finishing && cancelled != null

    /*
     * =================================================================================================
     * This is ready-to-use implementation for Deferred interface.
     * However, it is not type-safe. Conceptually it just exposes the value of the underlying
     * completed state as `Any?`
     * =================================================================================================
     */

    public val isCompletedExceptionally: Boolean get() = state is CompletedExceptionally

    public fun getCompletionExceptionOrNull(): Throwable? {
        val state = this.state
        check(state !is Incomplete) { "This job has not completed yet" }
        return state.exceptionOrNull
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun getCompletedInternal(): Any? {
        val state = this.state
        check(state !is Incomplete) { "This job has not completed yet" }
        if (state is CompletedExceptionally) throw state.cause
        return state
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal suspend fun awaitInternal(): Any? {
        // fast-path -- check state (avoid extra object creation)
        while(true) { // lock-free loop on state
            val state = this.state
            if (state !is Incomplete) {
                // already complete -- just return result
                if (state is CompletedExceptionally) throw state.cause
                return state

            }
            if (startInternal(state) >= 0) break // break unless needs to retry
        }
        return awaitSuspend() // slow-path
    }

    private suspend fun awaitSuspend(): Any? = suspendCancellableCoroutine { cont ->
        // We have to invoke await() handler only on cancellation, on completion we will be resumed regularly without handlers
        cont.disposeOnCancellation(invokeOnCompletion {
            val state = this.state
            check(state !is Incomplete)
            if (state is CompletedExceptionally)
                cont.resumeWithException(state.cause)
            else
                cont.resume(state)
        })
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    // registerSelectAwaitInternal
    @Suppress("UNCHECKED_CAST")
    internal fun <T, R> registerSelectClause1Internal(select: SelectInstance<R>, block: suspend (T) -> R) {
        // fast-path -- check state and select/return if needed
        loopOnState { state ->
            if (select.isSelected) return
            if (state !is Incomplete) {
                // already complete -- select result
                if (select.trySelect(null)) {
                    if (state is CompletedExceptionally)
                        select.resumeSelectCancellableWithException(state.cause)
                    else
                        block.startCoroutineUndispatched(state as T, select.completion)
                }
                return
            }
            if (startInternal(state) == 0) {
                // slow-path -- register waiter for completion
                select.disposeOnSelect(invokeOnCompletion(handler = SelectAwaitOnCompletion(this, select, block).asHandler))
                return
            }
        }
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    @Suppress("UNCHECKED_CAST")
    internal fun <T, R> selectAwaitCompletion(select: SelectInstance<R>, block: suspend (T) -> R) {
        val state = this.state
        // Note: await is non-atomic (can be cancelled while dispatched)
        if (state is CompletedExceptionally)
            select.resumeSelectCancellableWithException(state.cause)
        else
            block.startCoroutineCancellable(state as T, select.completion)
    }
}

// --------------- helper classes to simplify job implementation

internal const val ON_CANCEL_MAKE_CANCELLING = 0
internal const val ON_CANCEL_MAKE_COMPLETING = 1

private const val COMPLETING_ALREADY_COMPLETING = 0
private const val COMPLETING_COMPLETED = 1
private const val COMPLETING_WAITING_CHILDREN = 2

private const val RETRY = -1
private const val FALSE = 0
private const val TRUE = 1

@Suppress("PrivatePropertyName")
private val EmptyNew = Empty(false)
@Suppress("PrivatePropertyName")
private val EmptyActive = Empty(true)

private class Empty(override val isActive: Boolean) : Incomplete {
    override val list: NodeList? get() = null
    override fun toString(): String = "Empty{${if (isActive) "Active" else "New" }}"
}

internal class JobImpl(parent: Job? = null) : JobSupport(true) {
    init { initParentJobInternal(parent) }
    override val onCancelMode: Int get() = ON_CANCEL_MAKE_COMPLETING
}

// -------- invokeOnCompletion nodes

internal interface Incomplete {
    val isActive: Boolean
    val list: NodeList? // is null only for Empty and JobNode incomplete state objects
}

internal abstract class JobNode<out J : Job>(
    @JvmField val job: J
) : CompletionHandlerBase(), DisposableHandle, Incomplete {
    override val isActive: Boolean get() = true
    override val list: NodeList? get() = null
    override fun dispose() = (job as JobSupport).removeNode(this)
}

internal class NodeList(
    active: Boolean
) : LockFreeLinkedListHead(), Incomplete {
    private val _active = atomic(if (active) 1 else 0)

    override val isActive: Boolean get() = _active.value != 0
    override val list: NodeList get() = this

    fun tryMakeActive(): Int {
        if (_active.value != 0) return FALSE
        if (_active.compareAndSet(0, 1)) return TRUE
        return RETRY
    }

    override fun toString(): String = buildString {
        append("List")
        append(if (isActive) "{Active}" else "{New}")
        append("[")
        var first = true
        this@NodeList.forEach<JobNode<*>> { node ->
            if (first) first = false else append(", ")
            append(node)
        }
        append("]")
    }
}

private class InvokeOnCompletion(
    job: Job,
    private val handler: CompletionHandler
) : JobNode<Job>(job)  {
    override fun invoke(cause: Throwable?) = handler.invoke(cause)
    override fun toString() = "InvokeOnCompletion[$classSimpleName@$hexAddress]"
}

private class ResumeOnCompletion(
    job: Job,
    private val continuation: Continuation<Unit>
) : JobNode<Job>(job)  {
    override fun invoke(cause: Throwable?) = continuation.resume(Unit)
    override fun toString() = "ResumeOnCompletion[$continuation]"
}

internal class DisposeOnCompletion(
    job: Job,
    private val handle: DisposableHandle
) : JobNode<Job>(job) {
    override fun invoke(cause: Throwable?) = handle.dispose()
    override fun toString(): String = "DisposeOnCompletion[$handle]"
}

private class SelectJoinOnCompletion<R>(
    job: JobSupport,
    private val select: SelectInstance<R>,
    private val block: suspend () -> R
) : JobNode<JobSupport>(job) {
    override fun invoke(cause: Throwable?) {
        if (select.trySelect(null))
            block.startCoroutineCancellable(select.completion)
    }
    override fun toString(): String = "SelectJoinOnCompletion[$select]"
}

private class SelectAwaitOnCompletion<T, R>(
    job: JobSupport,
    private val select: SelectInstance<R>,
    private val block: suspend (T) -> R
) : JobNode<JobSupport>(job) {
    override fun invoke(cause: Throwable?) {
        if (select.trySelect(null))
            job.selectAwaitCompletion(select, block)
    }
    override fun toString(): String = "SelectAwaitOnCompletion[$select]"
}

// -------- invokeOnCancellation nodes

/**
 * Marker for node that shall be invoked on cancellation (in _cancelling_ state).
 * **Note: may be invoked multiple times during cancellation.**
 */
internal abstract class JobCancellationNode<out J : Job>(job: J) : JobNode<J>(job)

private class InvokeOnCancellation(
    job: Job,
    private val handler: CompletionHandler
) : JobCancellationNode<Job>(job)  {
    // delegate handler shall be invoked at most once, so here is an additional flag
    private val _invoked = atomic(0)
    override fun invoke(cause: Throwable?) {
        if (_invoked.compareAndSet(0, 1)) handler.invoke(cause)
    }
    override fun toString() = "InvokeOnCancellation[$classSimpleName@$hexAddress]"
}

internal class ChildJob(
    parent: JobSupport,
    @JvmField val childJob: Job
) : JobCancellationNode<JobSupport>(parent) {
    override fun invoke(cause: Throwable?) {
        // Always materialize the actual instance of parent's completion exception and cancel child with it
        childJob.cancel(job.getCancellationException())
    }
    override fun toString(): String = "ChildJob[$childJob]"
}

// Same as ChildJob, but for cancellable continuation
internal class ChildContinuation(
    parent: Job,
    @JvmField val child: AbstractContinuation<*>
) : JobCancellationNode<Job>(parent) {
    override fun invoke(cause: Throwable?) {
        child.cancel(job.getCancellationException())
    }
    override fun toString(): String = "ChildContinuation[$child]"
}

private class ChildCompletion(
    private val parent: JobSupport,
    private val child: ChildJob,
    private val proposedUpdate: Any?
) : JobNode<Job>(child.childJob) {
    override fun invoke(cause: Throwable?) {
        parent.continueCompleting(child, proposedUpdate)
    }
}
