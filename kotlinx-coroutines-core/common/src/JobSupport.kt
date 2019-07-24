/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION_ERROR")

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.js.*
import kotlin.jvm.*

/**
 * A concrete implementation of [Job]. It is optionally a child to a parent job.
 *
 * This is an open class designed for extension by more specific classes that might augment the
 * state and mare store addition state information for completed jobs, like their result values.
 *
 * @param active when `true` the job is created in _active_ state, when `false` in _new_ state. See [Job] for details.
 * @suppress **This is unstable API and it is subject to change.**
 */
@Deprecated(level = DeprecationLevel.ERROR, message = "This is internal API and may be removed in the future releases")
public open class JobSupport constructor(active: Boolean) : Job, ChildJob, ParentJob, SelectClause0 {
    final override val key: CoroutineContext.Key<*> get() = Job

    /*
       === Internal states ===

       name       state class              public state  description
       ------     ------------             ------------  -----------
       EMPTY_N    EmptyNew               : New           no listeners
       EMPTY_A    EmptyActive            : Active        no listeners
       SINGLE     JobNode                : Active        a single listener
       SINGLE+    JobNode                : Active        a single listener + NodeList added as its next
       LIST_N     InactiveNodeList       : New           a list of listeners (promoted once, does not got back to EmptyNew)
       LIST_A     NodeList               : Active        a list of listeners (promoted once, does not got back to JobNode/EmptyActive)
       COMPLETING Finishing              : Completing    has a list of listeners (promoted once from LIST_*)
       CANCELLING Finishing              : Cancelling    -- " --
       FINAL_C    Cancelled              : Cancelled     Cancelled (final state)
       FINAL_R    <any>                  : Completed     produced some result

       === Transitions ===

           New states      Active states       Inactive states

          +---------+       +---------+                          }
          | EMPTY_N | ----> | EMPTY_A | ----+                    } Empty states
          +---------+       +---------+     |                    }
               |  |           |     ^       |    +----------+
               |  |           |     |       +--> |  FINAL_* |
               |  |           V     |       |    +----------+
               |  |         +---------+     |                    }
               |  |         | SINGLE  | ----+                    } JobNode states
               |  |         +---------+     |                    }
               |  |              |          |                    }
               |  |              V          |                    }
               |  |         +---------+     |                    }
               |  +-------> | SINGLE+ | ----+                    }
               |            +---------+     |                    }
               |                 |          |
               V                 V          |
          +---------+       +---------+     |                    }
          | LIST_N  | ----> | LIST_A  | ----+                    } [Inactive]NodeList states
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


       This state machine and its transition matrix are optimized for the common case when a job is created in active
       state (EMPTY_A), at most one completion listener is added to it during its life-time, and it completes
       successfully without children (in this case it directly goes from EMPTY_A or SINGLE state to FINAL_R
       state without going to COMPLETING state)

       Note that the actual `_state` variable can also be a reference to atomic operation descriptor `OpDescriptor`

       ---------- TIMELINE of state changes and notification in Job lifecycle ----------

       | The longest possible chain of events in shown, shorter versions cut-through intermediate states,
       |  while still performing all the notifications in this order.

         + Job object is created
       ## NEW: state == EMPTY_ACTIVE | is InactiveNodeList
         + initParentJob / initParentJobInternal (invokes attachChild on its parent, initializes parentHandle)
         ~ waits for start
         >> start / join / await invoked
       ## ACTIVE: state == EMPTY_ACTIVE | is JobNode | is NodeList
         + onStartInternal / onStart (lazy coroutine is started)
         ~ active coroutine is working (or scheduled to execution)
         >> childCancelled / cancelImpl invoked
       ## CANCELLING: state is Finishing, state.rootCause != null
        ------ cancelling listeners are not admitted anymore, invokeOnCompletion(onCancelling=true) returns NonDisposableHandle
        ------ new children get immediately cancelled, but are still admitted to the list
         + onCancelling
         + notifyCancelling (invoke all cancelling listeners -- cancel all children, suspended functions resume with exception)
         + cancelParent (rootCause of cancellation is communicated to the parent, parent is cancelled, too)
         ~ waits for completion of coroutine body
         >> makeCompleting / makeCompletingOnce invoked
       ## COMPLETING: state is Finishing, state.isCompleting == true
        ------ new children are not admitted anymore, attachChild returns NonDisposableHandle
         ~ waits for children
         >> last child completes
         - computes the final exception
       ## SEALED: state is Finishing, state.isSealed == true
        ------ cancel/childCancelled returns false (cannot handle exceptions anymore)
         + cancelParent (final exception is communicated to the parent, parent incorporates it)
         + handleJobException ("launch" StandaloneCoroutine invokes CoroutineExceptionHandler)
       ## COMPLETE: state !is Incomplete (CompletedExceptionally | Cancelled)
        ------ completion listeners are not admitted anymore, invokeOnCompletion returns NonDisposableHandle
         + parentHandle.dispose
         + notifyCompletion (invoke all completion listeners)
         + onCompletionInternal / onCompleted / onCancelled

       ---------------------------------------------------------------------------------
     */

    // Note: use shared objects while we have no listeners
    private val _state = atomic<Any?>(if (active) EMPTY_ACTIVE else EMPTY_NEW)

    @Volatile
    @JvmField
    internal var parentHandle: ChildHandle? = null

    // ------------ initialization ------------

    /**
     * Initializes parent job.
     * It shall be invoked at most once after construction after all other initialization.
     */
    internal fun initParentJobInternal(parent: Job?) {
        assert { parentHandle == null }
        if (parent == null) {
            parentHandle = NonDisposableHandle
            return
        }
        parent.start() // make sure the parent is started
        @Suppress("DEPRECATION")
        val handle = parent.attachChild(this)
        parentHandle = handle
        // now check our state _after_ registering (see tryFinalizeSimpleState order of actions)
        if (isCompleted) {
            handle.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    // ------------ state query ------------
    /**
     * Returns current state of this job.
     * If final state of the job is [Incomplete], then it is boxed into [IncompleteStateBox]
     * and should be [unboxed][unboxState] before returning to user code.
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

    public override val isActive: Boolean get() {
        val state = this.state
        return state is Incomplete && state.isActive
    }

    public final override val isCompleted: Boolean get() = state !is Incomplete

    public final override val isCancelled: Boolean get() {
        val state = this.state
        return state is CompletedExceptionally || (state is Finishing && state.isCancelling)
    }

    // ------------ state update ------------

    // Finalizes Finishing -> Completed (terminal state) transition.
    // ## IMPORTANT INVARIANT: Only one thread can be concurrently invoking this method.
    private fun tryFinalizeFinishingState(state: Finishing, proposedUpdate: Any?, mode: Int): Boolean {
        /*
         * Note: proposed state can be Incomplete, e.g.
         * async {
         *     something.invokeOnCompletion {} // <- returns handle which implements Incomplete under the hood
         * }
         */
        require(this.state === state) // consistency check -- it cannot change
        require(!state.isSealed) // consistency check -- cannot be sealed yet
        require(state.isCompleting) // consistency check -- must be marked as completing
        val proposedException = (proposedUpdate as? CompletedExceptionally)?.cause
        // Create the final exception and seal the state so that no more exceptions can be added
        var wasCancelling = false // KLUDGE: we cannot have contract for our own expect fun synchronized
        val finalException = synchronized(state) {
            wasCancelling = state.isCancelling
            val exceptions = state.sealLocked(proposedException)
            val finalCause = getFinalRootCause(state, exceptions)
            if (finalCause != null) addSuppressedExceptions(finalCause, exceptions)
            finalCause
        }
        // Create the final state object
        val finalState = when {
            // was not cancelled (no exception) -> use proposed update value
            finalException == null -> proposedUpdate
            // small optimization when we can used proposeUpdate object as is on cancellation
            finalException === proposedException -> proposedUpdate
            // cancelled job final state
            else -> CompletedExceptionally(finalException)
        }
        // Now handle the final exception
        if (finalException != null) {
            val handled = cancelParent(finalException) || handleJobException(finalException)
            if (handled) (finalState as CompletedExceptionally).makeHandled()
        }
        // Process state updates for the final state before the state of the Job is actually set to the final state
        // to avoid races where outside observer may see the job in the final state, yet exception is not handled yet.
        if (!wasCancelling) onCancelling(finalException)
        onCompletionInternal(finalState)
        // Then CAS to completed state -> it must succeed
        require(_state.compareAndSet(state, finalState.boxIncomplete())) { "Unexpected state: ${_state.value}, expected: $state, update: $finalState" }
        // And process all post-completion actions
        completeStateFinalization(state, finalState, mode)
        return true
    }

    private fun getFinalRootCause(state: Finishing, exceptions: List<Throwable>): Throwable? {
        // A case of no exceptions
        if (exceptions.isEmpty()) {
            // materialize cancellation exception if it was not materialized yet
            if (state.isCancelling) return createJobCancellationException()
            return null
        }
        // Take either the first real exception (not a cancellation) or just the first exception
        return exceptions.firstOrNull { it !is CancellationException } ?: exceptions[0]
    }

    private fun addSuppressedExceptions(rootCause: Throwable, exceptions: List<Throwable>) {
        if (exceptions.size <= 1) return // nothing more to do here
        val seenExceptions = identitySet<Throwable>(exceptions.size)
        /*
         * Note that root cause may be a recovered exception as well.
         * To avoid cycles we unwrap the root cause and check for self-suppression against unwrapped cause,
         * but add suppressed exceptions to the recovered root cause (as it is our final exception)
         */
        val unwrappedCause = unwrap(rootCause)
        for (exception in exceptions) {
            val unwrapped = unwrap(exception)
            if (unwrapped !== rootCause && unwrapped !== unwrappedCause &&
                unwrapped !is CancellationException && seenExceptions.add(unwrapped)) {
                rootCause.addSuppressedThrowable(unwrapped)
            }
        }
    }

    // fast-path method to finalize normally completed coroutines without children
    private fun tryFinalizeSimpleState(state: Incomplete, update: Any?, mode: Int): Boolean {
        assert { state is Empty || state is JobNode<*> } // only simple state without lists where children can concurrently add
        assert { update !is CompletedExceptionally } // only for normal completion
        if (!_state.compareAndSet(state, update.boxIncomplete())) return false
        onCancelling(null) // simple state is not a failure
        onCompletionInternal(update)
        completeStateFinalization(state, update, mode)
        return true
    }

    // suppressed == true when any exceptions were suppressed while building the final completion cause
    private fun completeStateFinalization(state: Incomplete, update: Any?, mode: Int) {
        /*
         * Now the job in THE FINAL state. We need to properly handle the resulting state.
         * Order of various invocations here is important.
         *
         * 1) Unregister from parent job.
         */
        parentHandle?.let {
            it.dispose() // volatile read parentHandle _after_ state was updated
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
        val cause = (update as? CompletedExceptionally)?.cause
        /*
         * 2) Invoke completion handlers: .join(), callbacks etc.
         *    It's important to invoke them only AFTER exception handling and everything else, see #208
         */
        if (state is JobNode<*>) { // SINGLE/SINGLE+ state -- one completion handler (common case)
            try {
                state.invoke(cause)
            } catch (ex: Throwable) {
                handleOnCompletionException(CompletionHandlerException("Exception in completion handler $state for $this", ex))
            }
        } else {
            state.list?.notifyCompletion(cause)
        }
        /*
         * 3) Resumes the rest of the code in scoped coroutines
         *    (runBlocking, coroutineScope, withContext, withTimeout, etc)
         */
        afterCompletionInternal(update, mode)
    }

    private fun notifyCancelling(list: NodeList, cause: Throwable) {
        // first cancel our own children
        onCancelling(cause)
        notifyHandlers<JobCancellingNode<*>>(list, cause)
        // then cancel parent
        cancelParent(cause) // tentative cancellation -- does not matter if there is no parent
    }

    /**
     * The method that is invoked when the job is cancelled to possibly propagate cancellation to the parent.
     * Returns `true` if the parent is responsible for handling the exception, `false` otherwise.
     *
     * Invariant: never returns `false` for instances of [CancellationException], otherwise such exception
     * may leak to the [CoroutineExceptionHandler].
     */
    private fun cancelParent(cause: Throwable): Boolean {
        // Is scoped coroutine -- don't propagate, will be rethrown
        if (isScopedCoroutine) return true

        /* CancellationException is considered "normal" and parent usually is not cancelled when child produces it.
         * This allow parent to cancel its children (normally) without being cancelled itself, unless
         * child crashes and produce some other exception during its completion.
         */
        val isCancellation = cause is CancellationException
        val parent = parentHandle
        // No parent -- ignore CE, report other exceptions.
        if (parent === null || parent === NonDisposableHandle) {
            return isCancellation
        }

        // Notify parent but don't forget to check cancellation
        return parent.childCancelled(cause) || isCancellation
    }

    private fun NodeList.notifyCompletion(cause: Throwable?) =
        notifyHandlers<JobNode<*>>(this, cause)

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
        exception?.let { handleOnCompletionException(it) }
    }

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
                if (!_state.compareAndSet(state, EMPTY_ACTIVE)) return RETRY
                onStartInternal()
                return TRUE
            }
            is InactiveNodeList -> { // LIST state -- inactive with a list of completion handlers
                if (!_state.compareAndSet(state, state.list)) return RETRY
                onStartInternal()
                return TRUE
            }
            else -> return FALSE // not a new state
        }
    }

    /**
     * Override to provide the actual [start] action.
     * This function is invoked exactly once when non-active coroutine is [started][start].
     */
    internal open fun onStartInternal() {}

    public final override fun getCancellationException(): CancellationException =
        when (val state = this.state) {
            is Finishing -> state.rootCause?.toCancellationException("$classSimpleName is cancelling")
                ?: error("Job is still new or active: $this")
            is Incomplete -> error("Job is still new or active: $this")
            is CompletedExceptionally -> state.cause.toCancellationException()
            else -> JobCancellationException("$classSimpleName has completed normally", null, this)
        }

    protected fun Throwable.toCancellationException(message: String? = null): CancellationException =
        this as? CancellationException ?:
            JobCancellationException(message ?: "$classSimpleName was cancelled", this, this@JobSupport)

    /**
     * Returns the cause that signals the completion of this job -- it returns the original
     * [cancel] cause, [CancellationException] or **`null` if this job had completed normally**.
     * This function throws [IllegalStateException] when invoked for an job that has not [completed][isCompleted] nor
     * is being cancelled yet.
     */
    protected val completionCause: Throwable?
        get() = when (val state = state) {
            is Finishing -> state.rootCause
                ?: error("Job is still new or active: $this")
            is Incomplete -> error("Job is still new or active: $this")
            is CompletedExceptionally -> state.cause
            else -> null
        }

    /**
     * Returns `true` when [completionCause] exception was handled by parent coroutine.
     */
    protected val completionCauseHandled: Boolean
        get() = state.let { it is CompletedExceptionally && it.handled }

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        invokeOnCompletion(onCancelling = false, invokeImmediately = true, handler = handler)

    public final override fun invokeOnCompletion(
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
                        var rootCause: Throwable? = null
                        var handle: DisposableHandle = NonDisposableHandle
                        if (onCancelling && state is Finishing) {
                            synchronized(state) {
                                // check if we are installing cancellation handler on job that is being cancelled
                                rootCause = state.rootCause // != null if cancelling job
                                // We add node to the list in two cases --- either the job is not being cancelled
                                // or we are adding a child to a coroutine that is not completing yet
                                if (rootCause == null || handler.isHandlerOf<ChildHandleNode>() && !state.isCompleting) {
                                    // Note: add node the list while holding lock on state (make sure it cannot change)
                                    val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                                    if (!addLastAtomic(state, list, node)) return@loopOnState // retry
                                    // just return node if we don't have to invoke handler (not cancelling yet)
                                    if (rootCause == null) return node
                                    // otherwise handler is invoked immediately out of the synchronized section & handle returned
                                    handle = node
                                }
                            }
                        }
                        if (rootCause != null) {
                            // Note: attachChild uses invokeImmediately, so it gets invoked when adding to cancelled job
                            if (invokeImmediately) handler.invokeIt(rootCause)
                            return handle
                        } else {
                            val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                            if (addLastAtomic(state, list, node)) return node
                        }
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
            (handler as? JobCancellingNode<*>)?.also { require(it.job === this) }
                ?: InvokeOnCancelling(this, handler)
        else
            (handler as? JobNode<*>)?.also { require(it.job === this && it !is JobCancellingNode) }
                ?: InvokeOnCompletion(this, handler)
    }

    private fun addLastAtomic(expect: Any, list: NodeList, node: JobNode<*>) =
        list.addLastIf(node) { this.state === expect }

    private fun promoteEmptyToNodeList(state: Empty) {
        // try to promote it to LIST state with the corresponding state
        val list = NodeList()
        val update = if (state.isActive) list else InactiveNodeList(list)
        _state.compareAndSet(state, update)
    }

    private fun promoteSingleToNodeList(state: JobNode<*>) {
        // try to promote it to list (SINGLE+ state)
        state.addOneIfEmpty(NodeList())
        // it must be in SINGLE+ state or state has changed (node could have need removed from state)
        val list = state.nextNode // either our NodeList or somebody else won the race, updated state
        // just attempt converting it to list if state is still the same, then we'll continue lock-free loop
        _state.compareAndSet(state, list)
    }

    public final override suspend fun join() {
        if (!joinInternal()) { // fast-path no wait
            coroutineContext.checkCompletion()
            return // do not suspend
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
                    block.startCoroutineUnintercepted(select.completion)
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
                    if (_state.compareAndSet(state, EMPTY_ACTIVE)) return
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
     * Returns `true` for job that do not have "body block" to complete and should immediately go into
     * completing state and start waiting for children.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open val onCancelComplete: Boolean get() = false

    // external cancel with cause, never invoked implicitly from internal machinery
    public override fun cancel(cause: CancellationException?) {
        cancelInternal(cause) // must delegate here, because some classes override cancelInternal(x)
    }

    // HIDDEN in Job interface. Invoked only by legacy compiled code.
    // external cancel with (optional) cause, never invoked implicitly from internal machinery
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Added since 1.2.0 for binary compatibility with versions <= 1.1.x")
    public override fun cancel(cause: Throwable?): Boolean =
        cancelInternal(cause)

    // It is overridden in channel-linked implementation
    // Note: Boolean result is used only in HIDDEN DEPRECATED functions that were public in versions <= 1.1.x
    public open fun cancelInternal(cause: Throwable?): Boolean =
        cancelImpl(cause) && handlesException

    // Parent is cancelling child
    public final override fun parentCancelled(parentJob: ParentJob) {
        cancelImpl(parentJob)
    }

    /**
     * Child was cancelled with a cause.
     * In this method parent decides whether it cancels itself (e.g. on a critical failure) and whether it handles the exception of the child.
     * It is overridden in supervisor implementations to completely ignore any child cancellation.
     * Returns `true` if exception is handled, `false` otherwise (then caller is responsible for handling an exception)
     *
     * Invariant: never returns `false` for instances of [CancellationException], otherwise such exception
     * may leak to the [CoroutineExceptionHandler].
     */
    public open fun childCancelled(cause: Throwable): Boolean {
        if (cause is CancellationException) return true
        return cancelImpl(cause) && handlesException
    }

    /**
     * Makes this [Job] cancelled with a specified [cause].
     * It is used in [AbstractCoroutine]-derived classes when there is an internal failure.
     */
    public fun cancelCoroutine(cause: Throwable?) = cancelImpl(cause)

    // cause is Throwable or ParentJob when cancelChild was invoked
    // returns true is exception was handled, false otherwise
    internal fun cancelImpl(cause: Any?): Boolean {
        if (onCancelComplete) {
            // make sure it is completing, if cancelMakeCompleting returns true it means it had make it
            // completing and had recorded exception
            if (cancelMakeCompleting(cause)) return true
            // otherwise just record exception via makeCancelling below
        }
        return makeCancelling(cause)
    }

    // cause is Throwable or ParentJob when cancelChild was invoked
    private fun cancelMakeCompleting(cause: Any?): Boolean {
        loopOnState { state ->
            if (state !is Incomplete || state is Finishing && state.isCompleting) {
                return false // already completed/completing, do not even propose update
            }
            val proposedUpdate = CompletedExceptionally(createCauseException(cause))
            when (tryMakeCompleting(state, proposedUpdate, mode = MODE_ATOMIC_DEFAULT)) {
                COMPLETING_ALREADY_COMPLETING -> return false
                COMPLETING_COMPLETED, COMPLETING_WAITING_CHILDREN -> return true
                COMPLETING_RETRY -> return@loopOnState
                else -> error("unexpected result")
            }
        }
    }

    private fun createJobCancellationException() =
        JobCancellationException("Job was cancelled", null, this)

    override fun getChildJobCancellationCause(): CancellationException {
        // determine root cancellation cause of this job (why is it cancelling its children?)
        val state = this.state
        val rootCause = when (state) {
            is Finishing -> state.rootCause
            is CompletedExceptionally -> state.cause
            is Incomplete -> error("Cannot be cancelling child in this state: $state")
            else -> null // create exception with the below code on normal completion
        }
        return (rootCause as? CancellationException) ?: JobCancellationException("Parent job is ${stateString(state)}", rootCause, this)
    }

    // cause is Throwable or ParentJob when cancelChild was invoked
    private fun createCauseException(cause: Any?): Throwable = when (cause) {
        is Throwable? -> cause ?: createJobCancellationException()
        else -> (cause as ParentJob).getChildJobCancellationCause()
    }

    // transitions to Cancelling state
    // cause is Throwable or ParentJob when cancelChild was invoked
    private fun makeCancelling(cause: Any?): Boolean {
        var causeExceptionCache: Throwable? = null // lazily init result of createCauseException(cause)
        loopOnState { state ->
            when (state) {
                is Finishing -> { // already finishing -- collect exceptions
                    val notifyRootCause = synchronized(state) {
                        if (state.isSealed) return false // too late, already sealed -- cannot add exception nor mark cancelled
                        // add exception, do nothing is parent is cancelling child that is already being cancelled
                        val wasCancelling = state.isCancelling // will notify if was not cancelling
                        // Materialize missing exception if it is the first exception (otherwise -- don't)
                        if (cause != null || !wasCancelling) {
                            val causeException = causeExceptionCache ?: createCauseException(cause).also { causeExceptionCache = it }
                            state.addExceptionLocked(causeException)
                        }
                        // take cause for notification if was not in cancelling state before
                        state.rootCause.takeIf { !wasCancelling }
                    }
                    notifyRootCause?.let { notifyCancelling(state.list, it) }
                    return true
                }
                is Incomplete -> {
                    // Not yet finishing -- try to make it cancelling
                    val causeException = causeExceptionCache ?: createCauseException(cause).also { causeExceptionCache = it }
                    if (state.isActive) {
                        // active state becomes cancelling
                        if (tryMakeCancelling(state, causeException)) return true
                    } else {
                        // non active state starts completing
                        when (tryMakeCompleting(state, CompletedExceptionally(causeException), mode = MODE_ATOMIC_DEFAULT)) {
                            COMPLETING_ALREADY_COMPLETING -> error("Cannot happen in $state")
                            COMPLETING_COMPLETED, COMPLETING_WAITING_CHILDREN -> return true // ok
                            COMPLETING_RETRY -> return@loopOnState
                            else -> error("unexpected result")
                        }
                    }
                }
                else -> return false // already complete
            }
        }
    }

    // Performs promotion of incomplete coroutine state to NodeList for the purpose of
    // converting coroutine state to Cancelling, returns null when need to retry
    private fun getOrPromoteCancellingList(state: Incomplete): NodeList? = state.list ?:
        when (state) {
            is Empty -> NodeList() // we can allocate new empty list that'll get integrated into Cancelling state
            is JobNode<*> -> {
                // SINGLE/SINGLE+ must be promoted to NodeList first, because otherwise we cannot
                // correctly capture a reference to it
                promoteSingleToNodeList(state)
                null // retry
            }
            else -> error("State should have list: $state")
        }

    // try make new Cancelling state on the condition that we're still in the expected state
    private fun tryMakeCancelling(state: Incomplete, rootCause: Throwable): Boolean {
        assert { state !is Finishing } // only for non-finishing states
        assert { state.isActive } // only for active states
        // get state's list or else promote to list to correctly operate on child lists
        val list = getOrPromoteCancellingList(state) ?: return false
        // Create cancelling state (with rootCause!)
        val cancelling = Finishing(list, false, rootCause)
        if (!_state.compareAndSet(state, cancelling)) return false
        // Notify listeners
        notifyCancelling(list, rootCause)
        return true
    }

    /**
     * This function is used by [CompletableDeferred.complete] (and exceptionally) and by [JobImpl.cancel].
     * It returns `false` on repeated invocation (when this job is already completing).
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun makeCompleting(proposedUpdate: Any?): Boolean = loopOnState { state ->
        when (tryMakeCompleting(state, proposedUpdate, mode = MODE_ATOMIC_DEFAULT)) {
            COMPLETING_ALREADY_COMPLETING -> return false
            COMPLETING_COMPLETED, COMPLETING_WAITING_CHILDREN -> return true
            COMPLETING_RETRY -> return@loopOnState
            else -> error("unexpected result")
        }
    }

    /**
     * This function is used by [AbstractCoroutine.resume].
     * It throws exception on repeated invocation (when this job is already completing).
     *
     * Returns:
     * * `true` if state was updated to completed/cancelled;
     * * `false` if made completing or it is cancelling and is waiting for children.
     *
     * @throws IllegalStateException if job is already complete or completing
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun makeCompletingOnce(proposedUpdate: Any?, mode: Int): Boolean = loopOnState { state ->
        when (tryMakeCompleting(state, proposedUpdate, mode)) {
            COMPLETING_ALREADY_COMPLETING -> throw IllegalStateException("Job $this is already complete or completing, " +
                "but is being completed with $proposedUpdate", proposedUpdate.exceptionOrNull)
            COMPLETING_COMPLETED -> return true
            COMPLETING_WAITING_CHILDREN -> return false
            COMPLETING_RETRY -> return@loopOnState
            else -> error("unexpected result")
        }
    }

    private fun tryMakeCompleting(state: Any?, proposedUpdate: Any?, mode: Int): Int {
        if (state !is Incomplete)
            return COMPLETING_ALREADY_COMPLETING
        /*
         * FAST PATH -- no children to wait for && simple state (no list) && not cancelling => can complete immediately
         * Cancellation (failures) always have to go through Finishing state to serialize exception handling.
         * Otherwise, there can be a race between (completed state -> handled exception and newly attached child/join)
         * which may miss unhandled exception.
         */
        if ((state is Empty || state is JobNode<*>) && state !is ChildHandleNode && proposedUpdate !is CompletedExceptionally) {
            if (!tryFinalizeSimpleState(state, proposedUpdate, mode)) return COMPLETING_RETRY
            return COMPLETING_COMPLETED
        }
        // The separate slow-path function to simplify profiling
        return tryMakeCompletingSlowPath(state, proposedUpdate, mode)
    }

    private fun tryMakeCompletingSlowPath(state: Incomplete, proposedUpdate: Any?, mode: Int): Int {
        // get state's list or else promote to list to correctly operate on child lists
        val list = getOrPromoteCancellingList(state) ?: return COMPLETING_RETRY
        // promote to Finishing state if we are not in it yet
        // This promotion has to be atomic w.r.t to state change, so that a coroutine that is not active yet
        // atomically transition to finishing & completing state
        val finishing = state as? Finishing ?: Finishing(list, false, null)
        // must synchronize updates to finishing state
        var notifyRootCause: Throwable? = null
        synchronized(finishing) {
            // check if this state is already completing
            if (finishing.isCompleting) return COMPLETING_ALREADY_COMPLETING
            // mark as completing
            finishing.isCompleting = true
            // if we need to promote to finishing then atomically do it here.
            // We do it as early is possible while still holding the lock. This ensures that we cancelImpl asap
            // (if somebody else is faster) and we synchronize all the threads on this finishing lock asap.
            if (finishing !== state) {
                if (!_state.compareAndSet(state, finishing)) return COMPLETING_RETRY
            }
            // ## IMPORTANT INVARIANT: Only one thread (that had set isCompleting) can go past this point
            require(!finishing.isSealed) // cannot be sealed
            // add new proposed exception to the finishing state
            val wasCancelling = finishing.isCancelling
            (proposedUpdate as? CompletedExceptionally)?.let { finishing.addExceptionLocked(it.cause) }
            // If it just becomes cancelling --> must process cancelling notifications
            notifyRootCause = finishing.rootCause.takeIf { !wasCancelling }
        }
        // process cancelling notification here -- it cancels all the children _before_ we start to to wait them (sic!!!)
        notifyRootCause?.let { notifyCancelling(list, it) }
        // now wait for children
        val child = firstChild(state)
        if (child != null && tryWaitForChild(finishing, child, proposedUpdate))
            return COMPLETING_WAITING_CHILDREN
        // otherwise -- we have not children left (all were already cancelled?)
        if (tryFinalizeFinishingState(finishing, proposedUpdate, mode))
            return COMPLETING_COMPLETED
        // otherwise retry
        return COMPLETING_RETRY
    }

    private val Any?.exceptionOrNull: Throwable?
        get() = (this as? CompletedExceptionally)?.cause

    private fun firstChild(state: Incomplete) =
        state as? ChildHandleNode ?: state.list?.nextChild()

    // return false when there is no more incomplete children to wait
    // ## IMPORTANT INVARIANT: Only one thread can be concurrently invoking this method.
    private tailrec fun tryWaitForChild(state: Finishing, child: ChildHandleNode, proposedUpdate: Any?): Boolean {
        val handle = child.childJob.invokeOnCompletion(
            invokeImmediately = false,
            handler = ChildCompletion(this, state, child, proposedUpdate).asHandler
        )
        if (handle !== NonDisposableHandle) return true // child is not complete and we've started waiting for it
        val nextChild = child.nextChild() ?: return false
        return tryWaitForChild(state, nextChild, proposedUpdate)
    }

    // ## IMPORTANT INVARIANT: Only one thread can be concurrently invoking this method.
    private fun continueCompleting(state: Finishing, lastChild: ChildHandleNode, proposedUpdate: Any?) {
        require(this.state === state) // consistency check -- it cannot change while we are waiting for children
        // figure out if we need to wait for next child
        val waitChild = lastChild.nextChild()
        // try wait for next child
        if (waitChild != null && tryWaitForChild(state, waitChild, proposedUpdate)) return // waiting for next child
        // no more children to wait -- try update state
        if (tryFinalizeFinishingState(state, proposedUpdate, MODE_ATOMIC_DEFAULT)) return
    }

    private fun LockFreeLinkedListNode.nextChild(): ChildHandleNode? {
        var cur = this
        while (cur.isRemoved) cur = cur.prevNode // rollback to prev non-removed (or list head)
        while (true) {
            cur = cur.nextNode
            if (cur.isRemoved) continue
            if (cur is ChildHandleNode) return cur
            if (cur is NodeList) return null // checked all -- no more children
        }
    }

    public final override val children: Sequence<Job> get() = sequence {
        when (val state = this@JobSupport.state) {
            is ChildHandleNode -> yield(state.childJob)
            is Incomplete -> state.list?.let { list ->
                list.forEach<ChildHandleNode> { yield(it.childJob) }
            }
        }
    }

    @Suppress("OverridingDeprecatedMember")
    public final override fun attachChild(child: ChildJob): ChildHandle {
        /*
         * Note: This function attaches a special ChildHandleNode node object. This node object
         * is handled in a special way on completion on the coroutine (we wait for all of them) and
         * is handled specially by invokeOnCompletion itself -- it adds this node to the list even
         * if the job is already cancelling. For cancelling state child is attached under state lock.
         * It's required to properly wait all children before completion and provide linearizable hierarchy view:
         * If child is attached when the job is already being cancelled, such child will receive immediate notification on
         * cancellation, but parent *will* wait for that child before completion and will handle its exception.
         */
        return invokeOnCompletion(onCancelling = true, handler = ChildHandleNode(this, child).asHandler) as ChildHandle
    }

    /**
     * Override to process any exceptions that were encountered while invoking completion handlers
     * installed via [invokeOnCompletion].
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun handleOnCompletionException(exception: Throwable) {
        throw exception
    }

    /**
     * This function is invoked once as soon as this job is being cancelled for any reason or completes,
     * similarly to [invokeOnCompletion] with `onCancelling` set to `true`.
     *
     * The meaning of [cause] parameter:
     * * Cause is `null` when the job has completed normally.
     * * Cause is an instance of [CancellationException] when the job was cancelled _normally_.
     *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
     * * Otherwise, the job had been cancelled or failed with exception.
     *
     * The specified [cause] is not the final cancellation cause of this job.
     * A job may produce other exceptions while it is failing and the final cause might be different.
     *
     * @suppress **This is unstable API and it is subject to change.*
     */
    protected open fun onCancelling(cause: Throwable?) {}

    /**
     * Returns `true` for scoped coroutines.
     * Scoped coroutine is a coroutine that is executed sequentially within the enclosing scope without any concurrency.
     * Scoped coroutines always handle any exception happened within -- they just rethrow it to the enclosing scope.
     * Examples of scoped coroutines are `coroutineScope`, `withTimeout` and `runBlocking`.
     */
    protected open val isScopedCoroutine: Boolean get() = false

    /**
     * Returns `true` for jobs that handle their exceptions or integrate them into the job's result via [onCompletionInternal].
     * A valid implementation of this getter should recursively check parent as well before returning `false`.
     *
     * The only instance of the [Job] that does not handle its exceptions is [JobImpl] and its subclass [SupervisorJobImpl].
     * @suppress **This is unstable API and it is subject to change.*
     */
    internal open val handlesException: Boolean get() = true

    /**
     * Handles the final job [exception] that was not handled by the parent coroutine.
     * Returns `true` if it handles exception (so handling at later stages is not needed).
     * It is designed to be overridden by launch-like coroutines
     * (`StandaloneCoroutine` and `ActorCoroutine`) that don't have a result type
     * that can represent exceptions.
     *
     * This method is invoked **exactly once** when the final exception of the job is determined
     * and before it becomes complete. At the moment of invocation the job and all its children are complete.
     */
    protected open fun handleJobException(exception: Throwable): Boolean = false

    /**
     * Override for completion actions that need to update some external object depending on job's state,
     * right before all the waiters for coroutine's completion are notified.
     *
     * @param state the final state.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun onCompletionInternal(state: Any?) {}

    /**
     * Override for the very last action on job's completion to resume the rest of the code in scoped coroutines.
     *
     * @param state the final state.
     * @param mode completion mode.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun afterCompletionInternal(state: Any?, mode: Int) {}

    // for nicer debugging
    public override fun toString(): String =
        "${toDebugString()}@$hexAddress"

    @InternalCoroutinesApi
    public fun toDebugString(): String = "${nameString()}{${stateString(state)}}"

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun nameString(): String = classSimpleName

    private fun stateString(state: Any?): String = when (state) {
        is Finishing -> when {
            state.isCancelling -> "Cancelling"
            state.isCompleting -> "Completing"
            else -> "Active"
        }
        is Incomplete -> if (state.isActive) "Active" else "New"
        is CompletedExceptionally -> "Cancelled"
        else -> "Completed"
    }

    // Completing & Cancelling states,
    // All updates are guarded by synchronized(this), reads are volatile
    @Suppress("UNCHECKED_CAST")
    private class Finishing(
        override val list: NodeList,
        @Volatile
        @JvmField var isCompleting: Boolean,
        @Volatile
        @JvmField var rootCause: Throwable? // NOTE: rootCause is kept even when SEALED
    ) : SynchronizedObject(), Incomplete {
        @Volatile
        private var _exceptionsHolder: Any? = null // Contains null | Throwable | ArrayList | SEALED

        // NotE: cannot be modified when sealed
        val isSealed: Boolean get() = _exceptionsHolder === SEALED
        val isCancelling: Boolean get() = rootCause != null
        override val isActive: Boolean get() = rootCause == null // !isCancelling

        // Seals current state and returns list of exceptions
        // guarded by `synchronized(this)`
        fun sealLocked(proposedException: Throwable?): List<Throwable> {
            val list = when(val eh = _exceptionsHolder) { // volatile read
                null -> allocateList()
                is Throwable -> allocateList().also { it.add(eh) }
                is ArrayList<*> -> eh as ArrayList<Throwable>
                else -> error("State is $eh") // already sealed -- cannot happen
            }
            val rootCause = this.rootCause // volatile read
            rootCause?.let { list.add(0, it) } // note -- rootCause goes to the beginning
            if (proposedException != null && proposedException != rootCause) list.add(proposedException)
            _exceptionsHolder = SEALED
            return list
        }

        // guarded by `synchronized(this)`
        fun addExceptionLocked(exception: Throwable) {
            val rootCause = this.rootCause // volatile read
            if (rootCause == null) {
                this.rootCause = exception
                return
            }
            if (exception === rootCause) return // nothing to do
            when (val eh = _exceptionsHolder) { // volatile read
                null -> _exceptionsHolder = exception
                is Throwable -> {
                    if (exception === eh) return // nothing to do
                    _exceptionsHolder = allocateList().apply {
                        add(eh)
                        add(exception)

                    }
                }
                is ArrayList<*> -> (eh as ArrayList<Throwable>).add(exception)
                else -> error("State is $eh") // already sealed -- cannot happen
            }
        }

        private fun allocateList() = ArrayList<Throwable>(4)

        override fun toString(): String =
            "Finishing[cancelling=$isCancelling, completing=$isCompleting, rootCause=$rootCause, exceptions=$_exceptionsHolder, list=$list]"
    }

    private val Incomplete.isCancelling: Boolean
        get() = this is Finishing && isCancelling

    // Used by parent that is waiting for child completion
    private class ChildCompletion(
        private val parent: JobSupport,
        private val state: Finishing,
        private val child: ChildHandleNode,
        private val proposedUpdate: Any?
    ) : JobNode<Job>(child.childJob) {
        override fun invoke(cause: Throwable?) {
            parent.continueCompleting(state, child, proposedUpdate)
        }
        override fun toString(): String =
            "ChildCompletion[$child, $proposedUpdate]"
    }

    private class AwaitContinuation<T>(
        delegate: Continuation<T>,
        private val job: JobSupport
    ) : CancellableContinuationImpl<T>(delegate, MODE_CANCELLABLE) {
        override fun getContinuationCancellationCause(parent: Job): Throwable {
            val state = job.state
            /*
             * When the job we are waiting for had already completely completed exceptionally or
             * is failing, we shall use its root/completion cause for await's result.
             */
            if (state is Finishing) state.rootCause?.let { return it }
            if (state is CompletedExceptionally) return state.cause
            return parent.getCancellationException()
        }

        protected override fun nameString(): String =
            "AwaitContinuation"
    }

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
        return state.unboxState()
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal suspend fun awaitInternal(): Any? {
        // fast-path -- check state (avoid extra object creation)
        while (true) { // lock-free loop on state
            val state = this.state
            if (state !is Incomplete) {
                // already complete -- just return result
                if (state is CompletedExceptionally) { // Slow path to recover stacktrace
                    recoverAndThrow(state.cause)
                }
                return state.unboxState()

            }
            if (startInternal(state) >= 0) break // break unless needs to retry
        }
        return awaitSuspend() // slow-path
    }

    private suspend fun awaitSuspend(): Any? = suspendCoroutineUninterceptedOrReturn { uCont ->
        /*
         * Custom code here, so that parent coroutine that is using await
         * on its child deferred (async) coroutine would throw the exception that this child had
         * thrown and not a JobCancellationException.
         */
        val cont = AwaitContinuation(uCont.intercepted(), this)
        cont.disposeOnCancellation(invokeOnCompletion(ResumeAwaitOnCompletion(this, cont).asHandler))
        cont.getResult()
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
                    if (state is CompletedExceptionally) {
                        select.resumeSelectCancellableWithException(state.cause)
                    }
                    else {
                        block.startCoroutineUnintercepted(state.unboxState() as T, select.completion)
                    }
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
            block.startCoroutineCancellable(state.unboxState() as T, select.completion)
    }
}

/*
 * Class to represent object as the final state of the Job
 */
private class IncompleteStateBox(@JvmField val state: Incomplete)
internal fun Any?.boxIncomplete(): Any? = if (this is Incomplete) IncompleteStateBox(this) else this
internal fun Any?.unboxState(): Any? = (this as? IncompleteStateBox)?.state ?: this

// --------------- helper classes & constants for job implementation

private const val COMPLETING_ALREADY_COMPLETING = 0
private const val COMPLETING_COMPLETED = 1
private const val COMPLETING_WAITING_CHILDREN = 2
private const val COMPLETING_RETRY = 3

private const val RETRY = -1
private const val FALSE = 0
private const val TRUE = 1

@SharedImmutable
private val SEALED = Symbol("SEALED")
@SharedImmutable
private val EMPTY_NEW = Empty(false)
@SharedImmutable
private val EMPTY_ACTIVE = Empty(true)

private class Empty(override val isActive: Boolean) : Incomplete {
    override val list: NodeList? get() = null
    override fun toString(): String = "Empty{${if (isActive) "Active" else "New" }}"
}

internal open class JobImpl(parent: Job?) : JobSupport(true), CompletableJob {
    init { initParentJobInternal(parent) }
    override val onCancelComplete get() = true
    /*
     * Check whether parent is able to handle exceptions as well.
     * With this check, an exception in that pattern will be handled once:
     * ```
     * launch {
     *     val child = Job(coroutineContext[Job])
     *     launch(child) { throw ... }
     * }
     * ```
     */
    override val handlesException: Boolean = handlesException()
    override fun complete() = makeCompleting(Unit)
    override fun completeExceptionally(exception: Throwable): Boolean =
        makeCompleting(CompletedExceptionally(exception))

    @JsName("handlesExceptionF")
    private fun handlesException(): Boolean {
        var parentJob = (parentHandle as? ChildHandleNode)?.job ?: return false
        while (true) {
            if (parentJob.handlesException) return true
            parentJob = (parentJob.parentHandle as? ChildHandleNode)?.job ?: return false
        }
    }
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

internal class NodeList : LockFreeLinkedListHead(), Incomplete {
    override val isActive: Boolean get() = true
    override val list: NodeList get() = this

    fun getString(state: String) = buildString {
        append("List{")
        append(state)
        append("}[")
        var first = true
        this@NodeList.forEach<JobNode<*>> { node ->
            if (first) first = false else append(", ")
            append(node)
        }
        append("]")
    }

    override fun toString(): String =
        if (DEBUG) getString("Active") else super.toString()
}

internal class InactiveNodeList(
    override val list: NodeList
) : Incomplete {
    override val isActive: Boolean get() = false
    override fun toString(): String = if (DEBUG) list.getString("New") else super.toString()
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

private class ResumeAwaitOnCompletion<T>(
    job: JobSupport,
    private val continuation: CancellableContinuationImpl<T>
) : JobNode<JobSupport>(job) {
    override fun invoke(cause: Throwable?) {
        val state = job.state
        assert { state !is Incomplete }
        if (state is CompletedExceptionally) {
            // Resume with exception in atomic way to preserve exception
            continuation.resumeWithExceptionMode(state.cause, MODE_ATOMIC_DEFAULT)
        } else {
            // Resuming with value in a cancellable way (AwaitContinuation is configured for this mode).
            @Suppress("UNCHECKED_CAST")
            continuation.resume(state.unboxState() as T)
        }
    }
    override fun toString() = "ResumeAwaitOnCompletion[$continuation]"
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
 * Marker for node that shall be invoked on in _cancelling_ state.
 * **Note: may be invoked multiple times.**
 */
internal abstract class JobCancellingNode<out J : Job>(job: J) : JobNode<J>(job)

private class InvokeOnCancelling(
    job: Job,
    private val handler: CompletionHandler
) : JobCancellingNode<Job>(job)  {
    // delegate handler shall be invoked at most once, so here is an additional flag
    private val _invoked = atomic(0) // todo: replace with atomic boolean after migration to recent atomicFu
    override fun invoke(cause: Throwable?) {
        if (_invoked.compareAndSet(0, 1)) handler.invoke(cause)
    }
    override fun toString() = "InvokeOnCancelling[$classSimpleName@$hexAddress]"
}

internal class ChildHandleNode(
    parent: JobSupport,
    @JvmField val childJob: ChildJob
) : JobCancellingNode<JobSupport>(parent), ChildHandle {
    override fun invoke(cause: Throwable?) = childJob.parentCancelled(job)
    override fun childCancelled(cause: Throwable): Boolean = job.childCancelled(cause)
    override fun toString(): String = "ChildHandle[$childJob]"
}

// Same as ChildHandleNode, but for cancellable continuation
internal class ChildContinuation(
    parent: Job,
    @JvmField val child: CancellableContinuationImpl<*>
) : JobCancellingNode<Job>(parent) {
    override fun invoke(cause: Throwable?) {
        child.cancel(child.getContinuationCancellationCause(job))
    }
    override fun toString(): String =
        "ChildContinuation[$child]"
}

