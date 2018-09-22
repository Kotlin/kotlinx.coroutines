/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*

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
       FINAL_C    Cancelled              : Cancelled     cancelled (final state)
       FINAL_F    CompletedExceptionally : Completed     failed for other reason (final state)
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


       This state machine and its transition matrix are optimized for the common case when job is created in active
       state (EMPTY_A), at most one completion listener is added to it during its life-time, and it completes
       successfully without children (in this case it directly goes from EMPTY_A or SINGLE state to FINAL_R
       state without going to COMPLETING state)

       Note, that the actual `_state` variable can also be a reference to atomic operation descriptor `OpDescriptor`

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
       ~ active coroutine is working
       >> childFailed / fail invoked
       ## FAILING: state is Finishing, state.rootCause != null
       ------ failing listeners are not admitted anymore, invokeOnCompletion(onFailing=true) returns NonDisposableHandle
       ------ new children get immediately cancelled, but are still admitted to the list
       + onFailing
       + notifyFailing (invoke all failing listeners -- cancel all children, suspended functions resume with exception)
       + failParent (rootCause of failure is communicated to the parent, parent starts failing, too)
       ~ waits for completion of coroutine body
       >> makeCompleting / makeCompletingOnce invoked
       ## COMPLETING: state is Finishing, state.isCompleting == true
       ------ new children are not admitted anymore, attachChild returns NonDisposableHandle
       ~ waits for children
       >> last child completes
       - computes the final exception
       ## SEALED: state is Finishing, state.isSealed == true
       ------ cancel/childFailed returns false (cannot handle exceptions anymore)
       + failParent (final exception is communicated to the parent, parent incorporates it)
       + handleJobException ("launch" StandaloneCoroutine invokes CoroutineExceptionHandler)
       ## COMPLETE: state !is Incomplete (CompletedExceptionally | Cancelled)
       ------ completion listeners are not admitted anymore, invokeOnCompletion returns NonDisposableHandle
       + parentHandle.dispose
       + notifyCompletion (invoke all completion listeners)
       + onCompletionInternal / onCompleted / onCompletedExceptionally

       ---------------------------------------------------------------------------------
     */

    // Note: use shared objects while we have no listeners
    private val _state = atomic<Any?>(if (active) EMPTY_ACTIVE else EMPTY_NEW)

    @Volatile
    private var parentHandle: ChildHandle? = null

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
        // now check our state _after_ registering (see tryFinalizeSimpleState order of actions)
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

    public override val isActive: Boolean get() {
        val state = this.state
        return state is Incomplete && state.isActive
    }

    public final override val isCompleted: Boolean get() = state !is Incomplete

    public final override val isFailed: Boolean get() {
        val state = this.state
        return state is CompletedExceptionally || (state is Finishing && state.isFailing)
    }

    public final override val isCancelled: Boolean get() {
        val state = this.state
        return state is Cancelled || (state is Finishing && state.isCancelling)
    }

    // ------------ state update ------------

    // Finalizes Finishing -> Completed (terminal state) transition.
    // ## IMPORTANT INVARIANT: Only one thread can be concurrently invoking this method.
    private fun tryFinalizeFinishingState(state: Finishing, proposedUpdate: Any?, mode: Int): Boolean {
        require(proposedUpdate !is Incomplete) // only incomplete -> completed transition is allowed
        require(this.state === state) // consistency check -- it cannot change
        require(!state.isSealed) // consistency check -- cannot be sealed yet
        require(state.isCompleting) // consistency check -- must be marked as completing
        val proposedException = (proposedUpdate as? CompletedExceptionally)?.cause
        val proposedCancel = proposedUpdate is Cancelled
        // Create the final exception and seal the state so that no more exceptions can be added
        var suppressed = false
        val finalException = synchronized(state) {
            val exceptions = state.sealLocked(proposedException)
            val rootCause = getFinalRootCause(state, exceptions)
            if (rootCause != null) suppressed = suppressExceptions(rootCause, exceptions)
            rootCause
        }
        // Create the final state object
        val finalState = when {
            // if we have not failed -> use proposed update value
            finalException == null -> proposedUpdate
            // small optimization when we can used proposeUpdate object as is on failure
            finalException === proposedException && proposedCancel == state.isCancelling -> proposedUpdate
            // cancelled job final state
            state.isCancelling -> Cancelled(finalException)
            // failed job final state
            else -> CompletedExceptionally(finalException)
        }
        // Now handle exception
        if (finalException != null) {
            if (!failParent(finalException)) {
                handleJobException(finalException)
            }
        }
        // Then CAS to completed state -> it must succeed
        require(_state.compareAndSet(state, finalState)) { "Unexpected state: ${_state.value}, expected: $state, update: $finalState" }
        // And process all post-completion actions
        completeStateFinalization(state, finalState, mode, suppressed)
        return true
    }

    private fun getFinalRootCause(state: Finishing, exceptions: List<Throwable>): Throwable? {
        // A case of no exceptions
        if (exceptions.isEmpty()) {
            // materialize cancellation exception if it was not materialized yet
            if (state.isCancelling) return createJobCancellationException()
            return null
        }
        /*
         * This is a place where we step on our API limitation:
         * We can't distinguish internal JobCancellationException from our parent
         * from external cancellation, thus we ought to collect all exceptions.
         *
         * But it has negative consequences: same exception can be added as suppressed more than once.
         * Consider concurrent parent-child relationship:
         * 1) Child throws E1 and parent throws E2.
         * 2) Parent goes to "Failing(E1)" and cancels child with E1
         * 3) Child goes to "Cancelling(E1)", but throws an exception E2
         * 4) When child throws, it notifies parent that it is failing, adding its exception to parent's list of exceptions/
         * 5) Child builds final exception: E1 with suppressed E2, reports it to parent.
         * 6) Parent aggregates three exceptions: original E1, reported E2 and "final" E1.
         *    It filters the third exception, but adds the second one to the first one, thus adding suppressed duplicate.
         *
         * Note that it's only happening when both parent and child throw exception simultaneously.
         */
        var rootCause = exceptions[0]
        if (rootCause is JobCancellationException) {
            val cause = unwrap(rootCause)
            rootCause = if (cause !== null) {
                cause
            } else {
                exceptions.firstOrNull { unwrap(it) != null } ?: return rootCause
            }
        }
        return rootCause
    }

    private fun suppressExceptions(rootCause: Throwable, exceptions: List<Throwable>): Boolean {
        if (exceptions.size <= 1) return false // nothing more to do here
        // TODO it should be identity set and optimized for small footprints
        val seenExceptions = HashSet<Throwable>(exceptions.size)
        var suppressed = false
        for (i in 1 until exceptions.size) {
            val unwrapped = unwrap(exceptions[i])
            if (unwrapped !== null && unwrapped !== rootCause) {
                if (seenExceptions.add(unwrapped)) {
                    rootCause.addSuppressedThrowable(unwrapped)
                    suppressed = true
                }
            }
        }
        return suppressed
    }

    private tailrec fun unwrap(exception: Throwable): Throwable? =
        if (exception is JobCancellationException) {
            val cause = exception.cause
            if (cause !== null) unwrap(cause) else null
        } else {
            exception
        }

    // fast-path method to finalize normally completed coroutines without children
    private fun tryFinalizeSimpleState(state: Incomplete, update: Any?, mode: Int): Boolean {
        check(state is Empty || state is JobNode<*>) // only simple state without lists where children can concurrently add
        check(update !is CompletedExceptionally) // only for normal completion
        if (!_state.compareAndSet(state, update)) return false
        completeStateFinalization(state, update, mode, false)
        return true
    }

    // suppressed == true when any exceptions were suppressed while building the final completion cause
    private fun completeStateFinalization(state: Incomplete, update: Any?, mode: Int, suppressed: Boolean) {
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
         * 2) Invoke onFailing: for resource cancellation resource cancellation etc.
         *    Only notify is was not notified yet.
         *    Note: we do not use notifyFailing here, since we are going to invoke all completion as our next step
         */
        if (!state.isFailing) onFailing(cause)
        /*
         * 3) Invoke completion handlers: .join(), callbacks etc.
         *    It's important to invoke them only AFTER exception handling, see #208
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
         * 4) Invoke onCompletionInternal: onNext(), timeout de-registration etc.
         *    It should be last so all callbacks observe consistent state
         *    of the job which doesn't depend on callback scheduling.
         */
        onCompletionInternal(update, mode, suppressed)
    }

    private fun notifyFailing(list: NodeList, cause: Throwable) {
        // first cancel our own children
        onFailing(cause)
        notifyHandlers<JobFailingNode<*>>(list, cause)
        // then report to the parent that we are failing
        failParent(cause) // tentative failure report -- does not matter if there is no parent
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

    public final override fun getCancellationException(): CancellationException {
        val state = this.state
        return when (state) {
            is Finishing -> state.rootCause?.toCancellationException("Job is failing")
                ?: error("Job is still new or active: $this")
            is Incomplete -> error("Job is still new or active: $this")
            is CompletedExceptionally -> state.cause.toCancellationException("Job has failed")
            else -> JobCancellationException("Job has completed normally", null, this)
        }
    }

    private fun Throwable.toCancellationException(message: String): CancellationException =
        this as? CancellationException ?: JobCancellationException(message, this, this@JobSupport)

    /**
     * Returns the cause that signals the completion of this job -- it returns the original
     * [cancel] cause, [JobCancellationException] or **`null` if this job had completed normally**.
     * This function throws [IllegalStateException] when invoked for an job that has not [completed][isCompleted] nor
     * failing yet.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun getCompletionCause(): Throwable? = loopOnState { state ->
        return when (state) {
            is Finishing -> state.rootCause
                ?: error("Job is still new or active: $this")
            is Incomplete -> error("Job is still new or active: $this")
            is CompletedExceptionally -> state.cause
            else -> null
        }
    }

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        invokeOnCompletion(onFailing = false, invokeImmediately = true, handler = handler)

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle =
        invokeOnCompletion(onFailing = onCancelling, invokeImmediately = true, handler = handler)

    @Suppress("OverridingDeprecatedMember")
    public final override fun invokeOnCompletion(onCancelling_: Boolean, handler: CompletionHandler): DisposableHandle =
        invokeOnCompletion(onFailing = onCancelling_, invokeImmediately = true, handler = handler)

    // todo: non-final as a workaround for KT-21968, should be final in the future
    public override fun invokeOnCompletion(
        onFailing: Boolean,
        invokeImmediately: Boolean,
        handler: CompletionHandler
    ): DisposableHandle {
        var nodeCache: JobNode<*>? = null
        loopOnState { state ->
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        // try move to SINGLE state
                        val node = nodeCache ?: makeNode(handler, onFailing).also { nodeCache = it }
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
                        if (onFailing && state is Finishing) {
                            synchronized(state) {
                                // check if we are installing failing handler on job that is failing
                                rootCause = state.rootCause // != null if we are failing
                                // We add node to the list in two cases --- either the job is not failing
                                // or we are adding a child to a coroutine that is not completing yet
                                if (rootCause == null || handler.isHandlerOf<ChildJob>() && !state.isCompleting) {
                                    // Note: add node the list while holding lock on state (make sure it cannot change)
                                    val node = nodeCache ?: makeNode(handler, onFailing).also { nodeCache = it }
                                    if (!addLastAtomic(state, list, node)) return@loopOnState // retry
                                    // just return node if we don't have to invoke handler (not failing yet)
                                    if (rootCause == null) return node
                                    // otherwise handler is invoked immediately out of the synchronized section & handle returned
                                    handle = node
                                }
                            }
                        }
                        if (rootCause != null) {
                            // Note: attachChild uses invokeImmediately, so it gets invoked when adding to failing job
                            if (invokeImmediately) handler.invokeIt(rootCause)
                            return handle
                        } else {
                            val node = nodeCache ?: makeNode(handler, onFailing).also { nodeCache = it }
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
            (handler as? JobFailingNode<*>)?.also { require(it.job === this) }
                ?: InvokeOnFailing(this, handler)
        else
            (handler as? JobNode<*>)?.also { require(it.job === this && it !is JobFailingNode) }
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
                    select.completion.context.checkCompletion() // always check for our completion
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
    internal open val onFailComplete: Boolean get() = false

    // external cancel with (optional) cause
    public override fun cancel(cause: Throwable?): Boolean =
        fail(cause, cancel = true) && handlesException

    // child is reporting failure to the parent
    internal fun childFailed(cause: Throwable) =
        fail(cause, cancel = false) && handlesException

    // parent is cancelling child
    public override fun cancelChild(parentJob: Job) {
        fail(parentJob, cancel = true)
    }

    // cause is Throwable or Job when cancelChild was invoked, cause can be null only on cancel
    // returns true is exception was handled, false otherwise
    private fun fail(cause: Any?, cancel: Boolean): Boolean {
        if (onFailComplete) {
            // make sure it is completing, if failMakeCompleting returns true it means it had make it
            // completing and had recorded exception
            if (failMakeCompleting(cause, cancel)) return true
            // otherwise just record failure via makeFailing below
        }
        return makeFailing(cause, cancel)
    }

    private fun failMakeCompleting(cause: Any?, cancel: Boolean): Boolean {
        loopOnState { state ->
            if (state !is Incomplete || state is Finishing && state.isCompleting) {
                return false // already completed/completing, do not even propose update
            }
            val proposedUpdate = createFailure(createCauseException(cause), cancel)
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

    // cause is Throwable or Job when cancelChild was invoked, cause can be null only on cancel
    private fun createCauseException(cause: Any?): Throwable = when(cause) {
        is Throwable? -> cause ?: createJobCancellationException()
        else -> (cause as Job).getCancellationException()
    }

    private fun createFailure(causeException: Throwable, cancel: Boolean): CompletedExceptionally =
        when {
            cancel -> Cancelled(causeException)
            else -> CompletedExceptionally(causeException)
        }

    // transitions to Failing state
    // cause is Throwable or Job when cancelChild was invoked, cause can be null only on cancel
    private fun makeFailing(cause: Any?, cancel: Boolean): Boolean {
        var causeExceptionCache: Throwable? = null // lazily init result of createCauseException(cause)
        loopOnState { state ->
            when (state) {
                is Finishing -> { // already finishing -- collect exceptions
                    var notifyRootCause: Throwable? = null
                    synchronized(state) {
                        if (state.isSealed) return false // too late, already sealed -- cannot add exception nor mark cancelled
                        // add exception, do nothing is parent is cancelling child that is already failing
                        val wasFailing = state.isFailing // will notify if was not failing
                        // Materialize missing exception if it is the first exception (otherwise -- don't)
                        if (cause != null || !wasFailing) {
                            val causeException = causeExceptionCache ?: createCauseException(cause).also { causeExceptionCache = it }
                            state.addExceptionLocked(causeException)
                        }
                        // mark as cancelling if cancel was requested
                        if (cancel) state.isCancelling = true
                        // take cause for notification is was not failing before
                        notifyRootCause = state.rootCause.takeIf { !wasFailing }
                    }
                    notifyRootCause?.let { notifyFailing(state.list, it) }
                    return true
                }
                is Incomplete -> {
                    // Not yet finishing -- try to make it failing
                    val list = tryPromoteToList(state) ?: return@loopOnState
                    val causeException = causeExceptionCache ?: createCauseException(cause).also { causeExceptionCache = it }
                    if (state.isActive) {
                        // active state becomes failing
                        if (tryMakeFailing(state, list, causeException, cancel)) return true
                    } else {
                        // non active state starts completing
                        when (tryMakeCompleting(state, createFailure(causeException, cancel), mode = MODE_ATOMIC_DEFAULT)) {
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

    // Performs promotion of incomplete coroutine state to NodeList, returns null when need to retry
    private fun tryPromoteToList(state: Incomplete): NodeList? = state.list ?: null.also {
        when (state) {
            is Empty -> promoteEmptyToNodeList(state)
            is JobNode<*> -> promoteSingleToNodeList(state)
            else -> error("State should have list: $state")
        }
    }

    // try make new failing state on the condition that we're still in the expected state
    private fun tryMakeFailing(state: Incomplete, list: NodeList, rootCause: Throwable, cancel: Boolean): Boolean {
        check(state !is Finishing) // only for non-finishing states
        check(state.isActive) // only for active states
        // Create failing state (with rootCause!)
        val failing = Finishing(list, cancel, false, rootCause)
        if (!_state.compareAndSet(state, failing)) return false
        // Notify listeners
        notifyFailing(list, rootCause)
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
        // FAST PATH -- no children to wait for && simple state (no list) && not failing => can complete immediately
        // Failures always have to go through Finishing state to serialize exception handling
        if ((state is Empty || state is JobNode<*>) && state !is ChildJob && proposedUpdate !is CompletedExceptionally) {
            if (!tryFinalizeSimpleState(state, proposedUpdate, mode)) return COMPLETING_RETRY
            return COMPLETING_COMPLETED
        }
        // get state's list or else promote to list to correctly operate on child lists
        val list = tryPromoteToList(state) ?: return COMPLETING_RETRY
        // promote to Finishing state if we are not in it yet
        // This promotion has to be atomic w.r.t to state change, so that a coroutine that is not active yet
        // atomically transition to finishing & completing state
        val finishing = state as? Finishing ?: Finishing(list, false, false, null)
        // must synchronize updates to finishing state
        var notifyRootCause: Throwable? = null
        synchronized(finishing) {
            // check if this state is already completing
            if (finishing.isCompleting) return COMPLETING_ALREADY_COMPLETING
            // mark as completing
            finishing.isCompleting = true
            // ## IMPORTANT INVARIANT: Only one thread (that had set isCompleting) can go past this point
            require(!finishing.isSealed) // cannot be sealed
            // mark as cancelling is the proposed update is to cancel
            if (proposedUpdate is Cancelled) finishing.isCancelling = true
            // add new proposed exception to the finishing state
            val wasFailing = finishing.isFailing
            (proposedUpdate as? CompletedExceptionally)?.let { finishing.addExceptionLocked(it.cause) }
            // If it just becomes failing --> must process failing notifications
            notifyRootCause = finishing.rootCause.takeIf { !wasFailing }
        }
        // if we need to promote to finishing then atomically do it here
        if (finishing !== state) {
            if (!_state.compareAndSet(state, finishing)) return COMPLETING_RETRY
        }
        // process failing notification here -- it cancels all the children _before_ we start to to wait them (sic!!!)
        notifyRootCause?.let { notifyFailing(list, it) }
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
        state as? ChildJob ?: state.list?.nextChild()

    // return false when there is no more incomplete children to wait
    // ## IMPORTANT INVARIANT: Only one thread can be concurrently invoking this method.
    private tailrec fun tryWaitForChild(state: Finishing, child: ChildJob, proposedUpdate: Any?): Boolean {
        val handle = child.childJob.invokeOnCompletion(
            invokeImmediately = false,
            handler = ChildCompletion(this, state, child, proposedUpdate).asHandler
        )
        if (handle !== NonDisposableHandle) return true // child is not complete and we've started waiting for it
        val nextChild = child.nextChild() ?: return false
        return tryWaitForChild(state, nextChild, proposedUpdate)
    }

    // ## IMPORTANT INVARIANT: Only one thread can be concurrently invoking this method.
    private fun continueCompleting(state: Finishing, lastChild: ChildJob, proposedUpdate: Any?) {
        require(this.state === state) // consistency check -- it cannot change while we are waiting for children
        // figure out if we need to wait for next child
        val waitChild = lastChild.nextChild()
        // try wait for next child
        if (waitChild != null && tryWaitForChild(state, waitChild, proposedUpdate)) return // waiting for next child
        // no more children to wait -- try update state
        if (tryFinalizeFinishingState(state, proposedUpdate, MODE_ATOMIC_DEFAULT)) return
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
    public final override fun attachChild(child: Job): ChildHandle {
        /*
         * Note: This function attaches a special ChildNode object. This node object
         * is handled in a special way on completion on the coroutine (we wait for all of them) and
         * is handled specially by invokeOnCompletion itself -- it adds this node to the list even
         * if the job is already failing.
         */
        return invokeOnCompletion(onFailing = true, handler = ChildJob(this, child).asHandler) as ChildHandle
    }

    @Suppress("OverridingDeprecatedMember")
    public final override fun cancelChildren(cause: Throwable?) {
        this.cancelChildren(cause) // use extension function
    }

    /**
     * Override to process any exceptions that were encountered while invoking completion handlers
     * installed via [invokeOnCompletion].
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun handleOnCompletionException(exception: Throwable) {
        throw exception
    }

    /**
     * This function is invoked once when job is failing or is completed.
     * It's an optimization for [invokeOnCompletion] with `onCancelling` set to `true`.
     *
     * @suppress **This is unstable API and it is subject to change.*
     */
    internal open fun onFailing(cause: Throwable?) {}

    /**
     * When this function returns `true` the parent fails on the failure of this job.
     *
     * @suppress **This is unstable API and it is subject to change.*
     */
    protected open val failsParent: Boolean get() = false

    /**
     * Returns `true` for jobs that handle their exceptions via [handleJobException] or integrate them
     * into the job's result via [onCompletionInternal]. The only instance of the [Job] that does not
     * handle its exceptions is [JobImpl].
     *
     * @suppress **This is unstable API and it is subject to change.*
     */
    protected open val handlesException: Boolean get() = true

    /**
     * This method is invoked **exactly once** when the final exception of the job is determined
     * and before it becomes complete. At the moment of invocation the job and all its children are complete.
     *
     * @suppress **This is unstable API and it is subject to change.*
     */
    protected open fun handleJobException(exception: Throwable) {}

    private fun failParent(cause: Throwable): Boolean {
        if (cause is CancellationException) return true
        if (!failsParent) return false
        return parentHandle?.childFailed(cause) == true
    }

    /**
     * Override for post-completion actions that need to do something with the state.
     * @param state the final state.
     * @param mode completion mode.
     * @param suppressed true when any exceptions were suppressed while building the final completion cause.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal open fun onCompletionInternal(state: Any?, mode: Int, suppressed: Boolean) {}

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
                when { // cancelling implies failing
                    state.isCancelling -> append("Cancelling")
                    state.isFailing -> append("Failing")
                    else -> append("Active")
                }
                if (state.isCompleting) append("Completing")
            }
            is Incomplete -> if (state.isActive) "Active" else "New"
            is Cancelled -> "Cancelled"
            is CompletedExceptionally -> "Failed"
            else -> "Completed"
        }
    }

    // Completing, Failing, Cancelling states,
    // All updates are guarded by synchronized(this), reads are volatile
    @Suppress("UNCHECKED_CAST")
    private class Finishing(
        override val list: NodeList,
        @Volatile
        @JvmField var isCancelling: Boolean,
        @Volatile
        @JvmField var isCompleting: Boolean,
        @Volatile
        @JvmField var rootCause: Throwable? // NOTE: rootCause is kept even when SEALED
    ) : SynchronizedObject(), Incomplete {
        @Volatile
        private var _exceptionsHolder: Any? = null // Contains null | Throwable | ArrayList | SEALED

        // NotE: cannot be modified when sealed
        val isSealed: Boolean get() = _exceptionsHolder === SEALED
        val isFailing: Boolean get() = rootCause != null
        override val isActive: Boolean get() = !isFailing

        // Seals current state and returns list of exceptions
        // guarded by `synchronized(this)`
        fun sealLocked(proposedException: Throwable?): List<Throwable> {
            val eh = _exceptionsHolder // volatile read
            val list = when(eh) {
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
            val eh = _exceptionsHolder // volatile read
            when (eh) {
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

    private val Incomplete.isFailing: Boolean
        get() = this is Finishing && isFailing

    private val Incomplete.isCancelling: Boolean
        get() = this is Finishing && isCancelling

    // Used by parent that is waiting for child completion
    private class ChildCompletion(
        private val parent: JobSupport,
        private val state: Finishing,
        private val child: ChildJob,
        private val proposedUpdate: Any?
    ) : JobNode<Job>(child.childJob) {
        override fun invoke(cause: Throwable?) {
            parent.continueCompleting(state, child, proposedUpdate)
        }
        override fun toString(): String =
            "ChildCompletion[$child, $proposedUpdate]"
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
                        block.startCoroutineUnintercepted(state as T, select.completion)
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

// --------------- helper classes & constants for job implementation

private const val COMPLETING_ALREADY_COMPLETING = 0
private const val COMPLETING_COMPLETED = 1
private const val COMPLETING_WAITING_CHILDREN = 2
private const val COMPLETING_RETRY = 3

private const val RETRY = -1
private const val FALSE = 0
private const val TRUE = 1

private val SEALED = Symbol("SEALED")

private val EMPTY_NEW = Empty(false)
private val EMPTY_ACTIVE = Empty(true)

private class Empty(override val isActive: Boolean) : Incomplete {
    override val list: NodeList? get() = null
    override fun toString(): String = "Empty{${if (isActive) "Active" else "New" }}"
}

internal class JobImpl(parent: Job? = null) : JobSupport(true) {
    init { initParentJobInternal(parent) }
    override val onFailComplete get() = true
    override val handlesException: Boolean get() = false
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

    override fun toString(): String = getString("Active")
}

internal class InactiveNodeList(
    override val list: NodeList
) : Incomplete {
    override val isActive: Boolean get() = false
    override fun toString(): String = list.getString("New")
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
 * Marker for node that shall be invoked on in _failing_ state.
 * **Note: may be invoked multiple times.**
 */
internal abstract class JobFailingNode<out J : Job>(job: J) : JobNode<J>(job)

private class InvokeOnFailing(
    job: Job,
    private val handler: CompletionHandler
) : JobFailingNode<Job>(job)  {
    // delegate handler shall be invoked at most once, so here is an additional flag
    private val _invoked = atomic(0) // todo: replace with atomic boolean after migration to recent atomicFu
    override fun invoke(cause: Throwable?) {
        if (_invoked.compareAndSet(0, 1)) handler.invoke(cause)
    }
    override fun toString() = "InvokeOnFailing[$classSimpleName@$hexAddress]"
}

internal class ChildJob(
    parent: JobSupport,
    @JvmField val childJob: Job
) : JobFailingNode<JobSupport>(parent), ChildHandle {
    override fun invoke(cause: Throwable?) = childJob.cancelChild(job)
    override fun childFailed(cause: Throwable): Boolean = job.childFailed(cause)
    override fun toString(): String = "ChildJob[$childJob]"
}

// Same as ChildJob, but for cancellable continuation
internal class ChildContinuation(
    parent: Job,
    @JvmField val child: AbstractContinuation<*>
) : JobFailingNode<Job>(parent) {
    override fun invoke(cause: Throwable?) {
        child.cancel(job.getCancellationException())
    }
    override fun toString(): String =
        "ChildContinuation[$child]"
}

