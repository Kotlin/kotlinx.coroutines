package kotlinx.coroutines.experimental

public expect object NonCancellable : Job {
    override val isActive: Boolean
    override val isCompleted: Boolean
    override val isCancelled: Boolean
    override fun start(): Boolean
    suspend override fun join()
    override fun getCancellationException(): CancellationException
    override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle
    override fun cancel(cause: Throwable?): Boolean
    override val children: Sequence<Job>
    @Suppress("OverridingDeprecatedMember")
    override fun attachChild(child: Job): DisposableHandle
}
