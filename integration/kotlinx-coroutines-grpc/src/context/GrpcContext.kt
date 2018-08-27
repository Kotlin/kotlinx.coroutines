package context

import kotlinx.coroutines.experimental.ThreadContextElement
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.CoroutineContext

class GrpcContext(
        /**
         * The value of [io.grpc.Context] grpc context.
         */
        public val context: io.grpc.Context = io.grpc.Context.current()
) : ThreadContextElement<io.grpc.Context>, AbstractCoroutineContextElement(Key) {
    /**
     * Key of [GrpcContext] in [CoroutineContext].
     */
    companion object Key : CoroutineContext.Key<GrpcContext>

    override fun updateThreadContext(context: CoroutineContext): io.grpc.Context =
            this@GrpcContext.context.attach()


    override fun restoreThreadContext(context: CoroutineContext, oldState: io.grpc.Context) {
        io.grpc.Context.current().detach(oldState)
    }

}