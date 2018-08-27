package kotlinx.coroutines.experimental.grpc.stub

import io.grpc.CallOptions
import io.grpc.Channel
import io.grpc.stub.AbstractStub
import kotlinx.coroutines.experimental.DefaultDispatcher
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.coroutineContext

abstract class AbstractGrpcCoroutineStub<T: AbstractGrpcCoroutineStub<T>>(
        channel:Channel,
        callOptions: CallOptions
) : AbstractStub<T>(channel, callOptions) {

    protected abstract val delegateStub: AbstractStub<*>

    val context: CoroutineContext get() =
        this.callOptions.getOption(CALL_OPTION_COROUTINE_CONTEXT_KEY)

    fun withCoroutineContext(context: CoroutineContext) : T =
            this.withOption(CALL_OPTION_COROUTINE_CONTEXT_KEY, context)

    suspend fun withCoroutineContext() : T =
            this.withOption(CALL_OPTION_COROUTINE_CONTEXT_KEY, coroutineContext)

    companion object {
        val CALL_OPTION_COROUTINE_CONTEXT_KEY: CallOptions.Key<CoroutineContext> =
                CallOptions.Key.createWithDefault("coroutineContext", DefaultDispatcher)
    }
}
