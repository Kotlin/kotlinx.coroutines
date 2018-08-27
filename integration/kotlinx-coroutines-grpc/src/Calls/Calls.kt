package kotlinx.coroutines.experimental.grpc

import io.grpc.stub.StreamObserver
import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.DefaultDispatcher
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.grpc.channels.ClientBidiCallChannel
import kotlinx.coroutines.experimental.grpc.channels.ClientStreamingCallChannel
import kotlinx.coroutines.experimental.grpc.channels.InboundStreamChannel
import kotlinx.coroutines.experimental.grpc.channels.SuspendingUnaryObserver
import kotlinx.coroutines.experimental.suspendCancellableCoroutine
import kotlin.coroutines.experimental.CoroutineContext


object ClientCalls{

    suspend inline fun <R> suspendingUnaryCall(
            crossinline block: (StreamObserver<R>)->Unit
    ): R = suspendCancellableCoroutine { cont: CancellableContinuation<R> ->
        block(SuspendingUnaryObserver(cont))
    }

    inline fun <ReqT, RespT> clientStreamingCall(
            context: CoroutineContext,
            crossinline block: (StreamObserver<RespT>)-> StreamObserver<ReqT>
    ): ClientStreamingCallChannel<ReqT, RespT> {
        val responseObserverChannel = InboundStreamChannel<RespT>(capacity = Channel.CONFLATED)
        val requestObserver = block(responseObserverChannel)
        val requestObserverChannel = requestObserver.toSendChannel(context)
        return ClientStreamingCallChannel(requestObserverChannel, responseObserverChannel)
    }

    inline fun <RespT> serverStreamingCall(crossinline block: (StreamObserver<RespT>)->Unit): ReceiveChannel<RespT> =
            InboundStreamChannel<RespT>().also{ block(it) }


    inline fun <ReqT, RespT> bidiCall(
            context: CoroutineContext,
            crossinline block: (StreamObserver<RespT>)-> StreamObserver<ReqT>
    ): ClientBidiCallChannel<ReqT, RespT> {
        val responseObserverChannel = InboundStreamChannel<RespT>()
        val requestObserver = block(responseObserverChannel)
        val requestObserverChannel = requestObserver.toSendChannel(context)
        return ClientBidiCallChannel(requestObserverChannel, responseObserverChannel)
    }


    fun <T> StreamObserver<T>.toSendChannel(context: CoroutineContext = DefaultDispatcher): SendChannel<T> =
            actor(context) {
                try{
                    channel.consumeEach { this@toSendChannel.onNext(it) }
                }catch (e:Exception){
                    this@toSendChannel.onError(e)
                    return@actor
                }
                this@toSendChannel.onCompleted()
            }
}

object ServerCalls {
    // TODO
}




