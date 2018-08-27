package kotlinx.coroutines.experimental.grpc.channels

import io.grpc.stub.StreamObserver
import kotlinx.coroutines.experimental.channels.Channel
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import kotlinx.coroutines.experimental.channels.SendChannel
import kotlin.coroutines.experimental.Continuation

// Client

data class ClientStreamingCallChannel<ReqT,RespT>(
        val requestChannel: SendChannel<ReqT>,
        private val responseChannel: ReceiveChannel<RespT>
) : SendChannel<ReqT> by requestChannel{

    suspend fun receive(): RespT = responseChannel.receive()
        .also{ responseChannel.cancel() }

    override fun close(cause: Throwable?): Boolean {
        responseChannel.cancel(cause)
        return requestChannel.close(cause)
    }

}

data class ClientBidiCallChannel<ReqT,RespT>(
        val requestChannel: SendChannel<ReqT>,
        val responseChannel: ReceiveChannel<RespT>
) : SendChannel<ReqT> by requestChannel,
    ReceiveChannel<RespT> by responseChannel



// Server

data class ServerStreamingCallChannel<ReqT,RespT>(
        val requestChannel: ReceiveChannel<ReqT>,
        private val responseChannel: SendChannel<RespT>
) : SendChannel<RespT> by responseChannel {

    suspend fun receive(): ReqT = requestChannel.receive()
            .also{ requestChannel.cancel() }

    override fun close(cause: Throwable?): Boolean {
        requestChannel.cancel(cause)
        return responseChannel.close(cause)
    }

}

data class ServerBidiCallChannel<ReqT,RespT>(
        val requestChannel: ReceiveChannel<ReqT>,
        val responseChannel: SendChannel<RespT>
) : SendChannel<RespT> by responseChannel,
    ReceiveChannel<ReqT> by requestChannel


class InboundStreamChannel<T>(
        capacity: Int = Channel.UNLIMITED,
        private val channel: Channel<T> = Channel(capacity)
) : StreamObserver<T>, ReceiveChannel<T> by channel {

    override fun onNext(value: T) {
        channel.offer(value)
    }

    override fun onError(t: Throwable?) {
        channel.close(t)
    }

    override fun onCompleted() {
        channel.close()
    }
}

class SuspendingUnaryObserver<RespT>(
        @Volatile @JvmField var cont: Continuation<RespT>?
) : StreamObserver<RespT> {

    override fun onNext(value: RespT) { cont?.resume(value) }
    override fun onError(t: Throwable) {
        cont?.resumeWithException(t)
        cont = null
    }
    override fun onCompleted() { cont = null }
}