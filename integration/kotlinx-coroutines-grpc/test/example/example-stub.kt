package example

import io.grpc.CallOptions
import io.grpc.stub.StreamObserver
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import kotlinx.coroutines.experimental.grpc.ClientCalls
import kotlinx.coroutines.experimental.grpc.channels.ClientBidiCallChannel
import kotlinx.coroutines.experimental.grpc.channels.ClientStreamingCallChannel
import kotlinx.coroutines.experimental.grpc.stub.AbstractGrpcCoroutineStub


object CoroutineHeroServiceGrpc {

    fun newStub(channel: io.grpc.Channel): HeroServiceCoroutineStub {
        return HeroServiceCoroutineStub(channel)
    }

    class HeroServiceCoroutineStub(
            channel: io.grpc.Channel,
            callOptions: io.grpc.CallOptions = CallOptions.DEFAULT
    ) : AbstractGrpcCoroutineStub<HeroServiceCoroutineStub>(channel,callOptions) {

        override val delegateStub: HeroServiceGrpc.HeroServiceStub =
                HeroServiceGrpc.newStub(channel).build(channel,callOptions)

        override fun build(channel: io.grpc.Channel, callOptions: io.grpc.CallOptions): HeroServiceCoroutineStub {
            return HeroServiceCoroutineStub(channel, callOptions)
        }

        /**
         * <pre>
         * Unary
         * <pre>
        </pre></pre> */
        suspend fun getHeroByNameUnary(request: HeroProto.GetHeroByNameRequest): HeroProto.Hero =
                ClientCalls.suspendingUnaryCall { responseObserver: StreamObserver<HeroProto.Hero> ->
                    delegateStub.getHeroByNameUnary(request,responseObserver)
                }

        /**
         * <pre>
         * Client Streaming
         * <pre>
        </pre></pre> */
        fun getHerosByName(): ClientStreamingCallChannel<HeroProto.GetHeroByNameRequest, HeroProto.GetHerosByNameResponse> =
                ClientCalls.clientStreamingCall(context){ responseObserver: StreamObserver<HeroProto.GetHerosByNameResponse> ->
                    delegateStub.getHerosByName(responseObserver)
                }

        /**
         * <pre>
         * Server Streaming
         * <pre>
        </pre></pre> */
        fun getSidekicksByHero(request: HeroProto.Hero): ReceiveChannel<HeroProto.Sidekick> =
                ClientCalls.serverStreamingCall { responseObserver: StreamObserver<HeroProto.Sidekick> ->
                    delegateStub.getSidekicksByHero(request,responseObserver)
                }

        /**
         * <pre>
         * Bidi Streaming
         * <pre>
        </pre></pre> */
        fun getSidekicksByHeros(): ClientBidiCallChannel<HeroProto.Hero, HeroProto.Sidekick> =
                ClientCalls.bidiCall(context){ responseObserver: StreamObserver<HeroProto.Sidekick> ->
                    delegateStub.getSidekicksByHeros(responseObserver)
                }
    }

}
