package example;

import static io.grpc.MethodDescriptor.generateFullMethodName;
import static io.grpc.stub.ClientCalls.asyncBidiStreamingCall;
import static io.grpc.stub.ClientCalls.asyncClientStreamingCall;
import static io.grpc.stub.ClientCalls.asyncServerStreamingCall;
import static io.grpc.stub.ClientCalls.asyncUnaryCall;
import static io.grpc.stub.ClientCalls.blockingServerStreamingCall;
import static io.grpc.stub.ClientCalls.blockingUnaryCall;
import static io.grpc.stub.ClientCalls.futureUnaryCall;
import static io.grpc.stub.ServerCalls.asyncBidiStreamingCall;
import static io.grpc.stub.ServerCalls.asyncClientStreamingCall;
import static io.grpc.stub.ServerCalls.asyncServerStreamingCall;
import static io.grpc.stub.ServerCalls.asyncUnaryCall;
import static io.grpc.stub.ServerCalls.asyncUnimplementedStreamingCall;
import static io.grpc.stub.ServerCalls.asyncUnimplementedUnaryCall;

/**
 */
@javax.annotation.Generated(
        value = "by gRPC proto compiler (version 1.14.0)",
        comments = "Source: kotlinx/coroutines/test/service.proto")
public final class HeroServiceGrpc {

  private HeroServiceGrpc() {}

  public static final String SERVICE_NAME = "kotlinx.coroutines.test.HeroService";

  // Static method descriptors that strictly reflect the proto.
  private static volatile io.grpc.MethodDescriptor<HeroProto.GetHeroByNameRequest,
          HeroProto.Hero> getGetHeroByNameUnaryMethod;

  @io.grpc.stub.annotations.RpcMethod(
          fullMethodName = SERVICE_NAME + '/' + "GetHeroByNameUnary",
          requestType = HeroProto.GetHeroByNameRequest.class,
          responseType = HeroProto.Hero.class,
          methodType = io.grpc.MethodDescriptor.MethodType.UNARY)
  public static io.grpc.MethodDescriptor<HeroProto.GetHeroByNameRequest,
          HeroProto.Hero> getGetHeroByNameUnaryMethod() {
    io.grpc.MethodDescriptor<HeroProto.GetHeroByNameRequest, HeroProto.Hero> getGetHeroByNameUnaryMethod;
    if ((getGetHeroByNameUnaryMethod = HeroServiceGrpc.getGetHeroByNameUnaryMethod) == null) {
      synchronized (HeroServiceGrpc.class) {
        if ((getGetHeroByNameUnaryMethod = HeroServiceGrpc.getGetHeroByNameUnaryMethod) == null) {
          HeroServiceGrpc.getGetHeroByNameUnaryMethod = getGetHeroByNameUnaryMethod =
                  io.grpc.MethodDescriptor.<HeroProto.GetHeroByNameRequest, HeroProto.Hero>newBuilder()
                          .setType(io.grpc.MethodDescriptor.MethodType.UNARY)
                          .setFullMethodName(generateFullMethodName(
                                  "kotlinx.coroutines.test.HeroService", "GetHeroByNameUnary"))
                          .setSampledToLocalTracing(true)
                          .setRequestMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.GetHeroByNameRequest.getDefaultInstance()))
                          .setResponseMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.Hero.getDefaultInstance()))
                          .setSchemaDescriptor(new HeroServiceMethodDescriptorSupplier("GetHeroByNameUnary"))
                          .build();
        }
      }
    }
    return getGetHeroByNameUnaryMethod;
  }

  private static volatile io.grpc.MethodDescriptor<HeroProto.GetHeroByNameRequest,
          HeroProto.GetHerosByNameResponse> getGetHerosByNameMethod;

  @io.grpc.stub.annotations.RpcMethod(
          fullMethodName = SERVICE_NAME + '/' + "GetHerosByName",
          requestType = HeroProto.GetHeroByNameRequest.class,
          responseType = HeroProto.GetHerosByNameResponse.class,
          methodType = io.grpc.MethodDescriptor.MethodType.CLIENT_STREAMING)
  public static io.grpc.MethodDescriptor<HeroProto.GetHeroByNameRequest,
          HeroProto.GetHerosByNameResponse> getGetHerosByNameMethod() {
    io.grpc.MethodDescriptor<HeroProto.GetHeroByNameRequest, HeroProto.GetHerosByNameResponse> getGetHerosByNameMethod;
    if ((getGetHerosByNameMethod = HeroServiceGrpc.getGetHerosByNameMethod) == null) {
      synchronized (HeroServiceGrpc.class) {
        if ((getGetHerosByNameMethod = HeroServiceGrpc.getGetHerosByNameMethod) == null) {
          HeroServiceGrpc.getGetHerosByNameMethod = getGetHerosByNameMethod =
                  io.grpc.MethodDescriptor.<HeroProto.GetHeroByNameRequest, HeroProto.GetHerosByNameResponse>newBuilder()
                          .setType(io.grpc.MethodDescriptor.MethodType.CLIENT_STREAMING)
                          .setFullMethodName(generateFullMethodName(
                                  "kotlinx.coroutines.test.HeroService", "GetHerosByName"))
                          .setSampledToLocalTracing(true)
                          .setRequestMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.GetHeroByNameRequest.getDefaultInstance()))
                          .setResponseMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.GetHerosByNameResponse.getDefaultInstance()))
                          .setSchemaDescriptor(new HeroServiceMethodDescriptorSupplier("GetHerosByName"))
                          .build();
        }
      }
    }
    return getGetHerosByNameMethod;
  }

  private static volatile io.grpc.MethodDescriptor<HeroProto.Hero,
          HeroProto.Sidekick> getGetSidekicksByHeroMethod;

  @io.grpc.stub.annotations.RpcMethod(
          fullMethodName = SERVICE_NAME + '/' + "GetSidekicksByHero",
          requestType = HeroProto.Hero.class,
          responseType = HeroProto.Sidekick.class,
          methodType = io.grpc.MethodDescriptor.MethodType.SERVER_STREAMING)
  public static io.grpc.MethodDescriptor<HeroProto.Hero,
          HeroProto.Sidekick> getGetSidekicksByHeroMethod() {
    io.grpc.MethodDescriptor<HeroProto.Hero, HeroProto.Sidekick> getGetSidekicksByHeroMethod;
    if ((getGetSidekicksByHeroMethod = HeroServiceGrpc.getGetSidekicksByHeroMethod) == null) {
      synchronized (HeroServiceGrpc.class) {
        if ((getGetSidekicksByHeroMethod = HeroServiceGrpc.getGetSidekicksByHeroMethod) == null) {
          HeroServiceGrpc.getGetSidekicksByHeroMethod = getGetSidekicksByHeroMethod =
                  io.grpc.MethodDescriptor.<HeroProto.Hero, HeroProto.Sidekick>newBuilder()
                          .setType(io.grpc.MethodDescriptor.MethodType.SERVER_STREAMING)
                          .setFullMethodName(generateFullMethodName(
                                  "kotlinx.coroutines.test.HeroService", "GetSidekicksByHero"))
                          .setSampledToLocalTracing(true)
                          .setRequestMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.Hero.getDefaultInstance()))
                          .setResponseMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.Sidekick.getDefaultInstance()))
                          .setSchemaDescriptor(new HeroServiceMethodDescriptorSupplier("GetSidekicksByHero"))
                          .build();
        }
      }
    }
    return getGetSidekicksByHeroMethod;
  }

  private static volatile io.grpc.MethodDescriptor<HeroProto.Hero,
          HeroProto.Sidekick> getGetSidekicksByHerosMethod;

  @io.grpc.stub.annotations.RpcMethod(
          fullMethodName = SERVICE_NAME + '/' + "GetSidekicksByHeros",
          requestType = HeroProto.Hero.class,
          responseType = HeroProto.Sidekick.class,
          methodType = io.grpc.MethodDescriptor.MethodType.BIDI_STREAMING)
  public static io.grpc.MethodDescriptor<HeroProto.Hero,
          HeroProto.Sidekick> getGetSidekicksByHerosMethod() {
    io.grpc.MethodDescriptor<HeroProto.Hero, HeroProto.Sidekick> getGetSidekicksByHerosMethod;
    if ((getGetSidekicksByHerosMethod = HeroServiceGrpc.getGetSidekicksByHerosMethod) == null) {
      synchronized (HeroServiceGrpc.class) {
        if ((getGetSidekicksByHerosMethod = HeroServiceGrpc.getGetSidekicksByHerosMethod) == null) {
          HeroServiceGrpc.getGetSidekicksByHerosMethod = getGetSidekicksByHerosMethod =
                  io.grpc.MethodDescriptor.<HeroProto.Hero, HeroProto.Sidekick>newBuilder()
                          .setType(io.grpc.MethodDescriptor.MethodType.BIDI_STREAMING)
                          .setFullMethodName(generateFullMethodName(
                                  "kotlinx.coroutines.test.HeroService", "GetSidekicksByHeros"))
                          .setSampledToLocalTracing(true)
                          .setRequestMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.Hero.getDefaultInstance()))
                          .setResponseMarshaller(io.grpc.protobuf.ProtoUtils.marshaller(
                                  HeroProto.Sidekick.getDefaultInstance()))
                          .setSchemaDescriptor(new HeroServiceMethodDescriptorSupplier("GetSidekicksByHeros"))
                          .build();
        }
      }
    }
    return getGetSidekicksByHerosMethod;
  }

  /**
   * Creates a new async stub that supports all call types for the service
   */
  public static HeroServiceStub newStub(io.grpc.Channel channel) {
    return new HeroServiceStub(channel);
  }

  /**
   * Creates a new blocking-style stub that supports unary and streaming output calls on the service
   */
  public static HeroServiceBlockingStub newBlockingStub(
          io.grpc.Channel channel) {
    return new HeroServiceBlockingStub(channel);
  }

  /**
   * Creates a new ListenableFuture-style stub that supports unary calls on the service
   */
  public static HeroServiceFutureStub newFutureStub(
          io.grpc.Channel channel) {
    return new HeroServiceFutureStub(channel);
  }

  /**
   */
  public static abstract class HeroServiceImplBase implements io.grpc.BindableService {

    /**
     * <pre>
     *Unary
     * </pre>
     */
    public void getHeroByNameUnary(HeroProto.GetHeroByNameRequest request,
                                   io.grpc.stub.StreamObserver<HeroProto.Hero> responseObserver) {
      asyncUnimplementedUnaryCall(getGetHeroByNameUnaryMethod(), responseObserver);
    }

    /**
     * <pre>
     *Client Streaming
     * </pre>
     */
    public io.grpc.stub.StreamObserver<HeroProto.GetHeroByNameRequest> getHerosByName(
            io.grpc.stub.StreamObserver<HeroProto.GetHerosByNameResponse> responseObserver) {
      return asyncUnimplementedStreamingCall(getGetHerosByNameMethod(), responseObserver);
    }

    /**
     * <pre>
     *Server Streaming
     * </pre>
     */
    public void getSidekicksByHero(HeroProto.Hero request,
                                   io.grpc.stub.StreamObserver<HeroProto.Sidekick> responseObserver) {
      asyncUnimplementedUnaryCall(getGetSidekicksByHeroMethod(), responseObserver);
    }

    /**
     * <pre>
     *Bidi Streaming
     * </pre>
     */
    public io.grpc.stub.StreamObserver<HeroProto.Hero> getSidekicksByHeros(
            io.grpc.stub.StreamObserver<HeroProto.Sidekick> responseObserver) {
      return asyncUnimplementedStreamingCall(getGetSidekicksByHerosMethod(), responseObserver);
    }

    @java.lang.Override public final io.grpc.ServerServiceDefinition bindService() {
      return io.grpc.ServerServiceDefinition.builder(getServiceDescriptor())
              .addMethod(
                      getGetHeroByNameUnaryMethod(),
                      asyncUnaryCall(
                              new MethodHandlers<
                                      HeroProto.GetHeroByNameRequest,
                                      HeroProto.Hero>(
                                      this, METHODID_GET_HERO_BY_NAME_UNARY)))
              .addMethod(
                      getGetHerosByNameMethod(),
                      asyncClientStreamingCall(
                              new MethodHandlers<
                                      HeroProto.GetHeroByNameRequest,
                                      HeroProto.GetHerosByNameResponse>(
                                      this, METHODID_GET_HEROS_BY_NAME)))
              .addMethod(
                      getGetSidekicksByHeroMethod(),
                      asyncServerStreamingCall(
                              new MethodHandlers<
                                      HeroProto.Hero,
                                      HeroProto.Sidekick>(
                                      this, METHODID_GET_SIDEKICKS_BY_HERO)))
              .addMethod(
                      getGetSidekicksByHerosMethod(),
                      asyncBidiStreamingCall(
                              new MethodHandlers<
                                      HeroProto.Hero,
                                      HeroProto.Sidekick>(
                                      this, METHODID_GET_SIDEKICKS_BY_HEROS)))
              .build();
    }
  }

  /**
   */
  public static final class HeroServiceStub extends io.grpc.stub.AbstractStub<HeroServiceStub> {
    private HeroServiceStub(io.grpc.Channel channel) {
      super(channel);
    }

    private HeroServiceStub(io.grpc.Channel channel,
                            io.grpc.CallOptions callOptions) {
      super(channel, callOptions);
    }

    @java.lang.Override
    protected HeroServiceStub build(io.grpc.Channel channel,
                                    io.grpc.CallOptions callOptions) {
      return new HeroServiceStub(channel, callOptions);
    }

    /**
     * <pre>
     *Unary
     * </pre>
     */
    public void getHeroByNameUnary(HeroProto.GetHeroByNameRequest request,
                                   io.grpc.stub.StreamObserver<HeroProto.Hero> responseObserver) {
      asyncUnaryCall(
              getChannel().newCall(getGetHeroByNameUnaryMethod(), getCallOptions()), request, responseObserver);
    }

    /**
     * <pre>
     *Client Streaming
     * </pre>
     */
    public io.grpc.stub.StreamObserver<HeroProto.GetHeroByNameRequest> getHerosByName(
            io.grpc.stub.StreamObserver<HeroProto.GetHerosByNameResponse> responseObserver) {
      return asyncClientStreamingCall(
              getChannel().newCall(getGetHerosByNameMethod(), getCallOptions()), responseObserver);
    }

    /**
     * <pre>
     *Server Streaming
     * </pre>
     */
    public void getSidekicksByHero(HeroProto.Hero request,
                                   io.grpc.stub.StreamObserver<HeroProto.Sidekick> responseObserver) {
      asyncServerStreamingCall(
              getChannel().newCall(getGetSidekicksByHeroMethod(), getCallOptions()), request, responseObserver);
    }

    /**
     * <pre>
     *Bidi Streaming
     * </pre>
     */
    public io.grpc.stub.StreamObserver<HeroProto.Hero> getSidekicksByHeros(
            io.grpc.stub.StreamObserver<HeroProto.Sidekick> responseObserver) {
      return asyncBidiStreamingCall(
              getChannel().newCall(getGetSidekicksByHerosMethod(), getCallOptions()), responseObserver);
    }
  }

  /**
   */
  public static final class HeroServiceBlockingStub extends io.grpc.stub.AbstractStub<HeroServiceBlockingStub> {
    private HeroServiceBlockingStub(io.grpc.Channel channel) {
      super(channel);
    }

    private HeroServiceBlockingStub(io.grpc.Channel channel,
                                    io.grpc.CallOptions callOptions) {
      super(channel, callOptions);
    }

    @java.lang.Override
    protected HeroServiceBlockingStub build(io.grpc.Channel channel,
                                            io.grpc.CallOptions callOptions) {
      return new HeroServiceBlockingStub(channel, callOptions);
    }

    /**
     * <pre>
     *Unary
     * </pre>
     */
    public HeroProto.Hero getHeroByNameUnary(HeroProto.GetHeroByNameRequest request) {
      return blockingUnaryCall(
              getChannel(), getGetHeroByNameUnaryMethod(), getCallOptions(), request);
    }

    /**
     * <pre>
     *Server Streaming
     * </pre>
     */
    public java.util.Iterator<HeroProto.Sidekick> getSidekicksByHero(
            HeroProto.Hero request) {
      return blockingServerStreamingCall(
              getChannel(), getGetSidekicksByHeroMethod(), getCallOptions(), request);
    }
  }

  /**
   */
  public static final class HeroServiceFutureStub extends io.grpc.stub.AbstractStub<HeroServiceFutureStub> {
    private HeroServiceFutureStub(io.grpc.Channel channel) {
      super(channel);
    }

    private HeroServiceFutureStub(io.grpc.Channel channel,
                                  io.grpc.CallOptions callOptions) {
      super(channel, callOptions);
    }

    @java.lang.Override
    protected HeroServiceFutureStub build(io.grpc.Channel channel,
                                          io.grpc.CallOptions callOptions) {
      return new HeroServiceFutureStub(channel, callOptions);
    }

    /**
     * <pre>
     *Unary
     * </pre>
     */
    public com.google.common.util.concurrent.ListenableFuture<HeroProto.Hero> getHeroByNameUnary(
            HeroProto.GetHeroByNameRequest request) {
      return futureUnaryCall(
              getChannel().newCall(getGetHeroByNameUnaryMethod(), getCallOptions()), request);
    }
  }

  private static final int METHODID_GET_HERO_BY_NAME_UNARY = 0;
  private static final int METHODID_GET_SIDEKICKS_BY_HERO = 1;
  private static final int METHODID_GET_HEROS_BY_NAME = 2;
  private static final int METHODID_GET_SIDEKICKS_BY_HEROS = 3;

  private static final class MethodHandlers<Req, Resp> implements
          io.grpc.stub.ServerCalls.UnaryMethod<Req, Resp>,
          io.grpc.stub.ServerCalls.ServerStreamingMethod<Req, Resp>,
          io.grpc.stub.ServerCalls.ClientStreamingMethod<Req, Resp>,
          io.grpc.stub.ServerCalls.BidiStreamingMethod<Req, Resp> {
    private final HeroServiceImplBase serviceImpl;
    private final int methodId;

    MethodHandlers(HeroServiceImplBase serviceImpl, int methodId) {
      this.serviceImpl = serviceImpl;
      this.methodId = methodId;
    }

    @java.lang.Override
    @java.lang.SuppressWarnings("unchecked")
    public void invoke(Req request, io.grpc.stub.StreamObserver<Resp> responseObserver) {
      switch (methodId) {
        case METHODID_GET_HERO_BY_NAME_UNARY:
          serviceImpl.getHeroByNameUnary((HeroProto.GetHeroByNameRequest) request,
                  (io.grpc.stub.StreamObserver<HeroProto.Hero>) responseObserver);
          break;
        case METHODID_GET_SIDEKICKS_BY_HERO:
          serviceImpl.getSidekicksByHero((HeroProto.Hero) request,
                  (io.grpc.stub.StreamObserver<HeroProto.Sidekick>) responseObserver);
          break;
        default:
          throw new AssertionError();
      }
    }

    @java.lang.Override
    @java.lang.SuppressWarnings("unchecked")
    public io.grpc.stub.StreamObserver<Req> invoke(
            io.grpc.stub.StreamObserver<Resp> responseObserver) {
      switch (methodId) {
        case METHODID_GET_HEROS_BY_NAME:
          return (io.grpc.stub.StreamObserver<Req>) serviceImpl.getHerosByName(
                  (io.grpc.stub.StreamObserver<HeroProto.GetHerosByNameResponse>) responseObserver);
        case METHODID_GET_SIDEKICKS_BY_HEROS:
          return (io.grpc.stub.StreamObserver<Req>) serviceImpl.getSidekicksByHeros(
                  (io.grpc.stub.StreamObserver<HeroProto.Sidekick>) responseObserver);
        default:
          throw new AssertionError();
      }
    }
  }

  private static abstract class HeroServiceBaseDescriptorSupplier
          implements io.grpc.protobuf.ProtoFileDescriptorSupplier, io.grpc.protobuf.ProtoServiceDescriptorSupplier {
    HeroServiceBaseDescriptorSupplier() {}

    @java.lang.Override
    public com.google.protobuf.Descriptors.FileDescriptor getFileDescriptor() {
      return HeroProto.getDescriptor();
    }

    @java.lang.Override
    public com.google.protobuf.Descriptors.ServiceDescriptor getServiceDescriptor() {
      return getFileDescriptor().findServiceByName("HeroService");
    }
  }

  private static final class HeroServiceFileDescriptorSupplier
          extends HeroServiceBaseDescriptorSupplier {
    HeroServiceFileDescriptorSupplier() {}
  }

  private static final class HeroServiceMethodDescriptorSupplier
          extends HeroServiceBaseDescriptorSupplier
          implements io.grpc.protobuf.ProtoMethodDescriptorSupplier {
    private final String methodName;

    HeroServiceMethodDescriptorSupplier(String methodName) {
      this.methodName = methodName;
    }

    @java.lang.Override
    public com.google.protobuf.Descriptors.MethodDescriptor getMethodDescriptor() {
      return getServiceDescriptor().findMethodByName(methodName);
    }
  }

  private static volatile io.grpc.ServiceDescriptor serviceDescriptor;

  public static io.grpc.ServiceDescriptor getServiceDescriptor() {
    io.grpc.ServiceDescriptor result = serviceDescriptor;
    if (result == null) {
      synchronized (HeroServiceGrpc.class) {
        result = serviceDescriptor;
        if (result == null) {
          serviceDescriptor = result = io.grpc.ServiceDescriptor.newBuilder(SERVICE_NAME)
                  .setSchemaDescriptor(new HeroServiceFileDescriptorSupplier())
                  .addMethod(getGetHeroByNameUnaryMethod())
                  .addMethod(getGetHerosByNameMethod())
                  .addMethod(getGetSidekicksByHeroMethod())
                  .addMethod(getGetSidekicksByHerosMethod())
                  .build();
        }
      }
    }
    return result;
  }
}
