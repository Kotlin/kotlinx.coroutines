module kotlinx.coroutines.reactive {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires kotlinx.atomicfu;
    requires org.reactivestreams;

    exports kotlinx.coroutines.reactive;

    uses kotlinx.coroutines.reactive.ContextInjector;
}
