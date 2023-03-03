module kotlinx.coroutines.reactive {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires org.reactivestreams;

    exports kotlinx.coroutines.reactive;

    uses kotlinx.coroutines.reactive.ContextInjector;
}
