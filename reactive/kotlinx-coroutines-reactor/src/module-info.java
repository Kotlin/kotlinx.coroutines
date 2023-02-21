import kotlinx.coroutines.reactive.ContextInjector;
import kotlinx.coroutines.reactor.ReactorContextInjector;

module kotlinx.coroutines.reactor {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires kotlinx.coroutines.reactive;
    requires org.reactivestreams;
    requires reactor.core;

    exports kotlinx.coroutines.reactor;

    provides ContextInjector with ReactorContextInjector;
}
