import kotlinx.coroutines.internal.MainDispatcherFactory;
import kotlinx.coroutines.test.internal.TestMainDispatcherFactory;

module kotlinx.coroutines.test {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;

    exports kotlinx.coroutines.test;

    provides MainDispatcherFactory with TestMainDispatcherFactory;
}
