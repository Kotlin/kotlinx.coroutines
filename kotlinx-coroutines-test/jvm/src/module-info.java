import kotlinx.coroutines.CoroutineExceptionHandler;
import kotlinx.coroutines.internal.MainDispatcherFactory;
import kotlinx.coroutines.test.internal.ExceptionCollectorAsService;
import kotlinx.coroutines.test.internal.TestMainDispatcherFactory;

module kotlinx.coroutines.test {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires kotlinx.atomicfu;

    exports kotlinx.coroutines.test;

    provides MainDispatcherFactory with TestMainDispatcherFactory;
    provides CoroutineExceptionHandler with ExceptionCollectorAsService;
}
