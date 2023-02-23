import kotlinx.coroutines.internal.MainDispatcherFactory;
import kotlinx.coroutines.javafx.JavaFxDispatcherFactory;

module kotlinx.coroutines.javafx {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires javafx.base;
    requires javafx.graphics;

    exports kotlinx.coroutines.javafx;

    provides MainDispatcherFactory with JavaFxDispatcherFactory;
}
