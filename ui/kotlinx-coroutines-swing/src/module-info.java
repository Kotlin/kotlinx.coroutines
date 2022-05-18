import kotlinx.coroutines.internal.MainDispatcherFactory;
import kotlinx.coroutines.swing.SwingDispatcherFactory;

module kotlinx.coroutines.swing {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires java.desktop;

    exports kotlinx.coroutines.swing;

    provides MainDispatcherFactory with SwingDispatcherFactory;
}
