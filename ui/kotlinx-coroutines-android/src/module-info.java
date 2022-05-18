import kotlinx.coroutines.android.AndroidDispatcherFactory;
import kotlinx.coroutines.internal.MainDispatcherFactory;

module kotlinx.coroutines.android {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;

    exports kotlinx.coroutines.android;

    provides MainDispatcherFactory with AndroidDispatcherFactory;
}
