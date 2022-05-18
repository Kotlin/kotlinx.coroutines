import kotlinx.coroutines.CoroutineExceptionHandler;
import kotlinx.coroutines.internal.MainDispatcherFactory;

module kotlinx.coroutines.core {
    requires transitive kotlin.stdlib;
    requires kotlinx.atomicfu;

    // these are used by kotlinx.coroutines.debug.AgentPremain
    requires static java.instrument; // contains java.lang.instrument.*
    requires static jdk.unsupported; // contains sun.misc.Signal

    exports kotlinx.coroutines;
    exports kotlinx.coroutines.channels;
    exports kotlinx.coroutines.debug;
    exports kotlinx.coroutines.debug.internal;
    exports kotlinx.coroutines.flow;
    exports kotlinx.coroutines.flow.internal;
    exports kotlinx.coroutines.future;
    exports kotlinx.coroutines.internal;
    exports kotlinx.coroutines.intrinsics;
    exports kotlinx.coroutines.scheduling;
    exports kotlinx.coroutines.selects;
    exports kotlinx.coroutines.stream;
    exports kotlinx.coroutines.sync;
    exports kotlinx.coroutines.time;

    uses CoroutineExceptionHandler;
    uses MainDispatcherFactory;
}
