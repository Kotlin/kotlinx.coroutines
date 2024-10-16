module kotlinx.coroutines.debug {
    requires java.management;
    requires java.instrument;
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires static net.bytebuddy;
    requires static net.bytebuddy.agent;
    requires static org.junit.jupiter.api;
    requires static org.junit.platform.commons;

    exports kotlinx.coroutines.debug;
    exports kotlinx.coroutines.debug.junit4;
    exports kotlinx.coroutines.debug.junit5;
}
