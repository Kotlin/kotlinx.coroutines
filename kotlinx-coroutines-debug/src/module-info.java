module kotlinx.coroutines.debug {
    requires java.management;
    requires java.instrument;
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires net.bytebuddy;
    requires net.bytebuddy.agent;
    requires org.junit.jupiter.api;
    requires org.junit.platform.commons;

//    exports kotlinx.coroutines.debug; // already exported by kotlinx.coroutines.core
    exports kotlinx.coroutines.debug.junit4;
    exports kotlinx.coroutines.debug.junit5;
}
