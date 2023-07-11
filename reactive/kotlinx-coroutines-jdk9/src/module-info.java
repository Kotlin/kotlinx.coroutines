@SuppressWarnings("JavaModuleNaming")
module kotlinx.coroutines.jdk9 {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires kotlinx.coroutines.reactive;
    requires org.reactivestreams;

    exports kotlinx.coroutines.jdk9;
}
