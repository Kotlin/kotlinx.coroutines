@SuppressWarnings("JavaModuleNaming")
module kotlinx.coroutines.rx3 {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires kotlinx.coroutines.reactive;
    requires kotlinx.atomicfu;
    requires io.reactivex.rxjava3;

    exports kotlinx.coroutines.rx3;
}
