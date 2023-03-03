@SuppressWarnings("JavaModuleNaming")
module kotlinx.coroutines.rx2 {
    requires kotlin.stdlib;
    requires kotlinx.coroutines.core;
    requires kotlinx.coroutines.reactive;
    requires io.reactivex.rxjava2;

    exports kotlinx.coroutines.rx2;
}
