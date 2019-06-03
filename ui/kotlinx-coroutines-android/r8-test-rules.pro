# Entry point for retaining MainDispatcherLoader which uses a ServiceLoader.
-keep class kotlinx.coroutines.Dispatchers {
  ** getMain();
}

# Entry point for retaining CoroutineExceptionHandlerImpl.handlers which uses a ServiceLoader.
-keep class kotlinx.coroutines.CoroutineExceptionHandlerKt {
  void handleCoroutineException(...);
}

# Ensure the custom, fast service loader implementation is removed. In the case of fast service
# loader encountering an exception it falls back to regular ServiceLoader in a way that cannot be
# optimized out by R8.
-assumevalues class kotlinx.coroutines.internal.MainDispatcherLoader {
  boolean FAST_SERVICE_LOADER_ENABLED return false;
}
-checkdiscard class kotlinx.coroutines.internal.FastServiceLoader

# We are cheating a bit by not having android.jar on R8's library classpath. Ignore those warnings.
-ignorewarnings
