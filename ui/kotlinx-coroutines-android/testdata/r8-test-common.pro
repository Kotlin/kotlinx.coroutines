# Entry point for retaining MainDispatcherLoader which uses a ServiceLoader.
-keep class kotlinx.coroutines.Dispatchers {
  ** getMain();
}

# Entry point for retaining CoroutineExceptionHandlerImpl.handlers which uses a ServiceLoader.
-keep class kotlinx.coroutines.CoroutineExceptionHandlerKt {
  void handleCoroutineException(...);
}

# Entry point for the rest of coroutines machinery
-keep class kotlinx.coroutines.BuildersKt {
  ** runBlocking(...);
  ** launch(...);
}

# We are cheating a bit by not having android.jar on R8's library classpath. Ignore those warnings.
-ignorewarnings