-include r8-test-common.pro

-include ../resources/META-INF/com.android.tools/r8-from-1.6.0/coroutines.pro

# Validate that service-loader & debugger classes are discarded
-checkdiscard class kotlinx.coroutines.internal.FastServiceLoader
-checkdiscard class kotlinx.coroutines.DebugKt
-checkdiscard class kotlinx.coroutines.internal.StackTraceRecoveryKt
-checkdiscard class kotlinx.coroutines.debug.internal.DebugProbesKt

# Should not keep this class, but it is still there (R8 bug)
#-checkdiscard class kotlinx.coroutines.CoroutineId
