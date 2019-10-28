-include r8-test-common.pro

# Ensure the custom, fast service loader implementation is removed. In the case of fast service
# loader encountering an exception it falls back to regular ServiceLoader in a way that cannot be
# optimized out by R8.
-include resources/META-INF/com.android.tools/r8-from-1.6.0/coroutines.pro
-checkdiscard class kotlinx.coroutines.internal.FastServiceLoader