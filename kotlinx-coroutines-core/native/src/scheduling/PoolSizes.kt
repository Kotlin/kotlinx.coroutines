package kotlinx.coroutines.scheduling

internal actual val CONCURRENT_CORE_POOL_SIZE: Int = Platform.getAvailableProcessors().coerceAtLeast(2)
internal actual val CONCURRENT_MAX_POOL_SIZE: Int = 2048
