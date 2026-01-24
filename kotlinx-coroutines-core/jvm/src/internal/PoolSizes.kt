package kotlinx.coroutines.internal

import kotlinx.coroutines.scheduling.CORE_POOL_SIZE
import kotlinx.coroutines.scheduling.MAX_POOL_SIZE

internal actual val CONCURRENT_CORE_POOL_SIZE: Int = CORE_POOL_SIZE
internal actual val CONCURRENT_MAX_POOL_SIZE: Int = MAX_POOL_SIZE
