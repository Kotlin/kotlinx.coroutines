package kotlinx.coroutines.scheduling

// Used for testing only, but is in src/... due to JVM implementation relying on internal constants from src.
internal expect val CONCURRENT_CORE_POOL_SIZE: Int
internal expect val CONCURRENT_MAX_POOL_SIZE: Int
