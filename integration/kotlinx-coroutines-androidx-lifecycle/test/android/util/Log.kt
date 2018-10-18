package android.util

import androidx.lifecycle.LifecycleRegistry

@Suppress("unused")
class Log {
    companion object {
        /**
         * Mocks Android Log method called in [LifecycleRegistry.sync].
         */
        @JvmStatic
        fun w(tag: String, message: String): Int = 0
    }
}
