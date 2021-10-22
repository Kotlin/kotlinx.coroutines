package android.os

import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.launch
import java.util.concurrent.*

class Handler(val looper: Looper) {
    fun post(r: Runnable): Boolean {
        try {
            GlobalScope.launch { r.run() }
        } catch (e: RejectedExecutionException) {
            // Execute leftover callbacks in place for tests
            r.run()
        }

        return true
    }
}

class Looper {
    companion object {
        @JvmStatic
        fun getMainLooper() = Looper()
    }
}
