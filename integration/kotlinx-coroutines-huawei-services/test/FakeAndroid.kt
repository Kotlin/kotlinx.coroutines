package android.os

import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.launch

class Handler(val looper: Looper) {
    fun post(r: Runnable): Boolean {
        GlobalScope.launch { r.run() }
        return true
    }
}

class Looper {
    companion object {
        @JvmStatic
        fun getMainLooper() = Looper()
    }
}
