package android.os

import kotlinx.coroutines.experimental.CommonPool

class Handler(val looper: Looper) {
    fun post(r: Runnable): Boolean {
        CommonPool.executor.execute(r)
        return true
    }
}

class Looper {
    companion object {
        @JvmStatic
        fun getMainLooper() = Looper()
    }
}
