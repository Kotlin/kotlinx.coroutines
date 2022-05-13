/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import android.os.*
import androidx.annotation.*
import kotlinx.coroutines.*
import java.lang.reflect.*
import kotlin.coroutines.*

@Keep
internal class AndroidExceptionPreHandler :
    AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler
{
    @Volatile
    private var _preHandler: Any? = this // uninitialized marker

    // Reflectively lookup pre-handler.
    private fun preHandler(): Method? {
        val current = _preHandler
        if (current !== this) return current as Method?
        val declared = try {
            Thread::class.java.getDeclaredMethod("getUncaughtExceptionPreHandler").takeIf {
                Modifier.isPublic(it.modifiers) && Modifier.isStatic(it.modifiers)
            }
        } catch (e: Throwable) {
            null /* not found */
        }
        _preHandler = declared
        return declared
    }

    override fun handleException(context: CoroutineContext, exception: Throwable) {
        /*
         * Android Oreo introduced private API for a global pre-handler for uncaught exceptions, to ensure that the
         * exceptions are logged even if the default uncaught exception handler is replaced by the app. The pre-handler
         * is invoked from the Thread's private dispatchUncaughtException() method, so our manual invocation of the
         * Thread's uncaught exception handler bypasses the pre-handler in Android Oreo, and uncaught coroutine
         * exceptions are not logged. This issue was addressed in Android Pie, which added a check in the default
         * uncaught exception handler to invoke the pre-handler if it was not invoked already (see
         * https://android-review.googlesource.com/c/platform/frameworks/base/+/654578/). So the issue is present only
         * in Android Oreo.
         *
         * We're fixing this by manually invoking the pre-handler using reflection, if running on an Android Oreo SDK
         * version (26 and 27).
         */
        if (Build.VERSION.SDK_INT in 26..27) {
            (preHandler()?.invoke(null) as? Thread.UncaughtExceptionHandler)
                ?.uncaughtException(Thread.currentThread(), exception)
        }
    }
}
