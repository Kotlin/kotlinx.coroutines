/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import android.os.*
import android.support.annotation.*
import kotlinx.coroutines.*
import java.lang.reflect.*
import kotlin.coroutines.*

private val getter by lazy {
     try {
         Thread::class.java.getDeclaredMethod("getUncaughtExceptionPreHandler").takeIf {
             Modifier.isPublic(it.modifiers) && Modifier.isStatic(it.modifiers)
         }
     } catch (e: Throwable) {
         null /* not found */
     }
 }

@Keep
internal class AndroidExceptionPreHandler :
    AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler
{
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        /*
         * If we are on old SDK, then use Android's `Thread.getUncaughtExceptionPreHandler()` that ensures that
         * an exception is logged before crashing the application.
         *
         * Since Android Pie default uncaught exception handler always ensures that exception is logged without interfering with
         * pre-handler, so reflection hack is no longer needed.
         *
         * See https://android-review.googlesource.com/c/platform/frameworks/base/+/654578/
         */
        val thread = Thread.currentThread()
        if (Build.VERSION.SDK_INT >= 28) {
            thread.uncaughtExceptionHandler.uncaughtException(thread, exception)
        } else {
            (getter?.invoke(null) as? Thread.UncaughtExceptionHandler)
                ?.uncaughtException(thread, exception)
        }
    }
}