/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swt

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.MainDispatcherFactory
import kotlinx.coroutines.swt.SwtDefault.delay
import org.eclipse.swt.widgets.Display
import kotlin.coroutines.CoroutineContext

/**
 * Dispatches execution onto SWT event dispatching thread of the **default** [Display] and provides native [delay] support.
 *
 * **NOTE:** Be aware that calling this method creates a default [Display] (making the thread that invokes this
 * method its user-interface thread) if it did not already exist.
 */
@Suppress("unused")
public val Dispatchers.SWT: MainCoroutineDispatcher
    get() = kotlinx.coroutines.swt.SwtDefault

/**
 * Dispatches execution onto SWT event dispatching thread of the given [Display] and provides native [delay] support.
 */
@Suppress("unused")
public fun Dispatchers.swt(display: Display): MainCoroutineDispatcher =
        SwtDispatcherImpl(display)

/**
 * Base dispatcher for SWT event dispatching thread.
 *
 * This class provides type-safety and a point for future extensions.
 */
internal abstract class SwtDispatcher(
        internal val display: Display,
        internal val name: String
) : MainCoroutineDispatcher(), Delay {

    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) = display.asyncExec(block)

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val action = Runnable {
            with(continuation) { resumeUndispatched(Unit) }
        }
        schedule(timeMillis, action)
        continuation.invokeOnCancellation { display.disposeExec(action) }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        schedule(timeMillis, block)
        return object : DisposableHandle {
            override fun dispose() {
                display.disposeExec(block)
            }
        }
    }

    private fun schedule(timeMillis: Long, action: Runnable) {
        display.timerExec(timeMillis.toInt(), action)
    }

    override fun toString() = "SWT-$name"
}

/**
 * Immediate dispatcher for SWT event dispatching for the given [Display].
 */
private class ImmediateSWTDispatcher(display: Display, name: String) : SwtDispatcher(display, name) {
    override val immediate: MainCoroutineDispatcher
        get() = this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean =
            Thread.currentThread() != display.thread

    override fun toString() = "${super.toString()} [immediate]"
}

/**
 * Dispatcher for SWT event dispatching for the given [Display].
 */
internal open class SwtDispatcherImpl(display: Display, name: String = display.toString()) : SwtDispatcher(display, name) {
    override val immediate: MainCoroutineDispatcher
        get() = ImmediateSWTDispatcher(display, name)
}

/**
 * [MainDispatcherFactory] that dispatches events for the **default** SWT [Display].
 */
internal class SWTDispatcherFactory : MainDispatcherFactory {
    override val loadPriority: Int
        get() = 2 // Swing has 0; JavaFx has 1

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher = SwtDefault
}

/**
 * Dispatches execution onto SWT event dispatching thread of the **default** [Display] and provides native [delay] support.
 */
internal object SwtDefault : SwtDispatcherImpl(Display.getDefault(), "Default")
