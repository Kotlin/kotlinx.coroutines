/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swt

import org.eclipse.swt.widgets.Display
import org.eclipse.swt.widgets.Shell
import java.util.concurrent.CompletableFuture
import kotlin.concurrent.thread

/**
 * Dispatcher thread for the SWT default [Display].
 *
 * Creates [Display.getDefault] in a new thread.
 * The new thread handles all dispatched events for the default [Display].
 */
class SWTDefaultDisplayDispatchThread {

    /** The name of the thread. */
    val name = "SWTDefaultDisplayDispatchThread"

    private var thread: Thread

    private val shell: Shell

    /** Get or create default [Display] and dispatcher. */
    val display: Display
        get() = shell.display

    init {
        // Start new thread and let it initialize Display and Shell
        val future = CompletableFuture<Shell>()
        thread = thread(name = name) {
            val display = Display.getDefault()
            val shell = Shell(display)
            future.complete(shell)

            // Start dispatch loop
            while (!shell.isDisposed) {
                if (!display.readAndDispatch()) {
                    display.sleep()
                }
            }
            display.dispose()
        }

        // Wait until Shell is ready
        shell = future.get()
    }

    /** Dispose the display and stop the event dispatcher thread. */
    fun dispose() {
        if (!display.isDisposed) {
            display.syncExec {
                shell.close()
            }

            thread.join()
        }
    }
}
