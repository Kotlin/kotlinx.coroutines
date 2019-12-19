/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package examples

import kotlinx.coroutines.*
import kotlinx.coroutines.swt.swt
import org.eclipse.swt.SWT
import org.eclipse.swt.layout.GridLayout
import org.eclipse.swt.widgets.Display
import org.eclipse.swt.widgets.ProgressBar
import org.eclipse.swt.widgets.Shell
import org.eclipse.swt.widgets.Text
import java.text.SimpleDateFormat
import java.util.*

/**
 * Main entry point of the SWT application.
 */
fun main() {
    // Create and show GUI
    val display = Display.getDefault()
    val shell = Shell(display)
    val gui = Gui(display, shell)
    gui.open()

    // Execute long running background operation and close window when finished
    GlobalScope.launch(Dispatchers.Default) {
        expensiveComputation(gui)
        gui.close()
    }

    // Start a coroutines using [Dispatchers.Main] to update time.
    // This works since timeText widget is part of the default display.
    GlobalScope.launch(Dispatchers.Main) {
        while (true) {
            gui.timeText.text = SimpleDateFormat("HH:mm:ss.SSS").format(Date())
            delay(250)
        }
    }

    // Dispatch events until SWT window is closed
    while (!shell.isDisposed) {
        if (!display.readAndDispatch()) {
            display.sleep()
        }
    }
    display.dispose()
}

/**
 * Execute long running operation and show progress in [gui] window.
 *
 * @param gui The [Gui] that will get updated.
 */
private fun expensiveComputation(gui: Gui) {
    for (i in 0..10) {
        val percent = i * 10
        gui.updateProgress(percent)
        Thread.sleep(1_000)
    }
}

/**
 * Allow to make changes to the GUI window.
 *
 * All updates are executed within SWT event dispatch thread.
 */
class Gui(
        private val display: Display,
        private val shell: Shell
) : CoroutineScope {

    override val coroutineContext = Dispatchers.swt(display)

    private val progressBar = ProgressBar(shell, SWT.SMOOTH).apply {
        minimum = 0
        maximum = 100
    }

    private val progressText = Text(shell, SWT.SINGLE).apply {
        editable = false
    }

    val timeText = Text(shell, SWT.SINGLE).apply {
        editable = false
    }

    init {
        shell.apply {
            text = "Async UI example"
            layout = GridLayout(2, true).apply {
                marginWidth = 0
                marginHeight = 0
            }
        }
    }

    /** Open GUI window.*/
    fun open() = launch {
        // Called within SWT event dispatch thread
        shell.open()
    }

    /** Close GUI window.*/
    fun close() = launch {
        // Called within SWT event dispatch thread
        shell.close()
    }

    /** Update progress information.*/
    fun updateProgress(percent: Int) = launch {
        // textArea and progressBar are updated within SWT event dispatch thread
        progressText.text = "$percent %"
        progressBar.selection = percent
        shell.layout(true, true)
    }
}
