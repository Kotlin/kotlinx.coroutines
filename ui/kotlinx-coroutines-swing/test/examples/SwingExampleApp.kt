/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package examples

import kotlinx.coroutines.*
import kotlinx.coroutines.future.*
import kotlinx.coroutines.swing.*
import java.awt.*
import java.util.concurrent.*
import javax.swing.*

private fun createAndShowGUI() {
    val frame = JFrame("Async UI example")
    frame.defaultCloseOperation = JFrame.EXIT_ON_CLOSE

    val jProgressBar = JProgressBar(0, 100).apply {
        value = 0
        isStringPainted = true
    }

    val jTextArea = JTextArea(11, 10)
    jTextArea.margin = Insets(5, 5, 5, 5)
    jTextArea.isEditable = false

    val panel = JPanel()

    panel.add(jProgressBar)
    panel.add(jTextArea)

    frame.contentPane.add(panel)
    frame.pack()
    frame.isVisible = true

    GlobalScope.launch(Dispatchers.Swing) {
        for (i in 1..10) {
            // 'append' method and consequent 'jProgressBar.setValue' are called
            // within Swing event dispatch thread
            jTextArea.append(
                    startLongAsyncOperation(i).await()
            )
            jProgressBar.value = i * 10
        }
    }
}

private fun startLongAsyncOperation(v: Int) =
        CompletableFuture.supplyAsync {
            Thread.sleep(1000)
            "Message: $v\n"
        }

fun main(args: Array<String>) {
    SwingUtilities.invokeLater(::createAndShowGUI)
}
