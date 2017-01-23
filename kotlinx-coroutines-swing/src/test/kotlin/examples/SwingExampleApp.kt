package examples

import kotlinx.coroutines.experimental.future.await
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.swing.Swing
import java.awt.Insets
import java.util.concurrent.CompletableFuture
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

    launch(Swing) {
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
