/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

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
