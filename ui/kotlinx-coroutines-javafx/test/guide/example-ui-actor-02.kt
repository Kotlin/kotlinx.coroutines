/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-ui.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.javafx.guide.actor02

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.javafx.JavaFx as Main
import javafx.application.Application
import javafx.event.EventHandler
import javafx.geometry.*
import javafx.scene.*
import javafx.scene.input.MouseEvent
import javafx.scene.layout.StackPane
import javafx.scene.paint.Color
import javafx.scene.shape.Circle
import javafx.scene.text.Text
import javafx.stage.Stage

fun main(args: Array<String>) {
    Application.launch(ExampleApp::class.java, *args)
}

class ExampleApp : Application() {
    val hello = Text("Hello World!").apply {
        fill = Color.valueOf("#C0C0C0")
    }

    val fab = Circle(20.0, Color.valueOf("#FF4081"))

    val root = StackPane().apply {
        children += hello
        children += fab
        StackPane.setAlignment(hello, Pos.CENTER)
        StackPane.setAlignment(fab, Pos.BOTTOM_RIGHT)
        StackPane.setMargin(fab, Insets(15.0))
    }

    val scene = Scene(root, 240.0, 380.0).apply {
        fill = Color.valueOf("#303030")
    }

    override fun start(stage: Stage) {
        stage.title = "Example"
        stage.scene = scene
        stage.show()
        setup(hello, fab)
    }
}

fun setup(hello: Text, fab: Circle) {
    fab.onClick { // start coroutine when the circle is clicked
        for (i in 10 downTo 1) { // countdown from 10 to 1 
            hello.text = "Countdown $i ..." // update text
            delay(500) // wait half a second
        }
        hello.text = "Done!"
    }
}

fun Node.onClick(action: suspend (MouseEvent) -> Unit) {
    // launch one actor to handle all events on this node
    val eventActor = GlobalScope.actor<MouseEvent>(Dispatchers.Main) {
        for (event in channel) action(event) // pass event to action
    }
    // install a listener to offer events to this actor
    onMouseClicked = EventHandler { event ->
        eventActor.offer(event)
    }
}
