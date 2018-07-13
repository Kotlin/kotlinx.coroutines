/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide-ui.md by Knit tool. Do not edit.
package kotlinx.coroutines.javafx.guide.blocking01

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.javafx.JavaFx as Main
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

fun Node.onClick(action: suspend (MouseEvent) -> Unit) {
    val eventActor = actor<MouseEvent>(Dispatchers.Main, capacity = Channel.CONFLATED) {
        for (event in channel) action(event) // pass event to action
    }
    onMouseClicked = EventHandler { event ->
        eventActor.offer(event)
    }
}

fun fib(x: Int): Int =
    if (x <= 1) x else fib(x - 1) + fib(x - 2)

fun setup(hello: Text, fab: Circle) {
    var result = "none" // the last result
    // counting animation 
    GlobalScope.launch(Dispatchers.Main) {
        var counter = 0
        while (true) {
            hello.text = "${++counter}: $result"
            delay(100) // update the text every 100ms
        }
    }
    // compute the next fibonacci number of each click
    var x = 1
    fab.onClick {
        result = "fib($x) = ${fib(x)}"
        x++
    }
}
