/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package examples

import javafx.application.*
import javafx.scene.*
import javafx.scene.control.*
import javafx.scene.layout.*
import javafx.scene.paint.*
import javafx.scene.shape.*
import javafx.stage.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.javafx.*
import java.text.*
import java.util.*
import kotlin.coroutines.experimental.*

fun main(args: Array<String>) {
    Application.launch(FxTestApp::class.java, *args)
}

fun log(msg: String) = println("${SimpleDateFormat("yyyyMMdd-HHmmss.sss").format(Date())} [${Thread.currentThread().name}] $msg")

class FxTestApp : Application(), CoroutineScope {
    val buttons = FlowPane().apply {
        children += Button("Rect").apply {
            setOnAction { doRect() }
        }
        children += Button("Circle").apply {
            setOnAction { doCircle() }
        }
        children += Button("Clear").apply {
            setOnAction { doClear() }
        }
    }

    val root = Pane().apply {
        children += buttons
    }

    val scene = Scene(root, 600.0, 400.0)

    override fun start(stage: Stage) {
        stage.title = "Hello world!"
        stage.scene = scene
        stage.show()
    }

    val random = Random()
    var animationIndex = 0
    var job = Job()
    override val coroutineContext: CoroutineContext
        get() = Dispatchers.JavaFx + job

    private fun animation(node: Node, block: suspend CoroutineScope.() -> Unit) {
        root.children += node
        launch(onCompletion = { root.children -= node }, block = block)
    }

    fun doRect() {
        val node = Rectangle(20.0, 20.0).apply {
            fill = Color.RED
        }
        val index = ++animationIndex
        val speed = 5.0
        animation(node) {
            log("Started new 'rect' coroutine #$index")
            var vx = speed
            var vy = speed
            var counter = 0
            while (true) {
                awaitPulse()
                node.x += vx
                node.y += vy
                val xRange = 0.0 .. scene.width - node.width
                val yRange = 0.0 .. scene.height - node.height
                if (node.x !in xRange ) {
                    node.x = node.x.coerceIn(xRange)
                    vx = -vx
                }
                if (node.y !in yRange) {
                    node.y = node.y.coerceIn(yRange)
                    vy = -vy
                }
                if (counter++ > 100) {
                    counter = 0
                    delay(1000) // pause a bit
                    log("Delayed #$index for a while, resume and turn")
                    val t = vx
                    vx = vy
                    vy = -t
                }
            }
        }
    }

    fun doCircle() {
        val node = Circle(20.0).apply {
            fill = Color.BLUE
        }
        val index = ++animationIndex
        val acceleration = 0.1
        val maxSpeed = 5.0
        animation(node) {
            log("Started new 'circle' coroutine #$index")
            var sx = random.nextDouble() * maxSpeed
            var sy = random.nextDouble() * maxSpeed
            while (true) {
                awaitPulse()
                val dx = root.width / 2 - node.translateX
                val dy = root.height / 2 - node.translateY
                val dn = Math.sqrt(dx * dx + dy * dy)
                sx += dx / dn * acceleration
                sy += dy / dn * acceleration
                val sn = Math.sqrt(sx * sx + sy * sy)
                val trim = sn.coerceAtMost(maxSpeed)
                sx = sx / sn * trim
                sy = sy / sn * trim
                node.translateX += sx
                node.translateY += sy
            }
        }
    }

    fun doClear() {
        job.cancel()
        job = Job()
    }
}