package examples

import javafx.application.Application
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.Button
import javafx.scene.layout.FlowPane
import javafx.scene.layout.Pane
import javafx.scene.paint.Color
import javafx.scene.shape.Circle
import javafx.scene.shape.Rectangle
import javafx.stage.Stage
import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.javafx.JavaFx
import kotlinx.coroutines.experimental.launch
import java.text.SimpleDateFormat
import java.util.*

fun main(args: Array<String>) {
    Application.launch(FxTestApp::class.java, *args)
}

fun log(msg: String) = println("${SimpleDateFormat("YYYYMMdd-HHmmss.sss").format(Date())} [${Thread.currentThread().name}] $msg")

class FxTestApp : Application() {
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

    override fun start(primaryStage: Stage) {
        primaryStage.title = "Hello world!"
        primaryStage.scene = scene
        primaryStage.show()
    }

    val random = Random()
    val animations = arrayListOf<Job>()
    var animationIndex = 0

    private fun animation(node: Node, block: suspend CoroutineScope.() -> Unit) {
        root.children += node
        val job = launch(JavaFx, block)
        animations += job
        job.onCompletion { root.children -= node }
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
                JavaFx.awaitPulse()
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
                JavaFx.awaitPulse()
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
        animations.forEach { it.cancel() }
    }
}