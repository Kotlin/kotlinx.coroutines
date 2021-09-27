/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.html.*
import kotlinx.html.div
import kotlinx.html.dom.*
import kotlinx.html.js.onClickFunction
import org.w3c.dom.*
import kotlinx.browser.*
import kotlin.coroutines.*
import kotlin.math.*
import kotlin.random.Random

external fun require(resource: String)

fun main() {
    require("style.css")
    println("Starting example application...")
    document.addEventListener("DOMContentLoaded", {
        Application().start()
    })
}

val Double.px get() = "${this}px"

private fun HTMLElement.setSize(w: Double, h: Double) {
    with(style) {
        width = w.px
        height = h.px
    }
}

private fun HTMLElement.setPosition(x: Double, y: Double) {
    with(style) {
        left = x.px
        top = y.px
    }
}

class Application : CoroutineScope {
    private val body get() = document.body!!
    private val scene get() = document.getElementById("scene") as HTMLElement
    private val sw = 800.0
    private val sh = 600.0
    private var animationIndex = 0
    private var job = Job()
    override val coroutineContext: CoroutineContext
        get() = job

    fun start() {
        body.append.div("content") {
            h1 {
                +"Kotlin Coroutines JS Example"
            }
            div {
                button {
                    +"Rect"
                    onClickFunction = { onRect() }
                }
                button {
                    +"Circle"
                    onClickFunction = { onCircle() }
                }
                button {
                    +"Clear"
                    onClickFunction = { onClear() }
                }
            }
            div {
                id = "scene"
            }
        }
        scene.setSize(sw, sh)
    }

    private fun animation(cls: String, size: Double, block: suspend CoroutineScope.(HTMLElement) -> Unit) {
        val elem = scene.append.div(cls)
        elem.setSize(size, size)
        val job = launch {
            block(elem)
        }

        job.invokeOnCompletion { scene.removeChild(elem) }
    }

    private fun onRect() {
        val index = ++animationIndex
        val speed = 0.3
        val rs = 20.0
        val turnAfter = 5000.0 // seconds
        val maxX = sw - rs
        val maxY = sh - rs
        animation("rect", rs) { rect ->
            println("Started new 'rect' coroutine #$index")
            val timer = AnimationTimer()
            var turnTime = timer.time + turnAfter
            val turnTimePhase = turnTime - floor(turnTime / turnAfter) * turnAfter
            var vx = speed
            var vy = speed
            var x = 0.0
            var y = 0.0
            while (true) {
                val dt = timer.await()
                x += vx * dt
                y += vy * dt
                if (x > maxX) {
                    x = 2 * maxX - x
                    vx = -vx
                }
                if (x < 0) {
                    x = -x
                    vx = -vx
                }
                if (y > maxY) {
                    y = 2 * maxY - y
                    vy = -vy
                }
                if (y < 0) {
                    y = -y
                    vy = -vy
                }
                rect.setPosition(x, y)
                if (timer.time >= turnTime) {
                    timer.delay(1000) // pause a bit
                    // flip direction
                    val t = vx
                    if (Random.nextDouble() > 0.5) {
                        vx = vy
                        vy = -t
                    } else {
                        vx = -vy
                        vy = t
                    }
                    // reset time, but keep turning time phase
                    turnTime = ceil(timer.reset() / turnAfter) * turnAfter + turnTimePhase
                    println("Delayed #$index for a while at ${timer.time}, resumed and turned")
                }
            }
        }
    }

    private fun onCircle() {
        val index = ++animationIndex
        val acceleration = 5e-4
        val initialRange = 0.7
        val maxSpeed = 0.4
        val initialSpeed = 0.1
        val radius = 20.0
        animation("circle", radius) { circle ->
            println("Started new 'circle' coroutine #$index")
            val timer = AnimationTimer()
            val initialAngle = Random.nextDouble() * 2 * PI
            var vx = sin(initialAngle) * initialSpeed
            var vy = cos(initialAngle) * initialSpeed
            var x = (Random.nextDouble() * initialRange + (1 - initialRange) / 2) * sw
            var y = (Random.nextDouble() * initialRange + (1 - initialRange) / 2) * sh
            while (true) {
                val dt = timer.await()
                val dx = sw / 2 - x
                val dy = sh / 2 - y
                val dn = sqrt(dx * dx + dy * dy)
                vx += dx / dn * acceleration * dt
                vy += dy / dn * acceleration * dt
                val vn = sqrt(vx * vx + vy * vy)
                val trim = vn.coerceAtMost(maxSpeed)
                vx = vx / vn * trim
                vy = vy / vn * trim
                x += vx * dt
                y += vy * dt
                circle.setPosition(x, y)
            }
        }

    }

    private fun onClear() {
        job.cancel()
        job = Job()
    }
}

class AnimationTimer {
    var time = window.performance.now()

    suspend fun await(): Double {
        val newTime = window.awaitAnimationFrame()
        val dt = newTime - time
        time = newTime
        return dt.coerceAtMost(200.0) // at most 200ms
    }

    fun reset(): Double {
        time = window.performance.now()
        return time
    }

    suspend fun delay(i: Int) {
        var dt = 0.0
        while (dt < i) {
            dt += await()
        }
    }
}
