package org.jetbrains.kotlinx.animation

import android.arch.lifecycle.LifecycleOwner
import android.arch.lifecycle.MutableLiveData
import android.arch.lifecycle.Observer
import android.arch.lifecycle.ViewModel
import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.RectF
import android.util.AttributeSet
import android.view.View
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.android.UI
import kotlinx.coroutines.experimental.launch
import java.util.*

sealed class AnimatedShape {
    var x = 0.5f // 0 .. 1
    var y = 0.5f // 0 .. 1
    var color = Color.BLACK
    var r = 0.05f
}

class AnimatedCircle : AnimatedShape()
class AnimatedSquare : AnimatedShape()

private val NO_SHAPES = emptySet<AnimatedShape>()

class AnimationView(
        context: Context, attributeSet: AttributeSet
) : View(context, attributeSet), Observer<Set<AnimatedShape>> {
    private var shapes = NO_SHAPES
    private val paint = Paint()
    private val rect = RectF()

    override fun onChanged(shapes: Set<AnimatedShape>?) {
        this.shapes = shapes ?: NO_SHAPES
        invalidate()
    }

    override fun onDraw(canvas: Canvas) {
        val scale = minOf(width, height) / 2.0f
        shapes.forEach { shape ->
            val x = (shape.x - 0.5f) * scale + width / 2
            val y = (shape.y - 0.5f) * scale + height / 2
            val r = shape.r * scale
            rect.set(x - r, y - r, x + r, y + r)
            paint.color = shape.color
            when (shape) {
                is AnimatedCircle -> canvas.drawArc(rect, 0.0f, 360.0f, true, paint)
                is AnimatedSquare -> canvas.drawRect(rect, paint)
            }
        }
    }
}

private val rnd = Random()

class AnimationModel : ViewModel() {
    private val shapes = MutableLiveData<Set<AnimatedShape>>()
    private val jobs = arrayListOf<Job>()

    fun observe(owner: LifecycleOwner, observer: Observer<Set<AnimatedShape>>) =
        shapes.observe(owner, observer)

    fun update(shape: AnimatedShape) {
        val old = shapes.value ?: NO_SHAPES
        shapes.value = if (shape in old) old else old + shape
    }

    fun addAnimation() {
        jobs += launch(UI) {
            animateShape(if (rnd.nextBoolean()) AnimatedCircle() else AnimatedSquare())
        }
    }

    fun clearAnimations() {
        jobs.forEach { it.cancel() }
        shapes.value = NO_SHAPES
    }
}

private fun norm(x: Float, y: Float) = Math.hypot(x.toDouble(), y.toDouble()).toFloat()

private const val ACC = 1e-18f
private const val MAX_SPEED = 2e-9f // in screen_fraction/nanos
private const val INIT_POS = 0.8f

private fun Random.nextColor() = Color.rgb(nextInt(256), nextInt(256), nextInt(256))
private fun Random.nextPos() = nextFloat() * INIT_POS + (1 - INIT_POS) / 2
private fun Random.nextSpeed() = nextFloat() * MAX_SPEED - MAX_SPEED / 2

suspend fun AnimationModel.animateShape(shape: AnimatedShape) {
    shape.x = rnd.nextPos()
    shape.y = rnd.nextPos()
    shape.color = rnd.nextColor()
    var sx = rnd.nextSpeed()
    var sy = rnd.nextSpeed()
    var time = System.nanoTime() // nanos
    var checkTime = time
    while (true) {
        val dt = time.let { old -> UI.awaitFrame().also { time = it } - old }
        if (dt > 0.5e9) continue // don't animate through over a half second lapses
        val dx = shape.x - 0.5f
        val dy = shape.y - 0.5f
        val dn = norm(dx, dy)
        sx -= dx / dn * ACC * dt
        sy -= dy / dn * ACC * dt
        val sn = norm(sx, sy)
        val trim = sn.coerceAtMost(MAX_SPEED)
        sx = sx / sn * trim
        sy = sy / sn * trim
        shape.x += sx * dt
        shape.y += sy * dt
        update(shape)
        // check once a second
        if (time > checkTime + 1e9) {
            checkTime = time
            when (rnd.nextInt(20)) { // roll d20
                0 -> {
                    animateColor(shape) // wait a second & animate color
                    time = UI.awaitFrame() // and sync with next frame
                }
                1 -> { // random speed change
                    sx = rnd.nextSpeed()
                    sy = rnd.nextSpeed()
                }
            }
        }
    }
}

suspend fun AnimationModel.animateColor(shape: AnimatedShape) {
    val duration = 1e9f
    val startTime = System.nanoTime()
    val aColor = shape.color
    val bColor = rnd.nextColor()
    while (true) {
        val time = UI.awaitFrame()
        val b = (time - startTime) / duration
        if (b >= 1.0f) break
        val a = 1 - b
        shape.color = Color.rgb(
            (Color.red(bColor) * b + Color.red(aColor) * a).toInt(),
            (Color.green(bColor) * b + Color.green(aColor) * a).toInt(),
            (Color.blue(bColor) * b + Color.blue(aColor) * a).toInt()
        )
        update(shape)
    }
    shape.color = bColor
    update(shape)
}
