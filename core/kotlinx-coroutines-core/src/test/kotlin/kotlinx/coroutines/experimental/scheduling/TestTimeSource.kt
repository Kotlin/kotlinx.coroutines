package kotlinx.coroutines.experimental.scheduling

internal class TestTimeSource(var time: Long) : TimeSource() {

    override fun nanoTime() = time

    fun step(delta: Long = WORK_STEALING_TIME_RESOLUTION) {
        time += delta
    }
}
