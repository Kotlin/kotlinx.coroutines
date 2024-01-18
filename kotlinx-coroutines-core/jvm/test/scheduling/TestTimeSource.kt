package kotlinx.coroutines.scheduling


internal class TestTimeSource(var time: Long) : SchedulerTimeSource() {

    override fun nanoTime() = time

    fun step(delta: Long = WORK_STEALING_TIME_RESOLUTION_NS) {
        time += delta
    }
}
