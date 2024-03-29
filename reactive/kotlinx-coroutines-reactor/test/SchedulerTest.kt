package kotlinx.coroutines.reactor

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.Before
import org.junit.Test
import reactor.core.scheduler.Schedulers
import kotlin.test.*

class SchedulerTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("single-")
    }

    @Test
    fun testSingleScheduler(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        withContext(Schedulers.single().asCoroutineDispatcher()) {
            val t1 = Thread.currentThread()
            assertNotSame(t1, mainThread)
            expect(2)
            delay(100)
            val t2 = Thread.currentThread()
            assertNotSame(t2, mainThread)
            expect(3)
        }
        finish(4)
    }
}