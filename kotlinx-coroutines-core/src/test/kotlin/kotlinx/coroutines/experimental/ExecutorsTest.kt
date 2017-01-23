package kotlinx.coroutines.experimental

import org.junit.After
import org.junit.Before
import org.junit.Test
import java.util.concurrent.Executors

class ExecutorsTest {
    fun threadNames(): Set<String> {
        val arrayOfThreads = Array<Thread?>(Thread.activeCount()) { null }
        val n = Thread.enumerate(arrayOfThreads)
        val names = hashSetOf<String>()
        for (i in 0 until n)
            names.add(arrayOfThreads[i]!!.name)
        return names
    }

    lateinit var threadNamesBefore: Set<String>

    @Before
    fun before() {
        threadNamesBefore = threadNames()
    }

    @After
    fun after() {
        // give threads some time to shutdown
        val waitTill = System.currentTimeMillis() + 1000L
        var diff: Set<String>
        do {
            val threadNamesAfter = threadNames()
            diff = threadNamesAfter - threadNamesBefore
            if (diff.isEmpty()) break
        } while (System.currentTimeMillis() <= waitTill)
        diff.forEach { println("Lost thread '$it'") }
        check(diff.isEmpty()) { "Lost ${diff.size} threads"}
    }

    fun checkThreadName(prefix: String) {
        val name = Thread.currentThread().name
        check(name.startsWith(prefix)) { "Expected thread name to start with '$prefix', found: '$name'" }
    }

    @Test
    fun testSingleThread() {
        val context = newSingleThreadContext("TestThread")
        runBlocking(context) {
            checkThreadName("TestThread")
        }
        context[Job]!!.cancel()
    }

    @Test
    fun testFixedThreadPool() {
        val context = newFixedThreadPoolContext(2, "TestPool")
        runBlocking(context) {
            checkThreadName("TestPool")
        }
        context[Job]!!.cancel()
    }

    @Test
    fun testToExecutor() {
        val executor = Executors.newSingleThreadExecutor { r -> Thread(r, "TestExecutor") }
        runBlocking(executor.toCoroutineDispatcher()) {
            checkThreadName("TestExecutor")
        }
        executor.shutdown()
    }

    @Test
    fun testTwoThreads() {
        val ctx1 = newSingleThreadContext("Ctx1")
        val ctx2 = newSingleThreadContext("Ctx2")
        runBlocking(ctx1) {
            checkThreadName("Ctx1")
            run(ctx2) {
                checkThreadName("Ctx2")
            }
            checkThreadName("Ctx1")
        }
        ctx1[Job]!!.cancel()
        ctx2[Job]!!.cancel()
    }
}