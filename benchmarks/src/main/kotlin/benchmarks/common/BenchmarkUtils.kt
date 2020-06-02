/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.common

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.scheduling.*
import java.nio.file.*
import java.util.concurrent.*

/**
 * Performs [work] uncontended loop cycles on average (geometrically distributed)
 * in order to simulates additional work in benchmarks.
 */
public fun doGeomDistrWork(work: Int) {
    // We also checked on MacBook pro 13" (2017) that the resulting work times are
    // distributed geometrically, see https://github.com/Kotlin/kotlinx.coroutines/pull/1464#discussion_r355705325
    val p = 1.0 / work
    val r = ThreadLocalRandom.current()
    while (true) {
        if (r.nextDouble() < p) break
    }
}

/**
 * Set of dispatcher configurations considered in benchmarks.
 */
public enum class DispatcherCreator(public val create: (parallelism: Int) -> CoroutineDispatcher) {
    //    ForkJoin({ parallelism ->  ForkJoinPool(parallelism).asCoroutineDispatcher() }),
    Experimental({ parallelism -> ExperimentalCoroutineDispatcher(corePoolSize = parallelism, maxPoolSize = parallelism) })
}

/**
 * Set of channel configurations considered in benchmarks.
 */
public enum class ChannelCreator(private val capacity: Int) {
    Rendezvous(Channel.RENDEZVOUS),
    `Buffered(16)`(16),
    `Buffered(128)`(128),
    Unlimited(Channel.UNLIMITED);

    public fun create(): Channel<Int> = Channel(capacity)
}

/**
 * Runs the specified process and waits until it is terminated.
 * Returns `true` if the termination is normal, `false` on failure.
 */
public fun runProcess(classNameToRun : String, jvmOptions : List<String>, args : Array<String>) : Boolean {
    val runJavaProcessCommand = ArrayList<String>()
    runJavaProcessCommand.run {
        this.add(JAVA_PATH)
        this.addAll(jvmOptions)
        this.add("-cp")
        this.add(CLASS_PATH)
        this.add(classNameToRun)
        this.addAll(args)
    }
    val processBuilder = ProcessBuilder(runJavaProcessCommand)
    val process = processBuilder.inheritIO().redirectError(ProcessBuilder.Redirect.INHERIT).start()
    return process.waitFor() == 0
}

private val CLASS_PATH = System.getProperty("java.class.path")
private val JAVA_PATH = Paths.get(System.getProperty("java.home")).resolve("bin").resolve("java").toString()
