/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.openjdk.jmh.annotations.*
import org.openjdk.jmh.annotations.State
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger

/**
 * The benchmark is supposed to show the DebugProbes overhead for a non-concurrent sequence builder.
 * The code is actually part of the IDEA codebase, originally reported here: https://github.com/Kotlin/kotlinx.coroutines/issues/3527
 */
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
open class DebugSequenceOverheadBenchmark {

    private fun <Node> generateRecursiveSequence(
        initialSequence: Sequence<Node>,
        children: (Node) -> Sequence<Node>
    ): Sequence<Node> {
        return sequence {
            val initialIterator = initialSequence.iterator()
            if (!initialIterator.hasNext()) {
                return@sequence
            }
            val visited = HashSet<Node>()
            val sequences = ArrayDeque<Sequence<Node>>()
            sequences.addLast(initialIterator.asSequence())
            while (sequences.isNotEmpty()) {
                val currentSequence = sequences.removeFirst()
                for (node in currentSequence) {
                    if (visited.add(node)) {
                        yield(node)
                        sequences.addLast(children(node))
                    }
                }
            }
        }
    }

    @Param("true", "false")
    var withDebugger = false

    @Setup
    fun setup() {
        DebugProbes.sanitizeStackTraces = false
        DebugProbes.enableCreationStackTraces = false
        if (withDebugger) {
            DebugProbes.install()
        }
    }

    @TearDown
    fun tearDown() {
        if (withDebugger) {
            DebugProbes.uninstall()
        }
    }

    // Shows the overhead of sequence builder with debugger enabled
    @Benchmark
    fun runSequenceSingleThread(): Int = runBlocking {
        generateRecursiveSequence((1..100).asSequence()) {
            (1..it).asSequence()
        }.sum()
    }

    // Shows the overhead of sequence builder with debugger enabled and debugger is concurrently stressed out
    @Benchmark
    fun runSequenceMultipleThreads(): Int = runBlocking {
        val result = AtomicInteger(0)
        repeat(Runtime.getRuntime().availableProcessors()) {
            launch(Dispatchers.Default) {
                result.addAndGet(generateRecursiveSequence((1..100).asSequence()) {
                    (1..it).asSequence()
                }.sum())
            }
        }
        result.get()
    }
}
