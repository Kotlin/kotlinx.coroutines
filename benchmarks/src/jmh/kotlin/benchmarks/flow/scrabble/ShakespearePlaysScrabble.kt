/*
 * Copyright 2016-2019 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble

import org.openjdk.jmh.annotations.*
import java.io.*
import java.util.stream.*
import java.util.zip.*

@State(Scope.Benchmark)
abstract class ShakespearePlaysScrabble {
    @Throws(Exception::class)
    abstract fun play(): List<Map.Entry<Int, List<String>>>

    public class MutableLong {
        var value: Long = 0
        fun get(): Long {
            return value
        }

        fun incAndSet(): MutableLong {
            value++
            return this
        }

        fun add(other: MutableLong): MutableLong {
            value += other.value
            return this
        }
    }

    public interface LongWrapper {
        fun get(): Long

        @JvmDefault
        fun incAndSet(): LongWrapper {
            return object : LongWrapper {
                override fun get(): Long = this@LongWrapper.get() + 1L
            }
        }

        @JvmDefault
        fun add(other: LongWrapper): LongWrapper {
            return object : LongWrapper {
                override fun get(): Long = this@LongWrapper.get() + other.get()
            }
        }

        companion object {
            fun zero(): LongWrapper {
                return object : LongWrapper {
                    override fun get(): Long = 0L
                }
            }
        }
    }

    @JvmField
    public val letterScores: IntArray = intArrayOf(1, 3, 3, 2, 1, 4, 2, 4, 1, 8, 5, 1, 3, 1, 1, 3, 10, 1, 1, 1, 1, 4, 4, 8, 4, 10)

    @JvmField
    public val scrabbleAvailableLetters: IntArray =
        intArrayOf(9, 2, 2, 1, 12, 2, 3, 2, 9, 1, 1, 4, 2, 6, 8, 2, 1, 6, 4, 6, 4, 2, 2, 1, 2, 1)

    @JvmField
    public val scrabbleWords: Set<String> = readResource("ospd.txt.gz")

    @JvmField
    public val shakespeareWords: Set<String> = readResource("words.shakespeare.txt.gz")

    private fun readResource(path: String) =
        BufferedReader(InputStreamReader(GZIPInputStream(this.javaClass.classLoader.getResourceAsStream(path)))).lines()
            .map { it.toLowerCase() }.collect(Collectors.toSet())

    init {
        val expected = listOf(120 to listOf("jezebel", "quickly"),
            118 to listOf("zephyrs"), 116 to listOf("equinox"))
        val actual = play().map { it.key to it.value }
        if (expected != actual) {
            error("Incorrect benchmark, output: $actual")
        }
    }
}
