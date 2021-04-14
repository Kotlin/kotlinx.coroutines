/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.lang.Long.*
import java.util.*
import java.util.concurrent.TimeUnit

@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class SaneFlowPlaysScrabble : ShakespearePlaysScrabble() {

    @Benchmark
    public override fun play(): List<Map.Entry<Int, List<String>>> {
        val score3: suspend (String) -> Int = { word: String ->
            val sum = score2(word) + bonusForDoubleLetter(word)
            sum * 2 + if (word.length == 7) 50 else 0
        }

        val buildHistoOnScore: ((suspend (String) -> Int) -> Flow<TreeMap<Int, List<String>>>) = { score ->
            flow {
                emit(shakespeareWords.asFlow()
                    .filter({ scrabbleWords.contains(it) && checkBlanks(it) })
                    .fold(TreeMap<Int, List<String>>(Collections.reverseOrder())) { acc, value ->
                        val key = score(value)
                        var list = acc[key] as MutableList<String>?
                        if (list == null) {
                            list = ArrayList()
                            acc[key] = list
                        }
                        list.add(value)
                        acc
                    })
            }
        }

        return runBlocking {
            buildHistoOnScore(score3)
                .flatMapConcatIterable { it.entries }
                .take(3)
                .toList()
        }
    }

    private suspend inline fun score2(word: String): Int {
        return buildHistogram(word)
            .map { it.letterScore() }
            .sum()
    }

    private suspend inline fun bonusForDoubleLetter(word: String): Int {
        return toBeMaxed(word)
            .map { letterScores[it - 'a'.toInt()] }
            .max()
    }

    private fun Map.Entry<Int, MutableLong>.letterScore(): Int = letterScores[key - 'a'.toInt()] * Integer.min(
        value.get().toInt(),
        scrabbleAvailableLetters[key - 'a'.toInt()])

    private fun toBeMaxed(word: String) = concat(word.asSequence(), word.asSequence(endIndex = 3))

    private suspend inline fun checkBlanks(word: String) = numBlanks(word) <= 2L

    private suspend fun numBlanks(word: String): Long {
        return buildHistogram(word)
            .map { blanks(it) }
            .sum()
    }

    private fun blanks(entry: Map.Entry<Int, MutableLong>): Long =
        max(0L, entry.value.get() - scrabbleAvailableLetters[entry.key - 'a'.toInt()])

    private suspend inline fun buildHistogram(word: String): HashMap<Int, MutableLong> {
        return word.asSequence().fold(HashMap()) { accumulator, value ->
            var newValue: MutableLong? = accumulator[value]
            if (newValue == null) {
                newValue = MutableLong()
                accumulator[value] = newValue
            }
            newValue.incAndSet()
            accumulator
        }
    }

    private fun String.asSequence(startIndex: Int = 0, endIndex: Int = length) = flow {
        for (i in  startIndex until endIndex.coerceAtMost(length)) {
            emit(get(i).toInt())
        }
    }
}
