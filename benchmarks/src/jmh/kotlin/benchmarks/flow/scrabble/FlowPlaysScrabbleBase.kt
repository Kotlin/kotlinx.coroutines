/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.openjdk.jmh.annotations.*
import java.lang.Long.max
import java.util.*
import java.util.concurrent.*
import kotlin.math.*

@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class FlowPlaysScrabbleBase : ShakespearePlaysScrabble() {

    @Benchmark
    public override fun play(): List<Map.Entry<Int, List<String>>> {
        val scoreOfALetter = { letter: Int -> flowOf(letterScores[letter - 'a'.toInt()]) }

        val letterScore = { entry: Map.Entry<Int, LongWrapper> ->
            flowOf(
                letterScores[entry.key - 'a'.toInt()] * Integer.min(
                    entry.value.get().toInt(),
                    scrabbleAvailableLetters[entry.key - 'a'.toInt()]
                )
            )
        }

        val toIntegerStream = { string: String ->
            IterableSpliterator.of(string.chars().boxed().spliterator()).asFlow()
        }

        val histoOfLetters = { word: String ->
            flow {
                emit(toIntegerStream(word).fold(HashMap<Int, LongWrapper>()) { accumulator, value ->
                    var newValue: LongWrapper? = accumulator[value]
                    if (newValue == null) {
                        newValue = LongWrapper.zero()
                    }
                    accumulator[value] = newValue.incAndSet()
                    accumulator
                })
            }
        }

        val blank = { entry: Map.Entry<Int, LongWrapper> ->
            flowOf(max(0L, entry.value.get() - scrabbleAvailableLetters[entry.key - 'a'.toInt()]))
        }

        val nBlanks = { word: String ->
            flow {
                emit(histoOfLetters(word)
                    .flatMapConcat { map -> map.entries.iterator().asFlow() }
                    .flatMapConcat({ blank(it) })
                    .reduce { a, b -> a + b })
            }
        }

        val checkBlanks = { word: String ->
            nBlanks(word).flatMapConcat { l -> flowOf(l <= 2L) }
        }

        val score2 = { word: String ->
            flow {
                emit(histoOfLetters(word)
                    .flatMapConcat { map -> map.entries.iterator().asFlow() }
                    .flatMapConcat { letterScore(it) }
                    .reduce { a, b -> a + b })
            }
        }

        val first3 = { word: String ->
            IterableSpliterator.of(word.chars().boxed().limit(3).spliterator()).asFlow()
        }

        val last3 = { word: String ->
            IterableSpliterator.of(word.chars().boxed().skip(3).spliterator()).asFlow()
        }

        val toBeMaxed = { word: String -> flowOf(first3(word), last3(word)).flattenConcat() }

        // Bonus for double letter
        val bonusForDoubleLetter = { word: String ->
            flow {
                emit(toBeMaxed(word)
                    .flatMapConcat { scoreOfALetter(it) }
                    .reduce { a, b -> max(a, b) })
            }
        }

        val score3 = { word: String ->
            flow {
                emit(flowOf(
                    score2(word), score2(word),
                    bonusForDoubleLetter(word),
                    bonusForDoubleLetter(word),
                    flowOf(if (word.length == 7) 50 else 0)
                ).flattenConcat().reduce { a, b -> a + b })
            }
        }

        val buildHistoOnScore: (((String) -> Flow<Int>) -> Flow<TreeMap<Int, List<String>>>) = { score ->
            flow {
                emit(shakespeareWords.asFlow()
                    .filter({ scrabbleWords.contains(it) && checkBlanks(it).single() })
                    .fold(TreeMap<Int, List<String>>(Collections.reverseOrder())) { acc, value ->
                        val key = score(value).single()
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
                .flatMapConcat { map -> map.entries.iterator().asFlow() }
                .take(3)
                .toList()
        }
    }
}
