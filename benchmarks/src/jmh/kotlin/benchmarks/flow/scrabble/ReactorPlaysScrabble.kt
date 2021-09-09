/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble

import reactor.core.publisher.*
import java.lang.Long.*
import java.util.*
import java.util.function.Function

/*@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)*/
open class ReactorPlaysScrabble : ShakespearePlaysScrabble() {

//    @Benchmark
    public override fun play(): List<Map.Entry<Int, List<String>>> {
        val scoreOfALetter = Function<Int, Flux<Int>> { letter -> Flux.just(letterScores[letter - 'a'.toInt()]) }

        val letterScore = Function<Map.Entry<Int, LongWrapper>, Flux<Int>> { entry ->
            Flux.just(
                letterScores[entry.key - 'a'.toInt()] * Integer.min(
                    entry.value.get().toInt(),
                    scrabbleAvailableLetters[entry.key - 'a'.toInt()]
                )
            )
        }

        val toIntegerStream = Function<String, Flux<Int>> { string ->
            Flux.fromIterable(IterableSpliterator.of(string.chars().boxed().spliterator()))
        }

        val histoOfLetters = Function<String, Flux<HashMap<Int, LongWrapper>>> { word ->
            Flux.from(toIntegerStream.apply(word)
                .collect(
                    { HashMap() },
                    { map: HashMap<Int, LongWrapper>, value: Int ->
                        var newValue: LongWrapper? = map[value]
                        if (newValue == null) {
                            newValue = LongWrapper.zero()
                        }
                        map[value] = newValue.incAndSet()
                    }

                ))
        }

        val blank = Function<Map.Entry<Int, LongWrapper>, Flux<Long>> { entry ->
            Flux.just(max(0L, entry.value.get() - scrabbleAvailableLetters[entry.key - 'a'.toInt()]))
        }

        val nBlanks = Function<String, Flux<Long>> { word ->
            Flux.from(histoOfLetters.apply(word)
                .flatMap<Map.Entry<Int, LongWrapper>> { map -> Flux.fromIterable<Map.Entry<Int, LongWrapper>>(Iterable { map.entries.iterator() }) }
                .flatMap(blank)
                .reduce { a, b -> sum(a, b) })
        }

        val checkBlanks = Function<String, Flux<Boolean>> { word ->
            nBlanks.apply(word)
                .flatMap { l -> Flux.just(l <= 2L) }
        }


        val score2 = Function<String, Flux<Int>> { word ->
            Flux.from(histoOfLetters.apply(word)
                .flatMap<Map.Entry<Int, LongWrapper>> { map -> Flux.fromIterable<Map.Entry<Int, LongWrapper>>(Iterable { map.entries.iterator() }) }
                .flatMap(letterScore)
                .reduce { a, b -> Integer.sum(a, b) })

        }

        val first3 = Function<String, Flux<Int>> { word -> Flux.fromIterable(
            IterableSpliterator.of(
                word.chars().boxed().limit(3).spliterator()
            )
        ) }
        val last3 = Function<String, Flux<Int>> { word -> Flux.fromIterable(
            IterableSpliterator.of(
                word.chars().boxed().skip(3).spliterator()
            )
        ) }

        val toBeMaxed = Function<String, Flux<Int>> { word ->
            Flux.just(first3.apply(word), last3.apply(word))
                .flatMap { Stream -> Stream }
        }

        // Bonus for double letter
        val bonusForDoubleLetter = Function<String, Flux<Int>>  { word ->
            Flux.from<Int>(toBeMaxed.apply(word)
                .flatMap<Int>(scoreOfALetter)
                .reduce { a, b -> Integer.max(a, b) }
            )
        }

        val score3 = Function<String, Flux<Int>> { word ->
            Flux.from(Flux.just(
                score2.apply(word),
                score2.apply(word),
                bonusForDoubleLetter.apply(word),
                bonusForDoubleLetter.apply(word),
                Flux.just(if (word.length == 7) 50 else 0)
            )
                .flatMap { Stream -> Stream }
                .reduce { a, b -> Integer.sum(a, b) })
        }

        val buildHistoOnScore = Function<Function<String, Flux<Int>>, Flux<TreeMap<Int, List<String>>>> { score ->
            Flux.from(Flux.fromIterable(Iterable { shakespeareWords.iterator() })
                .filter( { scrabbleWords.contains(it) })
                .filter({ word -> checkBlanks.apply(word).toIterable().iterator().next() })
                .collect(
                    { TreeMap<Int, List<String>>(Collections.reverseOrder()) },
                    { map: TreeMap<Int, List<String>>, word: String ->
                        val key = score.apply(word).toIterable().iterator().next()
                        var list = map[key] as MutableList<String>?
                        if (list == null) {
                            list = ArrayList()
                            map[key] = list
                        }
                        list.add(word)
                    }
                ))
        }

        val finalList2 = Flux.from<ArrayList<Map.Entry<Int, List<String>>>>(buildHistoOnScore.apply(score3)
            .flatMap<Map.Entry<Int, List<String>>> { map -> Flux.fromIterable<Map.Entry<Int, List<String>>>(Iterable { map.entries.iterator() }) }
            .take(3)
            .collect<ArrayList<Map.Entry<Int, List<String>>>>(
                { ArrayList() },
                { list, entry -> list.add(entry) }
            )
        ).toIterable().iterator().next()

        return finalList2
    }

}

