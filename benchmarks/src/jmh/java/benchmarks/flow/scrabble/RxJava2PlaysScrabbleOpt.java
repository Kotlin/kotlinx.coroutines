/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble;

import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import hu.akarnokd.rxjava2.math.MathFlowable;
import org.openjdk.jmh.annotations.*;
import benchmarks.flow.scrabble.optimizations.*;
import io.reactivex.*;
import io.reactivex.functions.Function;

/**
 * Shakespeare plays Scrabble with RxJava 2 Flowable optimized.
 * @author José
 * @author akarnokd
 */
@Warmup(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 7, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 1)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
public class RxJava2PlaysScrabbleOpt extends ShakespearePlaysScrabble {
    static Flowable<Integer> chars(String word) {
//        return Flowable.range(0, word.length()).map(i -> (int)word.charAt(i));
        return StringFlowable.characters(word);
    }

    @Benchmark
    @Override
    public List<Entry<Integer, List<String>>> play() throws Exception {

        //  to compute the score of a given word
        Function<Integer, Integer> scoreOfALetter = letter -> letterScores[letter - 'a'];

        // score of the same letters in a word
        Function<Entry<Integer, MutableLong>, Integer> letterScore =
                entry ->
                        letterScores[entry.getKey() - 'a'] *
                        Integer.min(
                                (int)entry.getValue().get(),
                                scrabbleAvailableLetters[entry.getKey() - 'a']
                            )
                    ;


        Function<String, Flowable<Integer>> toIntegerFlowable =
                string -> chars(string);

        Map<String, Single<HashMap<Integer, MutableLong>>> histoCache = new HashMap<>();
        // Histogram of the letters in a given word
        Function<String, Single<HashMap<Integer, MutableLong>>> histoOfLetters =
                word -> { Single<HashMap<Integer, MutableLong>> s = histoCache.get(word);
                        if (s == null) {
                            s = toIntegerFlowable.apply(word)
                            .collect(
                                () -> new HashMap<>(),
                                (HashMap<Integer, MutableLong> map, Integer value) ->
                                    {
                                        MutableLong newValue = map.get(value) ;
                                        if (newValue == null) {
                                            newValue = new MutableLong();
                                            map.put(value, newValue);
                                        }
                                        newValue.incAndSet();
                                    }

                            );
                            histoCache.put(word, s);
                        }
                        return s;
                        };

        // number of blanks for a given letter
        Function<Entry<Integer, MutableLong>, Long> blank =
                entry ->
                        Long.max(
                            0L,
                            entry.getValue().get() -
                            scrabbleAvailableLetters[entry.getKey() - 'a']
                        )
                    ;

        // number of blanks for a given word
        Function<String, Flowable<Long>> nBlanks =
                word -> MathFlowable.sumLong(
                            histoOfLetters.apply(word).flattenAsFlowable(
                                    map -> map.entrySet()
                            )
                            .map(blank)
                        )
                    ;


        // can a word be written with 2 blanks?
        Function<String, Flowable<Boolean>> checkBlanks =
                word -> nBlanks.apply(word)
                            .map(l -> l <= 2L) ;

        // score taking blanks into account letterScore1
        Function<String, Flowable<Integer>> score2 =
                word -> MathFlowable.sumInt(
                            histoOfLetters.apply(word).flattenAsFlowable(
                                map -> map.entrySet()
                            )
                            .map(letterScore)
                            ) ;

        // Placing the word on the board
        // Building the streams of first and last letters
        Function<String, Flowable<Integer>> first3 =
                word -> chars(word).take(3) ;
        Function<String, Flowable<Integer>> last3 =
                word -> chars(word).skip(3) ;


        // Stream to be maxed
        Function<String, Flowable<Integer>> toBeMaxed =
            word -> Flowable.concat(first3.apply(word), last3.apply(word))
            ;

        // Bonus for double letter
        Function<String, Flowable<Integer>> bonusForDoubleLetter =
            word -> MathFlowable.max(toBeMaxed.apply(word)
                        .map(scoreOfALetter)
                        ) ;

        // score of the word put on the board
        Function<String, Flowable<Integer>> score3 =
            word ->
                MathFlowable.sumInt(Flowable.concat(
                    score2.apply(word),
                    bonusForDoubleLetter.apply(word)
                )).map(v -> v * 2 + (word.length() == 7 ? 50 : 0));

        Function<Function<String, Flowable<Integer>>, Single<TreeMap<Integer, List<String>>>> buildHistoOnScore =
                score -> Flowable.fromIterable(shakespeareWords)
                                .filter(scrabbleWords::contains)
                                .filter(word -> checkBlanks.apply(word).blockingFirst())
                                .collect(
                                    () -> new TreeMap<Integer, List<String>>(Comparator.reverseOrder()),
                                    (TreeMap<Integer, List<String>> map, String word) -> {
                                        Integer key = score.apply(word).blockingFirst() ;
                                        List<String> list = map.get(key) ;
                                        if (list == null) {
                                            list = new ArrayList<>() ;
                                            map.put(key, list) ;
                                        }
                                        list.add(word) ;
                                    }
                                ) ;

        // best key / value pairs
        List<Entry<Integer, List<String>>> finalList2 =
                    buildHistoOnScore.apply(score3).flattenAsFlowable(
                            map -> map.entrySet()
                    )
                    .take(3)
                    .collect(
                        () -> new ArrayList<Entry<Integer, List<String>>>(),
                        (list, entry) -> {
                            list.add(entry) ;
                        }
                    )
                    .blockingGet();

        return finalList2 ;
    }
}