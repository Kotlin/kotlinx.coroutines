/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble.optimizations;

import io.reactivex.Flowable;
import io.reactivex.FlowableTransformer;
import io.reactivex.internal.functions.ObjectHelper;
import io.reactivex.plugins.RxJavaPlugins;

import java.util.regex.Pattern;

public final class StringFlowable {
    /** Utility class. */
    private StringFlowable() {
        throw new IllegalStateException("No instances!");
    }

    /**
     * Signals each character of the given string CharSequence as Integers.
     * @param string the source of characters
     * @return the new Flowable instance
     */
    public static Flowable<Integer> characters(CharSequence string) {
        ObjectHelper.requireNonNull(string, "string is null");
        return RxJavaPlugins.onAssembly(new FlowableCharSequence(string));
    }

    /**
     * Splits the input sequence of strings based on a pattern even across subsequent
     * elements if needed.
     * @param pattern the Rexexp pattern to split along
     * @return the new FlowableTransformer instance
     *
     * @since 0.13.0
     */
    public static FlowableTransformer<String, String> split(Pattern pattern) {
        return split(pattern, Flowable.bufferSize());
    }

    /**
     * Splits the input sequence of strings based on a pattern even across subsequent
     * elements if needed.
     * @param pattern the Rexexp pattern to split along
     * @param bufferSize the number of items to prefetch from the upstream
     * @return the new FlowableTransformer instance
     *
     * @since 0.13.0
     */
    public static FlowableTransformer<String, String> split(Pattern pattern, int bufferSize) {
        ObjectHelper.requireNonNull(pattern, "pattern is null");
        ObjectHelper.verifyPositive(bufferSize, "bufferSize");
        return new FlowableSplit(null, pattern, bufferSize);
    }

    /**
     * Splits the input sequence of strings based on a pattern even across subsequent
     * elements if needed.
     * @param pattern the Rexexp pattern to split along
     * @return the new FlowableTransformer instance
     *
     * @since 0.13.0
     */
    public static FlowableTransformer<String, String> split(String pattern) {
        return split(pattern, Flowable.bufferSize());
    }

    /**
     * Splits the input sequence of strings based on a pattern even across subsequent
     * elements if needed.
     * @param pattern the Rexexp pattern to split along
     * @param bufferSize the number of items to prefetch from the upstream
     * @return the new FlowableTransformer instance
     *
     * @since 0.13.0
     */
    public static FlowableTransformer<String, String> split(String pattern, int bufferSize) {
        return split(Pattern.compile(pattern), bufferSize);
    }

}
