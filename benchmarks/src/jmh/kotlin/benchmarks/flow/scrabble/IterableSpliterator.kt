/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.flow.scrabble

import java.util.*

object IterableSpliterator {
    @JvmStatic
    public fun <T> of(spliterator: Spliterator<T>): Iterable<T> = Iterable { Spliterators.iterator(spliterator) }
}
