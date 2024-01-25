package benchmarks.flow.scrabble

import java.util.*

object IterableSpliterator {
    @JvmStatic
    public fun <T> of(spliterator: Spliterator<T>): Iterable<T> = Iterable { Spliterators.iterator(spliterator) }
}
