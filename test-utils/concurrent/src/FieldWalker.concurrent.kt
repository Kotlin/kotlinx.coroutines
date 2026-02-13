package kotlinx.coroutines.testing

/**
 * Ported from JVM to concurrent when porting JVM tests to concurrent.
 *
 * This object is only useful on JVM and has a dummy implementation on Native.
 */
expect object FieldWalker {
    /**
     * Native implementation's result should never be used.
     * Should always be used paired with `assertTrueJvm` which always asserts truth on Native.
     */
    fun walk(root: Any?): Set<Any>

    /**
     * Dummy implementation on Native.
     * Always asserts truth on Native.
     */
    fun assertReachableCount(expected: Int, root: Any?, rootStatics: Boolean = false, predicate: (Any) -> Boolean)
}
