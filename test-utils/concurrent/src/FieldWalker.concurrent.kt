package kotlinx.coroutines.testing

expect object FieldWalker {
    fun walk(root: Any?): Set<Any>
    fun assertReachableCount(expected: Int, root: Any?, rootStatics: Boolean = false, predicate: (Any) -> Boolean)
}
