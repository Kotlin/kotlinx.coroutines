package kotlinx.coroutines.testing

actual object FieldWalker {
    actual fun walk(root: Any?): Set<Any> {
        return emptySet()
    }

    actual fun assertReachableCount(expected: Int, root: Any?, rootStatics: Boolean, predicate: (Any) -> Boolean) {}
}
