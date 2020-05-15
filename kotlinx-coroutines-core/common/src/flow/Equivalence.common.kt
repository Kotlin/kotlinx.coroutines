package kotlinx.coroutines.flow

public typealias ValueEquivalence<T> = (old: T, new: T) -> Boolean

public expect object Equivalent {
    public val ByValue: ValueEquivalence<Any?>
    public val ByReference: ValueEquivalence<Any?>
    public val Never: ValueEquivalence<Any?>
}
