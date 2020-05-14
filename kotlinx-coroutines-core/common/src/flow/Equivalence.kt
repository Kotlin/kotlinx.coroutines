package kotlinx.coroutines.flow

public typealias ValueEquivalence<T> = (old: T, new: T) -> Boolean

public object Equivalent {
    public val ByValue: ValueEquivalence<Any?> = { old, new -> old == new }
    public val ByReference: ValueEquivalence<Any?> = { old, new -> old === new }
    public val Never: ValueEquivalence<Any?> = { old, new -> false }
}
