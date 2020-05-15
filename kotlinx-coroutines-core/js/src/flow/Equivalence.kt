package kotlinx.coroutines.flow

public actual object Equivalent {
    public actual val ByValue: ValueEquivalence<Any?> = { old, new -> old == new }
    public actual val ByReference: ValueEquivalence<Any?> = { old, new -> old === new }
    public actual val Never: ValueEquivalence<Any?> = { old, new -> false }
}
