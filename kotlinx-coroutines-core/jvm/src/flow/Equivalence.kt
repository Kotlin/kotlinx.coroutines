package kotlinx.coroutines.flow

public actual object Equivalent {
    public actual val ByValue: ValueEquivalence<Any?> = ValueEquivalenceImpl(0)
    public actual val ByReference: ValueEquivalence<Any?> = ValueEquivalenceImpl(1)
    public actual val Never: ValueEquivalence<Any?> = ValueEquivalenceImpl(2)
}

private class ValueEquivalenceImpl(private val impl: Int) : ValueEquivalence<Any?> {
    override fun invoke(old: Any?, new: Any?): Boolean = when (impl) {
        0 -> old == new
        1 -> old === new
        2 -> false
        else -> error("invalid")
    }

    override fun toString(): String = when (impl) {
        0 -> "ByValue"
        1 -> "ByReference"
        2 -> "Never"
        else -> error("invalid")
    }
}
