package kotlinx.coroutines.experimental.channels

enum class TestChannelKind {
    RENDEZVOUS {
        override fun create(): Channel<Int> = RendezvousChannel<Int>()
        override fun toString(): String = "RendezvousChannel"
    },
    ARRAY_1 {
        override fun create(): Channel<Int> = ArrayChannel<Int>(1)
        override fun toString(): String = "ArrayChannel(1)"
    },
    ARRAY_10 {
        override fun create(): Channel<Int> = ArrayChannel<Int>(8)
        override fun toString(): String = "ArrayChannel(8)"
    }
    ;

    abstract fun create(): Channel<Int>
}
