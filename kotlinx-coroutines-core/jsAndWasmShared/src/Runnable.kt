package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 *
 * Equivalent to the type `() -> Unit`.
 */
public actual fun interface Runnable {
    /**
     * @suppress
     */
    public actual fun run()
}

@Deprecated(
    "Preserved for binary compatibility, see https://github.com/Kotlin/kotlinx.coroutines/issues/4309",
    level = DeprecationLevel.HIDDEN
)
public inline fun Runnable(crossinline block: () -> Unit): Runnable =
    object : Runnable {
        override fun run() {
            block()
        }
    }
