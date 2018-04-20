package kotlinx.coroutines.experimental.internal

/**
 * Special kind of list intended to be used as collection of subscribers in [ArrayBroadcastChannel]
 * On JVM it's CopyOnWriteList and on JS it's MutableList.
 *
 * Note that this alias is intentionally not named as CopyOnWriteList to avoid accidental misusage outside of ArrayBroadcastChannel
 */
typealias SubscribersList<E> = MutableList<E>

expect fun <E> subscriberList(): SubscribersList<E>

expect class ReentrantLock() {
    fun tryLock(): Boolean
    fun unlock(): Unit
}

expect inline fun <T> ReentrantLock.withLock(action: () -> T): T
