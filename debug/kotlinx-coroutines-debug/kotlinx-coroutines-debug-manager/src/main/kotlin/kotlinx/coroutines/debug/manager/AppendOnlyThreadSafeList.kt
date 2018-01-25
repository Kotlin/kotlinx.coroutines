package kotlinx.coroutines.debug.manager

@Suppress("UNCHECKED_CAST")
// this is needed for fast lock-free reads and thread-safe adds
class AppendOnlyThreadSafeList<T>: AbstractMutableList<T>() {
    @Volatile
    private var a: Array<T> = arrayOfNulls<Any?>(8) as Array<T>

    @Volatile
    private var _size = 0

    override val size: Int
        get() = _size

    // lock-free
    override fun get(index: Int): T {
        check(index in 0..(_size - 1)) { "Index $index is out of range" }
        return a[index]
    }

    @Synchronized
    fun appendWithIndex(element: T): Int {
        val size = this._size
        var a = this.a
        if (size >= a.size) {
            a = a.copyOf(a.size * 2) as Array<T>
            this.a = a // replace cur array, volatile write
        }
        a[size] = element
        _size = size + 1
        return size
    }

    @Synchronized
    override fun add(index: Int, element: T) {
        check(index == _size) { "Can only append to the end" }
        appendWithIndex(element)
    }

    @Synchronized
    override fun removeAt(index: Int) = throw UnsupportedOperationException()

    @Synchronized
    override fun set(index: Int, element: T): T = throw UnsupportedOperationException()

}