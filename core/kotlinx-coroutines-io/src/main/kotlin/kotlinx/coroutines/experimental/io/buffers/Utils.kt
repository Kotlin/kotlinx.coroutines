package kotlinx.coroutines.experimental.io.buffers

internal tailrec fun BufferView?.releaseAll() {
    if (this == null) return
    release()
    next.releaseAll()
}

internal fun BufferView.copyAll(): BufferView {
    val copied = makeView()
    val next = this.next ?: return copied

    return next.copyAll(copied, copied)
}

private tailrec fun BufferView.copyAll(head: BufferView, prev: BufferView): BufferView {
    val copied = makeView()
    prev.next = copied

    val next = this.next ?: return head

    return next.copyAll(head, copied)
}

internal tailrec fun BufferView.tail(): BufferView {
    val next = this.next ?: return this
    return next.tail()
}

internal fun BufferView.remainingAll(): Long = remainingAll(0L)

private tailrec fun BufferView.remainingAll(n: Long): Long {
    val rem = readRemaining.toLong() + n
    val next = this.next ?: return rem

    return next.remainingAll(rem)
}

internal tailrec fun BufferView.isEmpty(): Boolean {
    if (readRemaining > 0) return false
    val next = this.next ?: return true
    return next.isEmpty()
}

class BufferLimitExceededException(message: String) : Exception(message)