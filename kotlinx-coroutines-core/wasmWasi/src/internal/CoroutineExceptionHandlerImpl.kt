@file:OptIn(UnsafeWasmMemoryApi::class)

package kotlinx.coroutines.internal

import kotlin.wasm.WasmImport
import kotlin.wasm.unsafe.UnsafeWasmMemoryApi
import kotlin.wasm.unsafe.withScopedMemoryAllocator

private const val STDERR = 2

/**
 * Write to a file descriptor. Note: This is similar to `writev` in POSIX.
 */
@WasmImport("wasi_snapshot_preview1", "fd_write")
private external fun wasiRawFdWrite(descriptor: Int, scatterPtr: Int, scatterSize: Int, errorPtr: Int): Int

@OptIn(UnsafeWasmMemoryApi::class)
private fun printlnErrorStream(message: String): Int = withScopedMemoryAllocator { allocator ->
    val data = message.encodeToByteArray()
    val dataSize = data.size
    val memorySize = dataSize + 1

    val ptr = allocator.allocate(memorySize)
    var currentPtr = ptr
    for (el in data) {
        currentPtr.storeByte(el)
        currentPtr += 1
    }
    (ptr + dataSize).storeByte(0x0A)

    val scatterPtr = allocator.allocate(8)
    (scatterPtr + 0).storeInt(ptr.address.toInt())
    (scatterPtr + 4).storeInt(memorySize)

    val rp0 = allocator.allocate(4)

    val ret = wasiRawFdWrite(
        descriptor = STDERR,
        scatterPtr = scatterPtr.address.toInt(),
        scatterSize = 1,
        errorPtr = rp0.address.toInt()
    )

    if (ret != 0) rp0.loadInt() else 0
}

/*
* Terminate the process normally with an exit code.
 */
@WasmImport("wasi_snapshot_preview1", "proc_exit")
private external fun wasiProcExit(exitCode: Int)

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    val errorCode = printlnErrorStream("!!!")
    val returnCode = if (errorCode != 0) errorCode else 1
    wasiProcExit(returnCode)
}