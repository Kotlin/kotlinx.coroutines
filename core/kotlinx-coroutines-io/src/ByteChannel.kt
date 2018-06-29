/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.internal.EmptyByteBuffer

/**
 * Channel for asynchronous reading and writing of sequences of bytes.
 * This is a buffered **single-reader single-writer channel**.
 *
 * Read operations can be invoked concurrently with write operations, but multiple reads or multiple writes
 * cannot be invoked concurrently with themselves. Exceptions are [close] and [flush] which can be invoked
 * concurrently with any other operations and between themselves at any time.
 */
interface ByteChannel : ByteReadChannel, ByteWriteChannel

/**
 * Creates buffered channel for asynchronous reading and writing of sequences of bytes.
 */
public fun ByteChannel(autoFlush: Boolean = false): ByteChannel =
    ByteBufferChannel(autoFlush)

/**
 * Creates channel for reading from the specified byte buffer.
 */
public fun ByteReadChannel(content: ByteBuffer): ByteReadChannel =
    ByteBufferChannel(content)

/**
 * Creates channel for reading from the specified byte array.
 */
public fun ByteReadChannel(content: ByteArray): ByteReadChannel =
    ByteBufferChannel(ByteBuffer.wrap(content))


/**
 * Byte channel that is always empty.
 */
val EmptyByteReadChannel: ByteReadChannel = ByteReadChannel(EmptyByteBuffer)