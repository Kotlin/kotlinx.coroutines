/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.io.core.*
import kotlinx.io.pool.*

internal val PACKET_BUFFER_SIZE = getIOIntProperty("PacketBufferSize", 4096)
internal val PACKET_BUFFER_POOL_SIZE = getIOIntProperty("PacketBufferPoolSize", 128)
internal val PACKET_MAX_COPY_SIZE = getIOIntProperty("PacketMaxCopySize", 500)

fun WritePacket(headerSizeHint: Int = 0): ByteWritePacket = BytePacketBuilder(headerSizeHint)
