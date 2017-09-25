package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.buffers.*

val ByteReadPacketEmpty: ByteReadPacket = ByteReadPacketViewBased(BufferView.Empty)