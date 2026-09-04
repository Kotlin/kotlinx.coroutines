package kotlinx.coroutines

import kotlin.native.concurrent.ObsoleteWorkersApi
import kotlin.native.concurrent.Worker

@OptIn(ObsoleteWorkersApi::class)
internal actual fun runningOnIoThread(): Boolean = Worker.current.name.startsWith("Dispatchers.IO")
