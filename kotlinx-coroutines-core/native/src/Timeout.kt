package kotlinx.coroutines.timeout

import kotlinx.coroutines.CopyableThrowable
import kotlinx.coroutines.Job

public actual class TimeoutException actual internal constructor(
    message: String, internal val coroutine: Job?
) : Exception(message) {

    actual internal constructor(message: String) : this(message, null)
}
