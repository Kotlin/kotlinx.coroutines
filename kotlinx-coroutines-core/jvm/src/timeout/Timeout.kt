package kotlinx.coroutines.timeout

import kotlinx.coroutines.CopyableThrowable
import kotlinx.coroutines.Job
import java.util.concurrent.TimeoutException as JavaTimeoutException


public actual class TimeoutException actual internal constructor(
    message: String,
    @JvmField @Transient internal val coroutine: Job?
) : JavaTimeoutException(message), CopyableThrowable<TimeoutException> {

    actual internal constructor(message: String) : this(message, null)

    override fun createCopy(): TimeoutException =
        TimeoutException(message ?: "", coroutine).also { it.initCause(this) }
}