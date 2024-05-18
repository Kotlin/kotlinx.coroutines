package kotlinx.coroutines.scheduling

/**
 * Introduced as part of IntelliJ patches.
 *
 * Runnables that are dispatched on [kotlinx.coroutines.CoroutineDispatcher] may optionally implement this interface
 * to declare an ability to compensate the associated parallelism resource.
 */
internal interface ParallelismCompensation {
    /**
     * Should increase both the limit and the effective parallelism.
     */
    fun increaseParallelismAndLimit()

    /**
     * Should only decrease the parallelism limit. The effective parallelism may temporarily stay higher than this limit.
     * Runnable should take care of checking whether effective parallelism needs to decrease to meet the desired limit.
     */
    fun decreaseParallelismLimit()
}