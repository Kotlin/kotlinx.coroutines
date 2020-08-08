/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*

/**
 * Classes that the timer flow can emit.
 *
 *  - OnTick emits every interval chosen with time left in millis
 *  - OnPause emits when function pause() is called with the remaining time in millis
 *  - OnContinue emits when function `continue`() is called
 *  - OnStop emits when time runs out or function stop() is called. This resets the timer and the function start() needs to be called again
 *  - OnError emits when an error occurs. For example when function start() is called on a timer that's already running
 */
public sealed class TimerResult {
    public class OnTick(public val timeLeftMillis: Long): TimerResult()
    public class OnPause(public val remainingTimeMillis: Long): TimerResult()
    public object OnContinue: TimerResult()
    public object OnStop: TimerResult()
    public class OnError(public val error: Exception): TimerResult()
}

/**
 * Different states for the timer
 */
private enum class TimerState {
    RUNNING, PAUSED, STOPPED
}

/**
 * Exception class the timer can emit
 */
private class TimerException(val type: TimerErrorTypes): Exception(type.message)

/**
 * Types of exceptions the [TimerException] @param type could be
 */
public enum class TimerErrorTypes(public val message: String) {
    ALREADY_RUNNING("This instance of the timer is already running, create a new instance or stop your current timer"),
    CURRENTLY_PAUSED("This timer is currently paused. Choose to continue or stop to start over"),
    NO_TIMER_RUNNING("Trying to stop or pause a timer that isn't running"),
    UNABLE_TO_CONTINUE("Trying to continue a timer which isn't paused")
}

/**
 * An instance of this class will create a timer. Every instance is a new separate timer
 */
public class FlowTimer {

    /**
     * Timer uses this state to keep track of itself
     */
    private var state: TimerState = TimerState.STOPPED

    /**
     * Caller can check if the timer is currently running
     */
    public val isRunning: Boolean = state == TimerState.RUNNING

    /**
     * Start the timer
     *
     * @param countDownTimeMillis is how many milliseconds the caller wants the timer to run
     * @param delayMillis is how much delay and how much time the caller wants to remove from timer. Default is 1 second
     *
     * Can cause timer to emit an exception if:
     *  - Caller tries to start a timer that is already running [TimerErrorTypes.ALREADY_RUNNING]
     *  - Caller tries to start a timer which is currently paused [TimerErrorTypes.CURRENTLY_PAUSED]. Function `continue`() should be used instead
     */
    public fun start(countDownTimeMillis: Long, delayMillis: Long = 1000): Flow<TimerResult> =
        flow {
            when (state) {
                TimerState.RUNNING -> {
                    emit(TimerResult.OnError(TimerException(TimerErrorTypes.ALREADY_RUNNING)))
                }
                TimerState.PAUSED -> {
                    emit(TimerResult.OnError(TimerException(TimerErrorTypes.CURRENTLY_PAUSED)))
                }
                else -> beginCountdown(countDownTimeMillis, delayMillis).collect { emit(it) }
            }
        }

    /**
     * Stop the timer
     *
     * Can cause timer to emit an exception if:
     *  - Caller tries to stop a timer which is already stopped [TimerErrorTypes.NO_TIMER_RUNNING]
     */
    public fun stop(): Flow<TimerResult> =
        flow {
            if (state == TimerState.STOPPED) {
                emit(TimerResult.OnError(TimerException(TimerErrorTypes.NO_TIMER_RUNNING)))
            } else {
                emit(TimerResult.OnStop)
            }
            state = TimerState.STOPPED
        }

    /**
     * Pause a running timer, will keep the timers current time if callers wants to continue it later
     *
     * Can cause timer to emit an exception if:
     *  - Caller tries to pause a timer which is not currently running [TimerErrorTypes.NO_TIMER_RUNNING]
     */
    public fun pause(): Flow<TimerResult> =
        flow {
            if (state == TimerState.STOPPED) {
                emit(TimerResult.OnError(TimerException(TimerErrorTypes.NO_TIMER_RUNNING)))
            } else {
                state = TimerState.PAUSED
            }
        }

    /**
     * Continue a timer which is paused
     *
     * Can cause timer to emit an exception if:
     *  - Caller tries to continue a timer which isn't currently paused [TimerErrorTypes.UNABLE_TO_CONTINUE]
     */
    public fun `continue`(): Flow<TimerResult> =
        flow {
            if (state == TimerState.STOPPED) {
                emit(TimerResult.OnError(TimerException(TimerErrorTypes.UNABLE_TO_CONTINUE)))
            } else {
                state = TimerState.RUNNING
                emit(TimerResult.OnContinue)
            }
        }

    /**
     * If the function start() doesn't emit an @exception it will call this function
     *
     * @param countDownTimeMillis is for how many milliseconds the caller wants the timer to run
     * @param delayMillis is how much delay and how much time the caller wants to remove from timer. Default is 1 second
     *
     * This function will start a while loop which will:
     *
     *  - If currently running emit [TimerResult.OnTick] with the time left after every time
     *  @param delayMillis has been delayed and removed from
     *  @param countDownTimeMillis
     *
     *  - If currently running and function pause() is called emit [TimerResult.OnPause] with the time that's left from
     *  @param countDownTimeMillis
     *
     *  - if while loop is still looping and function stop() is called or time runs out emit [TimerResult.OnStop] and break the loop
     */
    private fun beginCountdown(countDownTimeMillis: Long, delayMillis: Long = 1000): Flow<TimerResult> =
        flow {
            state = TimerState.RUNNING
            var timeLeftMillis = countDownTimeMillis

            timerLoop@ while (true) {
                when {
                    timeLeftMillis < 1 -> {
                        state = TimerState.STOPPED
                        this.emit(TimerResult.OnStop)
                        break@timerLoop
                    }
                    timeLeftMillis > 0 && state == TimerState.RUNNING -> {
                        this.emit(TimerResult.OnTick(timeLeftMillis))
                        delay(delayMillis)
                        timeLeftMillis -= delayMillis
                    }
                    state == TimerState.PAUSED -> {
                        this.emit(TimerResult.OnPause(timeLeftMillis))
                    }
                    state == TimerState.STOPPED -> {
                        this.emit(TimerResult.OnStop)
                        break@timerLoop
                    }
                }
            }
        }
}
