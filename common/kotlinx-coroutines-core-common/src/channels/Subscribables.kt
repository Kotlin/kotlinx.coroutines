/*
 * Copyright 2016-2018 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.Unconfined
import kotlin.properties.ReadOnlyProperty
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty

/**
 * Interface for classes allowing to open subscriptions.
 */
public interface Subscribable<out T> {

    /**
     * Subscribes and returns a channel to receive elements broadcasted by this Subscribable.
     * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this subscribable.
     */
    public fun openSubscription(): ReceiveChannel<T>
}

/**
 * Interface for a value holder where the value may change over time.
 *
 * The current value can be obtained with [value] and one can open a subscription in order to receive the new value when changed.
 *
 * The channel returned by [openSubscription] is "conflated" and start by the current value if any.
 */
public interface SubscribableValue<out T> : Subscribable<T>, ReadOnlyProperty<Any?, T> {

    /**
     * Current value
     */
    public val value: T

    /**
     * Returns the current value.
     *
     * @see value
     */
    public override fun getValue(thisRef: Any?, property: KProperty<*>): T = value
}

/**
 * Mutable version of [SubscribableValue].
 *
 * Provide ability to get and set the current value with [value].
 */
public interface SubscribableVariable<T> : SubscribableValue<T>, ReadWriteProperty<Any?, T> {

    /**
     * Current value
     */
    public override var value: T

    public override fun getValue(thisRef: Any?, property: KProperty<*>): T = value

    /**
     * Set the current value
     */
    public override fun setValue(thisRef: Any?, property: KProperty<*>, value: T) {
        this.value = value
    }
}

/**
 * Create an instance of [SubscribableValue] with the given [value]
 */
public fun <T> SubscribableValue(value: T): SubscribableValue<T> = SubscribableValueImpl(value)

/**
 * Create an instance of [SubscribableVariable] initialized with the given [initialValue]
 */
public fun <T> SubscribableVariable(initialValue: T): SubscribableVariable<T> = SubscribableVariableImpl(initialValue)

private class SubscribableValueImpl<T>(override val value: T): SubscribableValue<T> {
    override fun openSubscription() = produce(Unconfined) { send(value) }
}

private class SubscribableVariableImpl<T>(initialValue: T): SubscribableVariable<T> {
    private val broadcast = ConflatedBroadcastChannel(initialValue)

    override var value: T
        get() = broadcast.value
        set(value) {
            broadcast.offer(value)
        }

    override fun openSubscription() = broadcast.openSubscription()
}
