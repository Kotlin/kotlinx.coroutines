/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import org.junit.*
import org.reactivestreams.*
import reactor.core.*
import reactor.core.publisher.*
import java.util.concurrent.locks.*

class MonoAwaitCancellationStressTest {
    private val iterations = 10_000 * stressTestMultiplier

    @Test
    @Ignore // Will be able to test this after https://github.com/reactor/reactor-core/issues/3117 is fixed
    fun testAwaitCancellationOrder() = runBlocking {
        repeat(iterations) {
            val job = launch(Dispatchers.Default) {
                TestMono.awaitSingleOrNull()
            }
            job.cancelAndJoin()
        }
    }

    private object TestMono: Mono<Int>() {
        override fun subscribe(s: CoreSubscriber<in Int>) {
            val lock = ReentrantLock()
            s.onSubscribe(object : Subscription {
                override fun request(n: Long) {
                    check(lock.tryLock())
                    s.onNext(42)
                    lock.unlock()
                }

                override fun cancel() {
                    check(lock.tryLock())
                    lock.unlock()
                }
            })
        }
    }
}
