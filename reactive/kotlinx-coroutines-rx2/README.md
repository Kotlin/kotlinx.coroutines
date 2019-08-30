# Module kotlinx-coroutines-rx2

Utilities for [RxJava 2.x](https://github.com/ReactiveX/RxJava).

Coroutine builders:

| **Name**        | **Result**                              | **Scope**        | **Description**
| --------------- | --------------------------------------- | ---------------- | ---------------
| [rxCompletable] | `Completable`                           | [CoroutineScope] | Cold completable that starts coroutine on subscribe
| [rxMaybe]       | `Maybe`                                 | [CoroutineScope] | Cold maybe that starts coroutine on subscribe
| [rxSingle]      | `Single`                                | [CoroutineScope] | Cold single that starts coroutine on subscribe
| [rxObservable]  | `Observable`                            | [ProducerScope]  | Cold observable that starts coroutine on subscribe
| [rxFlowable]    | `Flowable`                              | [ProducerScope]  | Cold observable that starts coroutine on subscribe with **backpressure** support 

Suspending extension functions and suspending iteration:

| **Name** | **Description**
| -------- | ---------------
| [CompletableSource.await][io.reactivex.CompletableSource.await] | Awaits for completion of the completable value 
| [MaybeSource.await][io.reactivex.MaybeSource.await] | Awaits for the value of the maybe and returns it or null 
| [MaybeSource.awaitOrDefault][io.reactivex.MaybeSource.awaitOrDefault] | Awaits for the value of the maybe and returns it or default 
| [MaybeSource.openSubscription][io.reactivex.MaybeSource.openSubscription] | Subscribes to maybe and returns [ReceiveChannel] 
| [SingleSource.await][io.reactivex.SingleSource.await] | Awaits for completion of the single value and returns it 
| [ObservableSource.awaitFirst][io.reactivex.ObservableSource.awaitFirst] | Awaits for the first value from the given observable
| [ObservableSource.awaitFirstOrDefault][io.reactivex.ObservableSource.awaitFirstOrDefault] | Awaits for the first value from the given observable or default
| [ObservableSource.awaitFirstOrElse][io.reactivex.ObservableSource.awaitFirstOrElse] | Awaits for the first value from the given observable or default from a function
| [ObservableSource.awaitFirstOrNull][io.reactivex.ObservableSource.awaitFirstOrNull] | Awaits for the first value from the given observable or null
| [ObservableSource.awaitLast][io.reactivex.ObservableSource.awaitFirst] | Awaits for the last value from the given observable
| [ObservableSource.awaitSingle][io.reactivex.ObservableSource.awaitSingle] | Awaits for the single value from the given observable
| [ObservableSource.openSubscription][io.reactivex.ObservableSource.openSubscription] | Subscribes to observable and returns [ReceiveChannel] 

Note that `Flowable` is a subclass of [Reactive Streams](https://www.reactive-streams.org)
`Publisher` and extensions for it are covered by
[kotlinx-coroutines-reactive](../kotlinx-coroutines-reactive) module.

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [Job.asCompletable][kotlinx.coroutines.Job.asCompletable] | Converts job to hot completable
| [Deferred.asSingle][kotlinx.coroutines.Deferred.asSingle] | Converts deferred value to hot single
| [ReceiveChannel.asObservable][kotlinx.coroutines.channels.ReceiveChannel.asObservable] | Converts streaming channel to hot observable
| [Scheduler.asCoroutineDispatcher][io.reactivex.Scheduler.asCoroutineDispatcher] | Converts scheduler to [CoroutineDispatcher]

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
<!--- INDEX kotlinx.coroutines.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/index.html
<!--- MODULE kotlinx-coroutines-rx2 -->
<!--- INDEX kotlinx.coroutines.rx2 -->
[rxCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-completable.html
[rxMaybe]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-maybe.html
[rxSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-single.html
[rxObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-observable.html
[rxFlowable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-flowable.html
[io.reactivex.CompletableSource.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-completable-source/await.html
[io.reactivex.MaybeSource.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-maybe-source/await.html
[io.reactivex.MaybeSource.awaitOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-maybe-source/await-or-default.html
[io.reactivex.MaybeSource.openSubscription]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-maybe-source/open-subscription.html
[io.reactivex.SingleSource.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-single-source/await.html
[io.reactivex.ObservableSource.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-observable-source/await-first.html
[io.reactivex.ObservableSource.awaitFirstOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-observable-source/await-first-or-default.html
[io.reactivex.ObservableSource.awaitFirstOrElse]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-observable-source/await-first-or-else.html
[io.reactivex.ObservableSource.awaitFirstOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-observable-source/await-first-or-null.html
[io.reactivex.ObservableSource.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-observable-source/await-single.html
[io.reactivex.ObservableSource.openSubscription]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-observable-source/open-subscription.html
[kotlinx.coroutines.Job.asCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/kotlinx.coroutines.-job/as-completable.html
[kotlinx.coroutines.Deferred.asSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/kotlinx.coroutines.-deferred/as-single.html
[kotlinx.coroutines.channels.ReceiveChannel.asObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/kotlinx.coroutines.channels.-receive-channel/as-observable.html
[io.reactivex.Scheduler.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/io.reactivex.-scheduler/as-coroutine-dispatcher.html
<!--- END -->

# Package kotlinx.coroutines.rx2

Utilities for [RxJava 2.x](https://github.com/ReactiveX/RxJava).
