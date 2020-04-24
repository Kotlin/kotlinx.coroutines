# Module kotlinx-coroutines-rx3

Utilities for [RxJava 3.x](https://github.com/ReactiveX/RxJava).

Coroutine builders:

| **Name**        | **Result**                              | **Scope**        | **Description**
| --------------- | --------------------------------------- | ---------------- | ---------------
| [rxCompletable] | `Completable`                           | [CoroutineScope] | Cold completable that starts coroutine on subscribe
| [rxMaybe]       | `Maybe`                                 | [CoroutineScope] | Cold maybe that starts coroutine on subscribe
| [rxSingle]      | `Single`                                | [CoroutineScope] | Cold single that starts coroutine on subscribe
| [rxObservable]  | `Observable`                            | [ProducerScope]  | Cold observable that starts coroutine on subscribe
| [rxFlowable]    | `Flowable`                              | [ProducerScope]  | Cold observable that starts coroutine on subscribe with **backpressure** support 

Integration with [Flow]:

| **Name**                   | **Result**      | **Description**
| ---------------            | --------------  | ---------------
| [Flow.asFlowable]          | `Flowable`      | Converts the given flow to a cold Flowable.
| [Flow.asObservable]        | `Observable`    | Converts the given flow to a cold Observable.
| [ObservableSource.asFlow]  | `Flow`          | Converts the given cold ObservableSource to flow

Suspending extension functions and suspending iteration:

| **Name** | **Description**
| -------- | ---------------
| [CompletableSource.await][io.reactivex.rxjava3.core.CompletableSource.await] | Awaits for completion of the completable value 
| [MaybeSource.await][io.reactivex.rxjava3.core.MaybeSource.await] | Awaits for the value of the maybe and returns it or null 
| [MaybeSource.awaitOrDefault][io.reactivex.rxjava3.core.MaybeSource.awaitOrDefault] | Awaits for the value of the maybe and returns it or default 
| [SingleSource.await][io.reactivex.rxjava3.core.SingleSource.await] | Awaits for completion of the single value and returns it 
| [ObservableSource.awaitFirst][io.reactivex.rxjava3.core.ObservableSource.awaitFirst] | Awaits for the first value from the given observable
| [ObservableSource.awaitFirstOrDefault][io.reactivex.rxjava3.core.ObservableSource.awaitFirstOrDefault] | Awaits for the first value from the given observable or default
| [ObservableSource.awaitFirstOrElse][io.reactivex.rxjava3.core.ObservableSource.awaitFirstOrElse] | Awaits for the first value from the given observable or default from a function
| [ObservableSource.awaitFirstOrNull][io.reactivex.rxjava3.core.ObservableSource.awaitFirstOrNull] | Awaits for the first value from the given observable or null
| [ObservableSource.awaitLast][io.reactivex.rxjava3.core.ObservableSource.awaitFirst] | Awaits for the last value from the given observable
| [ObservableSource.awaitSingle][io.reactivex.rxjava3.core.ObservableSource.awaitSingle] | Awaits for the single value from the given observable

Note that `Flowable` is a subclass of [Reactive Streams](https://www.reactive-streams.org)
`Publisher` and extensions for it are covered by
[kotlinx-coroutines-reactive](../kotlinx-coroutines-reactive) module.

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [Job.asCompletable][kotlinx.coroutines.Job.asCompletable] | Converts job to hot completable
| [Deferred.asSingle][kotlinx.coroutines.Deferred.asSingle] | Converts deferred value to hot single
| [Scheduler.asCoroutineDispatcher][io.reactivex.rxjava3.core.Scheduler.asCoroutineDispatcher] | Converts scheduler to [CoroutineDispatcher]

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
<!--- INDEX kotlinx.coroutines.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
<!--- INDEX kotlinx.coroutines.flow -->
[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html
<!--- MODULE kotlinx-coroutines-rx3 -->
<!--- INDEX kotlinx.coroutines.rx3 -->
[rxCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/rx-completable.html
[rxMaybe]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/rx-maybe.html
[rxSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/rx-single.html
[rxObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/rx-observable.html
[rxFlowable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/rx-flowable.html
[Flow.asFlowable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/kotlinx.coroutines.flow.-flow/as-flowable.html
[Flow.asObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/kotlinx.coroutines.flow.-flow/as-observable.html
[ObservableSource.asFlow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-observable-source/as-flow.html
[io.reactivex.rxjava3.core.CompletableSource.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-completable-source/await.html
[io.reactivex.rxjava3.core.MaybeSource.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-maybe-source/await.html
[io.reactivex.rxjava3.core.MaybeSource.awaitOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-maybe-source/await-or-default.html
[io.reactivex.rxjava3.core.SingleSource.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-single-source/await.html
[io.reactivex.rxjava3.core.ObservableSource.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-observable-source/await-first.html
[io.reactivex.rxjava3.core.ObservableSource.awaitFirstOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-observable-source/await-first-or-default.html
[io.reactivex.rxjava3.core.ObservableSource.awaitFirstOrElse]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-observable-source/await-first-or-else.html
[io.reactivex.rxjava3.core.ObservableSource.awaitFirstOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-observable-source/await-first-or-null.html
[io.reactivex.rxjava3.core.ObservableSource.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-observable-source/await-single.html
[kotlinx.coroutines.Job.asCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/kotlinx.coroutines.-job/as-completable.html
[kotlinx.coroutines.Deferred.asSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/kotlinx.coroutines.-deferred/as-single.html
[io.reactivex.rxjava3.core.Scheduler.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx3/kotlinx.coroutines.rx3/io.reactivex.rxjava3.core.-scheduler/as-coroutine-dispatcher.html
<!--- END -->

# Package kotlinx.coroutines.rx3

Utilities for [RxJava 3.x](https://github.com/ReactiveX/RxJava).
