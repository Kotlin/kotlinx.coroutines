# Module kotlinx-coroutines-rx1

Utilities for [RxJava 1.x](https://github.com/ReactiveX/RxJava/tree/1.x).

Coroutine builders:

| **Name**        | **Result**                    | **Scope**        | **Description**
| --------------- | ----------------------------- | ---------------- | ---------------
| [rxCompletable] | `Completable`                 | [CoroutineScope] | Cold completable that starts coroutine on subscribe
| [rxSingle]      | `Single`                      | [CoroutineScope] | Cold single that starts coroutine on subscribe
| [rxObservable]  | `Observable`                  | [ProducerScope]  | Cold observable that starts coroutine on subscribe

Suspending extension functions and suspending iteration:

| **Name** | **Description**
| -------- | ---------------
| [Completable.awaitCompleted][rx.Completable.awaitCompleted] | Awaits for completion of the completable value 
| [Single.await][rx.Single.await] | Awaits for completion of the single value and returns it 
| [Observable.awaitFirst][rx.Observable.awaitFirst] | Returns the first value from the given observable
| [Observable.awaitFirstOrDefault][rx.Observable.awaitFirstOrDefault] | Returns the first value from the given observable or default
| [Observable.awaitFirstOrElse][rx.Observable.awaitFirstOrElse] | Returns the first value from the given observable or default from a function
| [Observable.awaitFirstOrNull][rx.Observable.awaitFirstOrNull] | Returns the first value from the given observable or null
| [Observable.awaitLast][rx.Observable.awaitFirst] | Returns the last value from the given observable
| [Observable.awaitSingle][rx.Observable.awaitSingle] | Returns the single value from the given observable
| [Observable.openSubscription][rx.Observable.openSubscription] | Subscribes to observable and returns [ReceiveChannel] 
./gradlew knit
Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [Job.asCompletable][kotlinx.coroutines.experimental.Job.asCompletable] | Converts job to hot completable
| [Deferred.asSingle][kotlinx.coroutines.experimental.Deferred.asSingle] | Converts deferred value to hot single
| [ReceiveChannel.asObservable][kotlinx.coroutines.experimental.channels.ReceiveChannel.asObservable] | Converts streaming channel to hot observable

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-producer-scope/index.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/index.html
<!--- MODULE kotlinx-coroutines-rx1 -->
<!--- INDEX kotlinx.coroutines.experimental.rx1 -->
[rxCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-coroutine-scope/rx-completable.html
[rxSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-coroutine-scope/rx-single.html
[rxObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-coroutine-scope/rx-observable.html
[rx.Completable.awaitCompleted]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-completable/await-completed.html
[rx.Single.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-single/await.html
[rx.Observable.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-first.html
[rx.Observable.awaitFirstOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-first-or-default.html
[rx.Observable.awaitFirstOrElse]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-first-or-else.html
[rx.Observable.awaitFirstOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-first-or-null.html
[rx.Observable.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-single.html
[rx.Observable.openSubscription]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/open-subscription.html
[kotlinx.coroutines.experimental.Job.asCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-job/as-completable.html
[kotlinx.coroutines.experimental.Deferred.asSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-deferred/as-single.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.asObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.channels.-receive-channel/as-observable.html
<!--- END -->

# Package kotlinx.coroutines.experimental.rx1

Utilities for [RxJava 1.x](https://github.com/ReactiveX/RxJava/tree/1.x).
