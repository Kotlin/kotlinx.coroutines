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
| [Single.await][rx.Single.await] | Awaits for completion of the single value and returns it 
| [Observable.awaitFirst][rx.Observable.awaitFirst] | Returns the first value from the given observable
| [Observable.awaitLast][rx.Observable.awaitFirst] | Returns the last value from the given observable
| [Observable.awaitSingle][rx.Observable.awaitSingle] | Returns the single value from the given observable
| [Observable.open][rx.Observable.open] | Subscribes to observable and returns [ReceiveChannel] 
| [Observable.iterator][rx.Observable.iterator] | Subscribes to observable and returns [ChannelIterator]

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [Job.asCompletable][kotlinx.coroutines.experimental.Job.asCompletable] | Converts job to hot completable
| [Deferred.asSingle][kotlinx.coroutines.experimental.Deferred.asSingle] | Converts deferred value to hot single
| [ReceiveChannel.asObservable][kotlinx.coroutines.experimental.channels.ReceiveChannel.asObservable] | Converts streaming channel to hot observable

<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core -->
<!--- DOCS_ROOT kotlinx-coroutines-core/target/dokka/kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-producer-scope/index.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/index.html
[ChannelIterator]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel-iterator/index.html
<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1 -->
<!--- DOCS_ROOT reactive/kotlinx-coroutines-rx1/target/dokka/kotlinx-coroutines-rx1 -->
<!--- INDEX kotlinx.coroutines.experimental.rx1 -->
[rxCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx-completable.html
[rxSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx-single.html
[rxObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx-observable.html
[rx.Single.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-single/await.html
[rx.Observable.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-first.html
[rx.Observable.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/await-single.html
[rx.Observable.open]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/open.html
[rx.Observable.iterator]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/rx.-observable/iterator.html
[kotlinx.coroutines.experimental.Job.asCompletable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-job/as-completable.html
[kotlinx.coroutines.experimental.Deferred.asSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.-deferred/as-single.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.asObservable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx1/kotlinx.coroutines.experimental.rx1/kotlinx.coroutines.experimental.channels.-receive-channel/as-observable.html
<!--- END -->

# Package kotlinx.coroutines.experimental.rx1

Utilities for [RxJava 1.x](https://github.com/ReactiveX/RxJava/tree/1.x).
