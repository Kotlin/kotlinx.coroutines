# Module kotlinx-coroutines-reactive

Utilities for [Reactive Streams](https://www.reactive-streams.org).

Coroutine builders:

| **Name**        | **Result**                    | **Scope**        | **Description**
| --------------- | ----------------------------- | ---------------- | ---------------
| [publish]       | `Publisher`                   | [ProducerScope] | Cold reactive publisher that starts coroutine on subscribe

Suspending extension functions and suspending iteration:

| **Name** | **Description**
| -------- | ---------------
| [Publisher.awaitFirst][org.reactivestreams.Publisher.awaitFirst] | Returns the first value from the given publisher
| [Publisher.awaitFirstOrDefault][org.reactivestreams.Publisher.awaitFirstOrDefault] | Returns the first value from the given publisher or default
| [Publisher.awaitFirstOrElse][org.reactivestreams.Publisher.awaitFirstOrElse] | Returns the first value from the given publisher or default from a function
| [Publisher.awaitFirstOrNull][org.reactivestreams.Publisher.awaitFirstOrNull] | Returns the first value from the given publisher or null
| [Publisher.awaitLast][org.reactivestreams.Publisher.awaitFirst] | Returns the last value from the given publisher
| [Publisher.awaitSingle][org.reactivestreams.Publisher.awaitSingle] | Returns the single value from the given publisher
| [Publisher.openSubscription][org.reactivestreams.Publisher.openSubscription] | Subscribes to publisher and returns [ReceiveChannel] 

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [ReceiveChannel.asPublisher][kotlinx.coroutines.channels.ReceiveChannel.asPublisher] | Converts streaming channel to hot publisher

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
<!--- INDEX kotlinx.coroutines.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/index.html
<!--- MODULE kotlinx-coroutines-reactive -->
<!--- INDEX kotlinx.coroutines.reactive -->
[publish]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/publish.html
[org.reactivestreams.Publisher.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first.html
[org.reactivestreams.Publisher.awaitFirstOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first-or-default.html
[org.reactivestreams.Publisher.awaitFirstOrElse]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first-or-else.html
[org.reactivestreams.Publisher.awaitFirstOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first-or-null.html
[org.reactivestreams.Publisher.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-single.html
[org.reactivestreams.Publisher.openSubscription]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/open-subscription.html
[kotlinx.coroutines.channels.ReceiveChannel.asPublisher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/kotlinx.coroutines.channels.-receive-channel/as-publisher.html
<!--- END -->

# Package kotlinx.coroutines.reactive

Utilities for [Reactive Streams](https://www.reactive-streams.org).
