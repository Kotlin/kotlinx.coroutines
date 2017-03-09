# Module kotlinx-coroutines-reactive

Utilities for [Reactive Streams](http://www.reactive-streams.org).

Coroutine builders:

| **Name**        | **Result**                    | **Scope**        | **Description**
| --------------- | ----------------------------- | ---------------- | ---------------
| [publish]       | `Publisher`                   | [ProducerScope] | Cold reactive publisher that starts coroutine on subscribe

Suspending extension functions and suspending iteration:

| **Name** | **Description**
| -------- | ---------------
| [Publisher.awaitFirst][org.reactivestreams.Publisher.awaitFirst] | Returns the first value from the given publisher
| [Publisher.awaitLast][org.reactivestreams.Publisher.awaitFirst] | Returns the last value from the given publisher
| [Publisher.awaitSingle][org.reactivestreams.Publisher.awaitSingle] | Returns the single value from the given publisher
| [Publisher.open][org.reactivestreams.Publisher.open] | Subscribes to publisher and returns [ReceiveChannel] 
| [Publisher.iterator][org.reactivestreams.Publisher.iterator] | Subscribes to publisher and returns [ChannelIterator]

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [ReceiveChannel.asPublisher][kotlinx.coroutines.experimental.channels.ReceiveChannel.asPublisher] | Converts streaming channel to hot publisher

<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core -->
<!--- DOCS_ROOT kotlinx-coroutines-core/target/dokka/kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-producer-scope/index.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/index.html
[ChannelIterator]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel-iterator/index.html
<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive -->
<!--- DOCS_ROOT reactive/kotlinx-coroutines-reactive/target/dokka/kotlinx-coroutines-reactive -->
<!--- INDEX kotlinx.coroutines.experimental.reactive -->
[publish]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/publish.html
[org.reactivestreams.Publisher.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/org.reactivestreams.-publisher/await-first.html
[org.reactivestreams.Publisher.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/org.reactivestreams.-publisher/await-single.html
[org.reactivestreams.Publisher.open]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/org.reactivestreams.-publisher/open.html
[org.reactivestreams.Publisher.iterator]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/org.reactivestreams.-publisher/iterator.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.asPublisher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/kotlinx.coroutines.experimental.channels.-receive-channel/as-publisher.html
<!--- END -->

# Package kotlinx.coroutines.experimental.reactive

Utilities for [Reactive Streams](http://www.reactive-streams.org).
