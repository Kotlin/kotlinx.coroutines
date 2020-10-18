# Module kotlinx-coroutines-reactive

Utilities for [Reactive Streams](https://www.reactive-streams.org).

Coroutine builders:

| **Name**        | **Result**                    | **Scope**        | **Description**
| --------------- | ----------------------------- | ---------------- | ---------------
| [kotlinx.coroutines.reactive.publish]       | `Publisher`                   | [ProducerScope] | Cold reactive publisher that starts the coroutine on subscribe

Integration with [Flow]:

| **Name**            | **Result**        | **Description**
| ---------------     | --------------    | ---------------
| [Publisher.asFlow]  | `Flow`            | Converts the given publisher to a flow
| [Flow.asPublisher]  | `Publisher`       | Converts the given flow to a TCK-compliant publisher

If these adapters are used along with `kotlinx-coroutines-reactor` in the classpath, then Reactor's `Context` is properly
propagated as coroutine context element (`ReactorContext`) and vice versa.

Suspending extension functions and suspending iteration:

| **Name** | **Description**
| -------- | ---------------
| [Publisher.awaitFirst][org.reactivestreams.Publisher.awaitFirst] | Returns the first value from the given publisher
| [Publisher.awaitFirstOrDefault][org.reactivestreams.Publisher.awaitFirstOrDefault] | Returns the first value from the given publisher or default
| [Publisher.awaitFirstOrElse][org.reactivestreams.Publisher.awaitFirstOrElse] | Returns the first value from the given publisher or default from a function
| [Publisher.awaitFirstOrNull][org.reactivestreams.Publisher.awaitFirstOrNull] | Returns the first value from the given publisher or null
| [Publisher.awaitLast][org.reactivestreams.Publisher.awaitFirst] | Returns the last value from the given publisher
| [Publisher.awaitSingle][org.reactivestreams.Publisher.awaitSingle] | Returns the single value from the given publisher

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
<!--- INDEX kotlinx.coroutines.flow -->
[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html
<!--- INDEX kotlinx.coroutines.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
<!--- MODULE kotlinx-coroutines-reactive -->
<!--- INDEX kotlinx.coroutines.reactive -->
[kotlinx.coroutines.reactive.publish]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/publish.html
[Publisher.asFlow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/as-flow.html
[Flow.asPublisher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/kotlinx.coroutines.flow.-flow/as-publisher.html
[org.reactivestreams.Publisher.awaitFirst]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first.html
[org.reactivestreams.Publisher.awaitFirstOrDefault]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first-or-default.html
[org.reactivestreams.Publisher.awaitFirstOrElse]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first-or-else.html
[org.reactivestreams.Publisher.awaitFirstOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-first-or-null.html
[org.reactivestreams.Publisher.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-single.html
<!--- END -->

# Package kotlinx.coroutines.reactive

Utilities for [Reactive Streams](https://www.reactive-streams.org).
