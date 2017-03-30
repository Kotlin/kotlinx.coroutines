# Module kotlinx-coroutines-reactor

Utilities for [Reactor](https://projectreactor.io).

Coroutine builders:

| **Name**        | **Result**                            | **Scope**        | **Description**
| --------------- | -------------------------------------- | ---------------- | ---------------
| [mono]          | `Mono`                                 | [CoroutineScope] | Cold mono that starts coroutine on subscribe
| [flux]          | `Flux`                                 | [CoroutineScope] | Cold flux that starts coroutine on subscribe

Note, that `Mono` and `Flux` are a subclass of [Reactive Streams](http://www.reactive-streams.org)
`Publisher` and extensions for it are covered by
[kotlinx-coroutines-reactive](../kotlinx-coroutines-reactive) module.

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [Job.asMono][kotlinx.coroutines.experimental.Job.asMono] | Converts job to hot mono
| [Deferred.asMono][kotlinx.coroutines.experimental.Deferred.asMono] | Converts deferred value to hot mono
| [ReceiveChannel.asFlux][kotlinx.coroutines.experimental.channels.ReceiveChannel.asFlux] | Converts streaming channel to hot flux
| [Scheduler.asCoroutineDispatcher][reactor.core.scheduler.Scheduler.asCoroutineDispatcher] | Converts scheduler to [CoroutineDispatcher]
| [TimedScheduler.asCoroutineDispatcher][reactor.core.scheduler.TimedScheduler.asCoroutineDispatcher] | Converts scheduler to [CoroutineDispatcher] supporting [Delay]

<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core -->
<!--- DOCS_ROOT kotlinx-coroutines-core/target/dokka/kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-dispatcher/index.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-producer-scope/index.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/index.html
[ChannelIterator]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel-iterator/index.html
<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor -->
<!--- DOCS_ROOT reactive/kotlinx-coroutines-reactor/target/dokka/kotlinx-coroutines-reactor -->
<!--- INDEX kotlinx.coroutines.experimental.reactor -->
[mono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/mono.html
[flux]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/flux.html
[kotlinx.coroutines.experimental.Job.asMono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/kotlinx.coroutines.experimental.-job/as-mono.html
[kotlinx.coroutines.experimental.Deferred.asMono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/kotlinx.coroutines.experimental.-deferred/as-mono.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.asFlux]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/kotlinx.coroutines.experimental.channels.-receive-channel/as-flux.html
[reactor.core.scheduler.Scheduler.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/reactor.core.scheduler.-scheduler/as-coroutine-dispatcher.html
[reactor.core.scheduler.TimedScheduler.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.experimental.reactor/reactor.core.scheduler.-timed-scheduler/as-coroutine-dispatcher.html
<!--- END -->

# Package kotlinx.coroutines.experimental.reactor

Utilities for [Reactor](https://projectreactor.io).
