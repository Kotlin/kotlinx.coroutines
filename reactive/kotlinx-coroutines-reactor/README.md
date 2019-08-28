# Module kotlinx-coroutines-reactor

Utilities for [Reactor](https://projectreactor.io).

Coroutine builders:

| **Name**        | **Result**  | **Scope**        | **Description**
| --------------- | ------------| ---------------- | ---------------
| [mono]          | `Mono`      | [CoroutineScope] | Cold mono that starts coroutine on subscribe
| [flux]          | `Flux`      | [CoroutineScope] | Cold flux that starts coroutine on subscribe

Note that `Mono` and `Flux` are a subclass of [Reactive Streams](https://www.reactive-streams.org)
`Publisher` and extensions for it are covered by
[kotlinx-coroutines-reactive](../kotlinx-coroutines-reactive) module.

Integration with [Flow]:

| **Name**        | **Result**     | **Description**
| --------------- | -------------- | ---------------
| [Flow.asFlux]   | `Flux`         | Converts the given flow to the TCK-compliant Flux.

This adapter is integrated with Reactor's `Context` and coroutines [ReactorContext].

Conversion functions:

| **Name** | **Description**
| -------- | ---------------
| [Job.asMono][kotlinx.coroutines.Job.asMono] | Converts job to hot mono
| [Deferred.asMono][kotlinx.coroutines.Deferred.asMono] | Converts deferred value to hot mono
| [ReceiveChannel.asFlux][kotlinx.coroutines.channels.ReceiveChannel.asFlux] | Converts streaming channel to hot flux
| [Scheduler.asCoroutineDispatcher][reactor.core.scheduler.Scheduler.asCoroutineDispatcher] | Converts scheduler to [CoroutineDispatcher]

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
<!--- INDEX kotlinx.coroutines.channels -->
<!--- INDEX kotlinx.coroutines.flow -->
[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html
<!--- MODULE kotlinx-coroutines-reactor -->
<!--- INDEX kotlinx.coroutines.reactor -->
[mono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/mono.html
[flux]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/flux.html
[Flow.asFlux]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/kotlinx.coroutines.flow.-flow/as-flux.html
[ReactorContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/-reactor-context/index.html
[kotlinx.coroutines.Job.asMono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/kotlinx.coroutines.-job/as-mono.html
[kotlinx.coroutines.Deferred.asMono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/kotlinx.coroutines.-deferred/as-mono.html
[kotlinx.coroutines.channels.ReceiveChannel.asFlux]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/kotlinx.coroutines.channels.-receive-channel/as-flux.html
[reactor.core.scheduler.Scheduler.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/reactor.core.scheduler.-scheduler/as-coroutine-dispatcher.html
<!--- END -->

# Package kotlinx.coroutines.reactor

Utilities for [Reactor](https://projectreactor.io).
