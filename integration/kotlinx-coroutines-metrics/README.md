# Module kotlinx-coroutines-metrics

Integration with [Metrics](https://metrics.dropwizard.io/4.0.0/).

## Example

Add instrumentation to the thread pool of a coroutine context.

```kotlin
val metricRegistry = MetricRegistry()
val context = newInstrumentedFixedThreadPoolContext(2, "my-coroutine-thread-pool", metricRegistry)
launch(context) {
    // your code
}
```
