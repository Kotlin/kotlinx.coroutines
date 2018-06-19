# Module kotlinx-coroutines-slf4j

Integration with SLF4J [MDC](https://logback.qos.ch/manual/mdc.html).

## Example

Extends a given Coroutine context so that the SLF4J MDC context is passed into the coroutine.

```kotlin
MDC.put("kotlin", "rocks") // put a value into the MDC context

launch(MDCContext(CommonPool)) {
   logger.info { "..." }   // the MDC context will contain the mapping here
}
```

# Package kotlinx.coroutines.experimental.slf4j

Integration with SLF4J [MDC](https://logback.qos.ch/manual/mdc.html).
