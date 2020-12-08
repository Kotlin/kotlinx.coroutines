# Module kotlinx-coroutines-slf4j

Integration with SLF4J [MDC](https://logback.qos.ch/manual/mdc.html).

## Example

Add [MDCContext] to the coroutine context so that the SLF4J MDC context is captured and passed into the coroutine.

```kotlin
MDC.put("kotlin", "rocks") // put a value into the MDC context

launch(MDCContext()) {
   logger.info { "..." }   // the MDC context will contain the mapping here
}
```

# Package kotlinx.coroutines.slf4j

Integration with SLF4J [MDC](https://logback.qos.ch/manual/mdc.html).

<!--- MODULE kotlinx-coroutines-slf4j -->
<!--- INDEX kotlinx.coroutines.slf4j -->

[MDCContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-slf4j/kotlinx.coroutines.slf4j/-m-d-c-context/index.html

<!--- END -->
