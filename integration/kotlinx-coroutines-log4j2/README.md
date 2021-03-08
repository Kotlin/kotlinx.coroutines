# Module kotlinx-coroutines-log4j2

Integration with Log4J2 [Thread Context Map](https://logging.apache.org/log4j/2.x/manual/thread-context.html) (aka MDC).

## Example

Add [MDCContext] to the coroutine context so that the Log4J2 Thread Context Map is captured and passed into the coroutine.

```kotlin
ThreadContext.put("kotlin", "rocks") // put a value into the Thread Context Map

launch(MDCContext()) {
   logger.info { "..." }   // the Thread Context will contain the mapping here
}
```

# Package kotlinx.coroutines.log4j2

Integration with Log4J2 [Thread Context Map](https://logging.apache.org/log4j/2.x/manual/thread-context.html) (aka MDC).

<!--- MODULE kotlinx-coroutines-log4j2 -->
<!--- INDEX kotlinx.coroutines.log4j2 -->

[MDCContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-log4j2/kotlinx.coroutines.log4j2/-m-d-c-context/index.html

<!--- END -->
