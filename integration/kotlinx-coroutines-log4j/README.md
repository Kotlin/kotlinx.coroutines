# Module kotlinx-coroutines-log4j

Integration with Log4J 2's [ThreadContext](https://logging.apache.org/log4j/2.x/manual/thread-context.html).

## Example

Add [Log4JThreadContext] to the coroutine context so that the Log4J `ThreadContext` state is captured and passed into the coroutine.

```kotlin
ThreadContext.put("kotlin", "rocks")

launch(Log4JThreadContext()) {
   logger.info(...)   // the ThreadContext will contain the mapping here
}
```

# Package kotlinx.coroutines.log4jj

Integration with Log4J 2's [ThreadContext](https://logging.apache.org/log4j/2.x/manual/thread-context.html).

<!--- MODULE kotlinx-coroutines-log4j -->
<!--- INDEX kotlinx.coroutines.log4j -->
[Log4JThreadContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-log4j/kotlinx.coroutines.log4j/-log4-j-thread-context/index.html
<!--- END -->
