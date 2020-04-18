# Module kotlinx-coroutines-log4j

Integration with Log4J 2's [ThreadContext](https://logging.apache.org/log4j/2.x/manual/thread-context.html).

## Example

Add a [DiagnosticContext] to the coroutine context so that the Log4J `ThreadContext` state is set for the duration of
coroutine context.

```kotlin
launch(MutableDiagnosticContext().put("kotlin", "rocks")) {
  logger.info(...)  // The ThreadContext will contain the mapping here
}

// If not modifying the context state, use an immutable context for fewer allocations
launch(immutableDiagnosticContext()) {
  logger.info(...)
}
```

# Package kotlinx.coroutines.log4jj

Integration with Log4J 2's [ThreadContext](https://logging.apache.org/log4j/2.x/manual/thread-context.html).

<!--- MODULE kotlinx-coroutines-log4j -->
<!--- INDEX kotlinx.coroutines.log4j -->
[DiagnosticContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-log4j/kotlinx.coroutines.log4j/-diagnostic-context/index.html
<!--- END -->
