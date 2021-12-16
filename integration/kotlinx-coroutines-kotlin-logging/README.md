# Module kotlinx-coroutines-kotlin-logging

Integration with [Kotlin Logging](https://github.com/MicroUtils/kotlin-logging).

## Example

Add a wrapper to a code block so that the SLF4J [MDC](https://logback.qos.ch/manual/mdc.html) uses a specific context
for that block of suspending code with an option to avoid restoring the context after the code block has executed.

```kotlin
withLoggingContextAsync("userId" to "A_USER_ID") {
    // The MDC context will contain the mapping of "userId"=>"A_USER_ID"
    // during this log statement.
    logger.info { "..." }
}
// The block will restore The MDC context so that it no longer contains
// the mapping of "userId"=>"A_USER_ID"

withLoggingContextAsync("userId" to "ANOTHER_USER_ID", restorePrevious = false) {
    logger.info { "..." }
}
// The MDC context will retain the mapping of "userId"=>"ANOTHER_USER_ID",
// as the previous context restoration was disabled.
```

# Package kotlinx.coroutines.kotlinlogging

Integration with [Kotlin Logging](https://github.com/MicroUtils/kotlin-logging).

<!--- MODULE kotlinx-coroutines-kotlinlogging -->
<!--- INDEX kotlinx.coroutines.kotlinlogging -->
<!--- END -->
