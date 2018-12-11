# ServiceLoader support
-keepnames class kotlinx.coroutines.test.internal.TestMainDispatcherFactory {}

# Most of volatile fields are updated with AFU and should not be mangled
-keepclassmembernames class kotlinx.** {
    volatile <fields>;
}
