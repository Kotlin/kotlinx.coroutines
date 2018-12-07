# ServiceLoader support
-keepnames class kotlinx.coroutines.test.internal.InjectableDispatcherFactory {}

# Most of volatile fields are updated with AFU and should not be mangled
-keepclassmembernames class kotlinx.** {
    volatile <fields>;
}
