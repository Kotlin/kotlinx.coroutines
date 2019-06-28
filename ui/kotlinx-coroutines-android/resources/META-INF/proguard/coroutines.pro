# Files in this directory will be ignored starting with Android Gradle Plugin 3.6.0+
# For rules that should work on AGP < 3.6.0, put them here.
# For rules that should also work on AGP >= 3.6.0,
# put them in META-INF/com.android.tools/(r8|proguard)/

-keep class kotlinx.coroutines.android.AndroidDispatcherFactory {*;}
