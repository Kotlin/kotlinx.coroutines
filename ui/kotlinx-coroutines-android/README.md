# Module kotlinx-coroutines-android

Provides `Dispatchers.Main` context for Android applications.

Read [Guide to UI programming with coroutines](https://github.com/Kotlin/kotlinx.coroutines/blob/master/ui/coroutines-guide-ui.md)
for tutorial on this module.

# Optimization

R8 and ProGuard rules are bundled into this module. 
R8 is a replacement for ProGuard in Android ecosystem, it is enabled by default since Android gradle plugin 3.4.0
(3.3.0-beta also had it enabled). 
For best results it is recommended to use a recent version of R8, which produces a smaller binary.

When optimizations are enabled with R8 version 1.6.0 or later
the following debugging features are permanently turned off to reduce the size of the resulting binary:

* [Debugging mode](../../docs/debugging.md#debug-mode)
* [Stacktrace recovery](../../docs/debugging.md#stacktrace-recovery)
* The internal assertions in the library are also permanently removed.

You can examine the corresponding rules in this 
[`coroutines.pro`](resources/META-INF/com.android.tools/r8-from-1.6.0/coroutines.pro) file.

# Package kotlinx.coroutines.android

Provides `Dispatchers.Main` context for Android applications.
