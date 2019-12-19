# Module kotlinx-coroutines-swt

Provides `Dispatchers.SWT` context, `Dispatchers.swt(Display)` context and `Dispatchers.Main` implementation for SWT UI 
applications.

The coroutine dispatcher `Dispatchers.SWT` (or `Dispatchers.Main`) dispatches events to the SWT default display.
Therefore, the SWT default display should be created before calling `Dispatchers.SWT`. Otherwise a new default display
is created (making the thread that invokes `Dispatchers.SWT` its user-interface thread).

Read [Guide to UI programming with coroutines](https://github.com/Kotlin/kotlinx.coroutines/blob/master/ui/coroutines-guide-ui.md)
for tutorial on this module.

# Package kotlinx.coroutines.swt

Provides `Dispatchers.SWT` context, `Dispatchers.swt(Display)` context and `Dispatchers.Main` implementation for SWT UI 
applications.
