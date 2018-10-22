# Module kotlinx-coroutines-core-test

Test utilities for `kotlinx.coroutines`. Provides `MainDispatcherInjector.inject` to override `Main` dispatcher.

## Using in your project

Add `kotlinx-coroutines-core-test` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core-test:1.0.0-RC1'
}
```

**Do not** depend on this project in your main sources, all utilities are intended and designed to be used only from tests. 

Once you have it in runtime, [`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html) mechanism will
overwrite [Dispatchers.Main] will injectable implementation, which uses `Dispatchers.Unconfined` default.

You can override this implementation using [inject][MainDispatcherInjector.inject] method with any [CoroutineDispatcher] implementation, e.g.:

```kotlin

class SomeTest {
    
    private val mainThreadSurrogate = newSingleThreadContext("UI thread")

    @Before
    fun setUp() {
        MainDispatcherInjector.inject(mainThreadSurrogate)
    }

    @After
    fun tearDown() {
        MainDispatcherInjector.reset() // reset main dispatcher to Unconfined
        mainThreadSurrogate.close()
    }
    
    @Test
    fun testSomeUI() = runBlocking {
        launch(Dispatchers.Main) {  
            ...
        }
    }
}
```

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
<!--- END -->
