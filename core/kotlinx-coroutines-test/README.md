# Module kotlinx-coroutines-test

Test utilities for `kotlinx.coroutines`. Provides `Dispatchers.setMain` to override the `Main` dispatcher.

## Using in your project

Add `kotlinx-coroutines-test` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-test:1.1.0-alpha'
}
```

**Do not** depend on this project in your main sources, all utilities are intended and designed to be used only from tests. 

Once you have this dependency in the runtime, [`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html) mechanism will
overwrite [Dispatchers.Main] with a testable implementation.

You can override the `Main` implementation using [setMain][setMain] method with any [CoroutineDispatcher] implementation, e.g.:

```kotlin

class SomeTest {
    
    private val mainThreadSurrogate = newSingleThreadContext("UI thread")

    @Before
    fun setUp() {
        Dispatchers.setMain(mainThreadSurrogate)
    }

    @After
    fun tearDown() {
        Dispatchers.resetMain() // reset main dispatcher to the original Main dispatcher
        mainThreadSurrogate.close()
    }
    
    @Test
    fun testSomeUI() = runBlocking {
        launch(Dispatchers.Main) {  // Will be launched in the mainThreadSurrogate dispatcher
            ...
        }
    }
}
```

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
<!--- MODULE kotlinx-coroutines-test -->
<!--- INDEX kotlinx.coroutines.test -->
[setMain]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/kotlinx.coroutines.-dispatchers/set-main.html
<!--- END -->
