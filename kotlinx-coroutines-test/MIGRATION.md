# Migration to the new kotlinx-coroutines-test API

In version 1.6.0, the API of the test module changed significantly.
This is a guide for gradually adapting the existing test code to the new API.
This guide is written step-by-step; the idea is to separate the migration into several sets of small changes.

## Remove custom `UncaughtExceptionCaptor`, `DelayController`, and `TestCoroutineScope` implementations

We couldn't find any code that defined new implementations of these interfaces, so they are deprecated. It's likely that
you don't need to do anything for this section.

### `UncaughtExceptionCaptor`

If the code base has an `UncaughtExceptionCaptor`, its special behavior as opposed to just `CoroutineExceptionHandler`
was that, at the end of `runBlockingTest` or `cleanupTestCoroutines` (or both), its `cleanupTestCoroutines` procedure
was called.

We currently don't provide a replacement for this.
However, `runTest` follows structured concurrency better than `runBlockingTest` did, so exceptions from child coroutines
are propagated structurally, which makes uncaught exception handlers less useful.

If you have a use case for this, please tell us about it at the issue tracker.
Meanwhile, it should be possible to use a custom exception captor, which should only implement
`CoroutineExceptionHandler` now, like this:

```kotlin
@Test
fun testFoo() = runTest {
    val customCaptor = MyUncaughtExceptionCaptor()
    launch(customCaptor) {
        // ...
    }
    advanceUntilIdle()
    customCaptor.cleanupTestCoroutines()
}
```

### `DelayController`

We don't provide a way to define custom dispatching strategies that support virtual time.
That said, we significantly enhanced this mechanism:
* Using multiple test dispatchers simultaneously is supported.
  For the dispatchers to have a shared knowledge of the virtual time, either the same `TestCoroutineScheduler` should be
  passed to each of them, or all of them should be constructed after `Dispatchers.setMain` is called with some test
  dispatcher.
* Both a simple `StandardTestDispatcher` that is always paused, and unconfined `UnconfinedTestDispatcher` are provided.

If you have a use case for `DelayController` that's not covered by what we provide, please tell us about it in the issue
tracker.

### `TestCoroutineScope`

This scope couldn't be meaningfully used in tandem with `runBlockingTest`: according to the definition of
`TestCoroutineScope.runBlockingTest`, only the scope's `coroutineContext` is used.
So, there could be two reasons for defining a custom implementation:

* Avoiding the restrictions on placed `coroutineContext` in the `TestCoroutineScope` constructor function.
  These restrictions consisted of requirements for `CoroutineExceptionHandler` being an `UncaughtExceptionCaptor`, and
  `ContinuationInterceptor` being a `DelayController`, so it is also possible to fulfill these restrictions by defining
  conforming instances. In this case, follow the instructions about replacing them.
* Using without `runBlockingTest`. In this case, you don't even need to implement `TestCoroutineScope`: nothing else
  accepts a `TestCoroutineScope` specifically as an argument.

## Remove usages of `TestCoroutineExceptionHandler` and `TestCoroutineScope.uncaughtExceptions`

It is already illegal to use a `TestCoroutineScope` without performing `cleanupTestCoroutines`, so the valid uses of
`TestCoroutineExceptionHandler` include:

* Accessing `uncaughtExceptions` in the middle of the test to make sure that there weren't any uncaught exceptions
  *yet*.
  If there are any, they will be thrown by the cleanup procedure anyway.
  We don't support this use case, given how comparatively rare it is, but it can be handled in the same way as the
  following one.
* Accessing `uncaughtExceptions` when the uncaught exceptions are actually expected.
  In this case, `cleanupTestCoroutines` will fail with an exception that is being caught later.
  It would be better in this case to use a custom `CoroutineExceptionHandler` so that actual problems that could be
  found by the cleanup procedure are not superseded by the exceptions that are expected.
  An example is shown below.

```kotlin
val exceptions = mutableListOf<Throwable>()
val customCaptor = CoroutineExceptionHandler { ctx, throwable ->
    exceptions.add(throwable) // add proper synchronization if the test is multithreaded
}

@Test
fun testFoo() = runTest {
    launch(customCaptor) {
        // ...
    }
    advanceUntilIdle()
    // check the list of the caught exceptions
}
```

## Auto-replace `TestCoroutineScope` constructor function with `createTestCoroutineScope`

This should not break anything, as `TestCoroutineScope` is now defined in terms of `createTestCoroutineScope`.
If it does break something, it means that you already supplied a `TestCoroutineScheduler` to some scope; in this case,
also pass this scheduler as the argument to the dispatcher.

## Replace usages of `pauseDispatcher` and `resumeDispatcher` with a `StandardTestDispatcher`

* In places where `pauseDispatcher` in its block form is called, replace it with a call to
  `withContext(StandardTestDispatcher(testScheduler))`
  (`testScheduler` is available as a field of `TestCoroutineScope`,
  or `scheduler` is available as a field of `TestCoroutineDispatcher`),
  followed by `advanceUntilIdle()`.
  This is not an automatic replacement, as there can be tricky situations where the test dispatcher is already paused
  when `pauseDispatcher { X }` is called. In such cases, simply replace `pauseDispatcher { X }` with `X`.
* Often, `pauseDispatcher()` in a non-block form is used at the start of the test.
  Then, attempt to remove `TestCoroutineDispatcher` from the arguments to `createTestCoroutineScope`,
  if a standalone `TestCoroutineScope` or the `scope.runBlockingTest` form is used,
  or pass a `StandardTestDispatcher` as an argument to `runBlockingTest`.
  This will lead to the test using a `StandardTestDispatcher`, which does not allow pausing and resuming,
  instead of the deprecated `TestCoroutineDispatcher`.
* Sometimes, `pauseDispatcher()` and `resumeDispatcher()` are employed used throughout the test.
  In this case, attempt to wrap everything until the next `resumeDispatcher()` in
  a `withContext(StandardTestDispatcher(testScheduler))` block, or try using some other combinations of
  `StandardTestDispatcher` (where dispatches are needed) and `UnconfinedTestDispatcher` (where it isn't important where
  execution happens).

## Replace `advanceTimeBy(n)` with `advanceTimeBy(n); runCurrent()`

For `TestCoroutineScope` and `DelayController`, the `advanceTimeBy` method is deprecated.
It is not deprecated for `TestCoroutineScheduler` and `TestScope`, but has a different meaning: it does not run the
tasks scheduled *at* `currentTime + n`.

There is an automatic replacement for this deprecation, which produces correct but inelegant code.

Alternatively, you can wait until replacing `TestCoroutineScope` with `TestScope`: it's possible that you will not
encounter this edge case.

## Replace `runBlockingTest` with `runTest(UnconfinedTestDispatcher())`

This is a major change, affecting many things, and can be done in parallel with replacing `TestCoroutineScope` with
`TestScope`.

Significant differences of `runTest` from `runBlockingTest` are each given a section below.

### It works properly with other dispatchers and asynchronous completions.

No action on your part is required, other than replacing `runBlocking` with `runTest` as well.

### It uses `StandardTestDispatcher` by default, not `TestCoroutineDispatcher`.

By now, calls to `pauseDispatcher` and `resumeDispatcher` should be purged from the code base, so only the unpaused
variant of `TestCoroutineDispatcher` should be used.
This version of the dispatcher, which can be observed has the property of eagerly entering `launch` and `async` blocks:
code until the first suspension is executed without dispatching.

We ensured sure that, when run with an `UnconfinedTestDispatcher`, `runTest` also eagerly enters `launch` and `async`
blocks, but *this only works at the top level*: if a child coroutine also called `launch` or `async`, we don't provide
any guarantees about their dispatching order.

So, using `UnconfinedTestDispatcher` as an argument to `runTest` will probably lead to the test being executed as it
did, but in the possible case that the test relies on the specific dispatching order of `TestCoroutineDispatcher`, it
will need to be tweaked.
If the test expects some code to have run at some point, but it hasn't, use `runCurrent` to force the tasks scheduled
at this moment of time to run.

### The job hierarchy is completely different.

- Structured concurrency is used, with the scope provided as the receiver of `runTest` actually being the scope of the
  created coroutine.
- Not `SupervisorJob` but a normal `Job` is used for the `TestCoroutineScope`.
- The job passed as an argument is used as a parent job.

Most tests should not be affected by this. In case your test is, try explicitly launching a child coroutine with a
`SupervisorJob`; this should make the job hierarchy resemble what it used to be.

```kotlin
@Test
fun testFoo() = runTest {
    val deferred = async(SupervisorJob()) {
        // test code
    }
    advanceUntilIdle()
    deferred.getCompletionExceptionOrNull()?.let {
      throw it
    }
}
```

### Only a single call to `runTest` is permitted per test.

In order to work on JS, only a single call to `runTest` must happen during one test, and its result must be returned
immediately:

```kotlin
@Test
fun testFoo(): TestResult {
    // arbitrary code here
    return runTest {
        // ...
    }
}
```

When used only on the JVM, `runTest` will work when called repeatedly, but this is not supported.
Please only call `runTest` once per test, and if for some reason you can't, please tell us about in on the issue
tracker.

### It uses `TestScope`, not `TestCoroutineScope`, by default.

There is a `runTestWithLegacyScope` method that allows migrating from `runBlockingTest` to `runTest` before migrating
from `TestCoroutineScope` to `TestScope`, if exactly the `TestCoroutineScope` needs to be passed somewhere else and
`TestScope` will not suffice.

## Replace `TestCoroutineScope.cleanupTestCoroutines` with `runTest`

Likely can be done together with the next step.

Remove all calls to `TestCoroutineScope.cleanupTestCoroutines` from the code base.
Instead, as the last step of each test, do `return scope.runTest`; if possible, the whole test body should go inside
the `runTest` block.

The cleanup procedure in `runTest` will not check that the virtual time doesn't advance during cleanup.
If a test must check that no other delays are remaining after it has finished, the following form may help:
```kotlin
runTest {
    testBody()
    val timeAfterTest = currentTime()
    advanceUntilIdle() // run the remaining tasks
    assertEquals(timeAfterTest, currentTime()) // will fail if there were tasks scheduled at a later moment
}
```
Note that this will report time advancement even if the job scheduled at a later point was cancelled.

It may be the case that `cleanupTestCoroutines` must be executed after de-initialization in `@AfterTest`, which happens
outside the test itself.
In this case, we propose that you write a wrapper of the form:

```kotlin
fun runTestAndCleanup(body: TestScope.() -> Unit) = runTest {
    try {
        body()
    } finally {
        // the usual cleanup procedures that used to happen before `cleanupTestCoroutines`
    }
}
```

## Replace `runBlockingTest` with `runBlockingTestOnTestScope`, `createTestCoroutineScope` with `TestScope`

Also, replace `runTestWithLegacyScope` with just `runTest`.
All of this can be done in parallel with replacing `runBlockingTest` with `runTest`.

This step should remove all uses of `TestCoroutineScope`, explicit or implicit.

Replacing `runTestWithLegacyScope` and `runBlockingTest` with `runTest` and `runBlockingTestOnTestScope` should be
straightforward if there is no more code left that requires passing exactly `TestCoroutineScope` to it.
Some tests may fail because `TestCoroutineScope.cleanupTestCoroutines` and the cleanup procedure in `runTest`
handle cancelled tasks differently: if there are *cancelled* jobs pending at the moment of
`TestCoroutineScope.cleanupTestCoroutines`, they are ignored, whereas `runTest` will report them.

Of all the methods supported by `TestCoroutineScope`, only `cleanupTestCoroutines` is not provided on `TestScope`,
and its usages should have been removed during the previous step.

## Replace `runBlocking` with `runTest`

Now that `runTest` works properly with asynchronous completions, `runBlocking` is only occasionally useful.
As is, most uses of `runBlocking` in tests come from the need to interact with dispatchers that execute on other
threads, like `Dispatchers.IO` or `Dispatchers.Default`.

## Replace `TestCoroutineDispatcher` with `UnconfinedTestDispatcher` and `StandardTestDispatcher`

`TestCoroutineDispatcher` is a dispatcher with two modes:
* ("unpaused") Almost (but not quite) unconfined, with the ability to eagerly enter `launch` and `async` blocks.
* ("paused") Behaving like a `StandardTestDispatcher`.

In one of the earlier steps, we replaced `pauseDispatcher` with `StandardTestDispatcher` usage, and replaced the
implicit `TestCoroutineScope` dispatcher in `runBlockingTest` with `UnconfinedTestDispatcher` during migration to
`runTest`.

Now, the rest of the usages should be replaced with whichever dispatcher is most appropriate.

## Simplify code by removing unneeded entities

Likely, now some code has the form

```kotlin
val dispatcher = StandardTestDispatcher()
val scope = TestScope(dispatcher)

@BeforeTest
fun setUp() {
    Dispatchers.setMain(dispatcher)
}

@AfterTest
fun tearDown() {
    Dispatchers.resetMain()
}

@Test
fun testFoo() = scope.runTest {
    // ...
}
```

The point of this pattern is to ensure that the test runs with the same `TestCoroutineScheduler` as the one used for
`Dispatchers.Main`.

However, now this can be simplified to just

```kotlin
@BeforeTest
fun setUp() {
  Dispatchers.setMain(StandardTestDispatcher())
}

@AfterTest
fun tearDown() {
  Dispatchers.resetMain()
}

@Test
fun testFoo() = runTest {
  // ...
}
```

The reason this works is that all entities that depend on `TestCoroutineScheduler` will attempt to acquire one from
the current `Dispatchers.Main`.