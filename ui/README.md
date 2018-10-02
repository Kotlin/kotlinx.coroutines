# Coroutines for UI

This directory contains modules for coroutine programming with various single-threaded UI libraries.
After adding dependency to the UI library, corresponding UI dispatcher will be available via `Dispatchers.Main`.
Module name below corresponds to the artifact name in Maven/Gradle.

## Modules

* [kotlinx-coroutines-android](kotlinx-coroutines-android/README.md) -- `Dispatchers.Main` context for Android applications.
* [kotlinx-coroutines-javafx](kotlinx-coroutines-javafx/README.md) -- `Dispatchers.JavaFx` context for JavaFX UI applications.
* [kotlinx-coroutines-swing](kotlinx-coroutines-swing/README.md) -- `Dispatchers.Swing` context for Swing UI applications.
