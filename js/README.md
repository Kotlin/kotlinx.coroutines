# Coroutines core for Kotlin/JS

This directory contains modules that provide core coroutines support on Kotlin/JS.

## Using in your projects

Use [`org.jetbrains.kotlinx:kotlinx-coroutines-core-js:<version>`](kotlinx-coroutines-core-js/README.md)
module in your Gradle/Maven dependencies 
or install [`kotlinx-coroutines-core`](https://www.npmjs.com/package/kotlinx-coroutines-core) package via NPM.

Since Kotlin/JS does not generally provide binary compatibility between versions, 
you should use the same version of Kotlin compiler as was used to build `kotlinx.coroutines`. 
See [gradle.properties](../gradle.properties). 

## Examples

* [example-frontend-js](example-frontend-js/README.md) -- frontend application written in Kotlin/JS
that uses coroutines to implement animations in imperative style.