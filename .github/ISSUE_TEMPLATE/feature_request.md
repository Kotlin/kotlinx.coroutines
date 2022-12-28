---
name: Feature request
about: We're missing something?
title: ''
labels: enhancement
assignees: ''

---

<!--
**Double-check**

* Maybe this feature is already here?
  - Did you check the latest version of the library?
  - Maybe it's in a form you didn't expect? Consider asking on [StackOverflow](https://stackoverflow.com/) or the [Kotlin Slack](https://surveys.jetbrains.com/s3/kotlin-slack-sign-up). The community will likely come up with some code that solves your need, and faster than it would take us to answer the issue!
* Do you actually *need* this feature? Maybe restructuring your code would neatly eliminate the problem the feature would be solving.
* Is the coroutines library the best place for this feature? Maybe it would be better suited for some third-party library?
-->

**Use case**

Explain what *specifically* you are trying to do and why.
- Example: "I have a `SharedFlow<Double>` that represents readings from an external device. The readings arrive in a set interval of 100 milliseconds. However, I also need to be able to calibrate the state of the external device by setting the readings from inside the program. When I set the state, the `SharedFlow<Double>` must immediately emit the value that was set and ignore any values coming from the device in the following 10 milliseconds since they are considered outdated, as the device is only guaranteed to recalibrate to the updated value after that period."
- Non-example: "I have a `SharedFlow<T>` that has several sources of its values, and these sources need to have priorities attached to them so that one source always takes precedence over the other in a close race."
- Non-example: "RxJava has feature X, so the coroutines library should also."

**The Shape of the API**

What could the desired API look like? What would some sample code using the new feature look like? If you don't have a clear idea, pseudocode or just explaining the API shape is also perfectly fine.

**Prior Art**

(Optional) Maybe you have seen something like the feature you need, but in other libraries, or there is something very similar but not quite sufficient in `kotlinx.coroutines`? Maybe there's already a way to do it, but it's too cumbersome and unclear?
