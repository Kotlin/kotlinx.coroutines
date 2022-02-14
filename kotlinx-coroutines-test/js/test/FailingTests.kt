package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*
import kotlin.test.*

/** These are tests that we want to fail. They are here so that, when the issue is fixed, their failure indicates that
 * everything is better now. */
class FailingTests
