/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package junit4

import kotlinx.coroutines.debug.*
import kotlinx.coroutines.debug.junit4.*
import org.junit.rules.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.io.*
import kotlin.test.*

internal fun TestFailureValidation(timeoutMs: Long, cancelOnTimeout: Boolean, vararg specs: TestResultSpec): RuleChain =
    RuleChain
        .outerRule(TestFailureValidation(specs.associateBy { it.testName }))
        .around(
            CoroutinesTimeout(
                timeoutMs,
                cancelOnTimeout
            )
        )

/**
 * Rule that captures test result, serr and sout and validates it against provided [testsSpec]
 */
internal class TestFailureValidation(private val testsSpec: Map<String, TestResultSpec>) : TestRule {

    companion object {
        init {
            DebugProbes.sanitizeStackTraces = false
        }
    }
    override fun apply(base: Statement, description: Description): Statement {
        return TestFailureStatement(base, description)
    }

    inner class TestFailureStatement(private val test: Statement, private val description: Description) : Statement() {
        private lateinit var sout: PrintStream
        private lateinit var serr: PrintStream
        private val capturedOut = ByteArrayOutputStream()

        override fun evaluate() {
            try {
                replaceOut()
                test.evaluate()
            } catch (e: Throwable) {
                validateFailure(e)
                return
            } finally {
                resetOut()
            }

            validateSuccess() // To avoid falling into catch
        }

        private fun validateSuccess() {
            val spec = testsSpec[description.methodName] ?: error("Test spec not found: ${description.methodName}")
            require(spec.error == null) { "Expected exception of type ${spec.error}, but test successfully passed" }

            val captured = capturedOut.toString()
            assertFalse(captured.contains("Coroutines dump"))
            assertTrue(captured.isEmpty(), captured)
        }

        private fun validateFailure(e: Throwable) {
            val spec = testsSpec[description.methodName] ?: error("Test spec not found: ${description.methodName}")
            if (spec.error == null || !spec.error.isInstance(e)) {
                throw IllegalStateException("Unexpected failure, expected ${spec.error}, had ${e::class}", e)
            }

            if (e !is TestTimedOutException) return

            val captured = capturedOut.toString()
            assertTrue(captured.contains("Coroutines dump"))
            for (part in spec.expectedOutParts) {
                assertTrue(captured.contains(part), "Expected $part to be part of the\n$captured")
            }

            for (part in spec.notExpectedOutParts) {
                assertFalse(captured.contains(part), "Expected $part not to be part of the\n$captured")
            }
        }

        private fun replaceOut() {
            sout = System.out
            serr = System.err

            System.setOut(PrintStream(capturedOut))
            System.setErr(PrintStream(capturedOut))
        }

        private fun resetOut() {
            System.setOut(sout)
            System.setErr(serr)
        }
    }
}

data class TestResultSpec(
    val testName: String, val expectedOutParts: List<String> = listOf(), val notExpectedOutParts:
    List<String> = listOf(), val error: Class<out Throwable>? = null
)
