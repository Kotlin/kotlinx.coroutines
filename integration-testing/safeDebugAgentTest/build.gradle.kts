import java.io.*

plugins {
    id("java")
    application
}

repositories {
    mavenCentral()
}

application {
    mainClass.set("Main")
}

val expectedAgentError =
    "kotlinx.coroutines debug agent failed to load.\n" +
        "Please ensure that the Kotlin standard library is present in the classpath.\n" +
        "Alternatively, you can disable kotlinx.coroutines debug agent by removing `-javaagent=/path/kotlinx-coroutines-core.jar` from your VM arguments.\n"


// In this test coroutine debug agent is attached as a javaagent vm argument
// to a pure Java project (safeDebugAgentTest) with no Kotlin stdlib dependency.
// In this case the error should be thrown from AgetnPremain class:
// "java.lang.IllegalStateException: kotlinx.coroutines debug agent failed to load."
tasks.register<Test>("runWithExpectedFailure") {
    val agentJar = System.getProperty("coroutines.debug.agent.path")
    val errorOutputStream = ByteArrayOutputStream()
    val standardOutputStream = ByteArrayOutputStream()

    project.javaexec {
        mainClass.set("Main")
        classpath = sourceSets.main.get().runtimeClasspath
        jvmArgs = listOf("-javaagent:$agentJar")
        errorOutput = errorOutputStream
        standardOutput = standardOutputStream
        isIgnoreExitValue = true
    }

    val errorOutput = errorOutputStream.toString()
    val standardOutput = standardOutputStream.toString()
    if (!errorOutput.contains(expectedAgentError)) {
        throw GradleException("':safeDebugAgentTest:runWithExpectedFailure' completed with an unexpected output:\n" + standardOutput + "\n" + errorOutput)
    }
    if (standardOutput.contains("OK!")) {
        throw GradleException("':safeDebugAgentTest:runWithExpectedFailure' was expected to throw the agent initializaion error, but Main was executed:\n" + standardOutput + "\n" + errorOutput)
    }
}

// This test checks, that if the argument `kotlinx.coroutines.ignore.debug.agent.error` is passed to the javaagent,
// then the initialization error will be just logged to the stderr and the execution will continue.
tasks.register<Test>("runWithIgnoredError") {
    val agentJar = System.getProperty("coroutines.debug.agent.path")
    val errorOutputStream = ByteArrayOutputStream()
    val standardOutputStream = ByteArrayOutputStream()

    project.javaexec {
        mainClass.set("Main")
        classpath = sourceSets.main.get().runtimeClasspath
        jvmArgs = listOf("-javaagent:$agentJar=kotlinx.coroutines.ignore.debug.agent.error")
        errorOutput = errorOutputStream
        standardOutput = standardOutputStream
        isIgnoreExitValue = false
    }

    val errorOutput = errorOutputStream.toString()
    val standardOutput = standardOutputStream.toString()
    if (!errorOutput.contains(expectedAgentError)) {
        throw GradleException("':safeDebugAgentTest:runWithIgnoredError' completed with an unexpected output:\n" + standardOutput + "\n" + errorOutput)
    }
    if (!standardOutput.contains("OK!")) {
        throw GradleException("':safeDebugAgentTest:runWithIgnoredError' was expected to log the agent initialization error and proceed with the execution of Main, but it completed with an unexpected output:\n" + standardOutput + "\n" + errorOutput)
    }
}