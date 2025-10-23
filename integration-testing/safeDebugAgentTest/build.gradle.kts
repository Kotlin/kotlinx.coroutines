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

// In this test coroutine debug agent is attached as a javaagent vm argument
// to a pure Java project (safeDebugAgentTest) with no Kotlin stdlib dependency.
// In this case the error should be thrown from AgetnPremain class:
// "java.lang.IllegalStateException: kotlinx.coroutines debug agent failed to load."
tasks.register<Test>("runWithExpectedFailure") {
    val agentJar = System.getProperty("coroutines.debug.agent.path")
    val errorOutputStream = ByteArrayOutputStream()
    var exitValue = 0

    try {
        project.javaexec {
            mainClass.set("Main")
            classpath = sourceSets.main.get().runtimeClasspath
            jvmArgs = listOf("-javaagent:$agentJar")
            errorOutput = errorOutputStream
        }
    } catch (e: Exception) {
        exitValue = -1
    }

    if (exitValue == 0) {
        throw GradleException("':safeDebugAgentTest:runWithExpectedFailure' was expected to fail with an error during initialization of the debug agent, but completed successfully.")
    }
    val expectedAgentError =
        "kotlinx.coroutines debug agent failed to load.\n" +
            "Please ensure that the Kotlin standard library is present in the classpath.\n" +
            "Alternatively, you can disable kotlinx.coroutines debug agent by removing `-javaagent=/path/kotlinx-coroutines-core.jar` from your VM arguments.\n"
    val errorOutput = errorOutputStream.toString()
    if (!errorOutput.contains(expectedAgentError)) {
        throw GradleException("':safeDebugAgentTest:runWithExpectedFailure' failed with an unexpected error:\n" + errorOutput)
    }
}