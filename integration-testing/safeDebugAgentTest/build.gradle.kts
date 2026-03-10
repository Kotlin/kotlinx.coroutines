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
tasks.register("attachAgentWithoutKotlinStdlib") {
    dependsOn("classes")

    doLast {
        val agentJar = System.getProperty("coroutines.debug.agent.path")
        val execResult = project.providers.javaexec {
            mainClass.set("Main")
            classpath = sourceSets.main.get().runtimeClasspath
            jvmArgs = listOf("-javaagent:$agentJar")
            isIgnoreExitValue = true
        }
        val exitCode = execResult.result.get().exitValue
        val stdout = execResult.standardOutput.asText.getOrElse("<not found>")
        val stderr = execResult.standardError.asText.getOrElse("<not found>")
        check (exitCode == 0) {
            "Process execution ended with non-zero exit code: $exitCode\nstdout:\n$stdout\nstderr:\n$stderr"
        }
        check(stderr.isEmpty()) {
            "Expected no output in the error stream, but got:\n$stderr"
        }
        check(stdout.contains("OK!")) {
            "Expected 'OK!' in the standard output, but got:\n$stdout"
        }
    }
}
