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
        val errorOutputStream = ByteArrayOutputStream()
        val standardOutputStream = ByteArrayOutputStream()

        project.javaexec {
            mainClass.set("Main")
            classpath = sourceSets.main.get().runtimeClasspath
            jvmArgs = listOf("-javaagent:$agentJar")
            errorOutput = errorOutputStream
            standardOutput = standardOutputStream
        }

        check(errorOutputStream.toString().isEmpty()) {
            "Expected no output in the error stream, but got:\n$errorOutputStream"
        }
        check(standardOutputStream.toString().contains("OK!")) {
            "Expected 'OK!' in the standard output, but got:\n$standardOutputStream"
        }
    }
}
