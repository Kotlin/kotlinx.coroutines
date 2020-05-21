import org.gradle.api.JavaVersion

if (!JavaVersion.current().isJava11Compatible) {
    val message = "Project required JDK 11+, but found ${JavaVersion.current()}"
    if (Idea.active) {
        logger.error(message)
    } else {
        throw GradleException(message)
    }
}
