if (javaVersionMajor < 11) {
    val message = "Project required JDK 11+, but found $javaVersion"
    if (Idea.active) {
        logger.error(message)
    } else {
        throw GradleException(message)
    }
}
