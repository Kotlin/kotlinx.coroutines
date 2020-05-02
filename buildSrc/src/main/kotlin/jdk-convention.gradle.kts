if (javaVersionMajor < 11) {
    throw GradleException("Project required JDK 11+, but found $javaVersion")
}
