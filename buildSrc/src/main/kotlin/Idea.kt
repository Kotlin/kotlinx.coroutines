object Idea {
    @JvmStatic // for Gradle
    val active: Boolean
        get() = System.getProperty("idea.active") == "true"
}
