object Idea {
    val active: Boolean
        get() = System.getProperty("idea.active") == "true"
}
