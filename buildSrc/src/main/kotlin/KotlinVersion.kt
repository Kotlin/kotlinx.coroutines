@file:JvmName("KotlinVersion")

fun isKotlinVersionAtLeast(kotlinVersion: String, atLeastMajor: Int, atLeastMinor: Int, atLeastPatch: Int): Boolean {
    val (major, minor) = kotlinVersion
        .split('.')
        .take(2)
        .map { it.toInt() }
    val patch = kotlinVersion.substringAfterLast('.').substringBefore('-').toInt()
    return when {
        major > atLeastMajor -> true
        major < atLeastMajor -> false
        else -> (minor == atLeastMinor && patch >= atLeastPatch) || minor > atLeastMinor
    }
}
