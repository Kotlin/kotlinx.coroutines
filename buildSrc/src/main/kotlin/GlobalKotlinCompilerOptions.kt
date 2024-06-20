import org.jetbrains.kotlin.gradle.dsl.KotlinCommonCompilerOptions

internal fun KotlinCommonCompilerOptions.configureGlobalKotlinArgumentsAndOptIns() {
    freeCompilerArgs.addAll("-progressive")
    optIn.addAll(
        "kotlin.experimental.ExperimentalTypeInference",
        // our own opt-ins that we don't want to bother with in our own code:
        "kotlinx.coroutines.DelicateCoroutinesApi",
        "kotlinx.coroutines.ExperimentalCoroutinesApi",
        "kotlinx.coroutines.ObsoleteCoroutinesApi",
        "kotlinx.coroutines.InternalCoroutinesApi",
        "kotlinx.coroutines.FlowPreview"
    )
}
