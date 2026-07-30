package kotlinx.coroutines.utils

@OptionalExpectation
@Target(AnnotationTarget.CLASS)
internal expect annotation class JsOptionalExport(val couldBeConvertedToExplicitExport: Boolean)
