package kotlinx.coroutines.internal

@OptionalExpectation
@Target(AnnotationTarget.CLASS)
internal expect annotation class JsOptionalExport(val couldBeConvertedToExplicitExport: Boolean)
