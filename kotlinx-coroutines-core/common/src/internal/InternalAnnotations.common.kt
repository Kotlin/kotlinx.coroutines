package kotlinx.coroutines.internal

// Ignore JRE requirements for animal-sniffer, compileOnly dependency
@Target(
    AnnotationTarget.FUNCTION,
    AnnotationTarget.PROPERTY_GETTER,
    AnnotationTarget.PROPERTY_SETTER,
    AnnotationTarget.CONSTRUCTOR,
    AnnotationTarget.CLASS,
    AnnotationTarget.FILE
)
@OptionalExpectation
internal expect annotation class IgnoreJreRequirement()
