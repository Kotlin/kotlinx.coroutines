package kotlinx.coroutines.selects

import kotlinx.coroutines.internal.*

// only for debugging
internal fun <R> SelectBuilder<R>.default(block: suspend () -> R) {
    this as SelectBuilderImpl // type assertion
    addAlternative(DEFAULT_OBJ_FOR_SELECT,::regDefault, ::processResDefault, PARAM_CLAUSE_0, block)
}

private val DEFAULT_OBJ_FOR_SELECT = Symbol("DEFAULT_OBJ_FOR_SELECT")
private fun regDefault(objForSelect: Any, select: SelectInstance<*>, param: Any?) =
    select.selectInRegPhase(objForSelect)
private fun processResDefault(objForSelect: Any, result: Any?): Any? = null