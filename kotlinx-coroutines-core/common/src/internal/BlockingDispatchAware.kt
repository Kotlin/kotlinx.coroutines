package kotlinx.coroutines.internal


internal interface BlockingDispatchAware {
    fun beforeDispatchElsewhere()
    fun afterDispatchBack()
}