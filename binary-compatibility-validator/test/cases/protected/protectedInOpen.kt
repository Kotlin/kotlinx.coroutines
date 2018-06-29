/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package cases.protected

public open class PublicOpenClass protected constructor() {
    protected val protectedVal = 1
    protected var protectedVar = 2

    protected fun protectedFun() = protectedVal
}
