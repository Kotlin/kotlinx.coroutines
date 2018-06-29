/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package cases.protected

public abstract class PublicAbstractClass protected constructor() {
    protected abstract val protectedVal: Int
    protected abstract var protectedVar: Any?

    protected abstract fun protectedFun()
}
