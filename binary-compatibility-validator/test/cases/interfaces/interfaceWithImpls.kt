/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package cases.interfaces

public interface BaseWithImpl {
    fun foo() = 42
}

public interface DerivedWithImpl : BaseWithImpl {
    override fun foo(): Int {
        return super.foo() + 1
    }
}

public interface DerivedWithoutImpl : BaseWithImpl

