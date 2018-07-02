/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import io.reactivex.Single
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.rx2.await
import retrofit2.Retrofit
import retrofit2.adapter.rxjava2.RxJava2CallAdapterFactory
import retrofit2.converter.gson.GsonConverterFactory
import retrofit2.http.GET
import retrofit2.http.Path

interface GitHub {
    @GET("/repos/{owner}/{repo}/contributors")
    fun contributors(
            @Path("owner") owner: String,
            @Path("repo") repo: String
    ): Single<List<Contributor>>

    @GET("users/{user}/repos")
    fun listRepos(@Path("user") user: String): Single<List<Repo>>
}

data class Contributor(val login: String, val contributions: Int)
data class Repo(val name: String)

fun main(args: Array<String>) = runBlocking {
    println("Making GitHub API request")
    
    val retrofit = Retrofit.Builder().apply {
        baseUrl("https://api.github.com")
        addConverterFactory(GsonConverterFactory.create())
        addCallAdapterFactory(RxJava2CallAdapterFactory.create())
    }.build()

    val github = retrofit.create(GitHub::class.java)

    val contributors =
            github.contributors("JetBrains", "Kotlin")
                  .await().take(10)

    for ((name, contributions) in contributors) {
        println("$name has $contributions contributions, other repos: ")

        val otherRepos =
                github.listRepos(name).await()
                      .map(Repo::name).joinToString(", ")

        println(otherRepos)
    }
}
