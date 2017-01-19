
import kotlinx.coroutines.experimental.rx.awaitSingle
import kotlinx.coroutines.experimental.rx.rxSingle
import retrofit2.Retrofit
import retrofit2.adapter.rxjava.RxJavaCallAdapterFactory
import retrofit2.converter.gson.GsonConverterFactory
import retrofit2.http.GET
import retrofit2.http.Path
import rx.Observable

interface GitHub {
    @GET("/repos/{owner}/{repo}/contributors")
    fun contributors(
            @Path("owner") owner: String,
            @Path("repo") repo: String
    ): Observable<List<Contributor>>

    @GET("users/{user}/repos")
    fun listRepos(@Path("user") user: String): Observable<List<Repo>>
}

data class Contributor(val login: String, val contributions: Int)
data class Repo(val name: String)

fun main(args: Array<String>) {
    val retrofit = Retrofit.Builder().apply {
        baseUrl("https://api.github.com")
        addConverterFactory(GsonConverterFactory.create())
        addCallAdapterFactory(RxJavaCallAdapterFactory.create())
    }.build()

    val github = retrofit.create(GitHub::class.java)

    rxSingle {
        val contributors =
                github.contributors("JetBrains", "Kotlin")
                      .awaitSingle().take(10)

        for ((name, contributions) in contributors) {
            println("$name has $contributions contributions, other repos: ")

            val otherRepos =
                    github.listRepos(name).awaitSingle()
                          .map(Repo::name).joinToString(", ")

            println(otherRepos)
        }
    }
}
