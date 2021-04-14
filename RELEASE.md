# kotlinx.coroutines release checklist

To release new `<version>` of `kotlinx-coroutines`:

1. Checkout `develop` branch: <br> 
   `git checkout develop`

2. Retrieve the most recent `develop`: <br> 
   `git pull`
   
3. Make sure the `master` branch is fully merged into `develop`:
   `git merge origin/master`   

4. Search & replace `<old-version>` with `<version>` across the project files. Should replace in:
   * Docs
     * [`README.md`](README.md) (native, core, test, debug, modules)
     * [`kotlinx-coroutines-debug/README.md`](kotlinx-coroutines-debug/README.md)
     * [`kotlinx-coroutines-test/README.md`](kotlinx-coroutines-test/README.md)
     * [`coroutines-guide-ui.md`](ui/coroutines-guide-ui.md)
   * Properties   
     * [`gradle.properties`](gradle.properties)  
   * Make sure to **exclude** `CHANGES.md` from replacements.
   
   As an alternative approach you can use `./bump-version.sh old_version new_version`
  
5. Write release notes in [`CHANGES.md`](CHANGES.md):
   * Use old releases as example of style.
   * Write each change on a single line (don't wrap with CR).
   * Study commit message from previous release.

6. Create the branch for this release:
   `git checkout -b version-<version>`

7. Commit updated files to a new version branch:<br>
   `git commit -a -m "Version <version>"`
   
8. Push new version into the branch:<br>
   `git push -u origin version-<version>`
   
9. Create Pull-Request on GitHub from `version-<version>` branch into `master`:
   * Review it.
   * Make sure it build on CI.
   * Get approval for it.
   
0. Merge new version branch into `master`:<br>
   `git checkout master`<br>
   `git merge version-<version>`<br>
   `git push`   

1. On [TeamCity integration server](https://teamcity.jetbrains.com/project.html?projectId=KotlinTools_KotlinxCoroutines):
   * Wait until "Build" configuration for committed `master` branch passes tests.
   * Run "Deploy (Configure, RUN THIS ONE)" configuration with the corresponding new version.    

2. In [GitHub](https://github.com/kotlin/kotlinx.coroutines) interface:
   * Create a release named `<version>`. 
   * Cut & paste lines from [`CHANGES.md`](CHANGES.md) into description.    

3. Build and publish documentation for web-site
   (make sure you have [Docker](https://www.docker.com/) installed first): <br>
   `site/deploy.sh <version> push`
   
4. In [Nexus](https://oss.sonatype.org/#stagingRepositories) admin interface:
   * Close the repository and wait for it to verify.
   * Release the repository.
   
5. Announce new release in [Slack](https://kotlinlang.slack.com)   

6. Switch into `develop` branch:<br>
   `git checkout develop`
 
7. Fetch the latest `master`:<br>
   `git fetch` 
   
8. Merge release from `master`:<br>
   `git merge origin/master`
   
9. Push updates to `develop`:<br>
   `git push`      
