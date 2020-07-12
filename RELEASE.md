# kotlinx.coroutines release checklist

To release new `<version>` of `kotlinx-coroutines`:

1. Checkout `develop` branch: <br> 
   `git checkout develop`

2. Retrieve the most recent `develop`: <br> 
   `git pull`
   
3. Make sure the `master` branch is fully merged into `develop`:
   `git merge origin/master`   

4. Search & replace `<old-version>` with `<version>` across the project files. Should replace in:
   * [`README.md`](README.md) (native, core, test, debug, modules)
   * [`coroutines-guide.md`](docs/coroutines-guide.md)
   * [`gradle.properties`](gradle.properties)
   * [`ui/kotlinx-coroutines-android/example-app/gradle.properties`](ui/kotlinx-coroutines-android/example-app/gradle.properties)    
   * [`ui/kotlinx-coroutines-android/animation-app/gradle.properties`](ui/kotlinx-coroutines-android/animation-app/gradle.properties)    
   * Make sure to **exclude** `CHANGES.md` from replacements.
   
   As an alternative approach you can use `./bump-version.sh old_version new_version`
  
5. Write release notes in [`CHANGES.md`](CHANGES.md):
   * Use old releases as example of style.
   * Write each change on a single line (don't wrap with CR).
   * Study commit message from previous release.

6. Create branch for this release:
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
   
4. In [Bintray](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines) admin interface:
   * Publish artifacts of the new version.
   * Wait until newly published version becomes the most recent.
   * Sync to Maven Central.
   
5. Announce new release in [Slack](https://kotlinlang.slack.com)   

6. Create a ticket to update coroutines version on [try.kotlinlang.org](try.kotlinlang.org).
   * Use [KT-30870](https://youtrack.jetbrains.com/issue/KT-30870) as a template
   * This step should be skipped for eap versions that are not merged to `master`

7. Switch into `develop` branch:<br>
   `git checkout develop`
 
8. Fetch the latest `master`:<br>
   `git fetch` 
   
9. Merge release from `master`:<br>
   `git merge origin/master`
   
0. Push updates to `develop`:<br>
   `git push`      
