# kotlinx.coroutines release checklist

To release a new `<version>` of `kotlinx-coroutines`:

1. Checkout the `develop` branch: <br>
   `git checkout develop`

2. Retrieve the most recent `develop`: <br>
   `git pull`

3. Make sure the `master` branch is fully merged into `develop`:<br>
   `git merge origin/master`

4. Search & replace `<old-version>` with `<version>` across the project files. Should replace in:
   * Docs
     * [`README.md`](README.md) (native, core, test, debug, modules)
     * [`kotlinx-coroutines-debug/README.md`](kotlinx-coroutines-debug/README.md)
     * [`kotlinx-coroutines-test/README.md`](kotlinx-coroutines-test/README.md)
     * [`coroutines-guide-ui.md`](ui/coroutines-guide-ui.md)
   * Properties
     * [`gradle.properties`](gradle.properties)
     * [`integration-testing/gradle.properties`](integration-testing/gradle.properties)
   * Make sure to **exclude** `CHANGES.md` from replacements.

   As an alternative approach, you can use `./bump-version.sh new_version`

5. Write release notes in [`CHANGES.md`](CHANGES.md):
   * Use the old releases for style guidance.
   * Write each change on a single line (don't wrap with CR).
   * Look through the commit messages since the previous release.

6. Create the branch for this release:<br>
   `git checkout -b version-<version>`

7. Commit the updated files to the new version branch:<br>
   `git commit -a -m "Version <version>"`

8. Push the new version to GitHub:<br>
   `git push -u origin version-<version>`

9. Create a Pull-Request on GitHub from the `version-<version>` branch into `master`:
   * Review it.
   * Make sure it builds on CI.
   * Get approval for it.

0. On [TeamCity integration server](https://teamcity.jetbrains.com/project.html?projectId=KotlinTools_KotlinxCoroutines):
   * Wait until "Build" configuration for committed `version-<version>` branch passes tests.
   * Run the [`Deployment/Deploy [RUN THIS ONE]`](https://teamcity.jetbrains.com/buildConfiguration/KotlinTools_KotlinxCoroutines_Deployment30_StartDeployment)
     configuration with the corresponding new version:
     - Use the `version-<version>` branch
     - Set the `Version` build parameter to `<version>`

1. Wait until the corresponding
   [`Deployment/Upload Deployment to Central Portal`](https://teamcity.jetbrains.com/buildConfiguration/KotlinTools_KotlinxCoroutines_Deployment30_UploadDeploymentToCentralPortal)
   build finishes.
   Check its `Artifacts` tab.
   It has to contain `deployment_<version>.zip` with the artifacts expected
   for `kotlinx.coroutines`.
   If it does, approve the corresponding
   [`Deployment/Publish deployment`](https://teamcity.jetbrains.com/buildConfiguration/KotlinTools_KotlinxCoroutines_Deployment30_PublishDeployment)
   build and wait for it to finish.

2. Merge the new version branch into `master`:<br>
   `git checkout master`<br>
   `git merge --ff-only version-<version>`<br>
   `git push`

3. In [GitHub](https://github.com/kotlin/kotlinx.coroutines) interface:
   * Create a release named `<version>`, creating the `<version>` tag.
   * Cut & paste lines from [`CHANGES.md`](CHANGES.md) into description.

4. Announce the new release in [Slack](https://kotlinlang.slack.com)

5. Switch onto the `develop` branch:<br>
   `git checkout develop`

6. Fetch the latest `master`:<br>
   `git fetch`

7. Merge the release from `master`:<br>
   `git merge origin/master`

8. Push the updates to GitHub:<br>
   `git push`

9. Propose the website documentation update:
   * Set new value for [`KOTLINX_COROUTINES_RELEASE_TAG`](https://github.com/JetBrains/kotlin-web-site/blob/master/.teamcity/BuildParams.kt), creating a Pull Request in the website's repository. 
