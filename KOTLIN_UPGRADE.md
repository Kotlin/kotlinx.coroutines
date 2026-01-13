# Checklist for upgrading to the new Kotlin version

1. Create a new branch based off `develop`:
   ```sh
   git fetch
   git checkout -b kotlin-<version> origin/develop
   ```

1. In `gradle.properties`,
   set `kotlin_version` to the `<version>`.

2. Likewise, set `kotlin_version` in `integration-testing/gradle.properties`.

3. In `README.md`,
   replace the occurrences of the old version with the `<version>`.
   These are:
   - A badge at the top of the file.
   - The Kotlin version corresponding to the latest release,
     mentioned in the first paragraph.
   - Maven and Gradle configuration blocks.

4. In `README.md`, find the link to https://pl.kotl.in/ and open it.
   Set the compiler version of Kotlin Playground to the same major version as `<version>`,
   click "Copy link", and replace the original link in `README.md` with the new one.

5. Perform a full build: `gradle clean check publishAllPublicationsToIntegrationTestingRepository`,
   followed by `gradle clean check` in the `integration-testing` directory.
   Fix any issues that arise.

6. Commit and push all changes to GitHub:
   ```sh
   git commit -am 'Upgrade to Kotlin <version>'
   git push -u origin kotlin-<version>
   ```

7. Wait for the TeamCity continuous integration builds to finish.

8. Open a new pull request, receive approval, and merge.
