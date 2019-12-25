# Reference documentation site

This module builds references documentation.

## Building docs

* Install [Docker](https://www.docker.com/)
* In the project root directory run `./gradlew site`
* The resulting HTML pages are generated in `site/build/dist`
* For continuous testing of the documentation run `./gradlew serve` and navigate
  to the URL that is printed on the screen
  * Update the docs via `./gradlew copyDocs` while `serve` is running

For release use [`deploy.sh`](deploy.sh) that performs clean build of the site and pushes the results
into `gh-pages` branch of the project.