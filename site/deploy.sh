#!/usr/bin/env bash

#
# Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
#

# Abort on first error
set -e

# Directories
SITE_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
ROOT_DIR="$SITE_DIR/.."
BUILD_DIR="$ROOT_DIR/build"
DIST_DIR="$BUILD_DIR/dokka/htmlMultiModule"
PAGES_DIR="$BUILD_DIR/pages"

# Init options
GRADLE_OPT=
PUSH_OPT=

# Set dry run if needed
if [ "$2" == "push" ] ; then
    echo "--- Doing LIVE site deployment, so do clean build"
    GRADLE_OPT=clean
else
    echo "--- Doing dry-run. To commit do 'deploy.sh <version> push'"
    PUSH_OPT=--dry-run
fi

# Makes sure that site is built
"$ROOT_DIR/gradlew" $GRADLE_OPT dokkaHtmlMultiModule

# Cleanup dist directory (and ignore errors)
rm -rf "$PAGES_DIR" || true

# Prune worktrees to avoid errors from previous attempts
git --work-tree "$ROOT_DIR" worktree prune

# Create git worktree for gh-pages branch
git --work-tree "$ROOT_DIR" worktree add -B gh-pages "$PAGES_DIR" origin/gh-pages

# Now work in newly created workspace
cd "$PAGES_DIR"

# Fixup all the old documentation files
# Remove non-.html files
git rm `find . -type f -not -name '*.html' -not -name '.git'` > /dev/null

# Remove all the old documentation
git rm -r * > /dev/null

# Copy new documentation from dist
cp -r "$DIST_DIR"/* "$PAGES_DIR"

# Add it all to git
git add *

# Commit docs for the new version
if [ -z "$1" ] ; then
    echo "No argument with version supplied -- skipping commit"
else
    git commit -m "Version $1 docs"
    git push $PUSH_OPT origin gh-pages:gh-pages
fi
