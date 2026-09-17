#!/usr/bin/env bash
set -euo pipefail

project_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

# Run only the cold Gradle User Home, cold Gradle Daemon, cold IntelliJ caches scenario.
gradle-profiler --benchmark \
    --warmups 1 \
    --iterations 3 \
    --project-dir "$project_dir" \
    --scenario-file "$project_dir/performance.scenarios" \
    --idea-install-dir "${IDEA_INSTALL_DIR:-$HOME/Applications/IntelliJ IDEA.app}" \
    --idea-sandbox-dir "$project_dir/idea-sandbox" \
    --gradle-user-home "$project_dir/gradle-user-home" \
    --output-dir "$project_dir/benchmark-out" \
    idea-sync-cold-cold-cold