#!/usr/bin/env bash
# The build entry point. Profiles:
#   (none)              typed compile, no publisher gates (the receipt says so)
#   --audit             every gate, including the network check
#   --audit --offline   every gate except external-link liveness
#   --update-baseline   bootstrap the permalink baseline on a FIRST-EVER deploy
set -euo pipefail
cd "$(dirname "$0")/.."
# Share NoGoals's dependency checkout (Mathlib is several GB) instead of a second copy.
[ -L .lake/packages ] || { mkdir -p .lake && ln -s ../../.lake/packages .lake/packages; }
lake exe build-site "$@"
