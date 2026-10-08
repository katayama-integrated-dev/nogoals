#!/usr/bin/env bash
# The build entry point. Profiles:
#   (none)              typed compile, no publisher gates (the receipt says so)
#   --audit             every gate, including the network check
#   --audit --offline   every gate except external-link liveness
#   --update-baseline   bootstrap the permalink baseline on a FIRST-EVER deploy
set -euo pipefail
cd "$(dirname "$0")/.."
lake exe build-site "$@"
