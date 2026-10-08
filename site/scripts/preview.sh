#!/usr/bin/env bash
# Build, then serve build/ at http://localhost:8124/ so root-absolute links
# resolve (a file:// open or a subpath viewer cannot do that). Ctrl-C stops it.
set -euo pipefail
cd "$(dirname "$0")/.."
./scripts/build.sh "$@"
echo; echo "Serving build/ at http://localhost:8124/  (Ctrl-C to stop)"
exec python3 -m http.server -d build --bind 127.0.0.1 8124
