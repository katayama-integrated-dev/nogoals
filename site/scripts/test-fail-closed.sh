#!/usr/bin/env bash
# Negative controls for the transactional build. The script is NoGoals's; run it
# from the site root, where `lake exe build-site` works.
cd "$(dirname "$0")/.." && exec ../tools/test-fail-closed.sh
