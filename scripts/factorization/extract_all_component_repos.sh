#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TARGET_BASE="${1:-$ROOT_DIR/_split_repos}"

mkdir -p "$TARGET_BASE"

"$ROOT_DIR/scripts/factorization/extract_component_repo.sh" supermanifolds "$TARGET_BASE/stringgeometry-supermanifolds"
"$ROOT_DIR/scripts/factorization/extract_component_repo.sh" riemann-surfaces "$TARGET_BASE/stringgeometry-riemann-surfaces"
"$ROOT_DIR/scripts/factorization/extract_component_repo.sh" super-riemann-surfaces "$TARGET_BASE/stringgeometry-super-riemann-surfaces"

echo
echo "All component repos exported under: $TARGET_BASE"
echo "Next: create GitHub repos and push each directory as its own remote."
