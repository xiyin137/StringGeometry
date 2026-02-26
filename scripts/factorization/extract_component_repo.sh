#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: extract_component_repo.sh <component> <output_dir> [--init-git]

Components:
  supermanifolds
  riemann-surfaces
  super-riemann-surfaces

Behavior:
  - Creates a standalone Lean repo at <output_dir>
  - Preserves StringGeometry module paths
  - Generates component-specific lakefile.lean and CI workflow

Notes:
  - riemann-surfaces includes StringGeometry/Topology because
    RiemannSurfaces imports Topology.Sheaves modules.
USAGE
}

if [[ $# -lt 2 ]]; then
  usage
  exit 1
fi

COMPONENT="$1"
OUT_DIR="$2"
INIT_GIT="false"
if [[ ${3:-} == "--init-git" ]]; then
  INIT_GIT="true"
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if [[ ! -d .git || ! -f lean-toolchain ]]; then
  echo "Run this script from inside the StringGeometry repo." >&2
  exit 1
fi

case "$COMPONENT" in
  supermanifolds)
    PKG_NAME="SGSupermanifolds"
    REPO_LABEL="stringgeometry-supermanifolds"
    ROOT_IMPORT='`StringGeometry.Supermanifolds'
    COPY_PATHS=(
      "StringGeometry/Supermanifolds"
      "StringGeometry/Supermanifolds.lean"
    )
    EXTRA_DEPS=""
    ;;
  riemann-surfaces)
    PKG_NAME="SGRiemannSurfaces"
    REPO_LABEL="stringgeometry-riemann-surfaces"
    ROOT_IMPORT='`StringGeometry.RiemannSurfaces'
    COPY_PATHS=(
      "StringGeometry/RiemannSurfaces"
      "StringGeometry/RiemannSurfaces.lean"
      "StringGeometry/Topology"
    )
    EXTRA_DEPS=""
    ;;
  super-riemann-surfaces)
    PKG_NAME="SGSuperRiemannSurfaces"
    REPO_LABEL="stringgeometry-super-riemann-surfaces"
    ROOT_IMPORT='`StringGeometry.SuperRiemannSurfaces.SuperRiemannSurfaces'
    COPY_PATHS=(
      "StringGeometry/SuperRiemannSurfaces"
    )
    EXTRA_DEPS=$(cat <<'DEPS'
require SGSupermanifolds from git
  "https://github.com/xiyin137/stringgeometry-supermanifolds.git" @ "main"

require SGRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-riemann-surfaces.git" @ "main"
DEPS
)
    ;;
  *)
    echo "Unknown component: $COMPONENT" >&2
    usage
    exit 1
    ;;
esac

rm -rf "$OUT_DIR"
mkdir -p "$OUT_DIR"

cp "$ROOT_DIR/lean-toolchain" "$OUT_DIR/lean-toolchain"

for p in "${COPY_PATHS[@]}"; do
  if [[ -d "$ROOT_DIR/$p" ]]; then
    mkdir -p "$OUT_DIR/$(dirname "$p")"
    cp -R "$ROOT_DIR/$p" "$OUT_DIR/$p"
  elif [[ -f "$ROOT_DIR/$p" ]]; then
    mkdir -p "$OUT_DIR/$(dirname "$p")"
    cp "$ROOT_DIR/$p" "$OUT_DIR/$p"
  else
    echo "Missing path for $COMPONENT: $p" >&2
    echo "This usually means the repository has already been refactored into umbrella mode." >&2
    echo "Use the split repositories on GitHub as source-of-truth instead of re-extracting from this checkout." >&2
    exit 1
  fi
done

cat > "$OUT_DIR/lakefile.lean" <<EOF_LAKE
import Lake
open Lake DSL

package "$REPO_LABEL" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

$EXTRA_DEPS
lean_lib $PKG_NAME where
  roots := #[$ROOT_IMPORT]
EOF_LAKE

mkdir -p "$OUT_DIR/.github/workflows"
cat > "$OUT_DIR/.github/workflows/lean-ci.yml" <<'EOF_CI'
name: lean-ci

on:
  pull_request:
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          use-mathlib-cache: true
      - name: Build
        run: lake build
EOF_CI

if command -v lake >/dev/null 2>&1; then
  if ! (cd "$OUT_DIR" && lake update >/dev/null); then
    echo "Warning: lake update failed for $OUT_DIR; run 'lake update' manually." >&2
  fi
fi

cat > "$OUT_DIR/README.md" <<EOF_README
# $REPO_LABEL

Split from https://github.com/xiyin137/StringGeometry.

## Build

    git clone <this-repo-url>
    cd $REPO_LABEL
    lake build

## Notes

- Lean module namespace remains under StringGeometry.* to minimize import churn.
- This repository was generated with:
  ./scripts/factorization/extract_component_repo.sh $COMPONENT <output_dir>
EOF_README

cat > "$OUT_DIR/.gitignore" <<'EOF_GITIGNORE'
.lake/
.elan/
build/
.DS_Store
EOF_GITIGNORE

if [[ "$INIT_GIT" == "true" ]]; then
  git -C "$OUT_DIR" init
  git -C "$OUT_DIR" add .
  git -C "$OUT_DIR" commit -m "Initial split from StringGeometry ($COMPONENT)"
fi

echo "Wrote $COMPONENT repo to: $OUT_DIR"
