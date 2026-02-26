# GitHub Factorization Runbook

## Target Architecture

- `stringgeometry-supermanifolds` (independent)
- `stringgeometry-riemann-surfaces` (includes `StringGeometry/Topology` sheaf infrastructure)
- `stringgeometry-super-riemann-surfaces` (depends on both repos above)

Dependency graph:

- `SGSupermanifolds`
- `SGRiemannSurfaces`
- `SGSuperRiemannSurfaces` -> `SGSupermanifolds`, `SGRiemannSurfaces`

## Why Topology is bundled with RiemannSurfaces

`StringGeometry/RiemannSurfaces` imports:

- `StringGeometry.Topology.Sheaves.CechCohomology`
- `StringGeometry.Topology.Sheaves.LongExactSequence`

To keep a 3-repo plan (instead of 4 repos), the split script exports `StringGeometry/Topology`
with the RiemannSurfaces repo.

## Local Extraction

From monorepo root:

```bash
./scripts/factorization/extract_all_component_repos.sh
```

This writes:

- `_split_repos/stringgeometry-supermanifolds`
- `_split_repos/stringgeometry-riemann-surfaces`
- `_split_repos/stringgeometry-super-riemann-surfaces`

Each output contains:

- `lean-toolchain`
- Component source subtree(s)
- `lakefile.lean`
- `lake-manifest.json` (auto-generated if `lake` is available during extraction)
- `.github/workflows/lean-ci.yml`

Workflow defaults in extracted repos:

- `pull_request`
- `workflow_dispatch`

(`push` is intentionally disabled by default to avoid noisy CI mail on every main-branch commit.)

## GitHub Creation and Push

Create empty repos on GitHub first, then:

```bash
cd _split_repos/stringgeometry-supermanifolds
git init
git add .
git commit -m "Initial split from StringGeometry"
git branch -M main
git remote add origin git@github.com:xiyin137/stringgeometry-supermanifolds.git
git push -u origin main
```

Repeat for:

- `stringgeometry-riemann-surfaces`
- `stringgeometry-super-riemann-surfaces`

## Versioning Discipline

After foundation updates:

1. Tag in foundation repo(s), e.g. `v0.1.0`
2. Update dependency refs in `stringgeometry-super-riemann-surfaces/lakefile.lean`
3. Commit manifest update (`lake update` + `lake-manifest.json`)

## Umbrella Repo (Current State)

This repository has been converted into an umbrella integration repo that:

- pins component dependency versions
- aggregates docs, references, and migration tooling

Source-of-truth Lean development lives in:

- `xiyin137/stringgeometry-supermanifolds`
- `xiyin137/stringgeometry-riemann-surfaces`
- `xiyin137/stringgeometry-super-riemann-surfaces`
