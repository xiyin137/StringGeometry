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
- `.github/workflows/lean-ci.yml`

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

## Optional Umbrella Repo

You can keep current monorepo as an umbrella integration repo that only:

- pins dependency versions
- aggregates docs and cross-module CI

If you do that, migrate to `lakefile.lean` with git dependencies instead of hosting all source trees.
