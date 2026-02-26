# StringGeometry (Umbrella Repo)

`StringGeometry` is an integration umbrella around three active Lean repositories:

- https://github.com/xiyin137/stringgeometry-supermanifolds
- https://github.com/xiyin137/stringgeometry-riemann-surfaces
- https://github.com/xiyin137/stringgeometry-super-riemann-surfaces

This repo is intentionally thin: it pins versions, aggregates top-level imports, and stores shared documentation/tooling for the split architecture.

## Architecture

### Component responsibilities

- `stringgeometry-supermanifolds`
  - Foundational supergeometry infrastructure.
- `stringgeometry-riemann-surfaces`
  - Riemann surface development (analytic, scheme-theoretic, GAGA) plus shared sheaf topology infrastructure.
- `stringgeometry-super-riemann-surfaces`
  - Super Riemann surface layer built on both foundations above.

### Dependency graph

```text
SGSupermanifolds
SGRiemannSurfaces
SGSuperRiemannSurfaces -> SGSupermanifolds, SGRiemannSurfaces
```

In this umbrella repo, these are pinned as git dependencies in `lakefile.lean`.

## What Lives Here

### Source and package wiring

- `StringGeometry.lean`
  - Umbrella entry point importing the three component libraries.
- `lakefile.lean`
  - Dependency pins for component repos.
- `lean-toolchain`
  - Lean toolchain version for integration builds.

### Documentation and migration tooling

- `docs/factorization/github-factorization-runbook.md`
  - End-to-end split/factorization runbook and architecture notes.
- `scripts/factorization/`
  - Extraction scripts used during monorepo factorization.

### Local work areas

- `_split_repos/`
  - Local export/scratch area for split repos (ignored by git).
- `references/`
  - Local reference material (ignored by git).

## Build and Check

From repo root:

```bash
lake update
lake build
```

This validates that the pinned component revisions integrate correctly.

## Workflow

1. Make theory/code changes in the relevant component repo.
2. Push and verify CI in that component repo.
3. Update commit pins in this repo's `lakefile.lean`.
4. Run `lake update` and commit `lake-manifest.json`.
5. Run `lake build` here to confirm cross-repo integration.

## Notes

- Namespace remains `StringGeometry.*` across component repos to keep imports stable.
- Source-of-truth mathematical development is in the component repos, not in this umbrella repo.
