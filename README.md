# StringGeometry (Umbrella Repo)

This repository is now an integration umbrella for the split component repos:

- https://github.com/xiyin137/stringgeometry-supermanifolds
- https://github.com/xiyin137/stringgeometry-riemann-surfaces
- https://github.com/xiyin137/stringgeometry-super-riemann-surfaces

It keeps cross-cutting documentation, references, and factorization tooling, while source-of-truth Lean development lives in the three component repositories.

## Local Build

```bash
lake update
lake build
```

The umbrella package imports the component modules through git dependencies pinned in `lakefile.lean`.

## Module Entry Point

- `StringGeometry.lean` aggregates the main imports used across the project.

## Migration Notes

Factorization artifacts are retained as historical documentation:

- `docs/factorization/github-factorization-runbook.md`
- `scripts/factorization/*` (archival; these expect the pre-split monorepo source tree)

## Notes

- Lean namespace remains `StringGeometry.*` across component repos to avoid import churn.
- `_split_repos/` is ignored locally as an export/work area.
