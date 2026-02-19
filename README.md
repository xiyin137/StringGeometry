# StringGeometry

Rigorous formalization of string theory geometry in Lean 4 with Mathlib. All definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. `axiom` is strictly forbidden.

Previously part of [ModularPhysics](https://github.com/xiyin137/ModularPhysics).

## Structure

```
StringGeometry/
├── RiemannSurfaces/
│   ├── Analytic/                    # Complex-analytic theory
│   │   ├── Applications/
│   │   ├── Helpers/
│   │   ├── HodgeTheory/
│   │   │   ├── Helpers/
│   │   │   └── Infrastructure/
│   │   ├── Jacobian/
│   │   └── Moduli/
│   ├── Combinatorial/               # Ribbon graphs, combinatorial moduli
│   ├── GAGA/                        # Analytic ↔ algebraic bridge
│   │   ├── AlgebraicCurves/
│   │   │   ├── Cohomology/
│   │   │   └── Core/
│   │   ├── Bridge/
│   │   ├── Cohomology/
│   │   ├── Helpers/
│   │   └── Moduli/
│   ├── Helpers/
│   ├── SchemeTheoretic/             # Algebraic geometry approach
│   │   ├── Cohomology/
│   │   ├── Helpers/
│   │   └── Sheaves/
│   └── Topology/
├── Supermanifolds/                  # ℤ/2-graded manifolds
│   ├── FPS/
│   ├── Helpers/
│   └── Sheaves/
├── SuperRiemannSurfaces/            # Worldsheet geometry for superstrings
└── Topology/                        # Homotopy, sheaves, spectra infrastructure
    ├── Homotopy/
    ├── Sheaves/
    └── Spectra/
```

### Riemann Surfaces

Develops Riemann surface theory from three complementary perspectives:

- **Analytic**: Complex-analytic definitions, meromorphic functions, Hodge theory (differential forms, Dolbeault cohomology, harmonic forms), Jacobian varieties, Abel-Jacobi maps, and analytic Riemann-Roch.
- **SchemeTheoretic**: Algebraic geometry approach via smooth projective curves over ℂ. Includes Čech cohomology with d²=0, sheaf cohomology, Riemann-Roch theorem (fully proven at the Euler characteristic level), canonical sheaf, and Serre duality.
- **GAGA**: Bridge between analytic and algebraic viewpoints.
- **Combinatorial**: Ribbon graphs and combinatorial moduli spaces.

### Supermanifolds

Defines supermanifolds as ringed spaces with ℤ/2-graded structure sheaves. Includes Berezin integration, Batchelor theorem, super Jacobian (Berezinian), and formal power series infrastructure.

### Super Riemann Surfaces

Worldsheet geometry for superstrings: super Riemann surfaces, superconformal maps, and supermoduli spaces.

### Topology

Infrastructure for homotopy theory (pointed spaces, suspensions, loop spaces, weak equivalences, exact sequences), Čech cohomology of sheaves, and stable homotopy theory (spectra, Eilenberg-MacLane spectra, homotopy groups).
