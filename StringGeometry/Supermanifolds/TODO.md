# Supermanifolds Folder - Status and Plan

## Summary

The algebraic foundations are well-developed and proven. The **global integration
pipeline** (Phases 1-8) is now implemented, providing:
- Full nilpotent Taylor expansion
- Super function composition
- Pullback of integral forms
- Nilpotent inverse in Grassmann algebra (with bridge from Classical.choose to explicit geometric series)
- Partition of unity construction
- Change of variables formula
- Global integral independence
- **Global Stokes Theorem** on closed supermanifolds

**Only 4 sorrys remain in the integration pipeline:**
1. `berezinianCarrierAt_grassmannSmooth` (Pullback.lean) — Berezinian coefficients are smooth
2. `berezin_change_of_variables` (GlobalStokes.lean) — assembly
3. `globalBerezinIntegral_independent_proper` (GlobalStokes.lean) — assembly
4. `globalExteriorDerivative.compatible_body` (GlobalStokes.lean) — assembly

---

## Current Status by File

### Excellent (no sorrys)
| File | Notes |
|------|-------|
| Superalgebra.lean | Complete algebraic foundations, `grassmann_basis_card` proven |
| SuperRingCat.lean | map_maxIdeal properly formulated |
| SuperDomainAlgebra.lean | Ring/Algebra instances for SuperDomainFunction proven |
| Supermanifolds.lean | All placeholders fixed, proper sheaf conditions |
| PartialOddDerivation.lean | `partialOdd_odd_derivation'` proven |
| SuperJacobian.lean | Super Jacobian with proper grading, parity proven |
| Helpers/SuperMatrix.lean | SuperMatrix with block multiplication |
| Helpers/Berezinian.lean | Berezinian computation, ber_congr |
| Helpers/BerezinianMul.lean | `ber_mul` proven (2900+ lines) |
| Helpers/FiniteGrassmann.lean | Ring instance, SuperCommutative, `grassmann_soul_nilpotent` proven |
| Helpers/SuperChainRule.lean | `berezinian_cocycle_from_chain_rule` proven |
| Helpers/PartialOddLeibniz.lean | Sign lemmas for Leibniz rule |
| Helpers/GrassmannSmooth.lean | GrassmannSmooth predicate, all closure properties proven |
| Helpers/NilpotentTaylor.lean | Full Taylor expansion, all proven (0 sorrys) |
| Helpers/NilpotentInverse.lean | Geometric series inverse, bridge lemmas, det/product smoothness — all proven (0 sorrys) |
| Integration/SuperCompose.lean | Super function composition — all proven (0 sorrys) |
| Integration/PartitionOfUnity.lean | Super PU from body PU — all proven (0 sorrys) |
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms, complete |
| Integration/StokesTheorem.lean | Local Stokes proven (0 sorrys) |
| Integration/ExteriorDerivative.lean | Super exterior derivative d = d_0 (0 sorrys) |

### Integration Pipeline — Remaining Sorrys
| File | Status | Remaining Sorrys |
|------|--------|-----------------|
| Integration/Pullback.lean | **Phase 3** | 1 sorry: `berezinianCarrierAt_grassmannSmooth` — needs matrix inverse entries GrassmannSmooth (adjugate + Ring.inverse bridge) |
| Integration/GlobalStokes.lean | **Phases 6-8** | 3 sorrys: `berezin_change_of_variables`, `globalBerezinIntegral_independent_proper`, `globalExteriorDerivative.compatible_body` — assembly proofs connecting local results |

### Good (sorrys but properly stated, independent of integration pipeline)
| File | Notes |
|------|-------|
| Batchelor.lean | `iso_compatible` proper statement. `splitting_nonuniqueness` intertwines two isos (sorry). Deep theorems (`batchelor_theorem`, `batchelor_splitting`) sorry. |
| BerezinIntegration.lean | Original sorrys remain (pullback placeholder, CoV, independence). The proper implementations are in the Integration/ pipeline files. |

### Known Placeholders (honest, not smuggled)
| Location | Issue | Plan |
|----------|-------|------|
| `SuperDomainFunction.compose` (FiniteGrassmann.lean:2435) | Returns 0 for non-body coefficients | Superseded by `composeProper` in SuperCompose.lean |
| `SmoothFunction.extendToGrassmann` (FiniteGrassmann.lean:2395) | First-order Taylor only | Superseded by `smoothTaylorGrassmann` in NilpotentTaylor.lean |
| `IntegralForm.pullback` (BerezinIntegration.lean:255) | Body is `sorry` | Superseded by `pullbackProper` in Pullback.lean |
| `splittingObstruction` (Batchelor.lean) | Returns `Unit` | Needs sheaf cohomology infrastructure |

---

## Sorry Classification

### Category A: Smoothness — `berezinianCarrierAt_grassmannSmooth`
The Berezinian `det(A - BD^{-1}C) * det(D)^{-1}` involves:
- `det_even_grassmannSmooth` (proven) — det of even matrix with smooth entries has smooth .val
- `finiteGrassmann_inv_grassmannSmooth` (proven) — Grassmann inverse preserves smoothness
- **Missing**: matrix inverse entries GrassmannSmooth (needs adjugate entries + Ring.inverse = Lambda.inv bridge)

### Category B: Assembly Proofs (GlobalStokes.lean)
- `berezin_change_of_variables` — connects pullback + Berezinian + body integral
- `globalBerezinIntegral_independent_proper` — uses change of variables + cocycle
- `globalExteriorDerivative.compatible_body` — exterior derivative commutes with body projection

### Category C: Deep Mathematics (Independent of Integration)
- `batchelor_theorem` / `batchelor_splitting` (Batchelor.lean)
- `splitting_nonuniqueness` (Batchelor.lean)

---

## Key Proven Infrastructure (Reusable)

| Component | File | Used By |
|-----------|------|---------|
| `grassmann_soul_nilpotent` | FiniteGrassmann.lean | Phase 1 (Taylor termination) |
| `hasNoConstant_pow_vanishes` | NilpotentInverse.lean | Phase 4 (geometric inverse) |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | Phases 4, 5 |
| `grassmannExplicitInverse_mul_right/left` | NilpotentInverse.lean | Bridge to Classical.choose |
| `finiteGrassmann_inv_val_eq_explicit` | NilpotentInverse.lean | Classical.choose = geometric series |
| `finiteGrassmann_inv_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |
| `det_even_grassmannSmooth` | NilpotentInverse.lean | Determinant smoothness |
| `evenProd_grassmannSmooth` | NilpotentInverse.lean | Product smoothness |
| `matMul_grassmannSmooth` | NilpotentInverse.lean | Matrix product smoothness |
| `matSub_grassmannSmooth` | NilpotentInverse.lean | Matrix subtraction smoothness |
| `GrassmannSmooth.zsmul_const` | NilpotentInverse.lean | Integer scalar mult smoothness |
| `smoothTaylorGrassmann` | NilpotentTaylor.lean | Phase 2 (composition) |
| `composeEvalAt` | SuperCompose.lean | Phases 3, 5 |
| `pullbackEvalAt` | Pullback.lean | Phases 6-8 |
| `normalizedPartition_sum_one` | PartitionOfUnity.lean | Phase 5 |
| `SuperJacobian.berezinianAt` | FiniteGrassmann.lean | Phase 3 (pullback) |
| `SuperMatrix.ber_mul` | BerezinianMul.lean | Phase 3 (pullback composition) |
| `berezinian_cocycle_from_chain_rule` | SuperChainRule.lean | Phase 7 |
| `body_jacobian_cocycle` | BerezinIntegration.lean | Phase 6 |
| `berezin_lift_factor` | BerezinIntegration.lean | Phase 5 |
| `berezinIntegralOdd_add/smul` | BerezinIntegration.lean | Phases 6-8 |
| `partialEven` / `partialOdd` | Supermanifolds.lean | Phase 1 |
| `SuperDomainFunction.mul` | SuperDomainAlgebra.lean | All phases |
| Local Stokes (2 theorems) | StokesTheorem.lean | Phase 8 |
| `FiniteGrassmannCarrier q` Ring | FiniteGrassmann.lean | All phases |

---

## File Organization

```
Supermanifolds/
  Helpers/
    NilpotentTaylor.lean       -- Phase 1: Full Taylor expansion (0 sorrys)
    NilpotentInverse.lean      -- Phase 4: (1+e)^-1 + bridge + det/product smoothness (0 sorrys)
    GrassmannSmooth.lean       -- GrassmannSmooth predicate + closure properties (0 sorrys)
    FiniteGrassmann.lean       -- Core algebra (old compose placeholder remains)
    ...other helpers...
  Integration/
    SuperCompose.lean          -- Phase 2: composeEvalAt + composeProper (0 sorrys)
    Pullback.lean              -- Phase 3: IntegralForm.pullbackProper (1 sorry)
    PartitionOfUnity.lean      -- Phase 5: super PU from body PU (0 sorrys)
    GlobalStokes.lean          -- Phases 6-8: CoV + independence + Stokes (3 sorrys)
    IntegralFormCodim.lean     -- Codim-1 integral forms (0 sorrys)
    ExteriorDerivative.lean    -- d = d_0 (0 sorrys)
    StokesTheorem.lean         -- Local Stokes proven (0 sorrys)
  ProofIdeas/
    PLAN.md                    -- High-level integration plan
    DesignNotes.md             -- Architecture decisions
    PartitionOfUnity.md        -- PU proof strategy
    StokesTheorem.md           -- Stokes proof strategy
    SuperComposition.md        -- Composition proof strategy
  BerezinIntegration.lean      -- Original pipeline (superseded by Integration/)
  ...other files...
```

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199): sections 3.1-3.5
- Rogers, "Supermanifolds" (2007): Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
- Deligne-Morgan, "Notes on Supersymmetry" (for supermatrix algebra)
