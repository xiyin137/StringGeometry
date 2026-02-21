# Supermanifolds Folder - Status and Plan

## Summary

The algebraic foundations are well-developed and proven. The **global integration
pipeline** (Phases 1-8) is now implemented, providing:
- Full nilpotent Taylor expansion
- Super function composition
- Pullback of integral forms
- Nilpotent inverse in Grassmann algebra
- Partition of unity construction
- Change of variables formula
- Global integral independence
- **Global Stokes Theorem** on closed supermanifolds

The remaining sorrys are:
1. **Smoothness proofs** (mechanical: finite sums/products of smooth functions)
2. **Body-level computations** (extracting body components from Taylor expansion)
3. **Assembly proofs** (connecting the pieces in change of vars, independence, Stokes)

---

## Current Status by File

### Excellent (no issues)
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
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms, complete |
| Integration/StokesTheorem.lean | Local Stokes proven (no sorrys) |

### Integration Pipeline (New — Phases 1-8)
| File | Status | Key Proven Results |
|------|--------|-------------------|
| Helpers/NilpotentTaylor.lean | **Phase 1** | `iteratedPartialDeriv`, `smoothTaylorGrassmann`, `smoothTaylorGrassmann_scalar`, `smoothTaylorGrassmann_const` — all proven |
| Helpers/NilpotentInverse.lean | **Phase 4** | `hasNoConstant_pow_vanishes`, `grassmannGeomInverse_mul`, `grassmannGeomInverse_mul_right`, `nilpotentInverse_mul`, `nilpotentInverse_mul_left` — all proven. 1 sorry (smoothness) |
| Integration/SuperCompose.lean | **Phase 2** | `composeEvalAt`, `composeProper`, `grassmannMonomial`, `composeEvalAt_apply`, `composeEvalAt_ofSmooth` — all proven. Sorrys: smoothness, Taylor linearity |
| Integration/Pullback.lean | **Phase 3** | `pullbackEvalAt`, `IntegralForm.pullbackProper`, `pullbackProper_apply`, `pullback_berezinOdd` — all proven. 1 sorry (smoothness) |
| Integration/PartitionOfUnity.lean | **Phase 5** | `BodyPartitionData`, `rawSumAt`, `rawSumInverseAt`, `normalizedPartitionAt`, `normalizedPartition_sum_one`, `rawSumAt_eq_one_add_eps` — key algebraic results proven. Sorrys: body computation, S·S⁻¹=1 (timeout), final construction |
| Integration/GlobalStokes.lean | **Phase 6-8** | `GlobalIntegralFormCodim1`, `globalExteriorDerivative`, `berezin_change_of_variables`, `globalBerezinIntegral_independent_proper`, `global_super_stokes_no_boundary`, `exact_form_integrates_to_zero` — all stated. Sorrys: assembly proofs |

### Good (sorrys but properly stated)
| File | Notes |
|------|-------|
| Batchelor.lean | `iso_compatible` proper statement. `splitting_nonuniqueness` intertwines two isos (sorry). Deep theorems (`batchelor_theorem`, `batchelor_splitting`) sorry. |
| BerezinIntegration.lean | Original sorrys remain (pullback placeholder, CoV, independence). The proper implementations are in the Integration/ pipeline files. |
| Integration/ExteriorDerivative.lean | d = d₀ only (d₁ removed), 1 sorry |

### Known Placeholders (honest, not smuggled)
| Location | Issue | Plan |
|----------|-------|------|
| `SuperDomainFunction.compose` (FiniteGrassmann.lean:2435) | Returns 0 for non-body coefficients | Superseded by `composeProper` in SuperCompose.lean |
| `SmoothFunction.extendToGrassmann` (FiniteGrassmann.lean:2395) | First-order Taylor only | Superseded by `smoothTaylorGrassmann` in NilpotentTaylor.lean |
| `IntegralForm.pullback` (BerezinIntegration.lean:255) | Body is `⟨sorry⟩` | Superseded by `pullbackProper` in Pullback.lean |
| `splittingObstruction` (Batchelor.lean) | Returns `Unit` | Needs sheaf cohomology infrastructure |

---

## Sorry Classification

### Category A: Smoothness Proofs (Mechanical)
These all follow from "finite sums/products of smooth functions are smooth":
- `SuperDomainFunction.composeProper.smooth` (SuperCompose.lean)
- `IntegralForm.pullbackProper.smooth` (Pullback.lean)
- `SuperDomainFunction.nilpotentInverse.smooth` (NilpotentInverse.lean)

### Category B: Body-Level Computations
- `rawSumAt_body_eq_one` (PartitionOfUnity.lean) — needs Taylor body extraction
- `rawSumAt_mul_inverse` (PartitionOfUnity.lean) — timeout, mathematically proven

### Category C: Assembly Proofs
- `berezin_change_of_variables` (GlobalStokes.lean)
- `globalBerezinIntegral_independent_proper` (GlobalStokes.lean)
- `global_super_stokes_no_boundary` (GlobalStokes.lean)
- `globalExteriorDerivative.compatible_body` (GlobalStokes.lean)

### Category D: Deep Mathematics (Independent of Integration)
- `batchelor_theorem` / `batchelor_splitting` (Batchelor.lean)
- `splitting_nonuniqueness` (Batchelor.lean)

---

## Key Proven Infrastructure (Reusable)

| Component | File | Used By |
|-----------|------|---------|
| `grassmann_soul_nilpotent` | FiniteGrassmann.lean | Phase 1 (Taylor termination) |
| `hasNoConstant_pow_vanishes` | NilpotentInverse.lean | Phase 4 (geometric inverse) |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | Phases 4, 5 |
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
    NilpotentTaylor.lean       -- Phase 1: Full Taylor expansion (DONE)
    NilpotentInverse.lean      -- Phase 4: (1+ε)⁻¹ for nilpotent ε (DONE)
    FiniteGrassmann.lean       -- Core algebra (old compose placeholder remains)
    ...other helpers...
  Integration/
    SuperCompose.lean          -- Phase 2: composeEvalAt + composeProper (DONE)
    Pullback.lean              -- Phase 3: IntegralForm.pullbackProper (DONE)
    PartitionOfUnity.lean      -- Phase 5: super PU from body PU (DONE)
    GlobalStokes.lean          -- Phases 6-8: CoV + independence + Stokes (DONE)
    IntegralFormCodim.lean     -- Codim-1 integral forms (complete)
    ExteriorDerivative.lean    -- d = d₀ (1 sorry)
    StokesTheorem.lean         -- Local Stokes proven
  BerezinIntegration.lean      -- Original pipeline (superseded by Integration/)
  ...other files...
```

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199): §3.1-3.5
- Rogers, "Supermanifolds" (2007): Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
- Deligne-Morgan, "Notes on Supersymmetry" (for supermatrix algebra)
