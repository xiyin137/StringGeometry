# Supermanifolds Folder - Status and Plan

## Summary

The algebraic foundations are substantial, with most local integration
infrastructure formalized. Global assembly still has open proof obligations.

**Post-audit status** (5 rounds of comprehensive audit + targeted fixes):
- `BodyIntegral.SatisfiesChangeOfVar` — was vacuously strong, now properly parameterized
- `globalBerezinIntegral` — now takes `Set` argument for domain localization
- `SuperPartitionOfUnity` — `super_sum_eq_one` REMOVED from structure (was vacuous:
  evaluated each ρ_α in its own chart). Now an explicit `hSuperSum` hypothesis
  in GlobalStokes.lean using `composeEvalAt`
- `GlobalIntegralForm.SatisfiesSuperCocycle` — restricted to atlas transitions
- `global_super_stokes_no_boundary` — proper `hDivThm` classical divergence theorem
- StokesTheorem.lean hypotheses fixed (now use `d0_is_divergence`)
- All vacuous proofs reverted to honest sorrys

**What IS genuinely proven** (real theorems, not tautologies):
- Local reduction: super Stokes → classical divergence theorem (via `d0_is_divergence`)
- Core algebraic infrastructure used by the active pipeline (Taylor, composition,
  pullback, Berezinian, partition normalization)
- Berezinian cocycle from chain rule
- `partialEven_mul`: product rule for ∂/∂xⁱ on Grassmann products

**Current folder total**: 27 `sorry` occurrences (allowlisted and tracked).

**What is NOT proven** (honest sorrys):
- Global Berezin integral independent of PU choice
- Global Stokes theorem
- Super PU exists from body PU + Mathlib paracompactness
- Body-level pullback identity needed by CoV bridge (`hPullbackBody`)

**Recently completed**:
- Leibniz rule for d₀ on products: `d0Codim1_mulByFunction`
  (proved in `Integration/ExteriorDerivative.lean`)

---

## Current Status by File

### Excellent (no sorrys, genuinely proven)
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
| Helpers/PartialOddLeibniz.lean | Sign lemmas for Leibniz rule |
| Helpers/GrassmannSmooth.lean | GrassmannSmooth predicate, all closure properties proven |
| Helpers/NilpotentTaylor.lean | Full Taylor expansion, all proven (0 sorrys) |
| Helpers/NilpotentInverse.lean | Geometric series inverse, bridge lemmas — all proven (0 sorrys) |
| Integration/SuperCompose.lean | Super function composition — all proven (0 sorrys) |
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms, complete |
| Integration/PartitionOfUnity.lean | All proven |
| Integration/StokesTheorem.lean | Local Stokes via d0_is_divergence reduction (0 sorrys) |
| Integration/Pullback.lean | pullbackProper, berezinianCarrierAt_grassmannSmooth — all proven (0 sorrys) |
| Integration/ExteriorDerivative.lean | d₀, linearity, `d0_is_divergence`, `partialEven_mul`, `d0Codim1_mulByFunction` (0 sorrys) |

### Has Honest Sorrys (definitions mostly correct, proofs pending)
| File | Sorrys | Notes |
|------|--------|-------|
| Helpers/FiniteGrassmann.lean | 3 | Legacy approximate composition (`composeLegacyApprox`) and downstream placeholder theorem |
| Helpers/SuperChainRule.lean | 5 | Legacy full-cocycle-to-chain-rule bridge has pending proofs |
| Integration/GlobalStokes.lean | 2 | `globalBerezinIntegral_independent_proper`, `global_super_stokes_no_boundary` |
| BerezinIntegration.lean | 4 | `pullbackLegacy`, `berezin_change_of_variables_formula_legacy`, `partition_of_unity_exists`, `globalBerezinIntegral_independent` |
| Helpers/FormalPowerSeries.lean | 1 | Jacobi identity bridge step remains sorry |
| FPS/LogExp.lean | 1 | Inverse identity bridge step remains sorry |

### Legacy/Tautological (marked, not counting as "proven")
| File | Notes |
|------|-------|
| BerezinIntegration.lean: `super_stokes_legacy` | Hypothesis restates conclusion. Superseded by StokesTheorem.lean |
| BerezinIntegration.lean: `super_divergence_theorem_legacy` | Proves `x = x` via rfl. Boundary integral not formalized |
| BerezinIntegration.lean: `IntegralForm.pullbackLegacy` | `⟨sorry⟩`. Superseded by `pullbackProper` in Pullback.lean |
| Integration/Legacy.lean | Deprecated compatibility aliases for legacy names |

### Sorrys Independent of Integration Pipeline
| File | Notes |
|------|-------|
| Batchelor.lean | `batchelor_theorem`, `batchelor_splitting`, `splitting_nonuniqueness` — deep theorems |

---

## Remaining Work (Integration Pipeline)

### Priority 1: Leibniz Rule for d₀ on Products — DONE
**Result**: `d0Codim1_mulByFunction` and `wedgeEvenDeriv` are now formalized in
`Integration/ExteriorDerivative.lean`.
**Use**: This is the key algebraic decomposition step for the global Stokes proof.

### Priority 2: Prove Body-Level Pullback Identity (`hPullbackBody`)
**Status**: `berezin_change_of_variables` is now proven in `GlobalStokes.lean`
using an explicit bridge hypothesis `hPullbackBody`.
**What remains**: Discharge that hypothesis from Pullback/Berezinian infrastructure:
`berezinIntegralOdd (pullbackProper φ ω).coefficient =
  (berezinIntegralOdd ω.coefficient) ∘ φ.bodyMap · det(Dφ.bodyMap)`.

### Priority 3: Prove `globalBerezinIntegral_independent_proper` (GlobalStokes.lean)
**What**: Independence of partition of unity choice.
**Requires**: `hSuperSum` hypothesis (✓), super cocycle (✓), change of variables (P2).
**How**: Double-sum trick (Witten §3.1)

### Priority 4: Prove `global_super_stokes_no_boundary` (GlobalStokes.lean)
**What**: ∫_M dν = 0 for closed M.
**Requires**: Leibniz rule (P1), local Stokes (✓), `hSuperSum` (✓).
**How**:
1. Leibniz: ρ_α · dν = d(ρ_α · ν) - correction_α
2. Each ∫ d(ρ_α · ν) = 0 by hDivThm
3. Σ_α correction_α = 0 because ∂(Σ_α ρ_α)/∂xⁱ = ∂1/∂xⁱ = 0

### Priority 5: `partition_of_unity_exists` (BerezinIntegration.lean)
**What**: Derive SuperPartitionOfUnity from Mathlib paracompactness.
**How**: Use Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, lift to super
via `superPartitionFromBody`.

---

## Dependency Flowchart (Global Stokes)

```text
Local algebraic derivative layer
--------------------------------
partialEven_mul
  └─> d0Codim1_mulByFunction (DONE)
        └─> Leibniz decomposition for chart terms: d0(ρ·ν) = ρ·d0(ν) + correction

Local integration layer
-----------------------
d0_is_divergence
super_stokes_codim1_no_boundary (StokesTheorem.lean)
hDivThm (classical divergence theorem hypothesis)
  └─> local chartwise vanishing of exact terms

Global change-of-variables layer
--------------------------------
pullbackEvalAt + berezinianCarrierAt + BodyIntegral.SatisfiesChangeOfVar
  └─> hPullbackBody bridge lemma (TODO)
        └─> berezin_change_of_variables (DONE, via bridge hypothesis)
              └─> globalBerezinIntegral_independent_proper (TODO, GlobalStokes.lean)

Global partition layer
----------------------
hSuperSum (super partition identity: Σ ρ_α = 1 in common chart)
SatisfiesSuperCocycle
BodyIntegral.IsLinear
  ├─> used in globalBerezinIntegral_independent_proper
  └─> correction-term cancellation in global_super_stokes_no_boundary

Final theorem
-------------
d0Codim1_mulByFunction
+ d0_is_divergence
+ super_stokes_codim1_no_boundary / hDivThm
+ hSuperSum cancellation
  └─> global_super_stokes_no_boundary (TODO, GlobalStokes.lean)
```

---

## Key Proven Infrastructure (Reusable)

| Component | File | Used By |
|-----------|------|---------|
| `grassmann_soul_nilpotent` | FiniteGrassmann.lean | Phase 1 (Taylor termination) |
| `hasNoConstant_pow_vanishes` | NilpotentInverse.lean | Phase 4 (geometric inverse) |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | Phases 4, 5 |
| `ringInverse_eq_grassmannInv` | NilpotentInverse.lean | Classical.choose = geometric series |
| `finiteGrassmann_inv_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |
| `det_even_grassmannSmooth` | NilpotentInverse.lean | Determinant smoothness |
| `adjugate_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness (Pullback) |
| `matInv_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness (Pullback) |
| `ringInverse_even_grassmannSmooth` | NilpotentInverse.lean | Ring.inverse smoothness |
| `berezinianCarrierAt_grassmannSmooth` | Pullback.lean | Phase 3 (pullback smoothness) |
| `smoothTaylorGrassmann` | NilpotentTaylor.lean | Phase 2 (composition) |
| `composeEvalAt` | SuperCompose.lean | Phases 3, 5 |
| `pullbackEvalAt` | Pullback.lean | Phases 6-8 |
| `normalizedPartition_sum_one` | PartitionOfUnity.lean | Phase 5 |
| `SuperMatrix.ber_mul` | BerezinianMul.lean | Phase 3 (pullback composition) |
| `berezinian_cocycle_from_chain_rule` | SuperChainRule.lean | Phase 7 |
| `d0_is_divergence` | ExteriorDerivative.lean | Local Stokes reduction |
| `partialEven_mul` | ExteriorDerivative.lean | Leibniz rule for d₀ |
| `d0Codim1_mulByFunction` | ExteriorDerivative.lean | Global Stokes decomposition step |
| Local Stokes (2 theorems) | StokesTheorem.lean | Global Stokes |

---

## Definitions Audit Summary (5 rounds)

### Fixed across audit rounds:
| Issue | Location | Fix |
|-------|----------|-----|
| **C1**: `SatisfiesChangeOfVar` vacuous | BerezinIntegration.lean | Now requires diffeomorphism Φ, signed det |
| **C2**: `globalBerezinIntegral` no domain | BerezinIntegration.lean | `bodyIntegral` now takes `Set` argument |
| **C3**: `SuperPartitionOfUnity` body-only sum | BerezinIntegration.lean | `super_sum_eq_one` REMOVED, now hypothesis `hSuperSum` |
| **H1**: Body-only cocycle | GlobalStokes.lean | Added `SatisfiesSuperCocycle` using `pullbackEvalAt` |
| **H1b**: `SatisfiesSuperCocycle` over-quantified | GlobalStokes.lean | Restricted to `SuperTransition` |
| **H2-H4**: Vacuous proofs exploiting C1 | GlobalStokes.lean | Reverted to honest sorrys |
| **H5**: StokesTheorem hypotheses vacuous | StokesTheorem.lean | Uses `d0_is_divergence` + classical div thm |
| **H6**: `hLocalStokes` per-chart (false) | GlobalStokes.lean | Replaced with `hDivThm` |

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199): sections 3.1-3.5
- Rogers, "Supermanifolds" (2007): Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
- Deligne-Morgan, "Notes on Supersymmetry" (for supermatrix algebra)
