# Supermanifolds Folder - Status and Plan

## Summary

The algebraic foundations are well-developed and proven. The **global integration
pipeline** has correct definitions and sound algebraic infrastructure.

**Post-audit status** (5 rounds of comprehensive audit):
- `BodyIntegral.SatisfiesChangeOfVar` — was vacuously strong (∀ U V f g, ∫f = ∫g),
  now properly parameterized by diffeomorphism Φ with pointwise equality constraint
- `globalBerezinIntegral` — now takes `Set` argument for domain localization
- `SuperPartitionOfUnity` — now requires `super_sum_eq_one` (full super-level Σ ρ_α = 1),
  not just body-level sum
- `GlobalIntegralForm.SatisfiesSuperCocycle` — full pullback cocycle condition using
  `pullbackEvalAt`, now restricted to atlas transitions via `SuperTransition.toSuperCoordChange`
  (was universally quantified over ALL `SuperCoordChange`, making it unsatisfiable)
- `global_super_stokes_no_boundary` — `hLocalStokes` was per-chart (mathematically
  false in general), replaced with proper `hDivThm` classical divergence theorem
- StokesTheorem.lean hypotheses fixed (were tautological, now use `d0_is_divergence`)
- Legacy tautologies in BerezinIntegration.lean marked as such
- Misleading names (`berezin_measure_anticommute`, `berezin_fubini`) documented
- All vacuous proofs reverted to honest sorrys

**What IS genuinely proven** (real theorems, not tautologies):
- Local reduction: super Stokes → classical divergence theorem (via `d0_is_divergence`)
- All algebraic infrastructure (Taylor, composition, pullback, Berezinian, partition normalization)
- Berezinian cocycle from chain rule

**What is NOT proven** (honest sorrys):
- Global Berezin integral independent of PU choice
- Global Stokes theorem
- Super PU exists from body PU + Mathlib paracompactness
- Berezin change of variables (super pullback → body-level CoV)

**What is NOT yet formalized** (needed infrastructure):
- Leibniz rule for d₀ on products: d₀(ρ · ν) = ρ · d₀ν + correction
- `partialEven_mul`: product rule ∂(fg)/∂xⁱ = (∂f/∂xⁱ)g + f(∂g/∂xⁱ)
- Concrete body integral via Mathlib measure-theoretic integration

**Definition fix needed**:
- `SuperPartitionOfUnity.super_sum_eq_one` currently evaluates each ρ_α in its
  OWN chart — too weak for double-sum trick. Must reformulate to require
  `Σ_α composeEvalAt(ρ_α, T_{αβ}, x) = 1` in a single chart β.
  The algebraic infrastructure is already proven (`normalizedPartition_sum_one`).

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
| Helpers/FiniteGrassmann.lean | Ring instance, SuperCommutative, `grassmann_soul_nilpotent` proven |
| Helpers/SuperChainRule.lean | `berezinian_cocycle_from_chain_rule` proven |
| Helpers/PartialOddLeibniz.lean | Sign lemmas for Leibniz rule |
| Helpers/GrassmannSmooth.lean | GrassmannSmooth predicate, all closure properties proven |
| Helpers/NilpotentTaylor.lean | Full Taylor expansion, all proven (0 sorrys) |
| Helpers/NilpotentInverse.lean | Geometric series inverse, bridge lemmas — all proven (0 sorrys) |
| Integration/SuperCompose.lean | Super function composition — all proven (0 sorrys) |
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms, complete |
| Integration/StokesTheorem.lean | Local Stokes via d0_is_divergence reduction (0 sorrys). Hypothesis is classical divergence theorem, NOT a restatement of conclusion |
| Integration/Pullback.lean | pullbackProper, berezinianCarrierAt_grassmannSmooth — all proven (0 sorrys) |
| Integration/ExteriorDerivative.lean | Super exterior derivative d = d_0, linearity, divergence characterization (0 sorrys) |

### Has Honest Sorrys (definitions correct, proofs pending)
| File | Sorrys | Notes |
|------|--------|-------|
| Integration/PartitionOfUnity.lean | 0 | All proven. But `SuperPartitionOfUnity.super_sum_eq_one` definition needs reformulation (see above) |
| Integration/GlobalStokes.lean | 3 | `berezin_change_of_variables`, `globalBerezinIntegral_independent_proper`, `global_super_stokes_no_boundary` — honest sorrys with correct signatures |
| BerezinIntegration.lean | 3 | `berezin_change_of_variables_formula` (legacy, superseded by GlobalStokes version), `partition_of_unity_exists`, `globalBerezinIntegral_independent` |

### Legacy/Tautological (marked, not counting as "proven")
| File | Notes |
|------|-------|
| BerezinIntegration.lean: `super_stokes` | Hypothesis restates conclusion. Superseded by StokesTheorem.lean |
| BerezinIntegration.lean: `super_divergence_theorem` | Proves `x = x` via rfl. Boundary integral not formalized |
| BerezinIntegration.lean: `IntegralForm.pullback` | `⟨sorry⟩`. Superseded by `pullbackProper` in Pullback.lean |

### Sorrys Independent of Integration Pipeline
| File | Notes |
|------|-------|
| Batchelor.lean | `batchelor_theorem`, `batchelor_splitting`, `splitting_nonuniqueness` — deep theorems |

---

## Remaining Work (Integration Pipeline)

### Priority 1: Leibniz Rule for d₀ on Products
**What**: Formalize d₀(ρ · ν) = ρ · d₀ν + Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · fᵢ
for a super function ρ and codim-1 form ν = Σᵢ fᵢ d̂xⁱ δ(dθ).
**Why**: This is needed for global Stokes (to decompose ρ_α · dν into d(ρ_α · ν)
minus a correction term that cancels when summed over α).
**How**: Direct computation using partialEven and the product rule for fderiv.
**File**: New infrastructure in Integration/ExteriorDerivative.lean or a new file.

### Priority 2: Prove `berezin_change_of_variables` (GlobalStokes.lean)
**What**: Show `∫_U φ*(ω) = ∫_V ω` using the corrected `SatisfiesChangeOfVar`.
**Requires**: Body-level reduction lemma.
**How**:
1. Show that pullbackProper extracts to `(f ∘ φ_body) · |det J_body|` at top θ-component
2. Apply `hChangeOfVar.change_of_var` with Φ = φ.bodyMap
3. Match the pointwise equality condition `hfΦJ` using Berezinian body-level identity

### Priority 3: Prove `globalBerezinIntegral_independent_proper` (GlobalStokes.lean)
**What**: Independence of partition of unity choice.
**Requires**: Super-level PU sum = 1 (`super_sum_eq_one`), full super cocycle
(`SatisfiesSuperCocycle`), change of variables (Priority 2).
**How**: Double-sum trick (Witten §3.1):
1. Insert 1 = Σ_β σ_β
2. Use super cocycle to relate f_α and f_β on overlaps
3. Change of variables to switch integration domains
4. Reorder sum and use Σ_α ρ_α = 1

### Priority 4: Prove `global_super_stokes_no_boundary` (GlobalStokes.lean)
**What**: ∫_M dν = 0 for closed M.
**Requires**: Leibniz rule (Priority 1), local Stokes, super PU sum = 1.
**How**:
1. Leibniz: ρ_α · dν = d(ρ_α · ν) - correction_α
2. Each ∫ d(ρ_α · ν) = 0 by local Stokes (compact support) + hDivThm
3. Σ_α correction_α = 0 because ∂(Σ_α ρ_α)/∂xⁱ = ∂1/∂xⁱ = 0

### Priority 5: `partition_of_unity_exists` (BerezinIntegration.lean)
**What**: Derive SuperPartitionOfUnity from Mathlib paracompactness.
**How**: Use Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, lift to super
via `superPartitionFromBody` (already implemented for body level).

---

## Key Proven Infrastructure (Reusable)

| Component | File | Used By |
|-----------|------|---------|
| `grassmann_soul_nilpotent` | FiniteGrassmann.lean | Phase 1 (Taylor termination) |
| `hasNoConstant_pow_vanishes` | NilpotentInverse.lean | Phase 4 (geometric inverse) |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | Phases 4, 5 |
| `finiteGrassmann_inv_val_eq_explicit` | NilpotentInverse.lean | Classical.choose = geometric series |
| `finiteGrassmann_inv_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |
| `det_even_grassmannSmooth` | NilpotentInverse.lean | Determinant smoothness |
| `adjugate_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness (Pullback) |
| `matInv_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness (Pullback) |
| `ringInverse_even_grassmannSmooth` | NilpotentInverse.lean | Ring.inverse smoothness |
| `ringInverse_eq_grassmannInv` | NilpotentInverse.lean | Bridge: Ring.inverse = geometric series |
| `berezinianCarrierAt_grassmannSmooth` | Pullback.lean | Phase 3 (pullback smoothness) |
| `smoothTaylorGrassmann` | NilpotentTaylor.lean | Phase 2 (composition) |
| `composeEvalAt` | SuperCompose.lean | Phases 3, 5 |
| `pullbackEvalAt` | Pullback.lean | Phases 6-8 |
| `normalizedPartition_sum_one` | PartitionOfUnity.lean | Phase 5 |
| `SuperJacobian.berezinianAt` | FiniteGrassmann.lean | Phase 3 (pullback) |
| `SuperMatrix.ber_mul` | BerezinianMul.lean | Phase 3 (pullback composition) |
| `berezinian_cocycle_from_chain_rule` | SuperChainRule.lean | Phase 7 |
| `d0_is_divergence` | ExteriorDerivative.lean | Local Stokes reduction |
| Local Stokes (2 theorems) | StokesTheorem.lean | Global Stokes |

---

## Definitions Audit Summary (4 rounds)

### Fixed across audit rounds:
| Issue | Location | Fix |
|-------|----------|-----|
| **C1**: `SatisfiesChangeOfVar` vacuous | BerezinIntegration.lean | Now requires diffeomorphism Φ, pointwise equality `fΦJ(x) = f(Φ(x)) · det DΦ(x)` (signed det, not \|det\|) |
| **C2**: `globalBerezinIntegral` no domain | BerezinIntegration.lean | `bodyIntegral` now takes `Set (Fin p → ℝ)` argument |
| **C3**: `SuperPartitionOfUnity` body-only sum | BerezinIntegration.lean | Added `super_sum_eq_one` field for all multi-indices I |
| **H1**: Body-only cocycle | GlobalStokes.lean | Added `SatisfiesSuperCocycle` using `pullbackEvalAt` |
| **H1b**: `SatisfiesSuperCocycle` over-quantified | GlobalStokes.lean | φ now tied to `SuperTransition` via `toSuperCoordChange`, not arbitrary |
| **H2-H4**: Vacuous proofs exploiting C1 | GlobalStokes.lean | Reverted to honest sorrys |
| **H5**: StokesTheorem hypotheses vacuous | StokesTheorem.lean | Now uses `d0_is_divergence` + classical divergence theorem |
| **H6**: `hLocalStokes` per-chart (false) | GlobalStokes.lean | Replaced with `hDivThm` (classical divergence theorem for compactly supported vector fields) |

### Investigated and confirmed correct (round 5):
| Item | Location | Analysis |
|------|----------|----------|
| `compatible_body` det factor | BerezinIntegration.lean | det(D_body) cancels between composition and Berezinian. Now uses signed `(det bodyJac)⁻¹` (not `\|det\|⁻¹`) — correct for integral forms (Berezinian sections), not measure-theoretic densities. |
| `berezin_measure_anticommute` | BerezinIntegration.lean | Just `rfl` (definitional unfolding of `berezinIntegralOdd`). Misleading name documented. |
| `berezin_fubini` | BerezinIntegration.lean | Just `rfl`. NOT Fubini's theorem. Would need partial Berezin integration infrastructure. Documented. |

### Sound definitions (verified across 5 audit rounds):
- `localBerezinIntegral`, `berezinIntegralOdd`, `IntegralForm`, `SuperCoordChange`
- `SuperPartitionOfUnity` (all fields), `BodyPartitionData`, `rawSumAt`
- `pullbackEvalAt`, `composeEvalAt`, `berezinianCarrierAt`
- `normalizedPartitionAt`, `normalizedPartition_sum_one`
- `GlobalIntegralFormCodim1.compatible_body`, `globalExteriorDerivative`
- `d0Codim1`, `superExteriorDerivativeCodim1`, `bodyDivergence`, `signedBerezinComponents`
- `d0_is_divergence` (genuine algebraic theorem)
- `SuperCoordChange.jacobian` (correct parity proofs)
- `BodyIntegral.SatisfiesChangeOfVar` (corrected)
- `BodyIntegral.IsLinear`
- `GlobalIntegralForm.SatisfiesSuperCocycle` (now restricted to atlas transitions)
- `SuperTransition.toSuperCoordChange` (bridge between `SuperTransition` and `SuperCoordChange`)
- All of NilpotentTaylor.lean, NilpotentInverse.lean, SuperCompose.lean, Pullback.lean

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199): sections 3.1-3.5
- Rogers, "Supermanifolds" (2007): Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
- Deligne-Morgan, "Notes on Supersymmetry" (for supermatrix algebra)
