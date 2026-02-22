# Integration Pipeline — Development Plan

## Architecture

**Track A (Local)**: Codimension-1 forms → d₀ → divergence → local Stokes. **COMPLETE (0 sorrys).**

**Track B (Global)**: Super composition → pullback → PU → CoV → independence → global Stokes. **Definitions corrected, 3 sorrys remain in GlobalStokes.lean.**

---

## Current State

### Complete (0 sorrys, genuinely proven)

| File | Content |
|------|---------|
| Helpers/NilpotentTaylor.lean | Full Taylor expansion in nilpotent elements |
| Helpers/NilpotentInverse.lean | (1+ε)⁻¹ via geometric series, bridge lemmas, det/adjugate/matInv smoothness |
| Helpers/GrassmannSmooth.lean | GrassmannSmooth predicate and closure properties |
| Helpers/SuperChainRule.lean | `berezinian_cocycle_from_chain_rule` |
| Helpers/BerezinianMul.lean | `ber_mul` (2900+ lines) |
| Helpers/Berezinian.lean | Ber computation |
| Integration/SuperCompose.lean | `composeEvalAt`, `composeProper` |
| Integration/Pullback.lean | `pullbackEvalAt`, `pullbackProper`, `berezinianCarrierAt_grassmannSmooth` |
| Integration/PartitionOfUnity.lean | `normalizedPartition_sum_one` (algebraic core) |
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms |
| Integration/ExteriorDerivative.lean | d₀, linearity, `d0_is_divergence` |
| Integration/StokesTheorem.lean | Local Stokes: super → classical divergence |

### Honest Sorrys (correct signatures, proofs pending)

| Location | Sorry | What's Needed |
|----------|-------|---------------|
| GlobalStokes.lean | `berezin_change_of_variables` | Body-level reduction lemma |
| GlobalStokes.lean | `globalBerezinIntegral_independent_proper` | Double-sum trick + PU fix |
| GlobalStokes.lean | `global_super_stokes_no_boundary` | Leibniz rule + partition derivative cancellation |
| BerezinIntegration.lean | `partition_of_unity_exists` | Connect Mathlib paracompactness |
| BerezinIntegration.lean | `globalBerezinIntegral_independent` | Same as `_proper` version |
| BerezinIntegration.lean | `berezin_change_of_variables_formula` | Legacy, superseded by GlobalStokes |
| BerezinIntegration.lean | `IntegralForm.pullback` | Superseded by `pullbackProper` |

### Definition Fix Needed

**`SuperPartitionOfUnity.super_sum_eq_one`** — current formulation evaluates each ρ_α in its own chart. For the double-sum trick, we need `Σ_α (ρ_α composed to chart β) = 1` in a single chart. Must reformulate to use `composeEvalAt`. See GlobalStokes.md for details.

---

## Proof Dependencies

```
berezin_change_of_variables
  ← body-level reduction lemma (NEW)
  ← pullbackEvalAt, berezinianCarrierAt (Pullback.lean) ✓
  ← BodyIntegral.SatisfiesChangeOfVar (fixed) ✓

globalBerezinIntegral_independent_proper
  ← berezin_change_of_variables
  ← SatisfiesSuperCocycle (fixed) ✓
  ← super_sum_eq_one IN A SINGLE CHART (needs PU definition fix)
  ← BodyIntegral.IsLinear ✓

global_super_stokes_no_boundary
  ← Leibniz rule: d₀(ρ·ν) = ρ·d₀ν + correction (NEW)
  ← partialEven_mul: product rule for ∂/∂xⁱ on products (NEW)
  ← d0_is_divergence ✓
  ← hDivThm (hypothesis: classical divergence theorem)
  ← partition derivative cancellation: ∂(Σρ_α)/∂xⁱ = 0
    ← super_sum_eq_one in single chart (needs PU fix)
```

---

## Execution Order

### Step 1: Fix SuperPartitionOfUnity definition

Reformulate `super_sum_eq_one` to require sum-to-one after composing all functions to a common chart:

```lean
super_sum_eq_one_in_chart : ∀ (β : SuperChart M)
    (transitions : index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt ...) = 1),
    Σ_α composeEvalAt (functions α) (transitions α) x = 1
```

This is exactly what `normalizedPartition_sum_one` proves. The Witten construction:
1. Lift ρ̃_α to chart α (θ-independent there)
2. Compose to common chart β via transitions → picks up θ-dependence
3. Raw sum S = 1 + nilpotent (body sum = 1, soul nilpotent)
4. S is invertible: S⁻¹ = geometric series
5. Normalize: ρ_α := (lift ρ̃_α ∘ T) · S⁻¹
6. Sum: Σ ρ_α = S · S⁻¹ = 1

All algebraic infrastructure for this is already proven.

### Step 2: Prove `partialEven_mul` (product rule)

```lean
theorem partialEven_mul (i : Fin p) (f g : SuperDomainFunction p q) :
    partialEven i (SuperDomainFunction.mul f g) =
    SuperDomainFunction.add
      (SuperDomainFunction.mul (partialEven i f) g)
      (SuperDomainFunction.mul f (partialEven i g))
```

Strategy: At each coefficient I and point x, this reduces to showing that
fderiv of the Grassmann product formula respects the Leibniz rule. Use
`fderiv_mul` from Mathlib applied to each term in the sum.

### Step 3: Prove Leibniz rule for d₀

Using `partialEven_mul`, show:

```lean
theorem d0_leibniz (ρ : SuperDomainFunction p q) (ν : IntegralFormCodim1 p q) :
    d0Codim1 (mulByCodim1 ρ ν) =
    IntegralForm.mulByFunction ρ (d0Codim1 ν) +
    correction_term ρ ν
```

where `correction_term ρ ν` is Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · fᵢ.

### Step 4: Prove body-level reduction lemma

Show that `berezinIntegralOdd(pullbackProper φ ω)` at body level equals
`(berezinIntegralOdd ω) ∘ φ.bodyMap · det(body Jacobian)`.

### Step 5: Prove `berezin_change_of_variables`

Combine body-level reduction with `hChangeOfVar.change_of_var`.

### Step 6: Prove `globalBerezinIntegral_independent_proper`

Double-sum trick using Steps 1 and 5.

### Step 7: Prove `global_super_stokes_no_boundary`

Leibniz (Step 3) + local Stokes + partition derivative cancellation (Step 1).

---

## Available Berezinian Infrastructure

| Lemma | File | Used By |
|-------|------|---------|
| `ber_mul` | BerezinianMul.lean | `berezinian_cocycle_from_chain_rule` |
| `SuperMatrix.ber` | Berezinian.lean | `berezinianAt`, `pullbackEvalAt` |
| `berezinianCarrierAt` | Pullback.lean | `pullbackProper`, CoV body reduction |
| `berezinianCarrierAt_grassmannSmooth` | Pullback.lean | Smoothness of Ber coefficients |
| `berezinian_cocycle_from_chain_rule` | SuperChainRule.lean | `berezinian_cocycle_full` |
| `ringInverse_eq_grassmannInv` | NilpotentInverse.lean | Bridge: Ring.inverse = geom series |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | PU normalization (S · S⁻¹ = 1) |
| `det_even_grassmannSmooth` | NilpotentInverse.lean | Determinant smoothness |
| `adjugate_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |
| `matInv_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |

---

## Key Definitions (Post-Audit, Verified Sound)

| Definition | Status |
|------------|--------|
| `BodyIntegral.SatisfiesChangeOfVar` | Fixed: requires Φ, hBij, signed det (not \|det\|) |
| `globalBerezinIntegral` | Fixed: bodyIntegral takes Set argument |
| `SuperPartitionOfUnity.super_sum_eq_one` | **NEEDS FIX**: must be in single chart |
| `GlobalIntegralForm.SatisfiesSuperCocycle` | Fixed: restricted to SuperTransition |
| `GlobalIntegralForm.compatible_body` | Fixed: signed det (not \|det\|) |

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199)
- Rogers, "Supermanifolds" (2007), Chapter 11
- Bernstein-Leites, "Integral Forms And Stokes Formula" (1977)
