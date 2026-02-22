# Global Stokes Theorem — Proof Ideas

## Status: 3 honest sorrys remaining in GlobalStokes.lean

## Overview of What's Needed

Three theorems need proofs:
1. `berezin_change_of_variables` — super CoV reduces to body CoV
2. `globalBerezinIntegral_independent_proper` — PU independence (double-sum trick)
3. `global_super_stokes_no_boundary` — ∫_M dν = 0

These depend on infrastructure that is partially built.

---

## 1. `berezin_change_of_variables`

**Statement**: ∫_U φ*(ω) = ∫_V ω under super coordinate change φ.

**Proof strategy**:

Step 1: Unfold both sides. LHS = bodyIntegral (berezinIntegralOdd (pullbackProper φ ω).coefficient) U.
RHS = bodyIntegral (berezinIntegralOdd ω.coefficient) V.

Step 2: The pullback coefficient is `composeEvalAt(f, φ, x) * berezinianCarrierAt(φ, x)`.
The Berezin integral extracts the top θ-component (Finset.univ coefficient).

Step 3: **Key body-level reduction lemma** (needs to be proved):
At body level (θ=0), the top-θ component of `(f ∘ φ) · Ber(J_φ)` equals
`f_top(φ_body(x)) · det(J_body(x))`.

Why: At θ=0, the only surviving term in the Grassmann product `(f ∘ φ) · Ber`
at the Finset.univ component comes from:
- `(f ∘ φ)_univ · Ber_∅` (top of f times body of Ber)
- All other terms have `(f ∘ φ)_I · Ber_J` with I ∪ J = univ, I ≠ univ,
  so Ber_J with J ≠ ∅ contributes nilpotent corrections.

At body level, these nilpotent corrections vanish, giving:
`berezinIntegralOdd(pullback) at body = f_top(φ_body(x)) · Ber_body(x)`

And `Ber_body = det(A_body)/det(D_body)`. After the det(D) cancellation in Berezin
integration (θ-substitution θ'=Dθ produces 1/det(D) which cancels the det(D) in the
Berezinian denominator), we get `det(A_body) = det(body Jacobian)`.

Step 4: Apply `hChangeOfVar.change_of_var` with Φ = φ.bodyMap, matching pointwise.

**Infrastructure needed**:
- Lemma: `berezinIntegralOdd(pullbackProper φ ω) = some function of (berezinIntegralOdd ω) ∘ φ.bodyMap`
- This requires extracting the top-θ component from the Grassmann product.
- The Grassmann product formula: `(a * b)_K = Σ_{I ∪ J = K, I ∩ J = ∅} sign(I,J) a_I b_J`
  is already implemented in `SuperDomainFunction.mul`.

**Available infrastructure**:
- `pullbackEvalAt` (Pullback.lean): computes the pullback at a body point
- `berezinianCarrierAt` (Pullback.lean): the Berezinian as Grassmann element
- `berezinianCarrierAt_grassmannSmooth` (Pullback.lean): smoothness of Ber coefficients
- `composeEvalAt` (SuperCompose.lean): super function composition at a point
- `BodyIntegral.SatisfiesChangeOfVar`: the classical CoV hypothesis (now properly formulated)

---

## 2. `globalBerezinIntegral_independent_proper`

**Statement**: Σ_α ∫_{U_α} ρ_α · f_α = Σ_β ∫_{U_β} σ_β · f_β

**Proof (double-sum trick, Witten §3.1)**:

Step 1: Insert 1 = Σ_β σ_β (super-level PU sum in chart α's coordinates):
  Σ_α ∫_{U_α} ρ_α · f_α = Σ_{α,β} ∫_{U_α} ρ_α · σ_β · f_α

Step 2: On U_α ∩ U_β, use super cocycle (SatisfiesSuperCocycle):
  f_α(x) = pullbackEvalAt(T_{βα}, f_β, x) = (f_β ∘ T)(x) · Ber(J)(x)

Step 3: Change of variables (theorem 1 above):
  ∫_{U_α} (ρ_α · σ_β) · f_α = ∫_{U_β} (ρ_α · σ_β) · f_β
  (The ρ_α · σ_β factor gets composed with the inverse transition)

Step 4: Reorder sum:
  = Σ_β ∫_{U_β} (Σ_α ρ_α) · σ_β · f_β
  = Σ_β ∫_{U_β} 1 · σ_β · f_β          (using Σ_α ρ_α = 1 in chart β)
  = Σ_β ∫_{U_β} σ_β · f_β

**Requirements**:
- `berezin_change_of_variables` (theorem 1)
- `SatisfiesSuperCocycle` on the GlobalIntegralForm
- `super_sum_eq_one` in a SINGLE chart (the Witten-normalized version)
- Linearity of bodyIntegral

**CRITICAL**: The `super_sum_eq_one` must hold in a single coordinate system.
The current formulation evaluates each ρ_α in its own chart — this is WRONG
for the double-sum trick. See section on PU fix below.

---

## 3. `global_super_stokes_no_boundary`

**Statement**: ∫_M dν = 0 for closed M.

**Proof outline**:

Step 1: Expand: ∫_M dν = Σ_α ∫_{U_α} ρ_α · (dν)_α

Step 2: Leibniz rule for d₀ on products:
  ρ_α · d₀(ν_α) = d₀(ρ_α · ν_α) - Σᵢ (-1)ⁱ (∂ρ_α/∂xⁱ) · (ν_α)_i

  where ν_α = Σᵢ fᵢ d̂xⁱ δ(dθ), so (ν_α)_i is the i-th component.

  This is the product rule: d₀(fg) = f·d₀g + d₀f · g, adapted to the
  codimension-1 form structure.

Step 3: Each ∫ d₀(ρ_α · ν_α) = 0:
  - ρ_α · ν_α has compact support in U_α (ρ_α vanishes on ∂U_α)
  - By d0_is_divergence: d₀(ρ_α · ν_α) = div(signed components)
  - By hDivThm: ∫_U div(compactly supported F) = 0

Step 4: Correction terms cancel:
  Σ_α Σᵢ (-1)ⁱ ∫ (∂ρ_α/∂xⁱ) · (ν_α)_i
  = Σᵢ (-1)ⁱ ∫ (∂(Σ_α ρ_α)/∂xⁱ) · fᵢ     (by linearity of ∂/∂xⁱ)
  = Σᵢ (-1)ⁱ ∫ (∂1/∂xⁱ) · fᵢ                (by Σ_α ρ_α = 1)
  = 0                                          (derivative of constant = 0)

Step 5: Combining: ∫_M dν = Σ_α [0 - correction_α] = 0 - 0 = 0.

**Infrastructure needed**:
(a) **Leibniz rule for d₀**: d₀(ρ · ν) = ρ · d₀ν + Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · fᵢ
    - This is a computation using `partialEven` and the product rule for fderiv
    - Should go in ExteriorDerivative.lean
    - The key identity: ∂(ρ·fᵢ)/∂xⁱ = ρ · ∂fᵢ/∂xⁱ + (∂ρ/∂xⁱ) · fᵢ
    - This follows from fderiv_mul (Mathlib)

(b) **Compact support of ρ_α · ν_α**: from `support_subset` of the PU

(c) **Partition derivative identity**: ∂(Σ_α ρ_α)/∂xⁱ = 0
    - Follows from Σ_α ρ_α = 1 (constant) and linearity of ∂/∂xⁱ
    - Needs super_sum_eq_one in a single chart (same issue as theorem 2)

(d) **Connection between ρ_α · ν_α and IntegralFormCodim1 structure**:
    - Need to show ρ_α · ν_α is a valid codim-1 form with compact support
    - Its components are ρ_α · fᵢ (super function times super function)

---

## SuperPartitionOfUnity Fix Needed

### Problem

The current `super_sum_eq_one` evaluates each `functions α` at chart α's own
coordinates. Since each function is `liftToSuper(ρ̃_α)` (θ-independent in its
own chart), the I≠∅ coefficients are trivially 0.

But for the double-sum trick and global Stokes, we need:
  **Σ_α (ρ_α expressed in chart β) = 1** as super functions in chart β.

When you express `liftToSuper(ρ̃_α)` in chart β via the transition T_{αβ},
you get θ-dependence from Taylor expansion. The raw sum in chart β is 1 + nilpotent,
NOT 1.

### Fix

The `SuperPartitionOfUnity` should store the **Witten-normalized** partition
functions, where each `functions α` is the normalized function expressed in
chart α's coordinates:

  ρ_α = (liftToSuper ρ̃_α) · S_α⁻¹

where S_α is the raw sum expressed in chart α. Then `super_sum_eq_one` should
require the sum after pulling back to any common chart β:

  Σ_α composeEvalAt(ρ_α, T_{αβ}, x) = 1

The existing `normalizedPartition_sum_one` already proves this for the
`normalizedPartitionAt` functions!

### Alternative (simpler)

Keep the PU structure as-is, but add a field for the composed/normalized sum:

```lean
super_sum_eq_one_in_chart : ∀ (β : SuperChart M)
    (transitions : index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ),
    Σ_α composeEvalAt(functions α, transitions α, x) = 1
```

This directly states what the double-sum trick needs.

### Infrastructure already available

- `rawSumAt`, `rawSumInverseAt` (PartitionOfUnity.lean)
- `normalizedPartitionAt` (PartitionOfUnity.lean)
- `normalizedPartition_sum_one` (PartitionOfUnity.lean): Σ_α norm_α = 1
- `rawSumAt_body_eq_one`: body of raw sum = 1
- `rawSumAt_mul_inverse`: S · S⁻¹ = 1
- `composeEvalAt` (SuperCompose.lean)
- `grassmannGeomInverse` (NilpotentInverse.lean)

---

## Leibniz Rule for d₀ — Detailed Strategy

### Mathematical Statement

For a super function ρ (even, in SuperDomainFunction p q) and a codim-1 form
ν = Σᵢ fᵢ d̂xⁱ δ(dθ):

  d₀(ρ · ν) = ρ · d₀ν + Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · fᵢ [Dx Dθ]

where ρ · ν is the codim-1 form with components (ρ · fᵢ).

### Proof

The i-th component of ρ · ν is `SuperDomainFunction.mul ρ (ν.components i)`.

d₀(ρ · ν) = Σᵢ (-1)ⁱ ∂(ρ · fᵢ)/∂xⁱ [Dx Dθ]

By the product rule for partialEven (needs to be proved):
  partialEven i (SuperDomainFunction.mul ρ f) =
  SuperDomainFunction.add
    (SuperDomainFunction.mul ρ (partialEven i f))
    (SuperDomainFunction.mul (partialEven i ρ) f)

This follows from the Leibniz rule for fderiv (fderiv_mul in Mathlib) applied
coefficient-by-coefficient.

Then:
  d₀(ρ · ν) = Σᵢ (-1)ⁱ [ρ · ∂fᵢ/∂xⁱ + (∂ρ/∂xⁱ) · fᵢ]
             = ρ · [Σᵢ (-1)ⁱ ∂fᵢ/∂xⁱ] + Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · fᵢ
             = ρ · d₀ν + correction

### Key helper lemma needed

```lean
theorem partialEven_mul {p q : ℕ} (i : Fin p) (f g : SuperDomainFunction p q) :
    partialEven i (SuperDomainFunction.mul f g) =
    SuperDomainFunction.add
      (SuperDomainFunction.mul (partialEven i f) g)
      (SuperDomainFunction.mul f (partialEven i g))
```

This is the main technical challenge. The proof requires:
1. Unfold `SuperDomainFunction.mul` to the Grassmann product formula
2. Apply fderiv to each term: fderiv(Σ sign · f_I · g_J) = Σ sign · (f_I' · g_J + f_I · g_J')
3. Regroup into two sums matching the RHS

The difficulty is that `SuperDomainFunction.mul` involves a sum over all
decompositions I ∪ J = K with signs (reorderSign). The product rule must be
applied to each term, and the result regrouped.

### Alternative approach for partialEven_mul

Instead of working through the full Grassmann product, observe that
at each body point x, `partialEven i` acts as `fderiv ℝ (·) x (eᵢ)` on
each coefficient. So we need:

  fderiv(f * g)_K(x)(eᵢ) = Σ_{I∪J=K} sign · [f_I'(x)(eᵢ) · g_J(x) + f_I(x) · g_J'(x)(eᵢ)]

This is just the product rule applied inside the sum, which is straightforward
if f_I and g_J are both differentiable (they are, being smooth functions).

---

## Berezinian Infrastructure Usage

The Integration/ files use the following from the Berezinian infrastructure:

1. **BerezinianMul.lean** (`ber_mul`): Used in `berezinian_cocycle_full`
   (BerezinIntegration.lean) via `berezinian_cocycle_from_chain_rule`.
   This proves Ber(J₁ · J₂) = Ber(J₁) · Ber(J₂).

2. **Berezinian.lean** (`SuperMatrix.ber`, `berezinianAt`): Used in Pullback.lean
   for `pullbackEvalAt` — the pullback multiplies by the Berezinian.

3. **SuperChainRule.lean** (`berezinian_cocycle_from_chain_rule`): Used in
   `berezinian_cocycle_full` in BerezinIntegration.lean.

4. **NilpotentInverse.lean** (geometric series, `grassmannGeomInverse`): Used in
   PartitionOfUnity.lean for `rawSumInverseAt` (inverting 1 + nilpotent).
   Also `ringInverse_eq_grassmannInv` bridges Ring.inverse to geometric series.

5. **GrassmannSmooth.lean** (`grassmannSmooth` predicate): Used in Pullback.lean
   for `berezinianCarrierAt_grassmannSmooth` (Ber coefficients are smooth in x).

For the remaining proofs:
- `berezin_change_of_variables` WILL use `berezinianCarrierAt` from Pullback.lean
- The body-level reduction lemma needs `Ber_body = det(A_body)/det(D_body)`,
  which connects to the Berezinian definition in Berezinian.lean.

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199), §3.1-3.5
- Rogers, "Supermanifolds" (2007), Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
