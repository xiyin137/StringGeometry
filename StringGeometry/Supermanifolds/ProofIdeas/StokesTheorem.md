# Phase 6: Stokes Theorem on Supermanifolds — Proof Ideas

## Statement

### Without Boundary (Witten eq. 3.50, 3.53)

For M a compact supermanifold without boundary, and ν a compactly supported integral form of codimension 1:

  ∫_M dν = 0

### With Boundary (Witten eq. 3.59)

For M a supermanifold with boundary ∂M:

  ∫_M dν = ∫_{∂M} ν

## Proof Strategy

The proof is surprisingly clean once the infrastructure is in place. It reduces to two independent results.

### Decomposition d = d₀ + d₁

The super exterior derivative decomposes as:
- d₀ = Σ_i dx^i ∂/∂x^i (even exterior derivative)
- d₁ = Σ_a dθ^a ∂/∂θ^a (odd exterior derivative)

So: ∫_M dν = ∫_M d₀ν + ∫_M d₁ν

### Part A: The d₁ Term Vanishes

**Claim**: ∫_M d₁ν = 0

**Proof**:
1. d₁ν involves ∂ν/∂θ^a, which lowers the θ-degree by 1
2. The Berezin integral extracts the top θ-component
3. After applying ∂/∂θ^a, the maximum θ-degree is q-1, so there is no top (degree q) component
4. Therefore the Berezin integral gives 0

**In Lean**: This is essentially `berezin_integration_by_parts_odd` applied to each summand.

**Key lemma already proven**:
```lean
theorem berezin_integration_by_parts_odd {p q : ℕ} (a : Fin q) (hq : 0 < q)
    (f : SuperDomainFunction p q) :
    berezinIntegralOdd (partialOdd a f) = SmoothFunction.const 0
```

For d₁ν = Σ_a (something involving ∂ν/∂θ^a), each term has vanishing Berezin integral. By linearity (already proven as `berezinIntegralOdd_add`), the sum vanishes.

### Part B: The d₀ Term Reduces to Classical Stokes

**Claim**: ∫_M d₀ν = ∫_{∂M} ν (or = 0 if M has no boundary)

**Proof**:
1. d₀ acts only on even coordinates, commuting with Berezin integration
2. After Berezin integration: ∫_M d₀ν = ∫_{M_red} (d₀ν)_top
3. Key: d₀ commutes with extracting top θ-component:
   (d₀ν)_top = d₀(ν_top) + (correction terms)

   Actually, d₀ does NOT mix θ-components (it doesn't touch θ's), so:
   (d₀ν)_top = d₀(ν_top)

4. Therefore: ∫_{M_red} (d₀ν)_top = ∫_{M_red} d₀(ν_top) = ∫_{∂M_red} ν_top

   The last step is ordinary Stokes' theorem on M_red.

**Crucial point**: d₀ and Berezin integration commute because d₀ = Σ_i dx^i ∂/∂x^i acts on the body coordinates, while Berezin integration extracts the θ^{univ} coefficient. Since ∂/∂x^i doesn't change which θ-monomials appear (it differentiates the x-dependent coefficients), these operations commute.

**Key lemma needed**:
```lean
/-- The even exterior derivative commutes with Berezin integration -/
theorem d0_commutes_berezin {p q : ℕ} (ν : IntegralFormCodim p q 1) :
    berezinIntegralOdd (d₀ ν).coefficient = d₀_body (berezinIntegralOdd ν.coefficient)
```

### Combining A and B

```
∫_M dν = ∫_M d₀ν + ∫_M d₁ν      (linearity)
       = ∫_M d₀ν + 0              (Part A)
       = ∫_{M_red} d₀(ν_top)      (Berezin integration + commutativity)
       = ∫_{∂M_red} ν_top         (classical Stokes)
       = ∫_{∂M} ν                 (∂M has same odd dimension)
```

## Lean Implementation Plan

### Step 1: Prove d₁ integration vanishes (easy, uses existing `berezin_integration_by_parts_odd`)

```lean
theorem berezin_d1_vanishes {p q : ℕ} (ν : IntegralFormCodim p q 1) :
    berezinIntegralOdd (superExteriorDerivativeOdd ν).coefficient = SmoothFunction.const 0 := by
  -- d₁ν = Σ_a (terms involving ∂ν/∂θ^a)
  -- Each term has berezinIntegralOdd = 0 by berezin_integration_by_parts_odd
  -- Sum of zeros is zero by linearity
```

### Step 2: Prove d₀ commutes with Berezin integration (medium, needs careful coefficient tracking)

```lean
theorem d0_commutes_berezin {p q : ℕ} (ν : IntegralFormCodim p q 1) :
    berezinIntegralOdd (superExteriorDerivativeEven ν).coefficient =
    evenExteriorDerivative (berezinIntegralOdd ν.coefficient) := by
  -- d₀ acts on x-coordinates only
  -- Berezin integral extracts coefficient at Finset.univ in θ
  -- Since d₀ doesn't change θ-indices, these operations commute
  -- This is a coefficient-level calculation
```

### Step 3: State and prove super Stokes (combines Steps 1, 2 with classical Stokes hypothesis)

```lean
theorem super_stokes_proper {p q : ℕ} (hp : 0 < p)
    (M : SupermanifoldWithBoundary ⟨p, q⟩)
    (ν : IntegralFormCodim p q 1)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (boundaryIntegral : SmoothFunction (p-1) → Set (Fin (p-1) → ℝ) → ℝ)
    -- Classical Stokes on the body
    (hClassicalStokes : ∀ (f : SmoothFunction p) (U : Set (Fin p → ℝ)) (bdry : Set (Fin (p-1) → ℝ)),
        bodyIntegral (evenExteriorDerivative f) U = boundaryIntegral (restrict f) bdry) :
    -- Super Stokes: ∫_M dν = ∫_{∂M} ν
    ... := by
  -- 1. Split d = d₀ + d₁
  -- 2. d₁ part vanishes (berezin_d1_vanishes)
  -- 3. d₀ part: factor through Berezin integral (d0_commutes_berezin)
  -- 4. Apply hClassicalStokes
```

## Subtleties and Warnings

### Orientation
- M_red must be oriented for integration
- The orientation of ∂M_red is induced from M_red (outward normal convention)
- Odd directions don't affect orientation

### Boundary in odd directions
- There is NO boundary in odd directions (θ-space is algebraic, not geometric)
- This is why d₁ integration vanishes — there's "nowhere for the boundary term to live"
- This is the mathematical content of `berezin_integration_by_parts_odd`

### Compact support
- For the without-boundary case, ν must be compactly supported
- Compact support is defined via M_red (as in `CompactlySupportedIntegralForm`)
- Odd directions are automatically "compact" (nilpotent/finite-dimensional)

### Non-trivial example: (1|1) case
Consider M = [0,1]^{1|1} with coordinates (x, θ).
Let ν = g(x,θ) [Dθ] be a codimension-1 integral form.

Then:
- d₀ν = (∂g/∂x) dx [Dθ]
- d₁ν = (∂g/∂θ) dθ [Dθ] = 0 (since dθ [Dθ] involves δ(dθ)dθ = 0)
- ∫_{[0,1]^{1|1}} dν = ∫₀¹ dx (∂g_top/∂x) = g_top(1) - g_top(0) = ∫_{∂[0,1]^{1|1}} ν

where g_top(x) = coefficient of θ in g(x,θ).

## Connection to Existing Code

The current `super_stokes` in `BerezinIntegration.lean` already has the right structure:
- It takes body Stokes as a hypothesis (`hStokesBody`)
- The proof is `exact hStokesBody`

The improvement needed is:
1. Replace the ad hoc `dω` parameter with proper `superExteriorDerivative`
2. Prove `hStokesBody` from `d₁ vanishes` + `d₀ commutes with Berezin` + classical Stokes
3. Remove the need for external `restrict` parameter by deriving it from boundary structure

## References

- Witten §3.5: "Stokes' theorem for supermanifolds"
- Rogers §12.3: "Integration and Stokes' theorem"
- The proof strategy follows Witten's presentation closely
