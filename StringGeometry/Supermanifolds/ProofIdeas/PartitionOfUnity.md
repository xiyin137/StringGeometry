# Partition of Unity on Supermanifolds

## The Construction (Witten, arXiv:1209.2199 §3.1)

### Step 1: Body partition of unity

Start with a smooth partition of unity {ρ̃_α} on M_red subordinate to the chart cover {U_α,red}. This exists by standard paracompactness of M_red (a smooth manifold).

Each ρ̃_α : M_red → ℝ is:
- Smooth, nonneg, supported in U_α,red
- Σ_α ρ̃_α(p) = 1 for all p ∈ M_red
- Falls off smoothly to 0 near the boundary of U_α,red

### Step 2: Naive lift to supermanifold

In chart α's coordinates, lift ρ̃_α to a θ-independent super function:

    (lift_α ρ̃_α)(x_α, θ_α) := ρ̃_α(x_α)

This is a perfectly good super function in chart α — it's the constant (in θ) extension.

### Step 3: The incompatibility on overlaps

**This is the key subtlety.** On the overlap U_α ∩ U_β, the naive lifts from different charts are **incompatible**.

Consider expressing (lift_α ρ̃_α) in chart β's coordinates. The transition function gives:

    x_α = x_α(x_β, θ_β) = a⁻¹(x_β) + (even nilpotent θ_β-corrections)

where a = body map of T_αβ. Then:

    (lift_α ρ̃_α)(x_β, θ_β) = ρ̃_α(x_α(x_β, θ_β))

Taylor expanding around the body point (terminates since Grassmann algebra is finite-dimensional):

    = ρ̃_α(a⁻¹(x_β)) + ρ̃'_α(a⁻¹(x_β)) · δ + ½ρ̃''_α(a⁻¹(x_β)) · δ² + ...

where δ = (even nilpotent θ_β-terms from the transition). **This has θ_β-dependence!**

So the naive lift from chart α, when viewed in chart β, is NOT θ-independent. The θ-dependence arises because the even coordinate transition x_α = x_α(x_β, θ_β) mixes in nilpotent even θ-corrections.

### Step 4: The raw sum is 1 + nilpotent

In any chart β's coordinates, the raw sum of all naive lifts is:

    S(x_β, θ_β) := Σ_α (lift_α ρ̃_α)(x_β, θ_β)
                  = Σ_α ρ̃_α(x_α(x_β, θ_β))

At θ = 0: S|_{θ=0} = Σ_α ρ̃_α(a⁻¹_αβ(x_β)) = 1 (by body partition of unity).

At higher θ-order: S = 1 + (even nilpotent corrections). The corrections are nonzero in general because different charts contribute different nilpotent terms.

### Step 5: Normalization by division

Since S = 1 + ε where ε is nilpotent and even, S is invertible in the Grassmann algebra:

    S⁻¹ = 1 - ε + ε² - ε³ + ... (terminates since ε is nilpotent)

Define the normalized partition of unity:

    ρ_α := (lift_α ρ̃_α) / S = (lift_α ρ̃_α) · S⁻¹

Then:
- Σ_α ρ_α = S · S⁻¹ = 1 **exactly** as a super function on M
- Each ρ_α is an **even super function with genuine θ-dependence**
- The θ-dependence comes from both the transition-induced corrections and the S⁻¹ factor
- At θ = 0 (body level): ρ_α|_{θ=0} = ρ̃_α (recovers the body partition)

### Summary of key properties

The resulting partition of unity {ρ_α} satisfies:
1. **Even parity**: only even θ-powers (I.card % 2 = 0)
2. **Genuine θ-dependence**: not just lifted body functions
3. **Exact sum**: Σ_α ρ_α = 1 as super functions on M
4. **Support**: supp(ρ_α) ⊂ U_α (inherited from body partition)
5. **Body reduction**: ρ_α|_{θ=0} = ρ̃_α

## Why the θ-dependence matters

The θ-dependence of partition functions is **not** an artifact — it's mathematically necessary for the global sum to be exactly 1 on M (not just on M_red). Without normalization:

- The sum is only 1 + O(θ²)
- The global integral ∫_M ω = Σ_α ∫ ρ_α ω would have errors at the nilpotent level
- The proof that the integral is independent of partition choice would fail

## Implications for the Lean definition

### Current definition is wrong

```lean
-- WRONG: uses SmoothFunction (θ-independent)
functions : index → SmoothFunction dim.even
```

### Correct definition

```lean
-- CORRECT: uses SuperDomainFunction (θ-dependent, even)
functions : index → SuperDomainFunction dim.even dim.odd
-- with even parity constraint:
functions_even : ∀ α I, I.card % 2 = 1 →
  (functions α).coefficients I = SmoothFunction.const 0
```

### Sum condition

The sum Σ_α ρ_α = 1 must hold as a **super function identity**, which means:
- Body (I = ∅): Σ_α (ρ_α).coefficients ∅ (x) = 1  (for x in the manifold)
- Higher (I ≠ ∅): Σ_α (ρ_α).coefficients I (x) = 0  (θ-corrections cancel)

But this requires expressing all ρ_α in the **same** coordinate system, which requires super function composition (pullback via transition functions). This is the main infrastructure gap.

**Practical formulation**: Since each ρ_α is given in chart α's coordinates, the sum condition is formulated chart-by-chart:

> For each chart β and each point x in chart β's domain:
> Σ_α (ρ_α pulled back to chart β) = 1 as a SuperDomainFunction

This requires the pullback/composition infrastructure from Phase 3 of the plan.

### Existence proof outline

1. M_red is paracompact → body partition of unity {ρ̃_α} exists (Mathlib)
2. Naive lift to each chart (θ-independent in own chart)
3. Compute raw sum S = 1 + nilpotent in each chart
4. S is invertible (nilpotent geometric series, uses `grassmann_soul_nilpotent`)
5. Normalize: ρ_α := (lift ρ̃_α) · S⁻¹
6. Verify: Σ_α ρ_α = 1, support ⊂ U_α, even parity

### Infrastructure needed

1. **Super function composition** (Phase 3): to express ρ_α from chart α in chart β's coordinates
2. **Grassmann inverse** for 1 + nilpotent: geometric series S⁻¹ = Σ_n (-ε)^n
3. **Body partition of unity from Mathlib**: connect M.body to `SmoothPartitionOfUnity`
4. **Taylor expansion with nilpotent increment**: for computing ρ̃_α(x + δ) where δ is nilpotent

## Interaction with Berezin integration

For the Berezin integral of ρ_α · ω:

    ∫ dθ [ρ_α · f](x,θ) ≠ ρ̃_α(x) · ∫ dθ f(x,θ)

because ρ_α is θ-dependent! The product ρ_α · f mixes θ-components, and the Berezin integral extracts the **new** top component of the product.

However, at leading order:
    ∫ dθ [ρ_α · f] = ρ̃_α(x) · f_top(x) + (corrections from θ-components of ρ_α)

The corrections involve lower θ-components of f multiplied by higher θ-components of ρ_α. These are suppressed (they come from nilpotent corrections in the transition functions) and cancel in the global sum Σ_α by the exact partition property.

**Key theorem**: The global integral Σ_α ∫ ρ_α · ω is independent of the choice of partition of unity. This uses:
- Σ_α ρ_α = 1 exactly (from normalization)
- Berezinian change of variables on overlaps
- Double-sum trick (insert Σ_β σ_β = 1 from second partition)

## Comparison with existing `berezin_lift_factor`

The existing theorem:

```lean
theorem berezin_lift_factor (f : SmoothFunction p) (g : SuperDomainFunction p q) :
    berezinIntegralOdd (SuperDomainFunction.mul (liftToSuper f) g) =
    SmoothFunction.mul f (berezinIntegralOdd g)
```

This is correct for θ-independent functions (the naive lift). But for the **actual** partition functions (after normalization), this factoring does NOT hold because the partition functions have θ-components.

The theorem is still useful as a component of the construction (it handles the leading-order term), but the full integration theory needs to work with the θ-dependent partition functions.

## References

- Witten, "Notes on Supermanifolds and Integration" (arXiv:1209.2199), §3.1
- Rogers, "Supermanifolds" (2007), §11.2
- Bernstein-Leites, "Integral Forms and the Stokes Formula on Supermanifolds" (1977)
- DeWitt, "Supermanifolds" (1992), Chapter 6
