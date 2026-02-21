# Partition of Unity on Supermanifolds — Proof Ideas

## The Subtlety

Partition of unity on supermanifolds is more subtle than simply lifting smooth functions from M_red. The key issues are:

1. **Coordinate dependence**: The partition functions live in local coordinate charts. On overlaps, they transform under coordinate changes. Even though the functions are "bosonic" (θ-independent), the coordinate change itself involves θ.

2. **SuperDomainFunction framework**: A partition of unity function ρ_α must be a proper `SuperDomainFunction p q` (not just a `SmoothFunction p`), because:
   - It multiplies integral forms, which are SuperDomainFunctions
   - The product ρ_α · f(x,θ) must respect the Grassmann algebra structure
   - The global integral independence proof requires ρ_α to be compatible with Berezinian transformation

3. **Sum condition**: The condition Σ_α ρ_α = 1 must hold as a SuperDomainFunction identity, not just pointwise on the body. This means for each θ-monomial I:
   - I = ∅: Σ_α (ρ_α)_∅(x) = 1 (the body condition)
   - I ≠ ∅: Σ_α (ρ_α)_I(x) = 0 (higher θ-components must cancel)

   For θ-independent partition functions (lifted from M_red), this is satisfied automatically since (ρ_α)_I = 0 for I ≠ ∅.

4. **Transformation under coordinate change**: On the overlap U_α ∩ U_β, the partition function ρ_α expressed in chart β coordinates is:

   ρ_α(x_β, θ_β) = ρ_α(body_map_αβ(x_β))   (if ρ_α is θ-independent)

   But the body map body_map_αβ involves only the even part of the transition. The subtlety: if we define ρ_α in chart α coordinates as θ-independent, it remains θ-independent in chart β coordinates ONLY because ρ_α depends on x through the body map, and the body map of a super coordinate change depends only on even coordinates.

   More precisely: if φ_αβ : (x_α, θ_α) ↦ (x_β, θ_β) is the transition, then:
   - x_β = a(x_α) + (even θ-polynomial terms)
   - The body map is just x_β|_{θ=0} = a(x_α)
   - ρ_α(x_α) = ρ_α(a⁻¹(x_β|_{θ=0}))

   In chart β: ρ_α becomes ρ_α(a⁻¹(x_β)) which IS still θ-independent. But this requires proving that the body map is well-defined and invertible on overlaps.

## Current State

The current `SuperPartitionOfUnity` structure in BerezinIntegration.lean uses `SmoothFunction dim.even` for partition functions. This is the body-level representation. The `liftToSuper` function lifts these to `SuperDomainFunction p q` by setting all θ-components to zero except ∅.

### What works
- `liftToSuper` correctly produces θ-independent SuperDomainFunctions
- `lift_sum_one` proves the sum condition for the ∅-component
- `berezin_lift_factor` proves that ρ_α factors through the Berezin integral

### What's missing
1. **Coordinate change compatibility**: No proof that lifted partition functions transform correctly under super coordinate changes
2. **Global well-definedness**: The partition functions are defined chart-by-chart, but we need them to be globally consistent
3. **Connection to Mathlib**: No connection to `Mathlib.Topology.PartitionOfUnity`

## Proper Development Plan

### Step 1: Chart-Local Partition of Unity

The partition of unity is constructed on M_red (the body manifold), then lifted.

**Key definition**: A partition of unity on a Supermanifold M is a collection of SuperDomainFunctions {ρ_α} such that:

```lean
structure SuperPartitionOfUnity' {dim : SuperDimension} (M : Supermanifold dim) where
  index : Type*
  [finIndex : Fintype index]
  charts : index → SuperChart M
  -- Partition functions as SuperDomainFunctions in each chart
  functions : (α : index) → SuperDomainFunction dim.even dim.odd
  -- Each ρ_α is purely even (θ-independent)
  functions_even : ∀ α I, I ≠ ∅ →
    (functions α).coefficients I = SmoothFunction.const 0
  -- Non-negativity on the body
  nonneg : ∀ α (x : Fin dim.even → ℝ), 0 ≤ (functions α).body x
  -- Sum to identity as SuperDomainFunctions
  sum_eq_one_super : ∀ (x : Fin dim.even → ℝ),
    Finset.univ.sum (fun α => (functions α).body x) = 1
  -- Support condition
  support_subset : ∀ α (x : Fin dim.even → ℝ),
    x ∉ (charts α).bodyCoord '' (charts α).domain →
    (functions α).body x = 0
  -- Compatibility: on overlaps, the function in chart β equals the
  -- pullback from chart α via the body transition map
  overlap_compatible : ∀ (α β : index) (t : SuperTransition (charts α) (charts β))
    (x : Fin dim.even → ℝ),
    (functions α).body x = (functions α).body (fun i => (t.evenTransition i).body x)
```

Wait — the last condition is circular. Let me think more carefully.

### Step 2: The Correct Framework

The partition of unity lives on M_red as a **global** object. Each ρ_α : M_red → ℝ is a smooth function on the body manifold. In chart α, it has coordinate expression ρ_α(x_α). In chart β, it has coordinate expression ρ_α(body_map_αβ⁻¹(x_β)).

The key insight: we don't need the partition functions to be SuperDomainFunctions on ℝ^{p|q}. We need them to be smooth functions on M_red that we then lift to SuperDomainFunctions in each chart.

The lift is straightforward:
- In chart α: ρ_α(x_α, θ_α) := ρ_α(x_α) (θ-independent)
- In chart β on the overlap: ρ_α(x_β, θ_β) := ρ_α(body_map_αβ⁻¹(x_β)) (still θ-independent)

The compatibility condition:
- The two expressions agree on the overlap because body_map_αβ(x_α) = x_β (by definition of the body map)

### Step 3: Proof that Lift is Compatible with Integration

The critical lemma for integration theory:

**Lemma**: For a lifted partition function ρ_α and an integral form ω with local expression f(x,θ) [Dx Dθ]:

  ∫ dθ [ρ_α · f](x,θ) = ρ_α(x) · ∫ dθ f(x,θ)

This is `berezin_lift_factor` (already proven).

**Lemma**: Under coordinate change φ : (x,θ) ↦ (y,η), the lifted function transforms as:

  (lift ρ_α) ∘ φ = lift(ρ_α ∘ body_φ)

This is because ρ_α is θ-independent, so composition with φ only involves the body map.

**Proof**:
- (lift ρ_α)(φ(x,θ)) = ρ_α(body(φ(x,θ))) = ρ_α(φ_body(x))
- [lift(ρ_α ∘ φ_body)](x,θ) = ρ_α(φ_body(x))
- These are equal.

In Lean, this requires:
1. `composeEvalAt (liftToSuper ρ_α) φ x = grassmannScalar (ρ_α (φ.bodyMap x))`
2. This follows from the fact that the Taylor expansion of ρ_α around the body point has no nilpotent corrections (since ρ_α doesn't depend on θ)

### Step 4: Interaction with Berezinian

When computing the pullback φ*(ρ_α · ω):

  φ*(ρ_α · f [Dx Dθ]) = (ρ_α ∘ φ) · (f ∘ φ) · Ber(J_φ) [Dx Dθ]
                        = ρ_α(φ_body(x)) · [(f ∘ φ) · Ber(J_φ)] [Dx Dθ]
                        = ρ_α(φ_body(x)) · φ*(f [Dx Dθ])

The partition function factors out of the pullback because it's a scalar (θ-independent).

This is essential for the proof that the global integral is independent of partition of unity choice.

### Step 5: Existence from Paracompactness

**Theorem**: Every paracompact Hausdorff supermanifold admits a partition of unity subordinate to any open cover.

**Proof sketch**:
1. M_red is a paracompact Hausdorff smooth manifold (assumption or proved from M's properties)
2. The chart domains {U_α,red} form an open cover of M_red
3. By standard differential topology (Mathlib: `PartitionOfUnity.exists_isSubordinate`), there exists a partition of unity {ρ̃_α} on M_red subordinate to {U_α,red}
4. Lift each ρ̃_α to a SuperDomainFunction via `liftToSuper`
5. The lifted functions satisfy all required properties:
   - Sum to 1 as SuperDomainFunctions (by `lift_sum_one`)
   - Factor through Berezin integral (by `berezin_lift_factor`)
   - Compatible with coordinate changes (by Step 3)

**Mathlib connection**: The key entry point is `PartitionOfUnity` in `Mathlib.Topology.PartitionOfUnity`. We need:
- `ParacompactSpace M.body`
- `NormalSpace M.body` (or `T2Space` + `LocallyCompactSpace`)
- An atlas giving an open cover
- `SmoothPartitionOfUnity` from `Mathlib.Geometry.Manifold.PartitionOfUnity` (if M.body has a smooth manifold structure in the Mathlib sense)

The gap: our `M.body` is just a `TopologicalSpace` with `Set.Finite` atlas. We need to show it's paracompact and admits smooth partitions of unity. This likely requires either:
(a) Assuming paracompactness directly (as the current code does), or
(b) Building the smooth manifold structure on M.body in the Mathlib sense and using their infrastructure

## Summary of Subtleties

1. **θ-independence is preserved by coordinate changes** — needs proof via body map factoring
2. **Factoring through Berezin integral** — already proven (`berezin_lift_factor`)
3. **Factoring through pullback** — needs super composition infrastructure (Phase 1)
4. **Global consistency** — follows from (1) once body map compatibility is established
5. **Existence** — standard paracompactness, but Mathlib connection is nontrivial
6. **Sum condition as SuperDomainFunction identity** — trivially satisfied for θ-independent functions

## References

- Witten, arXiv:1209.2199, §3.1: "one can find bosonic functions h_α on M..."
- Rogers, §11.2: Integration on supermanifolds with partition of unity
- The θ-independence of partition functions is not a simplification — it's mathematically necessary for the Berezin integral to work correctly
