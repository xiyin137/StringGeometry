# Integration Theory and Stokes Theorem on Supermanifolds — Development Plan

## Current State Assessment

### What's Already Built
The existing infrastructure is substantial:

- **Berezin integral** (`BerezinIntegration.lean`): extracts top θ-coefficient, proven linearity, integration by parts for odd derivatives, Fubini
- **Berezinian**: fully proven multiplicativity (`ber_mul`, 2900+ line proof), cocycle condition proven via chain rule
- **IntegralForm**: sections of Berezinian bundle with pullback (placeholder), local/global integration
- **Super Jacobian**: block structure with proper ℤ/2-grading, chain rule infrastructure
- **Partition of unity**: structure defined, existence statement requires paracompactness (sorry)
- **Super Stokes theorem**: skeleton with body-level reduction (trivial proof that defers to body Stokes)
- **Super divergence**: defined, divergence theorem stated

### Key Gaps
1. **IntegralForm.pullback** — returns identity (placeholder), needs super function composition + Berezinian multiplication
2. **SuperDomainFunction.compose** — simplified placeholder, needs full coefficient tracking
3. **Super exterior derivative** — returns `Unit` (placeholder)
4. **Integral forms of mixed codimension** — not implemented (needed for proper Stokes)
5. **Boundary operator for supermanifolds** — not implemented
6. **Change of variables formula** — statement correct, proof sorry
7. **Global integral independence** — proof outline documented, sorry

---

## Development Roadmap

### Phase 1: Super Function Composition (Foundation)

**Goal**: Implement `SuperDomainFunction.compose` with full coefficient tracking.

**Mathematical content**: Given f(y, η) = Σ_I f_I(y) η^I and coordinate change (y, η) = φ(x, θ):
  - y_i = φ^i_0(x) + Σ_{|J|≥2, even} φ^i_J(x) θ^J
  - η_a = Σ_{|K| odd} ψ^a_K(x) θ^K

We need (f ∘ φ)(x, θ) with full coefficient expansion. Since θ's are nilpotent (θ^{q+1} = 0), the Taylor expansion of f_I around the body point terminates:

  f_I(y(x,θ)) = f_I(y_body(x)) + Σ_k (∂f_I/∂y_k)(y_body(x)) · δy_k(x,θ) + ...

where δy_k = y_k - y_k|_{θ=0} is nilpotent (lies in the soul of the Grassmann algebra).

**Key files to modify**: `Helpers/FiniteGrassmann.lean`

**Proof ideas**:
- Use `grassmann_soul_nilpotent` (already proven: soul^{q+1} = 0)
- Taylor expand f_I at the body point; nilpotency ensures termination at finite order
- Track coefficients via the existing `FiniteGrassmannCarrier` Ring instance
- See Rogers §4.3 for the G∞ function composition formula
- See Witten §2.1 for the algebraic perspective

**New lemmas needed**:
1. `taylor_expansion_terminates`: For f smooth and δ nilpotent of order q+1, f(x + δ) = Σ_{n=0}^{q} (1/n!) f^(n)(x) δ^n
2. `compose_coefficient_formula`: Explicit formula for (f ∘ φ)_I in terms of f_J and φ coefficients
3. `compose_smooth`: Smoothness of composed super function (in the body variable x)

### Phase 2: Pullback of Integral Forms

**Goal**: Implement proper `IntegralForm.pullback`.

**Mathematical content** (Witten eq. 3.10):
  φ*[f(y,η) Dy Dη] = f(φ(x,θ)) · Ber(J_φ)(x,θ) · [Dx Dθ]

**Implementation**:
1. Compose coefficient with φ using Phase 1 infrastructure
2. Compute Berezinian of J_φ at each point using `SuperJacobian.berezinianAt`
3. Multiply: new coefficient = (f ∘ φ) * Ber(J_φ)

**Key connection**: The Berezinian is an element of the finite Grassmann algebra Λ_q. We need to multiply it with the composed function, both viewed as SuperDomainFunction values.

**Proof ideas**:
- `pullback_identity`: pullback by identity = identity
- `pullback_composition`: (ψ ∘ φ)* = φ* ∘ ψ* (uses `ber_mul`)
- `pullback_preserves_integral`: ∫_V ω = ∫_U φ*ω (the change of variables formula)

### Phase 3: Integral Forms of Arbitrary Codimension (Witten §3.2)

**Goal**: Define integral forms of codimension r|s, generalizing the current top-degree `IntegralForm`.

**Mathematical content**: On ℝ^{p|q}, integral forms of codimension r (where 0 ≤ r ≤ p) are sections of certain sheaves that can be integrated over (p-r)-dimensional submanifolds. The key objects are:

- **Codimension 0** (current `IntegralForm`): f(x,θ) [Dx Dθ] — integrable over M
- **Codimension 1**: objects integrable over hypersurfaces in M
- **Codimension r|0**: objects integrable over submanifolds of codimension r in the even directions

The critical distinction from differential forms: integral forms use delta functions δ(dx^i) in even directions and are polynomial in dθ^a.

**New structures**:
```
structure IntegralFormCodim (p q r : ℕ) where
  -- For codimension r, we integrate over (p-r)-dimensional submanifolds
  -- Local expression involves r delta functions in even directions
  coefficient : SuperDomainFunction p q
  -- Which even directions are "transverse" (delta-function directions)
  transverseDirections : Finset (Fin p)
  transverse_card : transverseDirections.card = r
```

**References**: Witten §3.2.1-3.2.3, especially the discussion of "integral forms of codimension r|n"

### Phase 4: Super Exterior Derivative

**Goal**: Define a proper exterior derivative d on integral forms.

**Mathematical content**: The exterior derivative on ℝ^{p|q} decomposes as d = d₀ + d₁ where:
- d₀ = Σ_i dx^i ∂/∂x^i acts on even coordinates (ordinary exterior derivative)
- d₁ = Σ_a dθ^a ∂/∂θ^a acts on odd coordinates

For integral forms, the action is:
- d₀ increases the even form degree (standard)
- d₁: for the Berezin measure [Dθ], d₁ acts by contracting with ∂/∂θ^a (lowering θ-degree), which is dual to the standard action

**Key property**: d² = 0, which splits into d₀² = 0, d₁² = 0, and d₀d₁ + d₁d₀ = 0.

**Implementation plan**:

For integral forms at top codimension (our current `IntegralForm`), the relevant "d" maps:
```
d : IntegralFormCodim p q 0 → IntegralFormCodim p q 1
```

In local coordinates on ℝ^{p|q}, for ω = f(x,θ) [Dx Dθ]:

**d₀ action**: d₀[f(x,θ) Dx Dθ] = 0 (already top even-form degree, so d₀ kills it)

**d₁ action**: The odd exterior derivative is more subtle. On the Berezin measure:
- Witten's approach: d₁ acts as ∂/∂(dθ^a) on the integral form representation
- This lowers the odd integration degree

For codimension-1 forms ν, we need d₀ν and d₁ν.

**New definitions**:
1. `superExteriorDerivativeEven`: d₀ acting on integral forms
2. `superExteriorDerivativeOdd`: d₁ acting on integral forms
3. `superExteriorDerivative`: d = d₀ + d₁

**Proof ideas**:
- `d_squared_zero_even`: d₀² = 0 (follows from ordinary d² = 0)
- `d_squared_zero_odd`: d₁² = 0 (follows from ∂²/∂θ^a∂θ^a = 0)
- `d_anticommute`: d₀d₁ + d₁d₀ = 0 (mixed partial derivatives anticommute)
- `d_squared_zero`: d² = 0

### Phase 5: Boundary Operator for Supermanifolds

**Goal**: Define the boundary of a supermanifold and the restriction of integral forms.

**Mathematical content** (Witten §3.5): The boundary of a supermanifold M with boundary is another supermanifold ∂M of dimension (p-1|q). Key points:

1. The boundary is defined by even coordinates only: if M = {f ≤ 0} for some even function f, then ∂M = {f = 0}
2. The odd dimension is unchanged: ∂M has the same number of odd coordinates
3. The boundary is well-defined up to the equivalence f ~ e^φ f where φ vanishes at θ = 0

**Implementation**:
```
structure SupermanifoldWithBoundary (dim : SuperDimension) extends Supermanifold dim where
  boundaryFunction : SuperDomainFunction dim.even dim.odd
  -- f is even
  boundaryFunction_even : ∀ I, I.card % 2 = 1 → boundaryFunction.coefficients I = SmoothFunction.const 0
  -- Body of f defines a proper boundary
  boundaryRegularity : ...
```

The restriction functor ι* maps integral forms on M to integral forms on ∂M.

### Phase 6: Stokes Theorem — Proper Formulation and Proof

**Goal**: State and prove Stokes' theorem for supermanifolds.

**Theorem** (Witten eq. 3.53, 3.59):

**(a) Without boundary**: For M compact without boundary, and ν a compactly supported integral form of codimension 1:
  ∫_M dν = 0

**(b) With boundary**: For M with boundary ∂M:
  ∫_M dν = ∫_{∂M} ν

**Proof strategy** (Witten §3.5):

The proof decomposes into even and odd parts:

1. **Split d = d₀ + d₁**:
   ∫_M dν = ∫_M d₀ν + ∫_M d₁ν

2. **The d₁ (odd) part vanishes**:
   ∫_M d₁ν = 0

   **Why**: d₁ = Σ_a dθ^a ∂/∂θ^a. The Berezin integral over odd variables of ∂f/∂θ^a vanishes (already proven as `berezin_integration_by_parts_odd`). More precisely, ∂/∂θ^a lowers the θ-degree by 1, so the top θ-component is absent.

   **Lean proof idea**: Use `berezin_integration_by_parts_odd` applied to each term in d₁ν.

3. **The d₀ (even) part reduces to classical Stokes**:
   ∫_M d₀ν = ∫_{∂M} ν

   After Berezin integration (extracting top θ-component), this becomes:
   ∫_{M_red} d₀(ν_top) = ∫_{∂M_red} ν_top

   This is ordinary Stokes' theorem on M_red.

   **Lean proof idea**: Factor through `berezinIntegralOdd`, then apply the body-level Stokes hypothesis (as currently done in `super_stokes`, but now with proper d₀ infrastructure).

**Key lemmas**:
1. `berezin_d1_vanishes`: ∫ dθ (d₁ν) = 0 for any integral form ν of codimension 1
2. `berezin_d0_factors`: ∫ dθ (d₀ν) = d₀(∫ dθ ν) — d₀ commutes with Berezin integration
3. `super_stokes_proper`: The full theorem combining (1) and (2) with classical Stokes

---

## Phase 7: Advanced Topics

### 7a: Change of Variables Formula (Completing existing sorry)

With Phase 2 (pullback) complete, the change of variables formula:
  ∫_U φ*ω = ∫_V ω

follows from:
1. Berezin integration of pullback extracts (f ∘ φ) · Ber(J_φ) at top θ-component
2. At the body level, Ber(J_φ)|_{θ=0} = det(A)/det(D)|_{θ=0} = det(∂y/∂x)
3. Apply classical change of variables on M_red

### 7b: Global Integral Independence (Completing existing sorry)

The proof that ∫_M ω is independent of partition of unity:
1. Use double-sum trick (already outlined in `globalBerezinIntegral_independent`)
2. On overlaps, use change of variables (Phase 7a)
3. Reorder sums and use partition of unity properties

### 7c: Integration on Submanifolds via Poincaré Dual

For a codimension r|0 submanifold N ⊂ M defined by f₁ = ... = f_r = 0:
  ∫_N μ = ∫_M δ_N ∧ μ

where δ_N = δ(f₁)...δ(f_r) df₁ ∧ ... ∧ df_r (Witten eq. 3.44).

This requires distributional integral forms (delta functions in even variables).

### 7d: De Rham Cohomology of Supermanifolds

Rogers' Theorem 10.3.5: The de Rham cohomology of a supermanifold M is isomorphic to that of M_red. This is because odd directions are contractible (nilpotent).

---

## File Organization

```
Supermanifolds/
  ProofIdeas/
    PLAN.md                          ← This file
    SuperComposition.md              ← Detailed proof ideas for Phase 1
    IntegralFormPullback.md          ← Detailed proof ideas for Phase 2
    ExteriorDerivative.md            ← Detailed proof ideas for Phase 4
    StokesTheorem.md                 ← Detailed proof ideas for Phase 6
  Integration/
    SuperCompose.lean                ← Phase 1: Super function composition
    Pullback.lean                    ← Phase 2: Integral form pullback
    IntegralFormCodim.lean           ← Phase 3: Mixed codimension forms
    ExteriorDerivative.lean          ← Phase 4: Super exterior derivative
    Boundary.lean                    ← Phase 5: Boundary operator
    StokesTheorem.lean               ← Phase 6: Stokes theorem
    ChangeOfVariables.lean           ← Phase 7a: Change of variables
    GlobalIntegration.lean           ← Phase 7b: Global integral independence
```

## Dependencies

```
Phase 1 (Compose) ←── Phase 2 (Pullback) ←── Phase 7a (Change of Variables)
                                            ←── Phase 7b (Global Independence)
Phase 3 (Codim Forms) ←── Phase 4 (Ext. Derivative) ←── Phase 6 (Stokes)
Phase 5 (Boundary) ←────────────────────────────────────┘
```

Phase 1 is the critical bottleneck — nearly everything else depends on having proper super function composition.

## Priority Order

1. **Phase 1** — Super function composition (unblocks everything)
2. **Phase 4** — Super exterior derivative (needed for Stokes, can be started in parallel with Phase 1 using abstract axioms)
3. **Phase 2** — Pullback (needs Phase 1)
4. **Phase 5** — Boundary operator (independent of Phase 1, can proceed in parallel)
5. **Phase 6** — Stokes theorem (needs Phases 4 and 5)
6. **Phase 3** — Codimension forms (enriches the theory but not strictly needed for basic Stokes)
7. **Phase 7** — Completing existing sorrys

## References

- Witten, "Notes On Supermanifolds And Integration" (arXiv:1209.2199) — primary reference for integral forms and Stokes
- Rogers, "Supermanifolds: Theory and Applications" (2007) — Chapter 11 for Berezin integration, Chapter 12 for calculus
- Deligne-Morgan, "Notes on Supersymmetry" — algebraic foundations
- Varadarajan, "Supersymmetry for Mathematicians" — background on superalgebras
