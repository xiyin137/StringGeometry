# Supermanifold Theory - Design Notes

## Key Distinction: Fermionic Coordinates vs Grassmann Algebra Coefficients

### The Local Model ℝ^{p|q}

For a super domain ℝ^{p|q}, there are **q fermionic coordinates** θ₁,...,θq.
The structure sheaf assigns to each open U ⊆ ℝ^p:

```
O(U) = C^∞(U, ℝ) ⊗_ℝ ∧(ℝ^q)
```

Sections have the form:
```
f(x,θ) = Σ_I f_I(x) θ^I
```
where:
- I ranges over subsets of {1,...,q}
- f_I : U → ℝ are smooth **ℝ-valued** coefficient functions
- θ^I = θ^{i₁} ∧ ... ∧ θ^{i_k} for I = {i₁ < ... < i_k}

**In the local model, coefficients are in ℝ**, not in a Grassmann algebra.

### Transition Maps and Grassmann Algebra Coefficients

When gluing local models to form a supermanifold, transition maps
```
φ_αβ : U_α ∩ U_β → ℝ^{p|q}
```
have the form:
```
x'_i = f^i_0(x) + θ^j f^i_j(x) + θ^j θ^k f^i_{jk}(x) + ...
θ'_s = ψ^s_j(x) θ^j + ψ^s_{jk}(x) θ^j θ^k + ...
```

For a **single supermanifold** (not a family):
- The coefficients f^i_I, ψ^s_I are still ℝ-valued

For **families of supermanifolds** (e.g., parameterized by odd moduli η₁,...,η_s):
- The coefficients can be **Grassmann algebra-valued** (involving η's)
- This is essential for super Riemann surfaces and supermoduli spaces

### Super Riemann Surfaces

As noted in Witten's "Notes On Supermanifolds And Integration" (arXiv:1209.2199):

> "Though M depends on η₁...ηs, it does not have a reduced space that depends on
> those parameters. The reason is that since the gluing functions ψ^i_αβ can depend
> on the η's, we will in general get gluing laws such as θ_α = θ_β + η and we cannot
> consistently set the θ's to zero unless we also set the η's to zero."

This is why:
- Supermoduli space of super Riemann surfaces involves Grassmann-valued transition maps
- There is no elementary map from supermoduli space to ordinary moduli space
- The Grassmann algebra for coefficients is **separate** from the fermionic coordinates

### Summary

| Context | Fermionic coords | Coefficient algebra |
|---------|-----------------|---------------------|
| Local model ℝ^{p|q} | θ₁,...,θq | ℝ |
| Single supermanifold | θ₁,...,θq | ℝ |
| Family of supermanifolds | θ₁,...,θq | Grassmann algebra (involving η's) |
| Supermoduli space | θ₁,...,θq (on fibers) | Full Grassmann algebra |

## Grassmann Algebra Matrix Warning

**Be careful when manipulating matrices over Grassmann algebra!**

Some properties of matrices over a field do **NOT** apply to matrices over a (super)commutative ring:

1. **Determinant multiplicativity**: `Matrix.det_mul` requires `CommRing` - OK for Grassmann algebra
2. **Invertibility criteria**: A matrix over Grassmann algebra may not have a standard inverse even if its body has nonzero determinant
3. **Eigenvalue decomposition**: Does not generally apply
4. **Rank-nullity**: More subtle over non-fields
5. **Berezinian**: Requires special invertibility conditions (D block must be invertible)

**Key distinction**:
- `body_jacobian_cocycle`: Works over ℝ - standard `Matrix.det_mul` applies
- `berezinian_cocycle_full`: Works over Grassmann algebra - requires `SuperMatrix.ber_mul` (which needs additional hypotheses)

When proving cocycle conditions:
- For body maps: Use `Matrix.det_mul` directly (matrices over ℝ)
- For full Berezinian: Need `SuperMatrix.ber_mul` with invertibility hypotheses

See Deligne-Morgan "Notes on Supersymmetry" for rigorous treatment of supermatrices.
