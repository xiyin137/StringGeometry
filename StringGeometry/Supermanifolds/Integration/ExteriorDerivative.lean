import StringGeometry.Supermanifolds.Integration.IntegralFormCodim
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Super Exterior Derivative on Integral Forms

This file defines the exterior derivative d on codimension-1 integral forms,
producing codimension-0 integral forms, and proves substantive properties.

## Mathematical Background: Why d = d₀ on Integral Forms

The de Rham differential decomposes as d = d₀ + d₁ where:
- d₀ = Σⱼ dxʲ ∂/∂xʲ differentiates in even directions
- d₁ = Σₐ dθᵃ ∂/∂θᵃ differentiates in odd directions

For a codimension-1 integral form ν = Σᵢ fᵢ(x,θ) d̂xⁱ · δ(dθ¹)...δ(dθ^q):

**d₀ν**: The factor dxⁱ ∧ d̂xⁱ fills the missing even slot, producing the
codimension-0 form [Dx Dθ]. So d₀ν ∈ Ω^{p,q}_{int} (codimension-0). ✓

**d₁ν**: The factor dθᵃ acts on δ(dθ¹)...δ(dθ^q) via the integral form algebra:
dθᵃ · δ(dθᵃ) = 1 (the delta function absorbs the differential). This REDUCES
the number of delta functions from q to q-1, producing an object in Ω^{p-1,q-1}_{int}.
This is NOT a codimension-0 integral form — it lives in a different graded piece
of the integral form complex.

Therefore, the codimension-0 component of dν is EXACTLY d₀ν. The d₁ part maps
to a different space (fewer delta functions) and does not contribute to the
Berezin integral ∫_M dν.

This is the mathematical content of "no boundary in odd directions":
d₁ν lives outside the integrable (codim-0) sector entirely.

## Main Results

1. **partialEven linearity** — ∂/∂xⁱ(f + g) = ∂f/∂xⁱ + ∂g/∂xⁱ (uses fderiv linearity)
2. **partialOdd linearity** — ∂/∂θᵃ(f + g) = ∂f/∂θᵃ + ∂g/∂θᵃ
3. **∂²/∂θᵃ∂θᵃ = 0** — partialOdd applied twice to same variable vanishes
4. **d₀ is additive** — d₀(ν₁ + ν₂) = d₀(ν₁) + d₀(ν₂)
5. **d₀ = classical divergence** after Berezin integration

## References

* Witten, "Notes on Supermanifolds and Integration" (arXiv:1209.2199), §3.2-3.3
* Bernstein-Leites, "Integral Forms and the Stokes Formula on Supermanifolds" (1977)
-/

namespace Supermanifolds

open Supermanifolds.Helpers

/-!
## Linearity of Partial Derivatives
-/

/-- Helper: smooth functions are differentiable (ContDiff ⊤ → Differentiable).
    In Mathlib v4.29+, `ContDiff.differentiable` takes `(hn : n ≠ 0)` not `(hn : 1 ≤ n)`. -/
theorem SmoothFunction.differentiable' {p : ℕ} (f : SmoothFunction p) :
    Differentiable ℝ f.toFun :=
  f.smooth.differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

/-- partialEven is additive: ∂(f+g)/∂xⁱ = ∂f/∂xⁱ + ∂g/∂xⁱ.
    Uses linearity of the Fréchet derivative. -/
theorem partialEven_add {p q : ℕ} (i : Fin p) (f g : SuperDomainFunction p q) :
    partialEven i (SuperDomainFunction.add f g) =
    SuperDomainFunction.add (partialEven i f) (partialEven i g) := by
  apply SuperDomainFunction.ext
  intro I
  apply SmoothFunction.ext
  intro x
  have hf : DifferentiableAt ℝ (f.coefficients I).toFun x :=
    (f.coefficients I).differentiable'.differentiableAt
  have hg : DifferentiableAt ℝ (g.coefficients I).toFun x :=
    (g.coefficients I).differentiable'.differentiableAt
  show fderiv ℝ (fun y => (f.coefficients I).toFun y + (g.coefficients I).toFun y) x
      (Pi.single i 1) =
    fderiv ℝ (f.coefficients I).toFun x (Pi.single i 1) +
    fderiv ℝ (g.coefficients I).toFun x (Pi.single i 1)
  -- eta-reduce the lambda so rw can match the fderiv_add pattern
  rw [show (fun y => (f.coefficients I).toFun y + (g.coefficients I).toFun y) =
    ((f.coefficients I).toFun + (g.coefficients I).toFun) from rfl, fderiv_add hf hg,
    ContinuousLinearMap.add_apply]

/-- partialEven is compatible with scalar multiplication:
    ∂(c·f)/∂xⁱ = c · ∂f/∂xⁱ -/
theorem partialEven_smul {p q : ℕ} (i : Fin p) (c : ℝ) (f : SuperDomainFunction p q) :
    partialEven i (SuperDomainFunction.smul c f) =
    SuperDomainFunction.smul c (partialEven i f) := by
  apply SuperDomainFunction.ext
  intro I
  apply SmoothFunction.ext
  intro x
  have hf : DifferentiableAt ℝ (f.coefficients I).toFun x :=
    (f.coefficients I).differentiable'.differentiableAt
  show fderiv ℝ (fun y => c * (f.coefficients I).toFun y) x (Pi.single i 1) =
    c * (fderiv ℝ (f.coefficients I).toFun x (Pi.single i 1))
  simp only [fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- partialOdd is additive: ∂(f+g)/∂θᵃ = ∂f/∂θᵃ + ∂g/∂θᵃ.
    Follows from linearity of the sign-scaled coefficient extraction. -/
theorem partialOdd_add {p q : ℕ} (a : Fin q) (f g : SuperDomainFunction p q) :
    partialOdd a (SuperDomainFunction.add f g) =
    SuperDomainFunction.add (partialOdd a f) (partialOdd a g) := by
  apply SuperDomainFunction.ext
  intro I
  by_cases h : a ∈ I
  · -- a ∈ I: partialOdd gives 0 on all three terms
    simp only [partialOdd, if_neg (not_not_intro h), SuperDomainFunction.add]
    simp
  · -- a ∉ I: sign • (f_J + g_J) = sign • f_J + sign • g_J
    simp only [partialOdd, if_pos h, SuperDomainFunction.add]
    exact smul_add _ _ _

/-- partialOdd is compatible with scalar multiplication -/
theorem partialOdd_smul {p q : ℕ} (a : Fin q) (c : ℝ) (f : SuperDomainFunction p q) :
    partialOdd a (SuperDomainFunction.smul c f) =
    SuperDomainFunction.smul c (partialOdd a f) := by
  apply SuperDomainFunction.ext
  intro I
  by_cases h : a ∈ I
  · -- a ∈ I: 0 = c • 0
    simp only [partialOdd, if_neg (not_not_intro h), SuperDomainFunction.smul]
    simp
  · -- a ∉ I: sign • (c • f_J) = c • (sign • f_J)
    simp only [partialOdd, if_pos h, SuperDomainFunction.smul]
    rw [smul_smul, smul_smul, mul_comm]

/-- partialOdd applied twice to the same variable vanishes: ∂²f/∂θᵃ∂θᵃ = 0.

    After the first derivative removes a from the index set, the second derivative
    tries to check if a ∉ (insert a I), but a ∈ insert a I always, giving 0.
    This is the Grassmann relation θᵃ² = 0 at the derivative level. -/
theorem partialOdd_partialOdd_same {p q : ℕ} (a : Fin q) (f : SuperDomainFunction p q) :
    partialOdd a (partialOdd a f) = SuperDomainFunction.zero := by
  apply SuperDomainFunction.ext
  intro I
  by_cases h : a ∈ I
  · -- a ∈ I: outer partialOdd gives 0
    simp only [partialOdd, if_neg (not_not_intro h), SuperDomainFunction.zero]
  · -- a ∉ I: outer applies, inner checks a ∉ (insert a I) — false since a ∈ insert a I
    simp only [partialOdd, if_pos h, SuperDomainFunction.zero]
    simp only [if_neg (not_not_intro (Finset.mem_insert_self a I))]
    exact smul_zero _

/-- Two distinct partialOdd derivatives anticommute:
    ∂/∂θᵃ ∘ ∂/∂θᵇ = -∂/∂θᵇ ∘ ∂/∂θᵃ for a ≠ b.
    This is the derivative-level manifestation of θᵃθᵇ = -θᵇθᵃ. -/
theorem partialOdd_partialOdd_anticomm {p q : ℕ} (a b : Fin q) (hab : a ≠ b)
    (f : SuperDomainFunction p q) :
    partialOdd a (partialOdd b f) =
    SuperDomainFunction.neg (partialOdd b (partialOdd a f)) := by
  apply SuperDomainFunction.ext'; intro I x
  simp only [partialOdd, SuperDomainFunction.neg]
  by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
  · -- a ∈ I, b ∈ I: outer derivative gives 0 in both cases
    simp [ha, hb, SmoothFunction.zero_apply]
  · -- a ∈ I, b ∉ I
    simp only [ha, not_true_eq_false, ↓reduceIte, SmoothFunction.zero_apply,
      hb, not_false_eq_true, Finset.mem_insert_of_mem ha, smul_zero, neg_zero]
  · -- a ∉ I, b ∈ I: symmetric
    simp only [ha, not_false_eq_true, ↓reduceIte, SmoothFunction.smul_apply,
      hb, not_true_eq_false, Finset.mem_insert_of_mem hb, SmoothFunction.zero_apply,
      mul_zero, neg_zero]
  · -- a ∉ I, b ∉ I: both derivatives apply, signs differ by -1
    have hb_ins_a : b ∉ insert a I := by
      simp only [Finset.mem_insert, not_or]; exact ⟨hab.symm, hb⟩
    have ha_ins_b : a ∉ insert b I := by
      simp only [Finset.mem_insert, not_or]; exact ⟨hab, ha⟩
    simp only [ha, not_false_eq_true, ↓reduceIte, hb_ins_a, hb, ha_ins_b,
      SmoothFunction.smul_apply, SmoothFunction.neg_apply]
    -- Both access f at insert b (insert a I) = insert a (insert b I)
    have heq : insert b (insert a I) = insert a (insert b I) := by
      ext x; simp only [Finset.mem_insert]; tauto
    rw [heq]
    -- Now both sides reference f.coefficients (insert a (insert b I)) x
    -- The sign from LHS is (-1)^|I.filter(< a)| * (-1)^|(insert a I).filter(< b)|
    -- The sign from RHS is -(-1)^|I.filter(< b)| * (-1)^|(insert b I).filter(< a)|
    -- These differ by -1 because exactly one of a<b, b<a holds,
    -- changing one filter cardinality by 1.
    set α := (I.filter (· < a)).card
    set β := (I.filter (· < b)).card
    -- Compute filter cardinalities for the enlarged sets
    have hfa : a ∉ I.filter (· < b) := fun h => ha (Finset.mem_of_mem_filter _ h)
    have hfb : b ∉ I.filter (· < a) := fun h => hb (Finset.mem_of_mem_filter _ h)
    rcases lt_or_gt_of_ne hab with hab' | hab'
    · -- Case a < b
      have hfilt_b : ((insert a I).filter (· < b)).card = β + 1 := by
        rw [Finset.filter_insert, if_pos hab']
        exact Finset.card_insert_of_notMem hfa
      have hfilt_a : ((insert b I).filter (· < a)).card = α := by
        rw [Finset.filter_insert, if_neg (not_lt.mpr (le_of_lt hab'))]
      rw [hfilt_b, hfilt_a]
      ring
    · -- Case b < a
      have hfilt_b : ((insert a I).filter (· < b)).card = β := by
        rw [Finset.filter_insert, if_neg (not_lt.mpr (le_of_lt hab'))]
      have hfilt_a : ((insert b I).filter (· < a)).card = α + 1 := by
        rw [Finset.filter_insert, if_pos hab']
        exact Finset.card_insert_of_notMem hfb
      rw [hfilt_b, hfilt_a]
      ring

/-!
## Even Exterior Derivative d₀
-/

/-- The even exterior derivative d₀ on codimension-1 integral forms.
    d₀(Σᵢ fᵢ dx̂ⁱ · δ(dθ)) = [Σᵢ (-1)ⁱ (∂fᵢ/∂xⁱ)] [Dx Dθ] -/
noncomputable def d0Codim1 {p q : ℕ} (ν : IntegralFormCodim1 p q) : IntegralForm p q :=
  ⟨⟨fun I =>
    Finset.univ.sum fun (i : Fin p) =>
      ((-1 : ℝ) ^ (i : ℕ)) • (partialEven i (ν.components i)).coefficients I⟩⟩

/-!
## Super Exterior Derivative on Integral Forms

The exterior derivative on integral forms d: Ω^{p-1,q}_{int} → Ω^{p,q}_{int}
is given by d₀ alone. The odd derivative d₁ maps to a different graded piece
Ω^{p-1,q-1}_{int} (see module docstring) and does not contribute.

This is the mathematical content of "no boundary in odd directions."
-/

/-- The super exterior derivative on codimension-1 integral forms.

    For ν = Σᵢ fᵢ(x,θ) d̂xⁱ · δ(dθ), the exterior derivative produces the
    codimension-0 integral form:

      dν = Σᵢ (-1)ⁱ (∂fᵢ/∂xⁱ) [Dx Dθ]

    This is ONLY the d₀ (even) part of the de Rham differential. The d₁ (odd) part
    dθᵃ · ∂/∂θᵃ maps codim-1 integral forms to the space Ω^{p-1,q-1}_{int}
    (with one fewer delta function), NOT to codim-0 integral forms. Therefore d₁
    does not contribute to the codim-0 component of dν.

    See Witten (arXiv:1209.2199), §3.3 and Bernstein-Leites (1977). -/
noncomputable def superExteriorDerivativeCodim1 {p q : ℕ}
    (ν : IntegralFormCodim1 p q) : IntegralForm p q :=
  d0Codim1 ν

/-!
## The Divergence Characterization

After Berezin integration, d₀(ν) produces the classical divergence of the
vector field F_i(x) = (-1)^i · (∫dθ fᵢ)(x).

This is NOT definitional: it requires that fderiv (c * f) = c * fderiv f
(linearity of the Fréchet derivative), which is a real theorem from Mathlib.
-/

/-- The body divergence: div(F)(x) = Σᵢ ∂Fᵢ/∂xⁱ (x). -/
noncomputable def bodyDivergence {p : ℕ} (F : Fin p → SmoothFunction p) :
    SmoothFunction p :=
  ⟨fun x => Finset.univ.sum fun (i : Fin p) =>
      fderiv ℝ (F i).toFun x (Pi.single i 1),
   by
    apply ContDiff.sum
    intro i _
    exact (F i).smooth.fderiv_right
      (le_of_eq (WithTop.top_add (1 : WithTop ℕ∞))) |>.clm_apply contDiff_const⟩

/-- The signed Berezin components: F_i(x) = (-1)^i · (∫dθ fᵢ)(x). -/
noncomputable def signedBerezinComponents {p q : ℕ} (ν : IntegralFormCodim1 p q) :
    Fin p → SmoothFunction p :=
  fun i => ⟨fun x => (-1 : ℝ) ^ (i : ℕ) * berezinIntegralOdd (ν.components i) x,
    contDiff_const.mul (berezinIntegralOdd (ν.components i)).smooth⟩

/-- **d₀ equals the classical divergence** after Berezin integration.

    (∫dθ d₀ν)(x) = div(F)(x) where F_i = (-1)^i · ∫dθ fᵢ.

    This bridges the super divergence d₀ with the classical divergence on the body ℝᵖ.
    The proof uses fderiv_const_mul: the Fréchet derivative of c·f equals c times
    the Fréchet derivative of f. This is a real Mathlib theorem, not definitional. -/
theorem d0_is_divergence {p q : ℕ} (ν : IntegralFormCodim1 p q) :
    berezinIntegralOdd (d0Codim1 ν).coefficient =
    bodyDivergence (signedBerezinComponents ν) := by
  apply SmoothFunction.ext
  intro x
  simp only [berezinIntegralOdd, d0Codim1, bodyDivergence, signedBerezinComponents, partialEven]
  -- LHS is (Σᵢ (-1)^i • sf_i).toFun x, need to distribute over sum
  rw [SuperDomainFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  -- LHS term: ((-1)^i • sf_i) x = (-1)^i * sf_i x
  simp only [SmoothFunction.smul_apply]
  -- RHS term: fderiv (fun y => (-1)^i * fI_univ y) x eᵢ
  -- Pull constant out of fderiv using fderiv_const_mul
  have hf : DifferentiableAt ℝ ((ν.components i).coefficients Finset.univ).toFun x :=
    ((ν.components i).coefficients Finset.univ).differentiable'.differentiableAt
  symm
  show fderiv ℝ (fun y => (-1 : ℝ) ^ (↑i : ℕ) *
      ((ν.components i).coefficients Finset.univ).toFun y) x (Pi.single i 1) = _
  simp only [fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-!
## Linearity of the Exterior Derivative
-/

/-- d₀ is additive on codimension-1 forms (coefficient-level).
    Uses `partialEven_add` (linearity of fderiv). -/
theorem d0Codim1_add {p q : ℕ} (ν₁ ν₂ : IntegralFormCodim1 p q) (I : Finset (Fin q)) :
    (d0Codim1 (ν₁ + ν₂)).coefficient.coefficients I =
    (d0Codim1 ν₁).coefficient.coefficients I +
    (d0Codim1 ν₂).coefficient.coefficients I := by
  simp only [d0Codim1]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  -- (ν₁ + ν₂).components i = add (ν₁.components i) (ν₂.components i)
  show (-1 : ℝ) ^ (i : ℕ) •
    (partialEven i (SuperDomainFunction.add (ν₁.components i) (ν₂.components i))).coefficients I =
    (-1 : ℝ) ^ (i : ℕ) • (partialEven i (ν₁.components i)).coefficients I +
    (-1 : ℝ) ^ (i : ℕ) • (partialEven i (ν₂.components i)).coefficients I
  rw [partialEven_add]
  -- Goal: sign • (add (pe f) (pe g)).coefficients I = sign • pe_f_I + sign • pe_g_I
  simp only [SuperDomainFunction.add]
  exact smul_add _ _ _

/-!
## Exterior Derivative Properties
-/

/-- The super exterior derivative equals d₀ (definitionally). -/
theorem superExteriorDerivativeCodim1_eq_d0 {p q : ℕ} (ν : IntegralFormCodim1 p q) :
    superExteriorDerivativeCodim1 ν = d0Codim1 ν := rfl

/-- The super exterior derivative is additive. -/
theorem superExteriorDerivativeCodim1_add {p q : ℕ}
    (ν₁ ν₂ : IntegralFormCodim1 p q) (I : Finset (Fin q)) :
    (superExteriorDerivativeCodim1 (ν₁ + ν₂)).coefficient.coefficients I =
    (superExteriorDerivativeCodim1 ν₁).coefficient.coefficients I +
    (superExteriorDerivativeCodim1 ν₂).coefficient.coefficients I :=
  d0Codim1_add ν₁ ν₂ I

end Supermanifolds
