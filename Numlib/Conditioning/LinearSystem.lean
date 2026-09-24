import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.RCLike.Lemmas
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Conditioning.Problem

/-!
# Perturbation theory for linear systems

Normwise error bounds for `A x = b` in terms of the condition number `κ(A) = ‖A‖ ‖A⁻¹‖`
([saad2003iterative] §1.13.2 (1.76), [han2009theoretical] (2.4.1), [kress1998numerical] Thm 5.3,
[higham2002accuracy] Thm 7.2, [quarteroni2000numerical] §3.1), the residual–error relation, and
the Rigal–Gaches formula for the normwise backward error ([higham2002accuracy] Thm 7.1,
[fong2012cg] (3.2)–(3.3)).  The normwise backward error of an approximate solution `y`, relative
to tolerances `α` on `A` and `β` on `b`, is the least `ξ` for which `y` solves exactly some system
`(A + ΔA) y = b + Δb` with `‖ΔA‖ ≤ ξ α ‖A‖` and `‖Δb‖ ≤ ξ β ‖b‖`; the Rigal–Gaches theorem
evaluates it in closed form as `‖b - A y‖ / (α ‖A‖ ‖y‖ + β ‖b‖)`.

The chapter-3 layer of [quarteroni2000numerical] is here as well:

* Kahan's distance to singularity, `ContinuousLinearEquiv.isLeast_dist_singular` (Remark 3.1,
  (3.6)): in any operator norm on a finite-dimensional space, the least relative distance from an
  isomorphism to a singular operator is `1 / κ`; its lower half
  `NormedRing.norm_le_of_not_isUnit_add` is the corrected (3.7);
* the two inequalities of Theorem 3.2 (`relative_error_le_condNumber_mul_relative_residual`,
  `ContinuousLinearEquiv.relative_residual_le_condNumber_mul_relative_error`) and the relative
  bounds (3.12)–(3.13) of Theorem 3.3 (`relative_error_le_of_norm_le_mul`,
  `norm_add_div_le_of_norm_le_mul`);
* Property 3.1 on approximate inverses, in a complete normed ring
  (`NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt` and its companions), with (3.19) and the a
  posteriori bound (3.20) (`norm_error_le_of_norm_mul_sub_one_lt`).

The condition number as the sensitivity of inversion ([golub2013matrix] §2.6):

* `relative_error_le_norm_inverse`, the rigorous form of (2.6.2), of which
  `relative_error_le_condNumber` is the consequence after `‖b‖ ≤ ‖A‖ ‖x‖`;
* `ContinuousLinearEquiv.relCondNumber_ringInverse`: `κ(A)` is the relative condition number
  (`Conditioning.relCondNumber` of `Numlib/Conditioning/Problem`) of `T ↦ T⁻¹` at `A`, because the
  derivative `H ↦ -A⁻¹ H A⁻¹` of inversion has norm `‖A⁻¹‖²`
  (`ContinuousLinearEquiv.norm_mulLeftRight_symm_symm`, from
  `ContinuousLinearMap.norm_mulLeftRight_apply_apply`);
* `ContinuousLinearEquiv.tendsto_iSup_norm_inverse_add_sub_div`: the book's limit formula (2.6.7)
  itself, by squeezing between `κ / (1 + ε κ)` and `κ / (1 - ε κ)`.

The componentwise theory (the Skeel condition numbers, (3.14)–(3.16)) is
`Numlib/Conditioning/LinearSystem/Componentwise`.

**Two backward errors.** The root-namespace `backwardError` of this module is the normwise,
weighted backward error of a linear system (Rigal–Gaches), a real number. The
`Conditioning.backwardError` of `Numlib/Conditioning/Method` is the `ℝ≥0∞`-valued infimum of the
sizes of the data perturbations for which a computed solution of an abstract problem is exact.
They measure different things — the former weights the perturbations of `A` and `b` relatively
and by tolerances, the latter is absolute on a single datum — and no bridge between them is
stated.
-/

open Filter NormedRing Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section TwoSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The two-space residual–error relation** ([han2009theoretical], (2.4.1)): for an isomorphism `L
: E ≃L[𝕜] F` of normed spaces, the relative error of the solution of `L v = w` is at most `κ L`
times the relative error of the data.

The single-space `relative_error_le_condNumber_mul_relative_residual` is the case `F = E`. -/
theorem ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual (L : E ≃L[𝕜] F)
    {v v' : E} {w w' : F} (hv : L v = w) (hv' : L v' = w') (hw : w ≠ 0) :
    ‖v - v'‖ / ‖v‖ ≤ L.condNumber * (‖w - w'‖ / ‖w‖) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hv]; simp)
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hvv : v - v' = (L.symm : F →L[𝕜] E) (w - w') := by
    rw [← hv, ← hv']
    simp
  have h1 : ‖v - v'‖ ≤ ‖(L.symm : F →L[𝕜] E)‖ * ‖w - w'‖ := by
    rw [hvv]
    exact (L.symm : F →L[𝕜] E).le_opNorm _
  have h2 : ‖w‖ ≤ ‖(L : E →L[𝕜] F)‖ * ‖v‖ := by
    rw [← hv]
    simpa using (L : E →L[𝕜] F).le_opNorm v
  rw [ContinuousLinearEquiv.condNumber, ← mul_div_assoc, div_le_div_iff₀ hvn hwn]
  calc ‖v - v'‖ * ‖w‖
      ≤ ‖(L.symm : F →L[𝕜] E)‖ * ‖w - w'‖ * (‖(L : E →L[𝕜] F)‖ * ‖v‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖(L : E →L[𝕜] F)‖ * ‖(L.symm : F →L[𝕜] E)‖ * ‖w - w'‖ * ‖v‖ := by ring

end TwoSpace

/-- Residual–error relation: `‖x - y‖ / ‖x‖ ≤ κ(A) ‖b - A y‖ / ‖b‖`, where `κ(A) = ‖A‖ ‖A⁻¹‖`
([han2009theoretical], (2.4.1)).  It is the case `F = E` of
`ContinuousLinearEquiv.relative_error_le_condNumber_mul_relative_residual`, with `w' = A y`. -/
theorem relative_error_le_condNumber_mul_relative_residual (A : E ≃L[𝕜] E) {b x y : E}
    (hx : A x = b) (hb : b ≠ 0) :
    ‖x - y‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) * (‖b - A y‖ / ‖b‖) := by
  rw [ContinuousLinearEquiv.condNumber_coe]
  exact A.relative_error_le_condNumber_mul_relative_residual hx rfl hb

/-- **The normwise perturbation bound with `‖A⁻¹‖`** ([golub2013matrix] (2.6.2), rigorous form):
if `A x = b`, `(A + ΔA) y = b + Δb`, `‖A⁻¹‖ ‖ΔA‖ < 1` and `x ≠ 0`, then
`‖y - x‖ / ‖x‖ ≤ ‖A⁻¹‖ / (1 - ‖A⁻¹‖ ‖ΔA‖) (‖Δb‖ / ‖x‖ + ‖ΔA‖)`. With `ΔA = ε F`, `Δb = ε f` this is
the book's first-order bound with its `O(ε²)` term made explicit as the factor
`1 / (1 - |ε| ‖A⁻¹‖ ‖F‖)`. From `A (y - x) = Δb - ΔA y` and `‖y‖ ≤ ‖y - x‖ + ‖x‖`. -/
theorem relative_error_le_norm_inverse (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) {b Δb x y : E}
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖Δb‖ / ‖x‖ + ‖ΔA‖) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hden : 0 < 1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ := by linarith
  -- the residual identity `A (y - x) = Δb - ΔA y`
  have hyx : y - x = (A.symm : E →L[𝕜] E) (Δb - ΔA y) := by
    have hAy : (A : E →L[𝕜] E) y + ΔA y = b + Δb := by rw [← hy]; simp
    have hb' : b = (A : E →L[𝕜] E) y + ΔA y - Δb := by rw [hAy]; abel
    have hsub : Δb - ΔA y = (A : E →L[𝕜] E) y - b := by rw [hb']; abel
    rw [hsub, ← hx]
    simp
  have h1 : ‖y - x‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖y‖ := by
    calc ‖y - x‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb - ΔA y‖ := by
          rw [hyx]
          exact (A.symm : E →L[𝕜] E).le_opNorm _
      _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * (‖Δb‖ + ‖ΔA‖ * ‖y‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (norm_sub_le _ _).trans (by gcongr; exact ΔA.le_opNorm _)
      _ = ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖y‖ := by ring
  have h2 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  have h3 : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖y‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * (‖y - x‖ + ‖x‖) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hexp : ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
        * (‖Δb‖ / ‖x‖ + ‖ΔA‖) * ‖x‖
      = (‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖x‖)
        / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖) := by
    field_simp
  rw [div_le_iff₀ hxn, hexp, le_div_iff₀ hden]
  nlinarith [h1, h3]

/-- Normwise perturbation bound ([saad2003iterative], (1.76); [kress1998numerical], Thm 5.3;
[higham2002accuracy], *Accuracy and Stability*, Thm 7.2): if `A x = b`, `(A + ΔA) y = b + Δb` and
`‖A⁻¹‖ ‖ΔA‖ < 1` then `‖y - x‖/‖x‖ ≤ κ(A)/(1 - ‖A⁻¹‖‖ΔA‖) (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)`. It is
`relative_error_le_norm_inverse` after `‖b‖ ≤ ‖A‖ ‖x‖`. -/
theorem relative_error_le_condNumber (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    {b Δb x y : E} (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hAb : ‖b‖ ≤ ‖(A : E →L[𝕜] E)‖ * ‖x‖ := by
    rw [← hx]
    simpa using (A : E →L[𝕜] E).le_opNorm x
  have hN : 0 < ‖(A : E →L[𝕜] E)‖ := by nlinarith [norm_nonneg (A : E →L[𝕜] E)]
  have hden : 0 < 1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ := by linarith
  refine (relative_error_le_norm_inverse A ΔA hx hy hsmall hx0).trans ?_
  have hexp : condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
        * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖)
      = ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
        * (‖(A : E →L[𝕜] E)‖ * ‖Δb‖ / ‖b‖ + ‖ΔA‖) := by
    rw [ContinuousLinearEquiv.condNumber_eq]
    field_simp
    ring
  rw [hexp]
  refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _)
    (div_nonneg (norm_nonneg _) hden.le)
  rw [div_le_div_iff₀ hxn hbn]
  nlinarith [norm_nonneg Δb]

/-- The perturbed operator is invertible and the perturbed solution exists (companion to
`relative_error_le_condNumber`). -/
theorem exists_perturbed_solution [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (b' : E) :
    ∃! y, ((A : E →L[𝕜] E) + ΔA) y = b' := by
  obtain ⟨e', he', -, -⟩ := ContinuousLinearEquiv.exists_symm_norm_le_of_add A ΔA hsmall
  refine ⟨e'.symm b', ?_, fun z hz => ?_⟩
  · rw [← he']; simp
  · rw [← he'] at hz
    rw [← hz]; simp

section BackwardError

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The normwise backward error of `y` for `A x = b` with tolerances `α` on `A` and `β` on `b`: `‖b
- A y‖ / (α ‖A‖ ‖y‖ + β ‖b‖)`.  By the Rigal–Gaches theorem (`isLeast_backwardError`) this is the
least `ξ` for which `y` solves exactly some `(A + ΔA) y = b + Δb` with `‖ΔA‖ ≤ ξ α ‖A‖` and `‖Δb‖ ≤
ξ β ‖b‖` ([fong2012cg], (3.2)). -/
noncomputable def backwardError (A : E →L[𝕜] E) (b y : E) (α β : ℝ) : ℝ :=
  ‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖)

/-- The defining quotient of `backwardError`, in a form `rw` can use. -/
private theorem backwardError_def (A : E →L[𝕜] E) (b y : E) (α β : ℝ) :
    backwardError A b y α β = ‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖) := rfl

/-- The backward error is nonnegative when its denominator is positive. -/
private theorem backwardError_nonneg (A : E →L[𝕜] E) (b y : E) {α β : ℝ}
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) : 0 ≤ backwardError A b y α β := by
  rw [backwardError_def]
  positivity

/-- The optimal perturbations ([fong2012cg], (3.3)): `ΔA = ((1 - ω) / ‖y‖²) r ⊗ y`, `Δb = -ω r`,
with `r = b - A y` and `ω = β ‖b‖ / (α ‖A‖ ‖y‖ + β ‖b‖)`.  They attain the backward error exactly.
-/
theorem exists_optimal_perturbation (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
      ‖ΔA‖ = backwardError A b y α β * α * ‖A‖ ∧ ‖Δb‖ = backwardError A b y α β * β * ‖b‖ := by
  have hη0 : 0 ≤ backwardError A b y α β := backwardError_nonneg A b y hpos
  by_cases hy : y = 0
  · subst hy
    have hbpos : 0 < β * ‖b‖ := by simpa using hpos
    have hβ0 : β ≠ 0 := by rintro rfl; simp at hbpos
    have hbne : ‖b‖ ≠ 0 := by rintro h; rw [h, mul_zero] at hbpos; exact lt_irrefl 0 hbpos
    refine ⟨((backwardError A b (0 : E) α β * α : ℝ) : 𝕜) • A, -b, by simp, ?_, ?_⟩
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity), mul_assoc]
    · rw [norm_neg, backwardError_def]
      simp only [map_zero, sub_zero, norm_zero, mul_zero, zero_add]
      field_simp
  · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set D : ℝ := α * ‖A‖ * ‖y‖ + β * ‖b‖ with hDdef
    set ω : ℝ := β * ‖b‖ / D with hωdef
    have hDne : D ≠ 0 := ne_of_gt hpos
    have hω0 : 0 ≤ ω := by rw [hωdef]; positivity
    have hω1 : 1 - ω = α * ‖A‖ * ‖y‖ / D := by
      rw [hωdef, eq_div_iff hDne, sub_mul, one_mul, div_mul_cancel₀ _ hDne, hDdef]
      ring
    have hc0 : 0 ≤ (1 - ω) / ‖y‖ ^ 2 := by
      rw [hω1]
      have : 0 ≤ α * ‖A‖ * ‖y‖ := by positivity
      positivity
    refine ⟨(innerSL 𝕜 y).smulRight ((((1 - ω) / ‖y‖ ^ 2 : ℝ) : 𝕜) • (b - A y)),
      ((-ω : ℝ) : 𝕜) • (b - A y), ?_, ?_, ?_⟩
    · have hyy : (inner 𝕜 y y : 𝕜) = ((‖y‖ ^ 2 : ℝ) : 𝕜) := by
        rw [inner_self_eq_norm_sq_to_K]
        push_cast
        ring
      have happ : ((innerSL 𝕜 y).smulRight ((((1 - ω) / ‖y‖ ^ 2 : ℝ) : 𝕜) • (b - A y))) y
          = ((1 - ω : ℝ) : 𝕜) • (b - A y) := by
        rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hyy, smul_smul,
          ← RCLike.ofReal_mul]
        congr 2
        field_simp
      rw [add_apply, happ]
      push_cast
      module
    · rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_smul,
        RCLike.norm_ofReal, abs_of_nonneg hc0, backwardError_def, ← hDdef, hω1]
      field_simp
    · rw [norm_smul, RCLike.norm_ofReal, abs_neg, abs_of_nonneg hω0, backwardError_def, ← hDdef,
        hωdef]
      field_simp

/-- The Rigal–Gaches theorem ([higham2002accuracy], *Accuracy and Stability*, Thm 7.1):
`backwardError A b y α β` is the least `ξ` such that `(A + ΔA) y = b + Δb` for some `‖ΔA‖ ≤ ξ α
‖A‖`, `‖Δb‖ ≤ ξ β ‖b‖`. -/
theorem isLeast_backwardError (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    IsLeast {ξ : ℝ | ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
        ‖ΔA‖ ≤ ξ * α * ‖A‖ ∧ ‖Δb‖ ≤ ξ * β * ‖b‖}
      (backwardError A b y α β) := by
  constructor
  · obtain ⟨ΔA, Δb, h1, h2, h3⟩ := exists_optimal_perturbation A b y hα hβ hpos
    exact ⟨ΔA, Δb, h1, h2.le, h3.le⟩
  · rintro ξ ⟨ΔA, Δb, h1, h2, h3⟩
    have hb : b = A y + ΔA y - Δb := by
      rw [← add_apply, h1]; abel
    have hr : b - A y = ΔA y - Δb := by rw [hb]; abel
    rw [backwardError_def, div_le_iff₀ hpos]
    calc ‖b - A y‖ = ‖ΔA y - Δb‖ := by rw [hr]
      _ ≤ ‖ΔA y‖ + ‖Δb‖ := norm_sub_le _ _
      _ ≤ ‖ΔA‖ * ‖y‖ + ‖Δb‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ξ * α * ‖A‖ * ‖y‖ + ξ * β * ‖b‖ := by gcongr
      _ = ξ * (α * ‖A‖ * ‖y‖ + β * ‖b‖) := by ring

/-- Stopping rule ([fong2012cg], (3.4)): with `r = b - A y`, `backwardError ≤ ξ ↔ ‖r‖ ≤ ξ (α ‖A‖ ‖y‖
+ β ‖b‖)`. -/
theorem backwardError_le_iff (A : E →L[𝕜] E) (b y : E) {α β ξ : ℝ}
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    backwardError A b y α β ≤ ξ ↔ ‖b - A y‖ ≤ ξ * (α * ‖A‖ * ‖y‖ + β * ‖b‖) := by
  rw [backwardError_def, div_le_iff₀ hpos]

end BackwardError

/-- **First-order perturbation theory for a linear system** ([saad2003iterative], (1.74)–(1.75);
[kress1998numerical], Thm 5.3; [higham2002accuracy], Ch. 7): for an isomorphism `A`, a perturbation
direction `B` of the operator and `e` of the right-hand side, the solution of `(A + ε B) x(ε) = b +
ε e` is differentiable in `ε` at `0`, with derivative `A⁻¹ (e - B (A⁻¹ b))`.

The solution is written with `Ring.inverse` in the algebra `E →L[𝕜] E`, whose junk value is
irrelevant here: `A` is a unit, so `A + ε B` is one for all small `ε` and the map differentiated
agrees with the solution of the perturbed system near `0`. -/
theorem hasDerivAt_perturbed_solution [CompleteSpace E] (A : E ≃L[𝕜] E) (B : E →L[𝕜] E)
    (b e : E) :
    HasDerivAt (fun ε : 𝕜 => (Ring.inverse ((A : E →L[𝕜] E) + ε • B)) (b + ε • e))
      ((A.symm : E →L[𝕜] E) (e - B ((A.symm : E →L[𝕜] E) b))) 0 := by
  obtain ⟨u, hu⟩ : IsUnit (A : E →L[𝕜] E) := ⟨A.toUnit, rfl⟩
  have hg : HasDerivAt (fun ε : 𝕜 => (A : E →L[𝕜] E) + ε • B) B 0 := by
    simpa using (hasDerivAt_const_add_iff (A : E →L[𝕜] E)).2
      (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) B)
  have hg0 : (fun ε : 𝕜 => (A : E →L[𝕜] E) + ε • B) 0 = (u : E →L[𝕜] E) := by
    simp [hu]
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (↑u⁻¹) (↑u⁻¹))
      ((fun ε : 𝕜 => (A : E →L[𝕜] E) + ε • B) 0) := by
    rw [hg0]
    exact hasFDerivAt_ringInverse u
  have hcomp : HasDerivAt (fun ε : 𝕜 => Ring.inverse ((A : E →L[𝕜] E) + ε • B))
      ((-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (↑u⁻¹) (↑u⁻¹)) B) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt 0 hinv hg
    exact h
  have hb : HasDerivAt (fun ε : 𝕜 => b + ε • e) e 0 := by
    simpa using (hasDerivAt_const_add_iff b).2
      (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) e)
  have hAinv : ((u⁻¹ : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) = (A.symm : E →L[𝕜] E) := by
    rw [← ContinuousLinearEquiv.ring_inverse_coe A, ← hu, Ring.inverse_unit]
  have hres := HasDerivAt.clm_apply hcomp hb
  convert hres using 1
  simp only [zero_smul, add_zero, ContinuousLinearEquiv.ring_inverse_coe, hAinv, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, map_sub]
  abel

/-! ### The lower inequality of the residual–error relation -/

section Lower

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The lower inequality of [quarteroni2000numerical] Theorem 3.2**, the first half of (3.11):
for an isomorphism `L : E ≃L[𝕜] F` with `L v = w`, `L v' = w'` and `v ≠ 0`, the relative change
of the data is at most `κ L` times the relative change of the solution, `‖w - w'‖ / ‖w‖ ≤ κ L
(‖v - v'‖ / ‖v‖)` — that is, `(1 / κ L) ‖δb‖ / ‖b‖ ≤ ‖δx‖ / ‖x‖`. It is the upper inequality for
`L.symm`, whose condition number is that of `L`. -/
theorem ContinuousLinearEquiv.relative_residual_le_condNumber_mul_relative_error (L : E ≃L[𝕜] F)
    {v v' : E} {w w' : F} (hv : L v = w) (hv' : L v' = w') (hv0 : v ≠ 0) :
    ‖w - w'‖ / ‖w‖ ≤ L.condNumber * (‖v - v'‖ / ‖v‖) := by
  have h := L.symm.relative_error_le_condNumber_mul_relative_residual (v := w) (v' := w')
    (w := v) (w' := v') (by rw [← hv]; simp) (by rw [← hv']; simp) hv0
  rwa [ContinuousLinearEquiv.condNumber_symm] at h

end Lower

/-! ### The distance to singularity -/

section Distance

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

omit [NormOneClass R] in
/-- **The lower half of Kahan's distance-to-singularity formula** ([quarteroni2000numerical]
Remark 3.1): a perturbation `t` that makes the unit `a` singular has norm at least `‖a⁻¹‖⁻¹`.
This is also the corrected [quarteroni2000numerical] (3.7): a perturbation with `‖δA‖ ‖A⁻¹‖ < 1`
leaves `A + δA` nonsingular (the printed (3.7) has `‖A‖` for `‖A⁻¹‖` and the implication
backwards). Contrapositive of `Units.isUnit_add_of_norm_lt`. -/
theorem NormedRing.norm_le_of_not_isUnit_add {a t : R} (ha : IsUnit a) (h : ¬ IsUnit (a + t)) :
    ‖Ring.inverse a‖⁻¹ ≤ ‖t‖ := by
  obtain ⟨x, rfl⟩ := ha
  by_contra hlt
  rw [not_le, Ring.inverse_unit] at hlt
  exact h (Units.isUnit_add_of_norm_lt x t hlt)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a finite-dimensional space the operator norm is attained on the unit sphere. -/
theorem ContinuousLinearMap.exists_norm_eq_one_and_norm_apply_eq [FiniteDimensional 𝕜 E]
    [Nontrivial E] (f : E →L[𝕜] E) : ∃ y : E, ‖y‖ = 1 ∧ ‖f y‖ = ‖f‖ := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have hne : (Metric.sphere (0 : E) 1).Nonempty := by
    have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    exact NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
    (f.continuous.norm.continuousOn)
  rw [mem_sphere_zero_iff_norm] at hy
  refine ⟨y, hy, le_antisymm (by simpa [hy] using f.le_opNorm y) ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound f (norm_nonneg _) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
  have h1 : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
      inv_mul_cancel₀ hxn]
  have h2 : ‖f (((‖x‖⁻¹ : ℝ) : 𝕜) • x)‖ ≤ ‖f y‖ := hmax (mem_sphere_zero_iff_norm.2 h1)
  rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (norm_nonneg x)),
    inv_mul_le_iff₀ (norm_pos_iff.2 hx0), mul_comm] at h2
  exact h2

/-- **The upper half of Kahan's distance-to-singularity formula** ([quarteroni2000numerical]
Remark 3.1, [Kah66], [Gas83]): on a nontrivial finite-dimensional space, an isomorphism `A` is
made singular by a rank-one perturbation of norm exactly `‖A⁻¹‖⁻¹`. With `y` a unit vector at
which `‖A⁻¹ y‖ = ‖A⁻¹‖`, `x = A⁻¹ y` and `φ` a norming functional of `x`, the perturbation
`t = -‖x‖⁻¹ φ(·) y` sends `x` to `-y`, so `(A + t) x = 0`. The construction is that of the
Rigal–Gaches optimal perturbation (`exists_optimal_perturbation`) with the inner product
replaced by a norming functional, which is what makes it valid in any operator norm. -/
theorem ContinuousLinearEquiv.exists_not_isUnit_add_norm_le [FiniteDimensional 𝕜 E]
    [Nontrivial E] (A : E ≃L[𝕜] E) :
    ∃ t : E →L[𝕜] E, ¬ IsUnit ((A : E →L[𝕜] E) + t) ∧ ‖t‖ = ‖(A.symm : E →L[𝕜] E)‖⁻¹ := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  obtain ⟨y, hy1, hy⟩ := (A.symm : E →L[𝕜] E).exists_norm_eq_one_and_norm_apply_eq
  set x := (A.symm : E →L[𝕜] E) y with hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  have hx0 : x ≠ 0 := by
    rw [hx]
    intro h
    exact hy0 (by simpa using congrArg A h)
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector 𝕜 x hxn
  refine ⟨-(((‖x‖⁻¹ : ℝ) : 𝕜) • φ.smulRight y), fun hu => ?_, ?_⟩
  · have hinj := (ContinuousLinearMap.isUnit_iff_bijective.1 hu).1
    have h0 : ((A : E →L[𝕜] E) + -(((‖x‖⁻¹ : ℝ) : 𝕜) • φ.smulRight y)) x = 0 := by
      change (A : E →L[𝕜] E) x + -(((‖x‖⁻¹ : ℝ) : 𝕜) • (φ x • y)) = 0
      rw [hφx, smul_smul, ← RCLike.ofReal_mul, inv_mul_cancel₀ hxn, RCLike.ofReal_one, one_smul,
        hx]
      simp
    exact hx0 (hinj (h0.trans (by simp)))
  · rw [norm_neg, norm_smul, ContinuousLinearMap.norm_smulRight_apply, hφ1, hy1, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)), hx, hy]
    ring

/-- On a nontrivial finite-dimensional space, for operators `a`, `b` there is an operator `T` of
norm `1` with `‖a T b‖ = ‖a‖ ‖b‖`: with unit vectors `y`, `z` at which `a` and `b` attain their
norms and a norming functional `φ` of `b z`, the rank-one `T = φ(·) y` sends `z` through
`a T b z = ‖b z‖ a y`. -/
theorem ContinuousLinearMap.exists_norm_eq_one_and_norm_mul_mul_eq [FiniteDimensional 𝕜 E]
    [Nontrivial E] (a b : E →L[𝕜] E) : ∃ T : E →L[𝕜] E, ‖T‖ = 1 ∧ ‖a * T * b‖ = ‖a‖ * ‖b‖ := by
  obtain ⟨y, hy1, hay⟩ := a.exists_norm_eq_one_and_norm_apply_eq
  obtain ⟨z, hz1, hbz⟩ := b.exists_norm_eq_one_and_norm_apply_eq
  obtain ⟨φ, hφ1, hφ⟩ := exists_dual_vector' 𝕜 (b z)
  have hT : ‖φ.smulRight y‖ = 1 := by rw [norm_smulRight_apply, hφ1, hy1, one_mul]
  refine ⟨φ.smulRight y, hT, le_antisymm ?_ ?_⟩
  · calc ‖a * φ.smulRight y * b‖ ≤ ‖a * φ.smulRight y‖ * ‖b‖ := _root_.norm_mul_le _ _
      _ ≤ ‖a‖ * ‖φ.smulRight y‖ * ‖b‖ := by gcongr; exact _root_.norm_mul_le _ _
      _ = ‖a‖ * ‖b‖ := by rw [hT, mul_one]
  have happ : (a * φ.smulRight y * b) z = ((‖b z‖ : ℝ) : 𝕜) • a y := by
    change a (φ (b z) • y) = _
    rw [hφ, map_smul]
  calc ‖a‖ * ‖b‖ = ‖(a * φ.smulRight y * b) z‖ := by
        rw [happ, norm_smul, RCLike.norm_ofReal, abs_norm, hbz, hay, mul_comm]
    _ ≤ ‖a * φ.smulRight y * b‖ * ‖z‖ := le_opNorm _ _
    _ = ‖a * φ.smulRight y * b‖ := by rw [hz1, mul_one]

/-- On a nontrivial finite-dimensional space, the two-sided multiplication `T ↦ a T b` of the
operator algebra has norm `‖a‖ ‖b‖`: `≤` is submultiplicativity
(`ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le`), `≥` is attained at the `T` of
`ContinuousLinearMap.exists_norm_eq_one_and_norm_mul_mul_eq`. -/
theorem ContinuousLinearMap.norm_mulLeftRight_apply_apply [FiniteDimensional 𝕜 E] [Nontrivial E]
    (a b : E →L[𝕜] E) : ‖ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) a b‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (opNorm_mulLeftRight_apply_apply_le 𝕜 _ a b) ?_
  obtain ⟨T, hT, hab⟩ := a.exists_norm_eq_one_and_norm_mul_mul_eq b
  calc ‖a‖ * ‖b‖ = ‖mulLeftRight 𝕜 (E →L[𝕜] E) a b T‖ := by rw [mulLeftRight_apply, hab]
    _ ≤ ‖mulLeftRight 𝕜 (E →L[𝕜] E) a b‖ * ‖T‖ := le_opNorm _ _
    _ = ‖mulLeftRight 𝕜 (E →L[𝕜] E) a b‖ := by rw [hT, mul_one]

/-- **The Fréchet derivative of inversion has norm `‖A⁻¹‖²`** in an operator norm on a nontrivial
finite-dimensional space: the derivative at `A` is `H ↦ -A⁻¹ H A⁻¹` (Mathlib
`hasFDerivAt_ringInverse`), and `ContinuousLinearMap.norm_mulLeftRight_apply_apply` computes the
norm of `H ↦ A⁻¹ H A⁻¹`. -/
theorem ContinuousLinearEquiv.norm_mulLeftRight_symm_symm [FiniteDimensional 𝕜 E] [Nontrivial E]
    (A : E ≃L[𝕜] E) :
    ‖ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (A.symm : E →L[𝕜] E) (A.symm : E →L[𝕜] E)‖
      = ‖(A.symm : E →L[𝕜] E)‖ ^ 2 := by
  rw [ContinuousLinearMap.norm_mulLeftRight_apply_apply, sq]

/-- **The condition number is the relative condition number of inversion** ([golub2013matrix]
(2.6.7), in the vocabulary of `Numlib/Conditioning/Problem`): on a nontrivial finite-dimensional
space, the relative condition number of `T ↦ T⁻¹` at an isomorphism `A` is `κ(A) = ‖A‖ ‖A⁻¹‖`. By
the first-order formula `Conditioning.relCondNumber_eq_enorm_fderiv`, it is
`‖H ↦ A⁻¹ H A⁻¹‖ ‖A‖ / ‖A⁻¹‖ = ‖A⁻¹‖² ‖A‖ / ‖A⁻¹‖`. -/
theorem ContinuousLinearEquiv.relCondNumber_ringInverse [FiniteDimensional 𝕜 E] [Nontrivial E]
    (A : E ≃L[𝕜] E) :
    Conditioning.relCondNumber (fun T : E →L[𝕜] E => Ring.inverse T) Set.univ (A : E →L[𝕜] E)
      = ENNReal.ofReal A.condNumber := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hne : ∀ B : E ≃L[𝕜] E, (B : E →L[𝕜] E) ≠ 0 := fun B hB => by
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact hy (B.injective (by simpa using congrArg (fun T : E →L[𝕜] E => T y) hB))
  have hsymm : 0 < ‖(A.symm : E →L[𝕜] E)‖ := norm_pos_iff.2 (hne A.symm)
  have hd : HasFDerivAt (fun T : E →L[𝕜] E => Ring.inverse T)
      (-ContinuousLinearMap.mulLeftRight 𝕜 (E →L[𝕜] E) (A.symm : E →L[𝕜] E)
        (A.symm : E →L[𝕜] E)) (A : E →L[𝕜] E) :=
    hasFDerivAt_ringInverse A.toUnit
  have hG : Ring.inverse (A : E →L[𝕜] E) = (A.symm : E →L[𝕜] E) := A.ring_inverse_coe
  rw [Conditioning.relCondNumber_eq_enorm_fderiv hd Filter.univ_mem (hne A)
      (by rw [hG]; exact hne A.symm), hG, enorm_neg, ← ofReal_norm, ← ofReal_norm,
    ← ofReal_norm, A.norm_mulLeftRight_symm_symm, ← ENNReal.ofReal_div_of_pos hsymm,
    ← ENNReal.ofReal_mul (by positivity), ContinuousLinearEquiv.condNumber]
  congr 1
  field_simp

/-- The two bounds behind `ContinuousLinearEquiv.tendsto_iSup_norm_inverse_add_sub_div`: for
`0 < ε` with `ε κ(A) < 1`, the largest change of the inverse under perturbations of relative size
`ε`, divided by `ε ‖A⁻¹‖`, lies between `κ / (1 + ε κ)` and `κ / (1 - ε κ)`. The upper bound is
`Units.norm_inverse_add_sub_le`; the lower one is attained at `ΔA = -ε ‖A‖ T` with `T` the
operator of `ContinuousLinearMap.exists_norm_eq_one_and_norm_mul_mul_eq` for `A⁻¹, A⁻¹`, through
`A⁻¹ ΔA A⁻¹ = (1 + A⁻¹ ΔA) ((A + ΔA)⁻¹ ΔA A⁻¹)` and `(A + ΔA)⁻¹ - A⁻¹ = -(A + ΔA)⁻¹ ΔA A⁻¹`. -/
private theorem ContinuousLinearEquiv.iSup_norm_inverse_add_sub_div_mem [FiniteDimensional 𝕜 E]
    [Nontrivial E] (A : E ≃L[𝕜] E) {ε : ℝ} (hε : 0 < ε) (hεκ : ε * A.condNumber < 1) :
    A.condNumber / (1 + ε * A.condNumber)
        ≤ (⨆ ΔA : {ΔA : E →L[𝕜] E // ‖ΔA‖ ≤ ε * ‖(A : E →L[𝕜] E)‖},
            ‖Ring.inverse ((A : E →L[𝕜] E) + ΔA) - (A.symm : E →L[𝕜] E)‖)
          / (ε * ‖(A.symm : E →L[𝕜] E)‖) ∧
      (⨆ ΔA : {ΔA : E →L[𝕜] E // ‖ΔA‖ ≤ ε * ‖(A : E →L[𝕜] E)‖},
            ‖Ring.inverse ((A : E →L[𝕜] E) + ΔA) - (A.symm : E →L[𝕜] E)‖)
          / (ε * ‖(A.symm : E →L[𝕜] E)‖) ≤ A.condNumber / (1 - ε * A.condNumber) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set A' : E →L[𝕜] E := (A : E →L[𝕜] E) with hA'
  set Ai : E →L[𝕜] E := (A.symm : E →L[𝕜] E) with hAi
  set a := ‖A'‖ with ha_def
  set s := ‖Ai‖ with hs_def
  have hne : ∀ B : E ≃L[𝕜] E, (B : E →L[𝕜] E) ≠ 0 := fun B hB => by
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact hy (B.injective (by simpa using congrArg (fun T : E →L[𝕜] E => T y) hB))
  have ha : 0 < a := norm_pos_iff.2 (hne A)
  have hs : 0 < s := norm_pos_iff.2 (hne A.symm)
  have hκ : A.condNumber = a * s := rfl
  rw [hκ] at hεκ ⊢
  have hεs : 0 < ε * s := mul_pos hε hs
  have hsmall : ∀ Δ : E →L[𝕜] E, ‖Δ‖ ≤ ε * a → ‖Δ‖ < ‖Ai‖⁻¹ := fun Δ hΔ => by
    rw [← hs_def, ← one_div, lt_div_iff₀ hs]
    nlinarith
  -- the upper bound, perturbation by perturbation
  have hup : ∀ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a},
      ‖Ring.inverse (A' + Δ) - Ai‖ ≤ s ^ 2 * (ε * a) / (1 - ε * (a * s)) := by
    rintro ⟨Δ, hΔ⟩
    have h : ‖Ring.inverse (A' + Δ) - Ai‖ ≤ s ^ 2 * ‖Δ‖ / (1 - s * ‖Δ‖) :=
      Units.norm_inverse_add_sub_le A.toUnit Δ (hsmall Δ hΔ)
    refine h.trans (div_le_div₀ (by positivity) (by gcongr) (by linarith) ?_)
    change 1 - ε * (a * s) ≤ 1 - s * ‖Δ‖
    nlinarith
  have : Nonempty {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a} := ⟨⟨0, by rw [norm_zero]; positivity⟩⟩
  have hbdd : BddAbove (Set.range fun Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a} =>
      ‖Ring.inverse (A' + Δ) - Ai‖) := ⟨_, Set.forall_mem_range.2 hup⟩
  -- the lower bound, at one perturbation
  obtain ⟨T, hT1, hTT⟩ := Ai.exists_norm_eq_one_and_norm_mul_mul_eq Ai
  set Δ₀ : E →L[𝕜] E := ((-(ε * a) : ℝ) : 𝕜) • T with hΔ₀_def
  have hΔ₀ : ‖Δ₀‖ = ε * a := by
    rw [hΔ₀_def, norm_smul, RCLike.norm_ofReal, abs_neg, abs_of_pos (by positivity), hT1,
      mul_one]
  have hunit : IsUnit (A' + Δ₀) := Units.isUnit_add_of_norm_lt A.toUnit Δ₀ (hsmall _ hΔ₀.le)
  set B := Ring.inverse (A' + Δ₀) with hB
  have hB1 : (A' + Δ₀) * B = 1 := Ring.mul_inverse_cancel _ hunit
  have hB2 : B * (A' + Δ₀) = 1 := Ring.inverse_mul_cancel _ hunit
  have hAiA : Ai * A' = 1 := by ext x; simp [hA', hAi]
  have hAAi : A' * Ai = 1 := by ext x; simp [hA', hAi]
  have hdiff : B - Ai = -(B * Δ₀ * Ai) := by
    calc B - Ai = B * (A' * Ai) - B * (A' + Δ₀) * Ai := by rw [hAAi, hB2, mul_one, one_mul]
      _ = -(B * Δ₀ * Ai) := by noncomm_ring
  have hkey : Ai * Δ₀ * Ai = (1 + Ai * Δ₀) * (B * Δ₀ * Ai) := by
    calc Ai * Δ₀ * Ai = Ai * ((A' + Δ₀) * B) * Δ₀ * Ai := by rw [hB1, mul_one]
      _ = (Ai * A' + Ai * Δ₀) * (B * Δ₀ * Ai) := by noncomm_ring
      _ = (1 + Ai * Δ₀) * (B * Δ₀ * Ai) := by rw [hAiA]
  have hn1 : ‖Ai * Δ₀ * Ai‖ = ε * a * s ^ 2 := by
    rw [hΔ₀_def, mul_smul_comm, smul_mul_assoc, norm_smul, RCLike.norm_ofReal, abs_neg,
      abs_of_pos (by positivity), hTT]
    ring
  have hn2 : ‖1 + Ai * Δ₀‖ ≤ 1 + ε * (a * s) := by
    refine (norm_add_le _ _).trans (add_le_add norm_one.le ?_)
    calc ‖Ai * Δ₀‖ ≤ s * ‖Δ₀‖ := _root_.norm_mul_le _ _
      _ = ε * (a * s) := by rw [hΔ₀]; ring
  have hD : ε * a * s ^ 2 ≤ (1 + ε * (a * s)) * ‖B - Ai‖ := by
    rw [← hn1, hkey, hdiff, norm_neg]
    exact (_root_.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn2 (norm_nonneg _))
  have hlow : ‖B - Ai‖ ≤ ⨆ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a}, ‖Ring.inverse (A' + Δ) - Ai‖ :=
    le_ciSup hbdd ⟨Δ₀, hΔ₀.le⟩
  constructor
  · rw [div_le_div_iff₀ (by positivity) hεs]
    calc a * s * (ε * s) = ε * a * s ^ 2 := by ring
      _ ≤ (1 + ε * (a * s)) * ‖B - Ai‖ := hD
      _ ≤ (1 + ε * (a * s)) * ⨆ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a},
            ‖Ring.inverse (A' + Δ) - Ai‖ := by gcongr
      _ = _ := by ring
  · rw [div_le_div_iff₀ hεs (by linarith)]
    calc (⨆ Δ : {Δ : E →L[𝕜] E // ‖Δ‖ ≤ ε * a}, ‖Ring.inverse (A' + Δ) - Ai‖)
          * (1 - ε * (a * s))
        ≤ s ^ 2 * (ε * a) / (1 - ε * (a * s)) * (1 - ε * (a * s)) :=
          mul_le_mul_of_nonneg_right (ciSup_le hup) (by linarith)
      _ = a * s * (ε * s) := by
          rw [div_mul_cancel₀ _ (by linarith : (0 : ℝ) < 1 - ε * (a * s)).ne']
          ring

/-- **The book's limit formula for the condition number** ([golub2013matrix] (2.6.7)): on a
nontrivial finite-dimensional space, `κ(A)` is the limit as `ε → 0⁺` of the largest change
`‖(A + ΔA)⁻¹ - A⁻¹‖` over perturbations with `‖ΔA‖ ≤ ε ‖A‖`, divided by `ε ‖A⁻¹‖`. The quotient
lies between `κ / (1 + ε κ)` and `κ / (1 - ε κ)`. -/
theorem ContinuousLinearEquiv.tendsto_iSup_norm_inverse_add_sub_div [FiniteDimensional 𝕜 E]
    [Nontrivial E] (A : E ≃L[𝕜] E) :
    Tendsto (fun ε : ℝ => (⨆ ΔA : {ΔA : E →L[𝕜] E // ‖ΔA‖ ≤ ε * ‖(A : E →L[𝕜] E)‖},
        ‖Ring.inverse ((A : E →L[𝕜] E) + ΔA) - (A.symm : E →L[𝕜] E)‖)
          / (ε * ‖(A.symm : E →L[𝕜] E)‖)) (𝓝[>] 0) (𝓝 A.condNumber) := by
  have hlim : ∀ c : ℝ, Tendsto (fun ε : ℝ => A.condNumber / (1 + c * (ε * A.condNumber)))
      (𝓝[>] 0) (𝓝 A.condNumber) := fun c => by
    have h : Tendsto (fun ε : ℝ => A.condNumber / (1 + c * (ε * A.condNumber))) (𝓝 0)
        (𝓝 (A.condNumber / (1 + c * (0 * A.condNumber)))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.mul
        (tendsto_id.mul tendsto_const_nhds))) (by simp)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε * A.condNumber < 1 := by
    have h2 : Tendsto (fun ε : ℝ => ε * A.condNumber) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_id.mul_const A.condNumber).mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    exact (eventually_mem_nhdsWithin.mono fun ε hε => hε).and
      (h2.eventually (gt_mem_nhds one_pos))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlim 1) (by
    simpa [sub_eq_add_neg] using hlim (-1)) (hev.mono fun ε h => ?_) (hev.mono fun ε h => ?_)
  · exact (A.iSup_norm_inverse_add_sub_div_mem h.1 h.2).1
  · exact (A.iSup_norm_inverse_add_sub_div_mem h.1 h.2).2

/-- **Kahan's distance-to-singularity formula** ([quarteroni2000numerical] Remark 3.1, (3.6);
[Kah66], [Gas83]): on a nontrivial finite-dimensional space, the least relative distance
`‖t‖ / ‖A‖` from an isomorphism `A` to a singular operator `A + t` is `1 / κ A`, in any operator
norm. The two halves are `NormedRing.norm_le_of_not_isUnit_add` and
`ContinuousLinearEquiv.exists_not_isUnit_add_norm_le`. -/
theorem ContinuousLinearEquiv.isLeast_dist_singular [FiniteDimensional 𝕜 E] [Nontrivial E]
    (A : E ≃L[𝕜] E) :
    IsLeast {r : ℝ | ∃ t : E →L[𝕜] E, ¬ IsUnit ((A : E →L[𝕜] E) + t) ∧
      ‖t‖ / ‖(A : E →L[𝕜] E)‖ = r} (1 / A.condNumber) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hA : 0 < ‖(A : E →L[𝕜] E)‖ := by
    obtain ⟨y, hy1, -⟩ := (A : E →L[𝕜] E).exists_norm_eq_one_and_norm_apply_eq
    have h1 := (A : E →L[𝕜] E).le_opNorm y
    have hAy : (A : E →L[𝕜] E) y ≠ 0 := fun h => by
      have hy0 : y = 0 := by simpa using congrArg A.symm h
      rw [hy0, norm_zero] at hy1
      exact zero_ne_one hy1
    rw [hy1, mul_one] at h1
    exact (norm_pos_iff.2 hAy).trans_le h1
  have hinv := A.ring_inverse_coe
  constructor
  · obtain ⟨t, ht, htn⟩ := A.exists_not_isUnit_add_norm_le
    refine ⟨t, ht, ?_⟩
    rw [htn, ContinuousLinearEquiv.condNumber, one_div, mul_inv, div_eq_mul_inv, mul_comm]
  · rintro r ⟨t, ht, rfl⟩
    have h := NormedRing.norm_le_of_not_isUnit_add (a := (A : E →L[𝕜] E)) ⟨A.toUnit, rfl⟩ ht
    rw [hinv] at h
    rw [ContinuousLinearEquiv.condNumber, one_div, mul_inv, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right h hA.le

end Distance

/-! ### The relative bounds of Theorem 3.3 -/

section Theorem33

open NormedRing

/-- **[quarteroni2000numerical] Theorem 3.3, (3.13)**: if `A x = b`, `(A + δA) y = b + δb` with
`‖δA‖ ≤ γ ‖A‖`, `‖δb‖ ≤ γ ‖b‖` and `γ κ(A) < 1`, then
`‖y - x‖ / ‖x‖ ≤ 2 γ κ(A) / (1 - γ κ(A))`. From `relative_error_le_condNumber`, since
`‖A⁻¹‖ ‖δA‖ ≤ γ κ(A)`. -/
theorem relative_error_le_of_norm_le_mul (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) {b Δb x y : E}
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb) {γ : ℝ}
    (hΔA : ‖ΔA‖ ≤ γ * ‖(A : E →L[𝕜] E)‖) (hΔb : ‖Δb‖ ≤ γ * ‖b‖)
    (hsmall : γ * condNumber (A : E →L[𝕜] E) < 1) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ 2 * γ / (1 - γ * condNumber (A : E →L[𝕜] E)) * condNumber (A : E →L[𝕜] E) := by
  have hκ := A.condNumber_eq
  set N := ‖(A : E →L[𝕜] E)‖ with hN
  set M := ‖(A.symm : E →L[𝕜] E)‖ with hM
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx]; simp)
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hAb : ‖b‖ ≤ N * ‖x‖ := by
    rw [← hx]
    simpa using (A : E →L[𝕜] E).le_opNorm x
  have hN0 : 0 < N := by nlinarith [norm_nonneg (A : E →L[𝕜] E), norm_nonneg x]
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMΔ : M * ‖ΔA‖ ≤ γ * (N * M) := by nlinarith
  rw [hκ] at hsmall ⊢
  have hsmall' : M * ‖ΔA‖ < 1 := hMΔ.trans_lt hsmall
  refine (relative_error_le_condNumber A ΔA hx hy hsmall' hx0 hb).trans ?_
  rw [hκ]
  have e1 : ‖ΔA‖ / N ≤ γ := (div_le_iff₀ hN0).2 hΔA
  have e2 : ‖Δb‖ / ‖b‖ ≤ γ := (div_le_iff₀ hbn).2 hΔb
  have h1 : ‖ΔA‖ / N + ‖Δb‖ / ‖b‖ ≤ 2 * γ := by linarith
  have hpos : 0 < 1 - M * ‖ΔA‖ := by linarith
  have hpos' : 0 < 1 - γ * (N * M) := by linarith
  calc N * M / (1 - M * ‖ΔA‖) * (‖ΔA‖ / N + ‖Δb‖ / ‖b‖)
      ≤ N * M / (1 - γ * (N * M)) * (2 * γ) :=
        mul_le_mul (div_le_div_of_nonneg_left (mul_nonneg hN0.le hM0) hpos' (by linarith)) h1
          (add_nonneg (div_nonneg (norm_nonneg _) hN0.le) (div_nonneg (norm_nonneg _) hbn.le))
          (div_nonneg (mul_nonneg hN0.le hM0) hpos'.le)
    _ = 2 * γ / (1 - γ * (N * M)) * (N * M) := by ring

/-- **[quarteroni2000numerical] Theorem 3.3, (3.12)**: under the same hypotheses,
`‖y‖ / ‖x‖ ≤ (1 + γ κ(A)) / (1 - γ κ(A))`, by the triangle inequality on (3.13). -/
theorem norm_add_div_le_of_norm_le_mul (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) {b Δb x y : E}
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb) {γ : ℝ}
    (hΔA : ‖ΔA‖ ≤ γ * ‖(A : E →L[𝕜] E)‖) (hΔb : ‖Δb‖ ≤ γ * ‖b‖)
    (hsmall : γ * condNumber (A : E →L[𝕜] E) < 1) (hb : b ≠ 0) :
    ‖y‖ / ‖x‖ ≤ (1 + γ * condNumber (A : E →L[𝕜] E)) / (1 - γ * condNumber (A : E →L[𝕜] E)) := by
  have h := relative_error_le_of_norm_le_mul A ΔA hx hy hΔA hΔb hsmall hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx]; simp)
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set k := condNumber (A : E →L[𝕜] E) with hk
  have hpos : 0 < 1 - γ * k := by linarith
  have hk0 : 0 ≤ k := condNumber_nonneg _
  have hy' : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
  rw [div_le_iff₀ hxn] at h ⊢
  calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := hy'
    _ ≤ 2 * γ / (1 - γ * k) * k * ‖x‖ + ‖x‖ := by linarith
    _ = (1 + γ * k) / (1 - γ * k) * ‖x‖ := by
        field_simp
        ring

end Theorem33

/-! ### Approximate inverses: Property 3.1 -/

section ApproxInverse

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

/-- **[quarteroni2000numerical] Property 3.1, the first bound**: if `R = A C - 1` has norm
less than one, then `‖A⁻¹‖ ≤ ‖C‖ / (1 - ‖R‖)`, since `A C = 1 + R` is a unit and `A⁻¹ = C (1 +
R)⁻¹`. Stated in a complete normed ring for a unit `a`. -/
theorem NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt {a c : R} (ha : IsUnit a)
    (hr : ‖a * c - 1‖ < 1) : ‖Ring.inverse a‖ ≤ ‖c‖ / (1 - ‖a * c - 1‖) := by
  have hr' : ‖-(a * c - 1)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(a * c - 1)) := isUnit_one_sub_of_norm_lt_one hr'
  have hac : 1 - -(a * c - 1) = a * c := by abel
  have hinv : Ring.inverse a = c * Ring.inverse (1 - -(a * c - 1)) := by
    calc Ring.inverse a
        = Ring.inverse a * ((1 - -(a * c - 1)) * Ring.inverse (1 - -(a * c - 1))) := by
          rw [Ring.mul_inverse_cancel _ hunit, mul_one]
      _ = c * Ring.inverse (1 - -(a * c - 1)) := by
          rw [hac, ← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ ha, one_mul]
  rw [hinv]
  calc ‖c * Ring.inverse (1 - -(a * c - 1))‖ ≤ ‖c‖ * ‖Ring.inverse (1 - -(a * c - 1))‖ :=
        _root_.norm_mul_le _ _
    _ ≤ ‖c‖ * (1 / (1 - ‖-(a * c - 1)‖)) :=
        mul_le_mul_of_nonneg_left (NormedRing.norm_inverse_one_sub_le hr') (norm_nonneg _)
    _ = ‖c‖ / (1 - ‖a * c - 1‖) := by rw [norm_neg]; ring

omit [NormOneClass R] in
/-- **[quarteroni2000numerical] Property 3.1, the upper bound of the second display**:
`‖C - A⁻¹‖ ≤ ‖C‖ ‖R‖ / (1 - ‖R‖)`, since `C - A⁻¹ = -C ((1 + R)⁻¹ - 1)`. -/
theorem NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt {a c : R} (ha : IsUnit a)
    (hr : ‖a * c - 1‖ < 1) :
    ‖c - Ring.inverse a‖ ≤ ‖c‖ * ‖a * c - 1‖ / (1 - ‖a * c - 1‖) := by
  have hr' : ‖-(a * c - 1)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(a * c - 1)) := isUnit_one_sub_of_norm_lt_one hr'
  have hac : 1 - -(a * c - 1) = a * c := by abel
  have hinv : Ring.inverse a = c * Ring.inverse (1 - -(a * c - 1)) := by
    calc Ring.inverse a
        = Ring.inverse a * ((1 - -(a * c - 1)) * Ring.inverse (1 - -(a * c - 1))) := by
          rw [Ring.mul_inverse_cancel _ hunit, mul_one]
      _ = c * Ring.inverse (1 - -(a * c - 1)) := by
          rw [hac, ← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ ha, one_mul]
  have hdiff : c - Ring.inverse a = -(c * (Ring.inverse (1 - -(a * c - 1)) - 1)) := by
    rw [hinv, mul_sub, mul_one]
    abel
  rw [hdiff, norm_neg]
  calc ‖c * (Ring.inverse (1 - -(a * c - 1)) - 1)‖
      ≤ ‖c‖ * ‖Ring.inverse (1 - -(a * c - 1)) - 1‖ := _root_.norm_mul_le _ _
    _ ≤ ‖c‖ * (‖-(a * c - 1)‖ / (1 - ‖-(a * c - 1)‖)) :=
        mul_le_mul_of_nonneg_left (NormedRing.norm_inverse_one_sub_sub_one_le hr') (norm_nonneg _)
    _ = ‖c‖ * ‖a * c - 1‖ / (1 - ‖a * c - 1‖) := by rw [norm_neg]; ring

omit [NormOneClass R] [CompleteSpace R] in
/-- **[quarteroni2000numerical] Property 3.1, the lower bound**: `‖A C - 1‖ / ‖A‖ ≤ ‖C - A⁻¹‖`
for a unit `A`, since `A C - 1 = A (C - A⁻¹)`. -/
theorem NormedRing.norm_mul_sub_one_div_norm_le_norm_sub_inverse {a c : R} (ha : IsUnit a) :
    ‖a * c - 1‖ / ‖a‖ ≤ ‖c - Ring.inverse a‖ := by
  have h : a * c - 1 = a * (c - Ring.inverse a) := by
    rw [mul_sub, Ring.mul_inverse_cancel _ ha]
  rcases eq_or_lt_of_le (norm_nonneg a) with h0 | h0
  · rw [← h0, div_zero]
    exact norm_nonneg _
  · rw [div_le_iff₀ h0, h, mul_comm]
    exact _root_.norm_mul_le _ _

omit [NormOneClass R] in
/-- **[quarteroni2000numerical] Property 3.1, "then `A` and `C` are nonsingular"**: in a
complete normed ring that is Dedekind-finite (`IsDedekindFiniteMonoid R`, which matrices over a
field satisfy), `‖A C - 1‖ < 1` makes `A C` a unit, hence `A` and `C`, a one-sided inverse being
two-sided. -/
theorem isUnit_of_norm_mul_sub_one_lt [IsDedekindFiniteMonoid R] {a c : R}
    (hr : ‖a * c - 1‖ < 1) : IsUnit a ∧ IsUnit c := by
  have hr' : ‖-(a * c - 1)‖ < 1 := by rwa [norm_neg]
  have hunit : IsUnit (1 - -(a * c - 1)) := isUnit_one_sub_of_norm_lt_one hr'
  have hac : 1 - -(a * c - 1) = a * c := by abel
  rw [hac] at hunit
  obtain ⟨u, hu⟩ := hunit
  have h1 : a * (c * ↑u⁻¹) = 1 := by rw [← mul_assoc, ← hu, Units.mul_inv]
  have h2 : (↑u⁻¹ * a) * c = 1 := by rw [mul_assoc, ← hu, Units.inv_mul]
  exact ⟨⟨⟨a, c * ↑u⁻¹, h1, mul_eq_one_symm h1⟩, rfl⟩, ⟨⟨c, ↑u⁻¹ * a, mul_eq_one_symm h2, h2⟩, rfl⟩⟩

omit [NormOneClass R] in
/-- **[quarteroni2000numerical] (3.19)**, the backward reading of Property 3.1 with the roles of
`A` and `C` exchanged: if `C` is a unit and `‖C A - 1‖ < 1`, the perturbation `δA = C⁻¹ - A` that
makes `C` an exact inverse satisfies `‖δA‖ ≤ ‖C A - 1‖ ‖A‖ / (1 - ‖C A - 1‖)`. The book writes the
residual as `A C - 1`; in a noncommutative ring `‖C A - 1‖` and `‖A C - 1‖` differ, and the proof
uses the former, which is the hypothesis taken here. -/
theorem NormedRing.norm_sub_le_of_norm_mul_sub_one_lt {a c : R} (hc : IsUnit c)
    (hr : ‖c * a - 1‖ < 1) :
    ‖Ring.inverse c - a‖ ≤ ‖c * a - 1‖ * ‖a‖ / (1 - ‖c * a - 1‖) := by
  rw [norm_sub_rev, mul_comm]
  exact NormedRing.norm_sub_inverse_le_of_norm_mul_sub_one_lt hc hr

end ApproxInverse

/-! ### A posteriori: the residual and an approximate inverse -/

section APosteriori

open NormedRing

/-- **[quarteroni2000numerical] (3.20)**: for an approximate inverse `C` of `A` with
`‖A C - 1‖ < 1`, the error of any approximate solution `y` of `A x = b` is bounded by its residual,
`‖y - x‖ ≤ ‖b - A y‖ ‖C‖ / (1 - ‖A C - 1‖)`, because `y - x = -A⁻¹ (b - A y)` and
`‖A⁻¹‖ ≤ ‖C‖ / (1 - ‖A C - 1‖)` (`NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt` in the ring
of operators). -/
theorem norm_error_le_of_norm_mul_sub_one_lt [CompleteSpace E] (A : E ≃L[𝕜] E) (C : E →L[𝕜] E)
    (hr : ‖(A : E →L[𝕜] E) * C - 1‖ < 1) {b x : E} (hx : A x = b) (y : E) :
    ‖y - x‖ ≤ ‖b - A y‖ * ‖C‖ / (1 - ‖(A : E →L[𝕜] E) * C - 1‖) := by
  have hpos : 0 < 1 - ‖(A : E →L[𝕜] E) * C - 1‖ := by linarith
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [Subsingleton.elim (y - x) 0, norm_zero]
    positivity
  have hyx : y - x = -((A.symm : E →L[𝕜] E) (b - A y)) := by
    rw [← hx]
    simp
  rw [hyx, norm_neg, div_eq_mul_inv, mul_assoc, mul_comm ‖C‖, ← div_eq_inv_mul, ← mul_div_assoc,
    mul_comm]
  calc ‖(A.symm : E →L[𝕜] E) (b - A y)‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖b - A y‖ := (A.symm : E →L[𝕜] E).le_opNorm _
    _ ≤ ‖C‖ / (1 - ‖(A : E →L[𝕜] E) * C - 1‖) * ‖b - A y‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h := NormedRing.norm_inverse_le_of_norm_mul_sub_one_lt (a := (A : E →L[𝕜] E))
          ⟨A.toUnit, rfl⟩ hr
        rwa [A.ring_inverse_coe] at h
    _ = ‖C‖ * ‖b - A y‖ / (1 - ‖(A : E →L[𝕜] E) * C - 1‖) := by ring

end APosteriori
