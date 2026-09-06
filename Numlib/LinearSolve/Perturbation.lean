import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Normed.Ring.Inverse

/-!
# Perturbation theory for linear systems

Normwise error bounds for `A x = b` in terms of the condition number `κ(A) = ‖A‖ ‖A⁻¹‖`
([saad2003iterative] §1.13.2 (1.76), [han2009theoretical] (2.4.1), [kress1998numerical] Thm 5.3,
[higham2002accuracy] Thm 7.2), the residual–error relation, and the Rigal–Gaches formula for the
normwise backward error ([higham2002accuracy] Thm 7.1, [fong2012cg] (3.2)–(3.3)).  The normwise
backward error of an approximate solution `y`, relative to tolerances `α` on `A` and `β` on `b`, is
the least `ξ` for which `y` solves exactly some system `(A + ΔA) y = b + Δb` with `‖ΔA‖ ≤ ξ α ‖A‖`
and `‖Δb‖ ≤ ξ β ‖b‖`; the Rigal–Gaches theorem evaluates it in closed form as `‖b - A y‖ / (α ‖A‖
‖y‖ + β ‖b‖)`.
-/

open NormedRing

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

/-- Normwise perturbation bound ([saad2003iterative], (1.76); [kress1998numerical], Thm 5.3;
[higham2002accuracy], *Accuracy and Stability*, Thm 7.2): if `A x = b`, `(A + ΔA) y = b + Δb` and
`‖A⁻¹‖ ‖ΔA‖ < 1` then `‖y - x‖/‖x‖ ≤ κ(A)/(1 - ‖A⁻¹‖‖ΔA‖) (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)`. -/
theorem relative_error_le_condNumber [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
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
  have hkey : (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖) * ‖y - x‖
      ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ + ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖x‖ := by
    nlinarith [h1, h3]
  have hlast : ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖
      ≤ ‖(A : E →L[𝕜] E)‖ * ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ * ‖x‖ / ‖b‖ := by
    rw [le_div_iff₀ hbn]
    nlinarith [mul_nonneg (norm_nonneg (A.symm : E →L[𝕜] E)) (norm_nonneg Δb)]
  rw [ContinuousLinearEquiv.condNumber_eq, div_le_iff₀ hxn]
  have hexp : ‖(A : E →L[𝕜] E)‖ * ‖(A.symm : E →L[𝕜] E)‖ /
        (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖) *
        (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖) * ‖x‖
      = (‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ * ‖x‖ +
          ‖(A : E →L[𝕜] E)‖ * ‖(A.symm : E →L[𝕜] E)‖ * ‖Δb‖ * ‖x‖ / ‖b‖) /
        (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖) := by
    field_simp
  rw [hexp, le_div_iff₀ hden]
  nlinarith

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
