import Numlib.Optimization.HighOrder.Criticality
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gradient and curvature bounds from Taylor criticality

First-order criticality equals the radius times the gradient norm. A small quadratic
criticality measure bounds every Hessian quadratic form from below and bounds the gradient
using two explicit Cauchy displacements. No model optimizer or multiplier is assumed.
-/

namespace TaylorModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

omit [ProperSpace E] in
/-- The first-order Taylor decrement is the negative directional derivative. -/
theorem decrement_one (f : E → ℝ) (x s : E) :
    decrement f 1 x s = -inner ℝ (gradient f x) s := by
  rw [decrement_eq, eval_eq_sum]
  norm_num [Finset.sum_range_succ, smul_eq_mul, iteratedFDeriv_one_apply]

omit [CompleteSpace E] [ProperSpace E] in
/-- A nonzero vector has a unit opposite direction giving its negative norm as inner product. -/
theorem exists_unit_opposite (g : E) (hg : g ≠ 0) :
    ∃ u : E, ‖u‖ = 1 ∧ inner ℝ g u = -‖g‖ := by
  have hnorm : 0 < ‖g‖ := norm_pos_iff.mpr hg
  refine ⟨-(‖g‖⁻¹ • g), ?_, ?_⟩
  · rw [norm_neg, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le),
      inv_mul_cancel₀ hnorm.ne']
  · rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

/-- Exact first-order criticality on a positive-radius Euclidean ball. -/
theorem criticality_one (f : E → ℝ) (x : E) {δ : ℝ} (hδ : 0 < δ) :
    criticality f 1 x δ = δ * ‖gradient f x‖ := by
  apply le_antisymm
  · obtain ⟨s, hs, heq⟩ := exists_decrement_eq_criticality f 1 x hδ.le
    rw [← heq, decrement_one]
    calc -inner ℝ (gradient f x) s ≤ ‖gradient f x‖ * ‖s‖ :=
        (neg_le_abs (inner ℝ (gradient f x) s)).trans (abs_real_inner_le_norm _ _)
      _ ≤ ‖gradient f x‖ * δ := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = _ := mul_comm _ _
  · by_cases hg : gradient f x = 0
    · simpa [hg] using criticality_nonneg f 1 x hδ.le
    · obtain ⟨u, hu, hgu⟩ := exists_unit_opposite (gradient f x) hg
      have hs : ‖δ • u‖ ≤ δ := by simp [norm_smul, Real.norm_of_nonneg hδ.le, hu]
      have hd := decrement_le_criticality f 1 x hs
      rw [decrement_one, real_inner_smul_right, hgu] at hd
      nlinarith

omit [ProperSpace E] in
/-- The quadratic Taylor decrement on a scalar displacement. -/
theorem decrement_two_smul (f : E → ℝ) (x u : E) (t : ℝ) :
    decrement f 2 x (t • u) = -t * inner ℝ (gradient f x) u -
      t ^ 2 * iteratedFDeriv ℝ 2 f x (fun _ => u) / 2 := by
  have hmap := (iteratedFDeriv ℝ 2 f x).map_smul_univ (fun _ => t) (fun _ => u)
  have heval := eval_two f x (t • u)
  rw [iteratedFDeriv_one_apply] at heval
  simp only [map_smul, smul_eq_mul] at heval
  rw [show (fun _ : Fin 2 => t • u) = (fun i => t • (fun _ : Fin 2 => u) i) from rfl,
    hmap] at heval
  simp only [Fin.prod_const, smul_eq_mul] at heval
  rw [← inner_gradient_left] at heval
  rw [decrement_eq]
  linarith

/-- Every unit-direction Hessian curvature is at least `-ε` when quadratic criticality
is at most `ε δ²/2`. The proof compares the two feasible displacements `±δu`. -/
theorem unit_curvature_ge_neg (f : E → ℝ) (x : E) {δ ε : ℝ} (hδ : 0 < δ)
    (hcrit : criticality f 2 x δ ≤ ε * δ ^ 2 / 2) (u : E) (hu : ‖u‖ = 1) :
    -ε ≤ iteratedFDeriv ℝ 2 f x (fun _ => u) := by
  have hfeas (t : ℝ) (ht : |t| ≤ δ) : ‖t • u‖ ≤ δ := by
    simpa [norm_smul, Real.norm_eq_abs, hu] using ht
  have hp := (decrement_le_criticality f 2 x (hfeas δ (by simp [abs_of_pos hδ]))).trans hcrit
  have hm := (decrement_le_criticality f 2 x (hfeas (-δ) (by simp [abs_of_pos hδ]))).trans hcrit
  rw [decrement_two_smul] at hp hm
  have hsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hmul : (-ε) * δ ^ 2 ≤ iteratedFDeriv ℝ 2 f x (fun _ => u) * δ ^ 2 := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hsq).mp hmul

/-- The full homogeneous quadratic lower bound corresponding to `λ_min(H) ≥ -ε`. -/
theorem curvature_ge_neg_mul_sq (f : E → ℝ) (x : E) {δ ε : ℝ} (hδ : 0 < δ)
    (hcrit : criticality f 2 x δ ≤ ε * δ ^ 2 / 2) (v : E) :
    -ε * ‖v‖ ^ 2 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v) := by
  by_cases hv : v = 0
  · subst v
    have hz : iteratedFDeriv ℝ 2 f x (fun _ => (0 : E)) = 0 :=
      (iteratedFDeriv ℝ 2 f x).map_coord_zero 0 (by rfl)
    simp [hz]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le), hvpos.ne']
    have hc := unit_curvature_ge_neg f x hδ hcrit u hu
    have hmap := (iteratedFDeriv ℝ 2 f x).map_smul_univ (fun _ => ‖v‖⁻¹) (fun _ => v)
    have he : iteratedFDeriv ℝ 2 f x (fun _ => u) =
        (‖v‖⁻¹) ^ 2 * iteratedFDeriv ℝ 2 f x (fun _ => v) := by
      simpa [u, smul_eq_mul] using hmap
    rw [he] at hc
    have h := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖v‖)
    have hi : ‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2 = 1 := by field_simp
    calc -ε * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * iteratedFDeriv ℝ 2 f x (fun _ => v)) * ‖v‖ ^ 2 := h
      _ = iteratedFDeriv ℝ 2 f x (fun _ => v) := by rw [mul_right_comm, hi, one_mul]

/-- The Cauchy displacement gives a gradient bound with a constant depending only on
 the Hessian norm. Both displacements used below belong to the actual radius ball. -/
theorem gradient_norm_le_of_criticality_two (f : E → ℝ) (x : E) {δ ε : ℝ}
    (hδ : 0 < δ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hcrit : criticality f 2 x δ ≤ ε * δ ^ 2 / 2) :
    ‖gradient f x‖ ≤ δ * Real.sqrt (max 1 ‖iteratedFDeriv ℝ 2 f x‖) * Real.sqrt ε := by
  let G := ‖gradient f x‖
  let M := ‖iteratedFDeriv ℝ 2 f x‖
  let B := max 1 M
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := by linarith
  have hMB : M ≤ B := le_max_right _ _
  have hG : 0 ≤ G := norm_nonneg _
  by_cases hg : gradient f x = 0
  · simp only [hg, norm_zero]
    positivity
  obtain ⟨u, hu, hgu⟩ := exists_unit_opposite (gradient f x) hg
  have hcurv : iteratedFDeriv ℝ 2 f x (fun _ => u) ≤ B := by
    have hh := (iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ => u)
    simp only [hu, Fin.prod_const, one_pow, mul_one] at hh
    exact (le_abs_self _).trans (hh.trans hMB)
  have htrial (t : ℝ) (ht : 0 ≤ t) (htδ : t ≤ δ) :
      t * G - t ^ 2 * B / 2 ≤ ε * δ ^ 2 / 2 := by
    have hs : ‖t • u‖ ≤ δ := by
      simpa [norm_smul, Real.norm_of_nonneg ht, hu] using htδ
    have hd := (decrement_le_criticality f 2 x hs).trans hcrit
    rw [decrement_two_smul, hgu] at hd
    have hm := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    dsimp [G]
    nlinarith
  have hboundary := htrial δ hδ.le le_rfl
  have hGB : G ≤ δ * B := by
    have heB : ε ≤ B := hε1.trans hB1
    have hh := mul_le_mul_of_nonneg_right heB (sq_nonneg δ)
    have hx : δ * G ≤ δ * (δ * B) := by nlinarith
    exact (mul_le_mul_iff_of_pos_left hδ).mp hx
  have htδ : G / B ≤ δ := (div_le_iff₀ hB).mpr hGB
  have hsmall := htrial (G / B) (div_nonneg hG hB.le) htδ
  have hdiv : G / B * G - (G / B) ^ 2 * B / 2 = G ^ 2 / (2 * B) := by
    field_simp
    ring
  rw [hdiv] at hsmall
  have hGsq : G ^ 2 ≤ ε * δ ^ 2 * B := by
    have hh := (div_le_iff₀ (show 0 < 2 * B by positivity)).mp hsmall
    nlinarith
  have hsB : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
  have hse : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε0
  have hrhs : 0 ≤ δ * Real.sqrt B * Real.sqrt ε := by positivity
  have heq : (δ * Real.sqrt B * Real.sqrt ε) ^ 2 = ε * δ ^ 2 * B := by
    rw [mul_pow, mul_pow, hsB, hse]
    ring
  change G ≤ δ * Real.sqrt B * Real.sqrt ε
  nlinarith

/-- The genuine Riesz representative of the derivative of the gradient functional. -/
noncomputable def hessianOperator (f : E → ℝ) (x v : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x v)

omit [ProperSpace E] in
/-- The Riesz Hessian quadratic form equals the actual second derivative tensor. -/
theorem inner_hessianOperator (f : E → ℝ) (x v w : E) :
    inner ℝ (hessianOperator f x v) w =
      iteratedFDeriv ℝ 2 f x ![v, w] := by
  rw [hessianOperator, InnerProductSpace.toDual_symm_apply, iteratedFDeriv_two_apply]
  rfl

/-- The quadratic bound implies the lower bound for every genuine Hessian eigenvalue,
 hence in particular for the smallest eigenvalue in positive finite dimension. -/
theorem eigenvalue_ge_neg_of_criticality_two (f : E → ℝ) (x : E) {δ ε μ : ℝ}
    (hδ : 0 < δ) (hcrit : criticality f 2 x δ ≤ ε * δ ^ 2 / 2)
    (v : E) (hv : v ≠ 0) (heigen : hessianOperator f x v = μ • v) : -ε ≤ μ := by
  have hh := curvature_ge_neg_mul_sq f x hδ hcrit v
  have he : iteratedFDeriv ℝ 2 f x (fun _ => v) = μ * ‖v‖ ^ 2 := by
    have hh := inner_hessianOperator f x v v
    rw [heigen, real_inner_smul_left, real_inner_self_eq_norm_sq] at hh
    have hvv : (![v, v] : Fin 2 → E) = fun _ => v := by funext i; fin_cases i <;> rfl
    simpa [hvv] using hh.symm
  rw [he] at hh
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hv))).mp hh

end TaylorModel
