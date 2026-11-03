import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Nonlinear equations and nonlinear least squares -/

open scoped BigOperators

namespace ConnGouldToint.Chapter16

variable {E F ι : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The least-squares objective (16.1.4). -/
noncomputable def leastSquaresObjective (c : E → F) (x : E) : ℝ :=
  ‖c x‖ ^ 2 / 2

/-- The affine Gauss–Newton residual (16.1.6), in step coordinates. -/
def gaussNewtonResidual (c₀ : F) (A : E →L[ℝ] F) (s : E) : F :=
  c₀ + A s

private theorem norm_iteratedFDeriv_two_half_sq_le {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {x : E} {K : ℝ} (hK : 0 ≤ K)
    (h₀ : ‖u x‖ ≤ K) (h₁ : ‖fderiv ℝ u x‖ ≤ K)
    (h₂ : ‖iteratedFDeriv ℝ 2 u x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ u y ^ 2 / 2) x‖ ≤ 2 * K ^ 2 := by
  have h := norm_iteratedFDeriv_mul_le hu hu x (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one] at h
  norm_num at h
  change _ ≤ |u x| * ‖iteratedFDeriv ℝ 2 u x‖ +
    2 * ‖fderiv ℝ u x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
    ‖iteratedFDeriv ℝ 2 u x‖ * ‖iteratedFDeriv ℝ 0 u x‖ at h
  rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one, ← Real.norm_eq_abs] at h
  have hb : ‖iteratedFDeriv ℝ 2 (fun y ↦ u y * u y) x‖ ≤ 4 * K ^ 2 := by
    have h02 := mul_le_mul h₀ h₂ (norm_nonneg _) hK
    have h11 := mul_le_mul h₁ h₁ (norm_nonneg _) hK
    nlinarith
  have heq : (fun y ↦ u y ^ 2 / 2) = (1 / 2 : ℝ) • (fun y ↦ u y * u y) := by
    funext y
    simp [Pi.smul_apply, div_eq_mul_inv, pow_two, mul_comm]
  rw [heq, iteratedFDeriv_const_smul_apply (hu.mul hu).contDiffAt, norm_smul]
  norm_num [Real.norm_eq_abs]
  linarith

/-- Theorem 16.1.1. A twice continuously differentiable residual with uniformly bounded
values, Jacobian, and component Hessians yields a twice continuously differentiable,
bounded-below least-squares objective with uniformly bounded Hessian. -/
theorem theorem_16_1_1 [Fintype ι] {c : E → EuclideanSpace ℝ ι}
    (hc : ContDiff ℝ 2 c) {K : ℝ} (hK : 0 < K)
    (hval : ∀ x, ‖c x‖ ≤ K) (hjac : ∀ x, ‖fderiv ℝ c x‖ ≤ K)
    (hhess : ∀ i x, ‖iteratedFDeriv ℝ 2 (fun y ↦ c y i) x‖ ≤ K) :
    ContDiff ℝ 2 (leastSquaresObjective c) ∧
      (∀ x, 0 ≤ leastSquaresObjective c x) ∧
      ∃ C > 0, ∀ x, ‖iteratedFDeriv ℝ 2 (leastSquaresObjective c) x‖ ≤ C := by
  refine ⟨(hc.norm_sq ℝ).div_const 2, fun x ↦ by unfold leastSquaresObjective; positivity,
    2 * (Fintype.card ι : ℝ) * K ^ 2 + 1, by positivity, fun x ↦ ?_⟩
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj _ _ i
  have hp (i : ι) : ‖p i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [p] using PiLp.norm_apply_le z i
  have hci (i : ι) : ContDiff ℝ 2 (fun y ↦ c y i) :=
    (p i).contDiff.comp hc
  have hfi (i : ι) :
      fderiv ℝ (fun y ↦ c y i) x = (p i).comp (fderiv ℝ c x) :=
    ((p i).hasFDerivAt.comp x (hc.differentiable (by norm_num) x).hasFDerivAt).fderiv
  have hi (i : ι) : ‖fderiv ℝ (fun y ↦ c y i) x‖ ≤ K := by
    rw [hfi i]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _))).trans (by simpa using hjac x)
  have heq : leastSquaresObjective c = fun y ↦ ∑ i : ι, c y i ^ 2 / 2 := by
    funext y
    unfold leastSquaresObjective
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
    simp [Real.norm_eq_abs, sq_abs]
  rw [heq, iteratedFDeriv_fun_sum_apply fun i _ ↦ (((hci i).pow 2).div_const 2).contDiffAt]
  refine (norm_sum_le _ _).trans ?_
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) fun i _ ↦
    norm_iteratedFDeriv_two_half_sq_le (hci i) hK.le
      ((PiLp.norm_apply_le (c x) i).trans (hval x)) (hi i) (hhess i x)
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

end ConnGouldToint.Chapter16
