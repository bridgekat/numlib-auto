import Numlib.Analysis.Calculus.BoundedJetInterpolation
import Mathlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Calculus.EuclideanOneHigherDeriv
import Numlib.Optimization.Newton

/-!
# A slow full-step Newton trajectory

Bounded scalar jets at integer knots produce globally bounded smooth objectives with uniform
Lipschitz constants. A constant positive Hessian at the knots makes Newton take unit steps,
while the gradient remains above the tolerance for an inverse-square number of iterations.
-/

noncomputable section
open scoped NNReal
namespace Optimization.NewtonLowerBound

/-- Length of the hard Newton trajectory. -/
def hardLength (ε : ℝ) : ℕ := ⌈(ε ^ 2)⁻¹⌉₊ + 1

/-- The objective, gradient and Hessian jets of the hard trajectory. -/
def hardJet (ε : ℝ) (N i j : ℕ) : ℝ :=
  if j = 0 then -(i : ℝ) * ε ^ 2 else
    if j = 1 then (if i < N then -2 * ε else 0) else
      if j = 2 then 2 * ε else 0

/-- The hard trajectory is longer than the inverse-square target. -/
theorem ceil_lt_hardLength (ε : ℝ) : ⌈(ε ^ 2)⁻¹⌉₊ < hardLength ε := by
  simp [hardLength]

/-- The hard trajectory spends a uniformly bounded amount of objective value. -/
theorem hardLength_mul_sq_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (hardLength ε : ℝ) * ε ^ 2 ≤ 3 := by
  have hs : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hi : 0 ≤ (ε ^ 2)⁻¹ := by positivity
  have hc : (⌈(ε ^ 2)⁻¹⌉₊ : ℝ) < (ε ^ 2)⁻¹ + 1 := Nat.ceil_lt_add_one hi
  have heq : (ε ^ 2)⁻¹ * ε ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt hs)
  have hsq : ε ^ 2 ≤ 1 := by nlinarith
  dsimp [hardLength]
  push_cast
  nlinarith [mul_lt_mul_of_pos_right hc hs]

/-- Every prescribed jet has a tolerance-independent bound. -/
theorem hardJet_abs_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (i : ℕ) (hi : i ≤ hardLength ε) (j : ℕ) : |hardJet ε (hardLength ε) i j| ≤ 3 := by
  have hv : (i : ℝ) * ε ^ 2 ≤ 3 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (sq_nonneg ε)).trans
      (hardLength_mul_sq_le hε hε1)
  simp only [hardJet]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg ε]

/-- A globally bounded twice continuously differentiable objective realizes the hard jets.
Both Lipschitz constants and the global objective bound are chosen before the tolerance. -/
theorem exists_scalar_hard_objective :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ LipschitzWith L (iteratedDeriv 2 f) ∧
        LipschitzWith B (deriv f) ∧
        (∀ t, |f t| ≤ B) ∧
        (∀ i ≤ hardLength ε, ∀ j ≤ 2,
          iteratedDeriv j f (i : ℝ) = hardJet ε (hardLength ε) i j) := by
  obtain ⟨L, B, h⟩ := Hermite.exists_contDiff_bounded_of_unit_knots 2 3 (by norm_num)
  refine ⟨L, B, ?_⟩
  intro ε hε hε1
  obtain ⟨f, hf, hLip, hjet, hb⟩ := h (hardLength ε) (by simp [hardLength])
    (hardJet ε (hardLength ε)) (fun i hi j _ => hardJet_abs_le hε hε1 i hi j)
  refine ⟨f, hf, hLip, ?_, ?_, hjet⟩
  · apply lipschitzWith_of_nnnorm_deriv_le
    · simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
    · intro t
      change ‖deriv (deriv f) t‖ ≤ (B : ℝ)
      simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero, Real.norm_eq_abs] using
        hb 2 (by omega) t
  · intro t
    simpa using hb 0 (by omega) t

/-- A bounded objective with uniformly Lipschitz gradient and Hessian forces genuine Newton
steps to exceed the inverse-square iteration count before their first stop.
The Hessian is positive definite at every visited knot and every step decreases the objective. -/
theorem exists_hard_run :
    ∃ Lg LH B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin 1))
        (N : ℕ),
        ContDiff ℝ 2 f ∧ LipschitzWith Lg (gradient f) ∧
        LipschitzWith LH (iteratedFDeriv ℝ 2 f) ∧
        (∀ u, |f u| ≤ B) ∧ x 0 = 0 ∧ Newton.IsRun f ε x s N ∧
        (∀ k ≤ N, ∀ u ≠ 0, 0 < fderiv ℝ (fderiv ℝ f) (x k) u u) ∧
        (∀ k < N, f (x k) - f (x (k + 1)) = ε ^ 2) ∧
        ⌈(ε ^ 2)⁻¹⌉₊ < N := by
  obtain ⟨LH, B, h⟩ := exists_scalar_hard_objective
  refine ⟨B, LH, B, ?_⟩
  intro ε hε hε1
  obtain ⟨f, hf, hLH, hLg, hb, hjet⟩ := h ε hε hε1
  let N := hardLength ε
  let x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => EuclideanOne.coord.symm (k : ℝ)
  let s : ℕ → EuclideanSpace ℝ (Fin 1) := fun _ => EuclideanOne.coord.symm 1
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have hg (k : ℕ) (hk : k ≤ N) : deriv f (k : ℝ) = hardJet ε N k 1 := by
    simpa only [iteratedDeriv_one] using hjet k hk 1 (by norm_num)
  have hH (k : ℕ) (hk : k ≤ N) (u v : EuclideanSpace ℝ (Fin 1)) :
      fderiv ℝ (fderiv ℝ (EuclideanOne.lift f)) (x k) u v =
        (2 * ε) * EuclideanOne.coord u * EuclideanOne.coord v := by
    have hj : deriv (deriv f) (k : ℝ) = 2 * ε := by
      simpa [iteratedDeriv_succ, iteratedDeriv_zero, hardJet] using hjet k hk 2 (by norm_num)
    apply EuclideanOne.fderiv_fderiv_apply hd
    simpa [x, hj] using (hd' (k : ℝ)).hasDerivAt
  have hn (k : ℕ) : ‖gradient (EuclideanOne.lift f) (x k)‖ = |deriv f (k : ℝ)| := by
    rw [EuclideanOne.gradient_eq_deriv hd]
    simp [x, Real.norm_eq_abs]
  refine ⟨EuclideanOne.lift f, x, s, N, EuclideanOne.contDiff hf,
    EuclideanOne.gradient_lipschitz hd hLg, EuclideanOne.iteratedFDeriv_lipschitz hf hLH,
    (fun u => hb _), ?_, ?_, ?_, ?_, ceil_lt_hardLength ε⟩
  · simp [x]
  · constructor
    · intro k hk
      rw [hn, hg k hk.le]
      simp only [hardJet, one_ne_zero, reduceIte, hk]
      rw [abs_of_nonpos (by linarith : -2 * ε ≤ 0)]
      linarith
    · rw [hn, hg N le_rfl]
      simp [hardJet, hε.le]
    · intro k hk u
      rw [hH k hk.le, EuclideanOne.fderiv_eq hd]
      simp [s, x, hg k hk.le, hardJet, hk]
    · intro k _
      apply EuclideanOne.coord.injective
      simp [x, s, Nat.cast_add, Nat.cast_one]
  · intro k hk u hu
    rw [hH k hk]
    have hcoord : EuclideanOne.coord u ≠ 0 := by
      intro hz
      apply hu
      exact EuclideanOne.coord.injective (by simpa using hz)
    nlinarith [sq_pos_of_ne_zero hcoord]
  · intro k hk
    have h0 := hjet k hk.le 0 (by norm_num)
    have h1 := hjet (k + 1) (by omega) 0 (by norm_num)
    simp only [iteratedDeriv_zero, hardJet, reduceIte] at h0 h1
    simp only [EuclideanOne.lift_apply, x, EuclideanOne.coord.apply_symm_apply]
    rw [h0, h1]
    push_cast
    ring

end Optimization.NewtonLowerBound
