import Numlib.Analysis.Calculus.SymmetricDerivativeNorm
import Numlib.Optimization.HigherOrderRegularization

/-!
# Operator-norm consequences of diagonal derivative control

For scalar objectives on finite-dimensional real inner product spaces, symmetry converts
homogeneous diagonal Lipschitz control into full operator-norm control. This supplies sharp
factorial-normalized remainder estimates for every derivative order of the Taylor model.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderRegularization

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {degree j : ℕ} {f : E → ℝ} {L : ℝ}

/-- Symmetric scalar derivative tensors turn diagonal Lipschitz bounds into operator bounds. -/
theorem DiagonalLipschitz.operator_bound (hf : DiagonalLipschitz f degree L)
    (hp : 1 ≤ degree) (x y : E) :
    ‖iteratedFDeriv ℝ degree f x - iteratedFDeriv ℝ degree f y‖ ≤ L * ‖x - y‖ := by
  rw [← diagonalNorm_iteratedFDeriv_sub_eq_norm hf.smooth.contDiffAt hf.smooth.contDiffAt
    (by omega : 0 < degree)]
  exact ((iteratedFDeriv ℝ degree f x - iteratedFDeriv ℝ degree f y).diagonalNorm_le_iff
    (by omega) (mul_nonneg hf.nonneg (norm_nonneg _))).mpr (hf.bound x y)

/-- Every actual derivative of the Taylor polynomial has the sharp Lipschitz remainder. -/
theorem DiagonalLipschitz.derivative_remainder (hf : DiagonalLipschitz f degree L)
    (hp : 1 ≤ degree) (hj : j ≤ degree) (x s : E) :
    ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (RegularizedTaylorModel.taylorModel f degree x) s‖ ≤
      L / ((degree - j + 1)! : ℝ) * ‖s‖ ^ (degree - j + 1) := by
  have h := norm_iteratedFDeriv_sub_taylorModel_le_holder
    (f := f) (p := degree) (j := j) (x := x) (s := s) (H := L) (β := 1)
    hj (by norm_num) (fun _ _ => hf.smooth.contDiffAt)
    (fun t _ => by
      simpa only [add_sub_cancel_left, Real.rpow_one] using
        hf.operator_bound hp (x + t • s) x)
  have hprod : ∀ k : ℕ, (∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1)) =
      ((k + 1)! : ℝ) := by
    intro k
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_ascFactorial 1 k)
    norm_num [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, Nat.cast_one,
      add_comm, add_left_comm, add_assoc] at hh ⊢
    exact hh
  rw [hprod, ← Nat.cast_add_one, Real.rpow_natCast] at h
  exact h

end Optimization.HigherOrderRegularization
