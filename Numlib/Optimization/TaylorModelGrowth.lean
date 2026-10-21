import Numlib.Optimization.RegularizedTaylorModel
import Mathlib.Tactic

/-!
# Polynomial growth of vector Taylor models

The sum of the norms of the factorially scaled coefficients bounds a Taylor polynomial
by a power of the step norm outside the unit ball, independently of its codomain.
-/

noncomputable section
open scoped Nat
namespace Optimization.RegularizedTaylorModel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Sum of the norms of the actual factorially scaled Taylor coefficients. -/
def normCoefficientBound (f : E → F) (p : ℕ) (x : E) : ℝ :=
  ∑ j ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ j f x‖ / (j ! : ℝ)

/-- Outside the unit ball, the highest scalar power dominates every Taylor coefficient. -/
theorem norm_taylorModel_le (f : E → F) (p : ℕ) (x s : E) (hs : 1 ≤ ‖s‖) :
    ‖taylorModel f p x s‖ ≤ normCoefficientBound f p x * ‖s‖ ^ p := by
  unfold taylorModel normCoefficientBound
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (j ! : ℝ))]
  have hA := (iteratedFDeriv ℝ j f x).le_opNorm (fun _ => s)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hA
  have hpow : ‖s‖ ^ j ≤ ‖s‖ ^ p :=
    pow_le_pow_right₀ hs (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc
    _ ≤ (j ! : ℝ)⁻¹ * (‖iteratedFDeriv ℝ j f x‖ * ‖s‖ ^ j) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ (j ! : ℝ)⁻¹ * (‖iteratedFDeriv ℝ j f x‖ * ‖s‖ ^ p) := by gcongr
    _ = _ := by ring

omit [NormedSpace ℝ E] in
/-- A positive radial term of one higher degree dominates any function with a polynomial
lower growth bound outside the unit ball. The threshold is constructed from that bound. -/
theorem eventually_ge_regularized_of_lower_bound {w : E → ℝ} (p : ℕ) {a C : ℝ}
    (ha : 0 < a) (hw : ∀ s : E, 1 ≤ ‖s‖ → -(C * ‖s‖ ^ p) ≤ w s) (b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s : E, R ≤ ‖s‖ → b ≤ w s + a * ‖s‖ ^ (p + 1) := by
  refine ⟨max 1 ((C + |b|) / a), (le_max_left _ _).trans' (by norm_num), ?_⟩
  intro s hs
  have hs1 : 1 ≤ ‖s‖ := (le_max_left _ _).trans hs
  have hsn : (C + |b|) / a ≤ ‖s‖ := (le_max_right _ _).trans hs
  have hmul : C + |b| ≤ a * ‖s‖ := by
    have := (div_le_iff₀ ha).mp hsn
    nlinarith
  have hpow : 1 ≤ ‖s‖ ^ p := one_le_pow₀ hs1
  have ht := hw s hs1
  have hab : |b| ≤ |b| * ‖s‖ ^ p := by nlinarith [abs_nonneg b]
  rw [pow_succ]
  nlinarith [le_abs_self b, mul_nonneg (by linarith : 0 ≤ a * ‖s‖ - C - |b|)
    (pow_nonneg (norm_nonneg s) p)]

end Optimization.RegularizedTaylorModel
