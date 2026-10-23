import Numlib.Optimization.Quadratic.Secular.Taylor
import Numlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Spectral moments and curvature inequalities

The actual generalized-eigenbasis coordinates give finite Cauchy–Schwarz bounds.
Distinct active eigenvalues characterize the strict estimate needed at the
exceptional transformed exponent minus one half.
-/

open scoped BigOperators Topology
open Filter
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The finite positive-power spectral moment with squared actual gradient coefficients. -/
noncomputable def moment (g : E) (a : ℕ) (z : ℝ) : ℝ :=
  ∑ i, (inner ℝ g (B.basis i)) ^ 2 / (z + B.eigenvalue i)^a

omit [Nonempty ι] in
/-- The second spectral moment is the squared metric resolvent norm. -/
theorem moment_two (g : E) (z : ℝ) : B.moment g 2 z = B.spectralSum g z := rfl

omit [Nonempty ι] in
/-- Cauchy-Schwarz bounds the squared third moment by the product of second and fourth
moments. -/
theorem cauchy_moments (g : E) (z : ℝ) :
    (B.moment g 3 z)^2 ≤ B.spectralSum g z * B.moment g 4 z := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => inner ℝ g (B.basis i) / (z + B.eigenvalue i))
    (fun i => inner ℝ g (B.basis i) / (z + B.eigenvalue i)^2)
  have h₃ : (∑ i, (inner ℝ g (B.basis i) / (z + B.eigenvalue i)) *
      (inner ℝ g (B.basis i) / (z + B.eigenvalue i)^2)) = B.moment g 3 z := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have h₂ : (∑ i, (inner ℝ g (B.basis i) / (z + B.eigenvalue i))^2) =
      B.spectralSum g z := by
    apply Finset.sum_congr rfl
    intro i _
    exact div_pow _ _ _
  have h₄ : (∑ i, (inner ℝ g (B.basis i) / (z + B.eigenvalue i)^2)^2) =
      B.moment g 4 z := by
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, ← pow_mul]
  rwa [h₃, h₂, h₄] at hh

omit [Nonempty ι] in
/-- Products of divided gradient coordinates sum to the moment at the sum of exponents. -/
theorem moment_add (g : E) (a b : ℕ) (z : ℝ) :
    (∑ i, (inner ℝ g (B.basis i) / (z + B.eigenvalue i)^a) *
      (inner ℝ g (B.basis i) / (z + B.eigenvalue i)^b)) = B.moment g (a + b) z := by
  apply Finset.sum_congr rfl
  intro i _
  rw [div_mul_div_comm, ← pow_add, ← sq]

/-- Two nonzero spectral components at distinct eigenvalues make the moment Cauchy-Schwarz
inequality strict. -/
theorem strict_cauchy_moments (g : E) {z : ℝ} (hz : B.edge < z)
    (hactive : ∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧
      inner ℝ g (B.basis j) ≠ 0 ∧ B.eigenvalue i ≠ B.eigenvalue j) :
    (B.moment g 3 z)^2 < B.spectralSum g z * B.moment g 4 z := by
  have hh := Finset.sum_mul_sq_lt_sq_mul_sq Finset.univ
    (fun i => inner ℝ g (B.basis i) / (z + B.eigenvalue i))
    (fun i => inner ℝ g (B.basis i) / (z + B.eigenvalue i)^2) (by
      obtain ⟨i,j,hi,hj,hij⟩ := hactive
      refine ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, ?_⟩
      intro heq
      have hdi := ne_of_gt (B.denominator_pos hz i)
      have hdj := ne_of_gt (B.denominator_pos hz j)
      have hi' : inner ℝ g (B.basis i) * inner ℝ g (B.basis j) ≠ 0 := mul_ne_zero hi hj
      have hc : (z + B.eigenvalue i) = z + B.eigenvalue j := by
        apply (mul_left_cancel₀ hi')
        field_simp [hdi,hdj] at heq
        rw [heq]
      exact hij (by linarith))
  have h₃ := B.moment_add g 1 2 z
  have h₂ := B.moment_add g 1 1 z
  have h₄ := B.moment_add g 2 2 z
  simp only [pow_one, ← sq, show 1 + 2=3 from rfl,
    show 1 + 1=2 from rfl, show 2 + 2=4 from rfl, moment_two] at h₂ h₃ h₄
  rwa [h₃,h₂,h₄] at hh

/-- A nonzero gradient gives a strictly positive secular value above the edge. -/
theorem spectralSum_pos {g : E} (hg : g ≠ 0) {z : ℝ} (hz : B.edge < z) :
    0 < B.spectralSum g z := by
  change 0 < ∑ i, (inner ℝ g (B.basis i))^2 / (z + B.eigenvalue i)^2
  exact B.positive_derivative_sum hg 0 hz

/-- The actual first spectral derivative equals minus twice the third moment. -/
theorem first_derivative_eq (g : E) {z : ℝ} (hz : B.edge < z) :
    deriv (B.spectralSum g) z = -2 * B.moment g 3 z := by
  simpa only [iteratedDeriv_one, moment, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, one_mul,
    mul_one, Nat.reduceAdd, pow_one, neg_one_mul] using
    B.spectralSum_deriv_formula g 1 hz

/-- The actual second spectral derivative equals six times the fourth moment. -/
theorem second_derivative_eq (g : E) {z : ℝ} (hz : B.edge < z) :
    iteratedDeriv 2 (B.spectralSum g) z = 6 * B.moment g 4 z := by
  have hh := B.spectralSum_deriv_formula g 2 hz
  norm_num only [show ((2 + 1).factorial : ℝ) = 6 from by norm_num,
    neg_one_sq, Nat.reduceAdd, one_mul] at hh
  exact hh

/-- The secular curvature satisfies three halves times the squared first derivative at most
the function times its second derivative. -/
theorem curvature_inequality (g : E) {z : ℝ} (hz : B.edge < z) :
    (3 / 2 : ℝ) * (deriv (B.spectralSum g) z)^2 ≤
      B.spectralSum g z * iteratedDeriv 2 (B.spectralSum g) z := by
  rw [B.first_derivative_eq g hz, B.second_derivative_eq g hz]
  nlinarith [B.cauchy_moments g z]

/-- Two distinct active eigenvalues make the secular curvature inequality strict. -/
theorem strict_curvature_inequality (g : E) {z : ℝ} (hz : B.edge < z)
    (hactive : ∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧
      inner ℝ g (B.basis j) ≠ 0 ∧ B.eigenvalue i ≠ B.eigenvalue j) :
    (3 / 2 : ℝ) * (deriv (B.spectralSum g) z)^2 <
      B.spectralSum g z * iteratedDeriv 2 (B.spectralSum g) z := by
  rw [B.first_derivative_eq g hz, B.second_derivative_eq g hz]
  nlinarith [B.strict_cauchy_moments g hz hactive]

/-- The real-power second-derivative bracket is nonnegative for exponents at least minus one
half. -/
theorem curvature_bracket_nonneg (g : E) {z β : ℝ} (hz : B.edge < z)
    (hβ : -(1 / 2 : ℝ) ≤ β) :
    0 ≤ (β - 1) * (deriv (B.spectralSum g) z)^2 +
      B.spectralSum g z * iteratedDeriv 2 (B.spectralSum g) z := by
  have hh := mul_nonneg (show 0 ≤ β + 1 / 2 by linarith)
    (sq_nonneg (deriv (B.spectralSum g) z))
  nlinarith [B.curvature_inequality g hz]

/-- A nonzero gradient makes the real-power curvature bracket positive for exponents strictly
greater than minus one half. -/
theorem curvature_bracket_pos {g : E} (hg : g ≠ 0) {z β : ℝ} (hz : B.edge < z)
    (hβ : -(1 / 2 : ℝ) < β) :
    0 < (β - 1) * (deriv (B.spectralSum g) z)^2 +
      B.spectralSum g z * iteratedDeriv 2 (B.spectralSum g) z := by
  have hder : deriv (B.spectralSum g) z < 0 := by
    simpa only [iteratedDeriv_one] using B.derivative_odd_neg hg (by decide : Odd 1) hz
  have hh := mul_pos (show 0 < β + 1 / 2 by linarith) (sq_pos_of_ne_zero hder.ne)
  nlinarith [B.curvature_inequality g hz]

end QuadraticSecular.PencilBasis
