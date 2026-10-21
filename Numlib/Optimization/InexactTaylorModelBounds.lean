import Numlib.Optimization.InexactTaylorModelDerivatives
import Numlib.Optimization.TaylorModelGrowth
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Geometry of supplied regularization models

Arbitrary finite tensor polynomials with positive radial regularization attain their global
minimum. The polynomial and radial derivative terms share a single factorial tail, giving
a common norm bound through the maximum of their coefficient bounds.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.InexactTaylorModels

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The regularized supplied polynomial is smooth through its polynomial degree. -/
theorem contDiff_regularizedPolynomial (c : ℝ) (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (σ : ℝ) : ContDiff ℝ p (regularizedPolynomial c A p σ) := by
  have hn : ContDiff ℝ p (fun z : E => ‖z‖ ^ (p + 1)) := by
    simpa only [Real.rpow_natCast] using contDiff_norm_rpow_of_lt (E := E)
      (n := p) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.lt_succ_self p)
  exact (contDiff_polynomial c A p p).add ((contDiff_const.mul hn).div_const _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The supplied finite polynomial has polynomial growth, without any relation between
its tensors and the derivatives of another objective. -/
theorem abs_polynomial_le_coefficient_sum [NormedSpace ℝ E] (c : ℝ) (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (s : E) (hs : 1 ≤ ‖s‖) :
    |polynomial c A p s| ≤
      (|c| + ∑ i ∈ Finset.Icc 1 p, ‖A i‖ / (i ! : ℝ)) * ‖s‖ ^ p := by
  unfold polynomial
  apply (abs_add_le _ _).trans
  have hc : |c| ≤ |c| * ‖s‖ ^ p := le_mul_of_one_le_right (abs_nonneg c) (one_le_pow₀ hs)
  rw [add_mul, Finset.sum_mul]
  apply add_le_add hc
  rw [← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have ht := (A i).le_opNorm (fun _ => s)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at ht
  rw [norm_div, Real.norm_natCast]
  calc
    _ ≤ ‖A i‖ * ‖s‖ ^ i / (i ! : ℝ) :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ ≤ ‖A i‖ * ‖s‖ ^ p / (i ! : ℝ) := by
      gcongr
      exact (Finset.mem_Icc.mp hi).2
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Positive radial regularization dominates every fixed finite supplied polynomial. -/
theorem regularizedPolynomial_eventually_ge [NormedSpace ℝ E] (c : ℝ) (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) {σ : ℝ} (hσ : 0 < σ) (b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s : E, R ≤ ‖s‖ → b ≤ regularizedPolynomial c A p σ s := by
  obtain ⟨R, hR, hb⟩ := RegularizedTaylorModel.eventually_ge_regularized_of_lower_bound
    (a := σ / ((p + 1)! : ℝ)) p (div_pos hσ (by positivity))
    (fun s hs => (abs_le.mp (abs_polynomial_le_coefficient_sum c A p s hs)).1) b
  exact ⟨R, hR, fun s hs => by simpa only [regularizedPolynomial, div_mul_eq_mul_div] using hb s hs⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every sublevel of a positively regularized supplied polynomial is compact. -/
theorem isCompact_regularizedPolynomial_sublevel [NormedSpace ℝ E] [ProperSpace E]
    (c : ℝ)
    (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 < σ) (b : ℝ) :
    IsCompact {s | regularizedPolynomial c A p σ s ≤ b} := by
  apply isCompact_of_isClosed_isBounded
    (isClosed_le ((contDiff_polynomial c A p 0).continuous.add
      ((continuous_const.mul (continuous_norm.pow _)).div_const _)) continuous_const)
  obtain ⟨R, hR, hb⟩ := regularizedPolynomial_eventually_ge c A p hσ (b + 1)
  apply (isBounded_closedBall (x := (0 : E)) (r := R)).subset
  intro s hs
  have hn : ‖s‖ ≤ R := by
    by_contra hn
    have := hb s (le_of_lt (lt_of_not_ge hn))
    change regularizedPolynomial c A p σ s ≤ b at hs
    linarith
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Positive regularization makes the actual supplied model attain its global minimum. -/
theorem exists_regularizedPolynomial_minimizer [NormedSpace ℝ E] [ProperSpace E]
    (c : ℝ)
    (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : E, ∀ t : E, regularizedPolynomial c A p σ s ≤ regularizedPolynomial c A p σ t := by
  let m := regularizedPolynomial c A p σ
  have hc := isCompact_regularizedPolynomial_sublevel c A p hσ (m 0)
  obtain ⟨s, hs, hmin⟩ := hc.exists_isMinOn (f := m) ⟨0, (show m 0 ≤ m 0 from le_rfl)⟩
    ((contDiff_polynomial c A p 0).continuous.add
      ((continuous_const.mul (continuous_norm.pow _)).div_const _)).continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases ht : m t ≤ m 0
  · exact hmin ht
  · exact hs.trans (le_of_not_ge ht)

/-- A supplied regularized polynomial has top derivative Lipschitz constant equal to its
regularization parameter, independently of symmetry of its coefficient tensors. -/
theorem diagonalLipschitz_regularizedPolynomial (c : ℝ)
    (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (p : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    HigherOrderRegularization.DiagonalLipschitz (regularizedPolynomial c A p σ) p σ := by
  have hn : ContDiff ℝ p (fun z : E => ‖z‖ ^ (p + 1)) := by
    simpa only [Real.rpow_natCast] using contDiff_norm_rpow_of_lt (E := E)
      (n := p) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.lt_succ_self p)
  apply HigherOrderRegularization.DiagonalLipschitz.of_operator
  · exact (contDiff_polynomial c A p p).add ((contDiff_const.mul hn).div_const _)
  · exact hσ
  · intro s t
    rw [iteratedFDeriv_regularizedPolynomial_of_le le_rfl,
      iteratedFDeriv_regularizedPolynomial_of_le le_rfl,
      iteratedFDeriv_polynomial_top_eq c A p s t, add_sub_add_left_eq_sub,
      ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hσ (by positivity))]
    calc
      _ ≤ (σ / ((p + 1)! : ℝ)) * (((p + 1)! : ℝ) * ‖s - t‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_iteratedFDeriv_norm_pow_le p s t)
          (div_nonneg hσ (by positivity))
      _ = _ := by field_simp

/-- The polynomial tail and radial term together have weight at most three on the unit
ball. Their common coefficient bound therefore occurs once, through `max L σ`. -/
theorem norm_iteratedFDeriv_regularizedPolynomial_le_three_max {j p : ℕ}
    (hj : 1 ≤ j) (hjp : j ≤ p) (c : ℝ) (A : ∀ i : ℕ,
      ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hA : ∀ i ∈ Finset.Icc j p, ‖A i‖ ≤ L) (s : E) (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (regularizedPolynomial c A p σ) s‖ ≤ 3 * max L σ := by
  let M := max L σ
  have hM : 0 ≤ M := hL.trans (le_max_left _ _)
  have hp : ‖iteratedFDeriv ℝ j (polynomial c A p) s‖ ≤
      ∑ i ∈ Finset.Icc 1 p, if j ≤ i then M / ((i - j)! : ℝ) else 0 := by
    apply (norm_iteratedFDeriv_polynomial_le hj c A p s).trans
    apply Finset.sum_le_sum
    intro i hi
    split_ifs with hji
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        ((hA i (Finset.mem_Icc.mpr ⟨hji, (Finset.mem_Icc.mp hi).2⟩)).trans
          (le_max_left _ _)) (pow_nonneg (norm_nonneg s) _)).trans
        (mul_le_of_le_one_right hM (pow_le_one₀ (norm_nonneg s) hs))
    · exact le_rfl
  have hr : ‖(σ / ((p + 1)! : ℝ)) •
      iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s‖ ≤
      M / ((p + 1 - j)! : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hσ (by positivity))]
    calc
      _ ≤ (σ / ((p + 1)! : ℝ)) *
          ((Nat.descFactorial (p + 1) j : ℝ) * ‖s‖ ^ (p + 1 - j)) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_norm_pow_le_of_le hjp s)
          (div_nonneg hσ (by positivity))
      _ ≤ (M / ((p + 1)! : ℝ)) * (Nat.descFactorial (p + 1) j : ℝ) := by
        have hpow := pow_le_one₀ (norm_nonneg s) hs (n := p + 1 - j)
        have hsm : σ ≤ M := le_max_right _ _
        gcongr
        exact mul_le_of_le_one_right (by positivity) hpow
      _ = M / ((p + 1 - j)! : ℝ) := by
        have hf : ((p + 1 - j)! : ℝ) * (Nat.descFactorial (p + 1) j : ℝ) =
            ((p + 1)! : ℝ) := by
          exact_mod_cast Nat.factorial_mul_descFactorial (by omega : j ≤ p + 1)
        have hf0 : ((p + 1)! : ℝ) ≠ 0 := by positivity
        have hg0 : ((p + 1 - j)! : ℝ) ≠ 0 := by positivity
        field_simp
        rw [← hf]
        ring
  rw [iteratedFDeriv_regularizedPolynomial_of_le hjp]
  apply (norm_add_le _ _).trans
  have hb := add_le_add hp hr
  have he : (∑ i ∈ Finset.Icc 1 p, if j ≤ i then M / ((i - j)! : ℝ) else 0) +
      M / ((p + 1 - j)! : ℝ) =
      ∑ i ∈ Finset.Icc 1 (p + 1), if j ≤ i then M / ((i - j)! : ℝ) else 0 := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ p + 1)]
    simp only [ite_eq_left (show j ≤ p + 1 by omega)]
  rw [he] at hb
  exact hb.trans (factorial_tail_sum_le_three hj (by omega) hM)

end Optimization.InexactTaylorModels
