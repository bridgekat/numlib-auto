import Numlib.Optimization.Quadratic.Secular.Moments
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real powers of actual secular functions

First and second derivatives follow the real-power chain rule and the sharp
spectral curvature inequality. The inverse-defined transform is matched to
its spectral expression locally, so every derivative concerns the actual map.
A zero gradient and the potentially affine exponent minus one half are explicit.
-/

open scoped BigOperators Topology
open Filter
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The actual derivative of a positive-base transformed spectral function follows the real-
power chain rule. -/
theorem transformed_hasDerivAt {g : E} (hg : g ≠ 0) (β : ℝ) {z : ℝ}
    (hz : B.edge < z) :
    HasDerivAt (fun y => (B.spectralSum g y)^β)
      (β * (B.spectralSum g z)^(β - 1) * deriv (B.spectralSum g) z) z := by
  convert ((B.contDiffAt_spectralSum g 1 hz).differentiableAt_one.hasDerivAt.rpow_const
    (p := β) (Or.inl (B.spectralSum_pos hg hz).ne')) using 1; ring

/-- Compute the true second derivative of every real power of the nonzero spectral function. -/
theorem transformed_second {g : E} (hg : g ≠ 0) (β : ℝ) {z : ℝ}
    (hz : B.edge < z) :
    iteratedDeriv 2 (fun y => (B.spectralSum g y)^β) z =
      β * (B.spectralSum g z)^(β - 2) *
        ((β - 1) * (deriv (B.spectralSum g) z)^2 +
          B.spectralSum g z * iteratedDeriv 2 (B.spectralSum g) z) := by
  let π := B.spectralSum g
  have hp : 0 < π z := B.spectralSum_pos hg hz
  have hπ : HasDerivAt π (deriv π z) z :=
    (B.contDiffAt_spectralSum g 1 hz).differentiableAt_one.hasDerivAt
  have hπ' : HasDerivAt (deriv π) (iteratedDeriv 2 π z) z := by
    have hh := (B.contDiffAt_spectralSum g 2 hz).derivWithin (m := 1) (by norm_num)
    simpa only [π, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      hh.differentiableAt_one.hasDerivAt
  have hevent : deriv (fun y => (π y)^β) =ᶠ[𝓝 z]
      (fun y => β * (π y)^(β - 1) * deriv π y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact (B.transformed_hasDerivAt hg β hy).deriv
  have hw := ((hπ.rpow_const (p := β - 1) (Or.inl hp.ne')).const_mul β).mul hπ'
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  change deriv (deriv (fun y => (π y)^β)) z = _
  rw [hevent.deriv_eq]
  have hw' : HasDerivAt (fun y => β * (π y)^(β - 1) * deriv π y)
      (β * (deriv π z * (β - 1) * (π z)^(β - 1 - 1)) * deriv π z +
        β * (π z)^(β - 1) * iteratedDeriv 2 π z) z := by
    convert! hw using 1
  rw [hw'.deriv]
  have hp1 : (π z)^(β - 1) = (π z)^(β - 2) * π z := by
    have hh := Real.rpow_add hp (β - 2) 1
    rw [Real.rpow_one] at hh
    convert hh using 1; congr 1; ring
  have hp2 : (π z)^(β - 1 - 1) = (π z)^(β - 2) := by congr 1; ring
  change β * (deriv π z * (β - 1) * (π z)^(β - 1 - 1)) * deriv π z +
    β * (π z)^(β - 1) * iteratedDeriv 2 π z = _
  rw [hp1,hp2]
  dsimp [π]
  ring

/-- The first derivative of every positive real power of a nonzero spectral function is
negative. -/
theorem transformed_first_pos_exponent {g : E} (hg : g ≠ 0) {β z : ℝ}
    (hβ : 0 < β) (hz : B.edge < z) :
    deriv (fun y => (B.spectralSum g y)^β) z < 0 := by
  rw [(B.transformed_hasDerivAt hg β hz).deriv]
  apply mul_neg_of_pos_of_neg
  · exact mul_pos hβ (Real.rpow_pos_of_pos (B.spectralSum_pos hg hz) _)
  · simpa only [iteratedDeriv_one] using B.derivative_odd_neg hg (by decide : Odd 1) hz

/-- The first derivative of every negative real power of a nonzero spectral function is
positive. -/
theorem transformed_first_neg_exponent {g : E} (hg : g ≠ 0) {β z : ℝ}
    (hβ : β < 0) (hz : B.edge < z) :
    0 < deriv (fun y => (B.spectralSum g y)^β) z := by
  rw [(B.transformed_hasDerivAt hg β hz).deriv]
  apply mul_pos_of_neg_of_neg
  · exact mul_neg_of_neg_of_pos hβ (Real.rpow_pos_of_pos (B.spectralSum_pos hg hz) _)
  · simpa only [iteratedDeriv_one] using B.derivative_odd_neg hg (by decide : Odd 1) hz

/-- Every positive power of a nonzero spectral function has positive second derivative. -/
theorem transformed_second_pos_exponent {g : E} (hg : g ≠ 0) {β z : ℝ}
    (hβ : 0 < β) (hz : B.edge < z) :
    0 < iteratedDeriv 2 (fun y => (B.spectralSum g y)^β) z := by
  rw [B.transformed_second hg β hz]
  exact mul_pos (mul_pos hβ (Real.rpow_pos_of_pos (B.spectralSum_pos hg hz) _))
    (B.curvature_bracket_pos hg hz (by linarith))

/-- For exponents from minus one half to zero the second derivative is nonpositive. -/
theorem transformed_second_neg_exponent {g : E} (hg : g ≠ 0) {β z : ℝ}
    (hβ : β < 0) (hβlow : -(1 / 2 : ℝ) ≤ β) (hz : B.edge < z) :
    iteratedDeriv 2 (fun y => (B.spectralSum g y)^β) z ≤ 0 := by
  rw [B.transformed_second hg β hz]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hβ.le (Real.rpow_nonneg (B.spectralSum_nonneg g z) _))
    (B.curvature_bracket_nonneg g hz hβlow)

/-- For exponents strictly between minus one half and zero the second derivative is negative. -/
theorem transformed_second_neg_strict {g : E} (hg : g ≠ 0) {β z : ℝ}
    (hβ : β < 0) (hβlow : -(1 / 2 : ℝ) < β) (hz : B.edge < z) :
    iteratedDeriv 2 (fun y => (B.spectralSum g y)^β) z < 0 := by
  rw [B.transformed_second hg β hz]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hβ (Real.rpow_pos_of_pos (B.spectralSum_pos hg hz) _))
    (B.curvature_bracket_pos hg hz hβlow)

/-- Two distinct active eigenvalues imply negative transformed second derivative including the
exponent minus one half. -/
theorem transformed_second_neg_strict_of_active {g : E} (hg : g ≠ 0) {β z : ℝ}
    (hβ : β < 0) (hβlow : -(1 / 2 : ℝ) ≤ β) (hz : B.edge < z)
    (hactive : ∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧
      inner ℝ g (B.basis j) ≠ 0 ∧ B.eigenvalue i ≠ B.eigenvalue j) :
    iteratedDeriv 2 (fun y => (B.spectralSum g y)^β) z < 0 := by
  rw [B.transformed_second hg β hz]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos hβ (Real.rpow_pos_of_pos (B.spectralSum_pos hg hz) _)
  · have hh := mul_nonneg (show 0 ≤ β + 1 / 2 by linarith)
      (sq_nonneg (deriv (B.spectralSum g) z))
    nlinarith [B.strict_curvature_inequality g hz hactive]

/-- The real-power transform of the actual inverse-defined secular function. -/
noncomputable def transformed (H M : E →L[ℝ] E) (g : E) (β z : ℝ) : ℝ :=
  (secular H M g z)^β

/-- The inverse-defined transformed function and its spectral expression have the same actual
iterated derivatives above the edge. -/
theorem transformed_derivative_eq [FiniteDimensional ℝ E] (g : E) (β : ℝ) (k : ℕ)
    {z : ℝ} (hz : B.edge < z) :
    iteratedDeriv k (transformed H M g β) z =
      iteratedDeriv k (fun y => (B.spectralSum g y)^β) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  unfold transformed
  rw [B.secular_eq_sum y (fun i => ne_of_gt (B.denominator_pos hy i)) g]
  rfl

omit [Nonempty ι] in
/-- A zero-gradient transformed spectral function is constant and all positive-order
derivatives vanish. -/
theorem transformed_zero_derivative (β : ℝ) (k : ℕ) (hk : k ≠ 0) (z : ℝ) :
    iteratedDeriv k (fun y => (B.spectralSum (0 : E) y)^β) z = 0 := by
  have heq : (fun y => (B.spectralSum (0 : E) y)^β) = (fun _ : ℝ => (0 : ℝ)^β) := by
    funext y
    simp only [spectralSum, inner_zero_left, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Finset.sum_const_zero]
  rw [heq]
  simp only [iteratedDeriv_const, ite_eq_right hk]

/-- All first- and second-derivative signs for the actual transformed secular function,
including zero-gradient equality and the exceptional affine endpoint. -/
theorem transformed_derivative_signs [FiniteDimensional ℝ E] (g : E) (β : ℝ)
    {z : ℝ} (hz : B.edge < z) :
    (0 < β → deriv (transformed H M g β) z ≤ 0 ∧
      0 ≤ iteratedDeriv 2 (transformed H M g β) z ∧
      (g ≠ 0 → deriv (transformed H M g β) z < 0 ∧
        0 < iteratedDeriv 2 (transformed H M g β) z)) ∧
    (β < 0 → g ≠ 0 → 0 < deriv (transformed H M g β) z ∧
      (-(1 / 2 : ℝ) ≤ β → iteratedDeriv 2 (transformed H M g β) z ≤ 0 ∧
        (-(1 / 2 : ℝ) < β → iteratedDeriv 2 (transformed H M g β) z < 0) ∧
        ((∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧ inner ℝ g (B.basis j) ≠ 0 ∧
          B.eigenvalue i ≠ B.eigenvalue j) →
          iteratedDeriv 2 (transformed H M g β) z < 0))) := by
  have h₁ : deriv (transformed H M g β) z =
      deriv (fun y => (B.spectralSum g y)^β) z := by
    simpa only [iteratedDeriv_one] using B.transformed_derivative_eq g β 1 hz
  rw [h₁, B.transformed_derivative_eq g β 2 hz]
  constructor
  · intro hβ
    by_cases hg : g = 0
    · subst g
      have h₁ := B.transformed_zero_derivative β 1 (by decide) z
      rw [iteratedDeriv_one] at h₁
      rw [h₁, B.transformed_zero_derivative β 2 (by decide) z]
      simp
    · exact ⟨(B.transformed_first_pos_exponent hg hβ hz).le,
        (B.transformed_second_pos_exponent hg hβ hz).le,
        fun _ => ⟨B.transformed_first_pos_exponent hg hβ hz,
          B.transformed_second_pos_exponent hg hβ hz⟩⟩
  · intro hβ hg
    refine ⟨B.transformed_first_neg_exponent hg hβ hz, fun hβlow => ?_⟩
    exact ⟨B.transformed_second_neg_exponent hg hβ hβlow hz,
      fun hh => B.transformed_second_neg_strict hg hβ hh hz,
      fun hh => B.transformed_second_neg_strict_of_active hg hβ hβlow hz hh⟩

end QuadraticSecular.PencilBasis
