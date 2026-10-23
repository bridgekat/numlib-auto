import Numlib.Optimization.Quadratic.Secular.Geometry
import Mathlib.Analysis.Calculus.Taylor

/-!
# First-order Taylor bounds for transformed secular functions

The Lagrange remainder of the actual transformed function gives the weak
inequalities for both displacement signs. Strictness includes the nonzero-step
condition and the non-affinity condition at exponent minus one half. Constant
zero-gradient transforms and zero displacements are handled explicitly.
-/

open scoped BigOperators Topology
open Filter
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [FiniteDimensional ℝ E]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The actual first-order Taylor polynomial of a transformed inverse-defined secular
function. -/
noncomputable def firstTaylor (H M : E →L[ℝ] E) (g : E) (β z δ : ℝ) : ℝ :=
  transformed H M g β z + deriv (transformed H M g β) z * δ

/-- The first-order Taylor remainder equals the actual second derivative at an interior point
times the squared displacement divided by two. -/
theorem firstTaylor_remainder {g : E} (hg : g ≠ 0) (β : ℝ) {z δ : ℝ}
    (hz : B.edge < z) (hδ : δ ≠ 0) (hzδ : B.edge < z + δ) :
    ∃ y ∈ Set.uIoo z (z + δ), B.edge < y ∧
      transformed H M g β (z + δ) - firstTaylor H M g β z δ =
        iteratedDeriv 2 (transformed H M g β) y * δ^2 / 2 := by
  let F := transformed H M g β
  have hne : z ≠ z + δ := by intro hh; exact hδ (by linarith)
  have hI : Set.uIcc z (z + δ) ⊆ Set.Ioi B.edge := by
    intro y hy
    exact lt_of_lt_of_le (lt_min hz hzδ) hy.1
  have hf : ContDiffOn ℝ 2 F (Set.uIcc z (z + δ)) :=
    fun y hy => (B.contDiffAt_transformed hg β 2 (hI hy)).contDiffWithinAt
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf
  have hcoef : iteratedDerivWithin 1 F (Set.uIcc z (z + δ)) z = deriv F z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (B.contDiffAt_transformed hg β 1 hz) Set.left_mem_uIcc, iteratedDeriv_one]
  have ht : taylorWithinEval F 1 (Set.uIcc z (z + δ)) z (z + δ) = firstTaylor H M g β z δ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval]
    simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
      mul_one, inv_one, one_mul, add_sub_cancel_left, pow_one, hcoef, smul_eq_mul]
    unfold firstTaylor
    dsimp [F]
    ring
  refine ⟨y, hy, hI (Set.uIoo_subset_uIcc_self hy), ?_⟩
  rw [ht, add_sub_cancel_left] at heq
  norm_num only [Nat.reduceAdd, Nat.factorial_succ, Nat.factorial_zero,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_one] at heq
  exact heq

omit [FiniteDimensional ℝ E] in
/-- A zero-gradient inverse-defined transform is the constant zero to the given real power. -/
theorem transformed_zero (H M : E →L[ℝ] E) (β z : ℝ) :
    transformed H M (0 : E) β z = (0 : ℝ)^β := by
  simp [transformed, secular, solution]

omit [FiniteDimensional ℝ E] in
/-- Every first-order Taylor polynomial for a zero-gradient transform is the same constant. -/
theorem firstTaylor_zero (H M : E →L[ℝ] E) (β z δ : ℝ) :
    firstTaylor H M (0 : E) β z δ = (0 : ℝ)^β := by
  have heq : transformed H M (0 : E) β = (fun _ : ℝ => (0 : ℝ)^β) :=
    funext (transformed_zero H M β)
  simp only [firstTaylor, heq, deriv_const, zero_mul, add_zero]

omit [FiniteDimensional ℝ E] in
/-- At zero displacement the first-order Taylor polynomial equals the actual transformed
function. -/
theorem firstTaylor_zero_step (H M : E →L[ℝ] E) (g : E) (β z : ℝ) :
    firstTaylor H M g β z 0 = transformed H M g β z := by simp [firstTaylor]

/-- Every positive-power transformed secular function lies above its first-order Taylor
polynomial, strictly for nonzero gradient and displacement. -/
theorem firstTaylor_lower_pos_exponent (g : E) {β z δ : ℝ} (hβ : 0 < β)
    (hz : B.edge < z) (hzδ : B.edge < z + δ) :
    firstTaylor H M g β z δ ≤ transformed H M g β (z + δ) ∧
      (g ≠ 0 → δ ≠ 0 → firstTaylor H M g β z δ < transformed H M g β (z + δ)) := by
  by_cases hg : g = 0
  · subst g
    simp [firstTaylor_zero, transformed_zero]
  by_cases hδ : δ = 0
  · subst δ
    simp [firstTaylor_zero_step]
  obtain ⟨y, _, hy, heq⟩ := B.firstTaylor_remainder hg β hz hδ hzδ
  have hsign := (((B.transformed_derivative_signs g β hy).1 hβ).2.2 hg).2
  have hh : 0 < iteratedDeriv 2 (transformed H M g β) y * δ^2 / 2 :=
    div_pos (mul_pos hsign (sq_pos_of_ne_zero hδ)) (by norm_num)
  have hlt : firstTaylor H M g β z δ < transformed H M g β (z + δ) := by linarith
  exact ⟨hlt.le, fun _ _ => hlt⟩

/-- For exponents from minus one half to zero the actual transformed function lies below its
first-order Taylor polynomial. Strictness needs nonzero displacement and either an
interior exponent or two distinct active eigenvalues. -/
theorem firstTaylor_upper_neg_exponent {g : E} (hg : g ≠ 0) {β z δ : ℝ}
    (hβ : β < 0) (hβlow : -(1 / 2 : ℝ) ≤ β)
    (hz : B.edge < z) (hzδ : B.edge < z + δ) :
    transformed H M g β (z + δ) ≤ firstTaylor H M g β z δ ∧
      (δ ≠ 0 → (-(1 / 2 : ℝ) < β ∨
        ∃ i j, inner ℝ g (B.basis i) ≠ 0 ∧ inner ℝ g (B.basis j) ≠ 0 ∧
          B.eigenvalue i ≠ B.eigenvalue j) →
        transformed H M g β (z + δ) < firstTaylor H M g β z δ) := by
  by_cases hδ : δ = 0
  · subst δ
    simp [firstTaylor_zero_step]
  obtain ⟨y, _, hy, heq⟩ := B.firstTaylor_remainder hg β hz hδ hzδ
  have hsign := (((B.transformed_derivative_signs g β hy).2 hβ hg).2 hβlow)
  refine ⟨?_, fun _ hstrict => ?_⟩
  · have hh : iteratedDeriv 2 (transformed H M g β) y * δ^2 / 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hsign.1 (sq_nonneg _))
        (by norm_num)
    linarith
  · have hh : iteratedDeriv 2 (transformed H M g β) y < 0 :=
      hstrict.elim hsign.2.1 hsign.2.2
    have hrem : iteratedDeriv 2 (transformed H M g β) y * δ^2 / 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hh (sq_pos_of_ne_zero hδ)) (by norm_num)
    linarith

end QuadraticSecular.PencilBasis
