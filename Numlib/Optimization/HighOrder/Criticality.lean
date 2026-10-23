import Numlib.Analysis.Calculus.TaylorModel
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# High-order Taylor criticality on closed balls

Criticality is the supremum of actual Taylor decrements. Compactness in a proper normed
space makes it an attained maximum, and feasibility of zero displacement makes it
nonnegative. Zero criticality is characterized by nonpositive feasible decrements.

Vanishing cubic criticality implies vanishing quadratic criticality. The proof uses
nonnegativity of each cubic line restriction, which forces its linear coefficient to
vanish; averaging the two endpoint values then controls the quadratic coefficient.

Successive Taylor models differ by their highest homogeneous term. Its operator-norm
bound controls the change in criticality and yields cascading approximate optimality
when the radius is sufficiently small.
-/

open Set

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Taylor polynomials are continuous in the displacement. -/
theorem continuous_eval (f : E → ℝ) (p : ℕ) (x : E) : Continuous (eval f p x) :=
  FormalMultilinearSeries.partialSum_continuous _ _
/-- Taylor decrements are continuous in the displacement. -/
theorem continuous_decrement (f : E → ℝ) (p : ℕ) (x : E) :
    Continuous (decrement f p x) := continuous_const.sub (continuous_eval _ _ _)
/-- The largest decrease of the genuine degree-`p` Taylor polynomial on the closed
ball of radius `δ`. For nonnegative radii in a proper normed space, the supremum is
attained and nonnegative. These properties are proved below. -/
noncomputable def criticality (f : E → ℝ) (p : ℕ) (x : E) (δ : ℝ) : ℝ :=
  sSup ((decrement f p x) '' Metric.closedBall 0 δ)
variable [ProperSpace E]
/-- The criticality supremum is attained. -/
theorem exists_decrement_eq_criticality (f : E → ℝ) (p : ℕ) (x : E) {δ : ℝ}
    (hδ : 0 ≤ δ) : ∃ s : E, ‖s‖ ≤ δ ∧ decrement f p x s = criticality f p x δ := by
  obtain ⟨s,hs,heq⟩ := (isCompact_closedBall (0 : E) δ).exists_sSup_image_eq
    ⟨0, by simpa using hδ⟩ (continuous_decrement f p x).continuousOn
  exact ⟨s, by simpa using hs, heq.symm⟩
/-- Each feasible Taylor decrement is bounded by the criticality measure. -/
theorem decrement_le_criticality (f : E → ℝ) (p : ℕ) (x : E) {δ : ℝ}
    {s : E} (hs : ‖s‖ ≤ δ) : decrement f p x s ≤ criticality f p x δ := by
  exact le_csSup ((isCompact_closedBall (0 : E) δ).image
    (continuous_decrement f p x)).bddAbove ⟨s, by simpa using hs, rfl⟩
/-- The criticality measure is nonnegative because zero displacement is feasible. -/
theorem criticality_nonneg (f : E → ℝ) (p : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ criticality f p x δ := by
  simpa using decrement_le_criticality f p x (s := 0) (by simpa using hδ)
/-- Zero criticality means all feasible Taylor decrements are nonpositive. -/
theorem criticality_eq_zero_iff (f : E → ℝ) (p : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    criticality f p x δ = 0 ↔ ∀ s : E, ‖s‖ ≤ δ → decrement f p x s ≤ 0 := by
  constructor
  · intro h s hs
    simpa [h] using decrement_le_criticality f p x hs
  · intro h
    apply le_antisymm _ (criticality_nonneg f p x hδ)
    obtain ⟨s,hs,heq⟩ := exists_decrement_eq_criticality f p x hδ
    rw [← heq]
    exact h s hs
end TaylorModel
open scoped Topology
/-- A cubic polynomial nonnegative near zero has vanishing linear coefficient. -/
private theorem cubic_nonneg_on_unit_interval {a b c : ℝ}
    (h : ∀ t ∈ Icc (-1 : ℝ) 1, 0 ≤ t * a + t ^ 2 * b + t ^ 3 * c) :
    a = 0 ∧ 0 ≤ b := by
  have hmin : IsLocalMin (fun t : ℝ => t * a + t ^ 2 * b + t ^ 3 * c) 0 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht
    simpa using h t ⟨ht.1.le, ht.2.le⟩
  have hd : HasDerivAt (fun t : ℝ => t * a + t ^ 2 * b + t ^ 3 * c) a 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).mul_const a).add
      ((hasDerivAt_pow 2 0).mul_const b)).add ((hasDerivAt_pow 3 0).mul_const c) using 1 <;>
      norm_num [Pi.add_def]
  have ha := hmin.hasDerivAt_eq_zero hd
  refine ⟨ha, ?_⟩
  have hp := h 1 (by norm_num)
  have hm := h (-1) (by norm_num)
  norm_num at hp hm
  linarith
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The cubic Taylor model along a line has its expected homogeneous coefficients. -/
theorem eval_three_smul (f : E → ℝ) (x s : E) (t : ℝ) :
    eval f 3 x (t • s) - f x =
      t * iteratedFDeriv ℝ 1 f x (fun _ => s) +
      t ^ 2 * (iteratedFDeriv ℝ 2 f x (fun _ => s) / 2) +
      t ^ 3 * (iteratedFDeriv ℝ 3 f x (fun _ => s) / 6) := by
  have hmap (j : ℕ) : iteratedFDeriv ℝ j f x (fun _ => t • s) =
      t ^ j * iteratedFDeriv ℝ j f x (fun _ => s) := by
    simpa [smul_eq_mul] using (iteratedFDeriv ℝ j f x).map_smul_univ (fun _ => t) (fun _ => s)
  rw [eval_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hmap]
  norm_num [smul_eq_mul]
  ring
/-- The quadratic Taylor model along a line has its expected homogeneous coefficients. -/
theorem eval_two (f : E → ℝ) (x s : E) :
    eval f 2 x s - f x = iteratedFDeriv ℝ 1 f x (fun _ => s) +
      iteratedFDeriv ℝ 2 f x (fun _ => s) / 2 := by
  rw [eval_eq_sum]
  norm_num [Finset.sum_range_succ, smul_eq_mul]
  ring
end TaylorModel
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
/-- Vanishing cubic Taylor criticality forces vanishing quadratic Taylor criticality.
Restriction to each line through zero gives a nonnegative cubic polynomial on `[-1,1]`.
Its linear coefficient vanishes, and its quadratic coefficient is nonnegative. -/
theorem criticality_two_eq_zero_of_three (f : E → ℝ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : criticality f 3 x δ = 0) : criticality f 2 x δ = 0 := by
  apply (criticality_eq_zero_iff f 2 x hδ).2
  intro s hs
  have hc : ∀ t ∈ Icc (-1 : ℝ) 1,
      0 ≤ t * iteratedFDeriv ℝ 1 f x (fun _ => s) +
        t ^ 2 * (iteratedFDeriv ℝ 2 f x (fun _ => s) / 2) +
        t ^ 3 * (iteratedFDeriv ℝ 3 f x (fun _ => s) / 6) := by
    intro t ht
    have ht1 : |t| ≤ 1 := abs_le.mpr ht
    have hts : ‖t • s‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg s) ht1).trans hs
    have hdec := (criticality_eq_zero_iff f 3 x hδ).1 h (t • s) hts
    rw [← eval_three_smul f x s t]
    rw [decrement_eq] at hdec
    linarith
  obtain ⟨ha,hb⟩ := cubic_nonneg_on_unit_interval hc
  have heq := eval_two f x s
  rw [decrement_eq]
  linarith
end TaylorModel
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- If a cubic model is nonnegative on a centered ball, its quadratic truncation is
nonnegative there too. A symmetric Hessian and symmetric cubic tensor are allowed, but
symmetry is unnecessary because only diagonal evaluations occur. -/
theorem quadratic_nonneg_of_cubic_nonneg (g : E) (H : E →L[ℝ] E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) {δ : ℝ}
    (h : ∀ s : E, ‖s‖ ≤ δ → 0 ≤ inner ℝ g s + inner ℝ s (H s) / 2 +
      T (fun _ => s) / 6) :
    ∀ s : E, ‖s‖ ≤ δ → 0 ≤ inner ℝ g s + inner ℝ s (H s) / 2 := by
  intro s hs
  have hc : ∀ t ∈ Icc (-1 : ℝ) 1,
      0 ≤ t * inner ℝ g s + t ^ 2 * (inner ℝ s (H s) / 2) +
        t ^ 3 * (T (fun _ => s) / 6) := by
    intro t ht
    have hts : ‖t • s‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg s) (abs_le.mpr ht)).trans hs
    have hT : T (fun _ => t • s) = t ^ 3 * T (fun _ => s) := by
      simpa [smul_eq_mul] using T.map_smul_univ (fun _ => t) (fun _ => s)
    have hts' := h (t • s) hts
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right, hT] at hts'
    nlinarith
  obtain ⟨ha,hb⟩ := cubic_nonneg_on_unit_interval hc
  linarith
end TaylorModel

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Successive Taylor models differ by their highest-degree term. -/
theorem eval_succ_sub_eval (f : E → F) (p : ℕ) (x s : E) :
    eval f (p + 1) x s - eval f p x s =
      (((p + 1).factorial : ℝ)⁻¹) • iteratedFDeriv ℝ (p + 1) f x (fun _ => s) := by
  rw [eval_eq_sum, eval_eq_sum, Finset.sum_range_succ]
  abel
/-- The difference of successive Taylor models is controlled by the highest derivative. -/
theorem norm_eval_succ_sub_eval_le (f : E → F) (p : ℕ) (x s : E) :
    ‖eval f (p + 1) x s - eval f p x s‖ ≤
      ‖iteratedFDeriv ℝ (p + 1) f x‖ * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  rw [eval_succ_sub_eval, norm_smul]
  have hnorm : ‖((p + 1).factorial : ℝ)⁻¹‖ = ((p + 1).factorial : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm]
  have hmap : ‖iteratedFDeriv ℝ (p + 1) f x (fun _ => s)‖ ≤
      ‖iteratedFDeriv ℝ (p + 1) f x‖ * ‖s‖ ^ (p + 1) := by
    simpa using (iteratedFDeriv ℝ (p + 1) f x).le_opNorm (fun _ => s)
  calc ((p + 1).factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ (p + 1) f x (fun _ => s)‖ ≤
      ((p + 1).factorial : ℝ)⁻¹ *
        (‖iteratedFDeriv ℝ (p + 1) f x‖ * ‖s‖ ^ (p + 1)) := by gcongr
    _ = _ := by ring
variable [ProperSpace E]
/-- Successive Taylor criticality measures differ by at most the highest-order term bound. -/
theorem criticality_le_succ_add (f : E → ℝ) (p : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    criticality f p x δ ≤ criticality f (p + 1) x δ +
      ‖iteratedFDeriv ℝ (p + 1) f x‖ * δ ^ (p + 1) / (p + 1).factorial := by
  obtain ⟨s, hs, heq⟩ := exists_decrement_eq_criticality f p x hδ
  have hnext := decrement_le_criticality f (p + 1) x hs
  have hbound := norm_eval_succ_sub_eval_le f p x s
  rw [Real.norm_eq_abs] at hbound
  have hdiff : decrement f p x s - decrement f (p + 1) x s =
      eval f (p + 1) x s - eval f p x s := by rw [decrement_eq, decrement_eq]; ring
  have hpow : ‖s‖ ^ (p + 1) ≤ δ ^ (p + 1) := pow_le_pow_left₀ (norm_nonneg s) hs _
  have hterm : ‖iteratedFDeriv ℝ (p + 1) f x‖ * ‖s‖ ^ (p + 1) / (p + 1).factorial ≤
      ‖iteratedFDeriv ℝ (p + 1) f x‖ * δ ^ (p + 1) / (p + 1).factorial := by gcongr
  have hupper := (abs_le.1 hbound).2
  rw [← heq]
  linarith
end TaylorModel
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
/-- A sufficiently small radius transfers a higher-order criticality tolerance to the
preceding order. The multiplied radius condition permits a zero highest derivative,
when the smallness restriction is automatic. -/
theorem criticality_cascade (f : E → ℝ) (p : ℕ) (hp : 1 ≤ p) (x : E)
    {δ ε εprev : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hεprev : ε ≤ εprev)
    (hsmall : 2 * δ * ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ (p + 1 : ℕ) * ε)
    (hcrit : criticality f (p + 1) x δ ≤ ε * δ ^ (p + 1) / (p + 1).factorial) :
    criticality f p x δ ≤ εprev * δ ^ p / p.factorial := by
  have hj : (2 : ℝ) ≤ (p + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hp
  have heδ : ε * δ ≤ ε := mul_le_of_le_one_right hε hδ1
  have hje : 2 * ε ≤ (p + 1 : ℕ) * ε := mul_le_mul_of_nonneg_right hj hε
  have hcoef : (ε + ‖iteratedFDeriv ℝ (p + 1) f x‖) * δ ≤ (p + 1 : ℕ) * εprev := by
    have hnext : (p + 1 : ℕ) * ε ≤ (p + 1 : ℕ) * εprev := by gcongr
    nlinarith
  calc criticality f p x δ ≤ criticality f (p + 1) x δ +
        ‖iteratedFDeriv ℝ (p + 1) f x‖ * δ ^ (p + 1) / (p + 1).factorial :=
      criticality_le_succ_add f p x hδ
    _ ≤ ε * δ ^ (p + 1) / (p + 1).factorial +
        ‖iteratedFDeriv ℝ (p + 1) f x‖ * δ ^ (p + 1) / (p + 1).factorial :=
      add_le_add hcrit le_rfl
    _ = (δ ^ p / ((p + 1).factorial : ℝ)) *
        ((ε + ‖iteratedFDeriv ℝ (p + 1) f x‖) * δ) := by rw [pow_succ]; ring
    _ ≤ (δ ^ p / ((p + 1).factorial : ℝ)) * ((p + 1 : ℕ) * εprev) :=
      mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = εprev * δ ^ p / p.factorial := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
end TaylorModel
