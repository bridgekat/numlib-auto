import Numlib.Optimization.HighOrder.Criticality
import Numlib.Analysis.Calculus.TaylorModel.Perturbation

/-!
# Criticality of computed derivative jets

The actual finite polynomial determines a maximum on the radius ball. Tensor
error budgets control the difference between exact and computed criticality,
and a passing computed test with a verified budget certifies true optimality.
-/

open scoped BigOperators
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The largest computed Taylor decrement on the closed radius ball. -/
noncomputable def jetCriticality (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (δ : ℝ) : ℝ :=
  sSup ((jetDecrement A p) '' Metric.closedBall 0 δ)

/-- A computed Taylor decrement is a continuous finite polynomial. -/
theorem continuous_jetDecrement (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) :
    Continuous (jetDecrement A p) :=
  continuous_const.sub (FormalMultilinearSeries.partialSum_continuous _ _)

variable [ProperSpace E]

/-- Compactness attains the computed Taylor criticality supremum. -/
theorem exists_jetDecrement_eq_jetCriticality (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ s : E, ‖s‖ ≤ δ ∧ jetDecrement A p s = jetCriticality A p δ := by
  obtain ⟨s, hs, heq⟩ := (isCompact_closedBall (0 : E) δ).exists_sSup_image_eq
    ⟨0, by simpa using hδ⟩ (continuous_jetDecrement A p).continuousOn
  exact ⟨s, by simpa using hs, heq.symm⟩

/-- Every feasible computed decrement is bounded by computed criticality. -/
theorem jetDecrement_le_jetCriticality (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {δ : ℝ} {s : E} (hs : ‖s‖ ≤ δ) : jetDecrement A p s ≤ jetCriticality A p δ := by
  exact le_csSup ((isCompact_closedBall (0 : E) δ).image
    (continuous_jetDecrement A p)).bddAbove ⟨s, by simpa using hs, rfl⟩

/-- Computed criticality is nonnegative because the zero step is feasible. -/
theorem jetCriticality_nonneg (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ jetCriticality A p δ := by
  simpa only [jetDecrement, sub_self] using
    jetDecrement_le_jetCriticality A p (s := 0) (by simpa using hδ)

/-- A bound on computed criticality is equivalent to a bound on every feasible decrement. -/
theorem jetCriticality_le_iff (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {δ b : ℝ} (hδ : 0 ≤ δ) :
    jetCriticality A p δ ≤ b ↔ ∀ s : E, ‖s‖ ≤ δ → jetDecrement A p s ≤ b := by
  constructor
  · exact fun h s hs => (jetDecrement_le_jetCriticality A p hs).trans h
  · intro h
    obtain ⟨s, hs, heq⟩ := exists_jetDecrement_eq_jetCriticality A p hδ
    exact heq ▸ h s hs

omit [ProperSpace E] in
/-- Uniform tensor error bounds control every computed decrement on the radius ball. -/
theorem norm_jetDecrement_sub_le_radius (A B : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {δ : ℝ} (e : ℕ → ℝ)
    (he : ∀ a, 1 ≤ a → a ≤ p → ‖A a - B a‖ ≤ e a) {s : E} (hs : ‖s‖ ≤ δ) :
    ‖jetDecrement A p s - jetDecrement B p s‖ ≤
      ∑ i ∈ Finset.range p, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial := by
  apply (norm_jetDecrement_sub_le A B p s).trans
  apply Finset.sum_le_sum
  intro i hi
  have hip : i + 1 ≤ p := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hei := he (i + 1) (by omega) hip
  exact mul_le_mul hei (pow_le_pow_left₀ (norm_nonneg s) hs _)
    (pow_nonneg (norm_nonneg s) _) ((norm_nonneg _).trans hei)

/-- Actual tensor errors bound the change in the genuine computed optimality measure. -/
theorem abs_jetCriticality_sub_le (A B : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (e : ℕ → ℝ)
    (he : ∀ a, 1 ≤ a → a ≤ p → ‖A a - B a‖ ≤ e a) :
    |jetCriticality A p δ - jetCriticality B p δ| ≤
      ∑ i ∈ Finset.range p, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial := by
  have hupper (C D : FormalMultilinearSeries ℝ E ℝ)
      (hCD : ∀ a, 1 ≤ a → a ≤ p → ‖C a - D a‖ ≤ e a) :
      jetCriticality C p δ - jetCriticality D p δ ≤
        ∑ i ∈ Finset.range p, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial := by
    obtain ⟨s, hs, hcrit⟩ := exists_jetDecrement_eq_jetCriticality C p hδ
    have herr := norm_jetDecrement_sub_le_radius C D p e hCD hs
    have hb := jetDecrement_le_jetCriticality D p hs
    have hu := (le_abs_self (jetDecrement C p s - jetDecrement D p s)).trans herr
    rw [hcrit] at hu
    linarith
  exact abs_le.mpr ⟨by linarith [hupper B A (by
    intro a ha hap; simpa only [norm_sub_rev] using he a ha hap)], hupper A B he⟩

omit [ProperSpace E] in
/-- Exact derivative jets recover the original Taylor criticality measure. -/
@[simp] theorem jetCriticality_ftaylorSeries (f : E → ℝ) (p : ℕ) (x : E) (δ : ℝ) :
    jetCriticality (ftaylorSeries ℝ f x) p δ = criticality f p x δ := rfl

end TaylorModel

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
/-- A verified tensor error budget and a passing computed optimality check certify
true Taylor criticality at the same requested radius. -/
theorem criticality_le_of_verified_jet (f : E → ℝ)
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (x d : E)
    {δ ζ ε : ℝ} (hδ : 0 ≤ δ) (hζ : 0 < ζ) (e : ℕ → ℝ)
    (he : ∀ a, 1 ≤ a → a ≤ p → ‖A a - iteratedFDeriv ℝ a f x‖ ≤ e a)
    (happrox : ζ * jetCriticality A p δ ≤ jetDecrement A p d)
    (hpass : jetDecrement A p d ≤ ζ / 2 * ε * δ ^ p / p.factorial)
    (hbudget : ∑ i ∈ Finset.range p, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial ≤
      ε / 2 * δ ^ p / p.factorial) :
    criticality f p x δ ≤ ε * δ ^ p / p.factorial := by
  have hcomputed : jetCriticality A p δ ≤ ε / 2 * δ ^ p / p.factorial := by
    apply (mul_le_mul_iff_right₀ hζ).mp
    convert happrox.trans hpass using 1; ring
  have herr := abs_jetCriticality_sub_le A (ftaylorSeries ℝ f x) p hδ e he
  rw [jetCriticality_ftaylorSeries] at herr
  have hlo := (neg_le_abs (jetCriticality A p δ - criticality f p x δ)).trans herr
  have heq : ε * δ ^ p / p.factorial = 2 * (ε / 2 * δ ^ p / p.factorial) := by ring
  linarith
end TaylorModel
