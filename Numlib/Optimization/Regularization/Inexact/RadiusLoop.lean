import Numlib.Optimization.Regularization.Inexact.ModelDecrease
import Numlib.Optimization.LineSearch.Backtracking

/-!
# Finite optimality-radius loops with inexact Taylor models

The two actual computed exit tests either finish the optimality check or
supply a direction with sufficient regularized model decrease. Halving cannot
continue indefinitely, and the first exit retains a quantitative radius floor.
-/

namespace InexactRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two exits from the radius-halving loop in the optimality check:
the computed optimality test passes or the actual regularized model decreases. -/
def HalvingAccepts (A : FormalMultilinearSeries ℝ E ℝ) (j p : ℕ)
    (σ ζ ε δ₀ : ℝ) (d : ℕ → E) (t : ℕ) : Prop :=
  TaylorModel.jetDecrement A j (d t) ≤
      ζ / 2 * ε * BacktrackingGradient.step δ₀ t ^ j / j.factorial ∨
    ζ / 4 * ε * BacktrackingGradient.step δ₀ t ^ j / j.factorial ≤
      ModelDecrease.penalized (TaylorModel.ofJet A p) p σ 0 -
        ModelDecrease.penalized (TaylorModel.ofJet A p) p σ (d t)

/-- Geometric candidates are positive when their initial radius is positive. -/
theorem halving_radius_pos {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (t : ℕ) :
    0 < BacktrackingGradient.step δ₀ t := by
  exact div_pos hδ₀ (by positivity)

/-- Halving radii decrease with the number of reductions. -/
theorem halving_radius_antitone {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) :
    Antitone (BacktrackingGradient.step δ₀) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [BacktrackingGradient.step_succ]
  exact div_le_self (div_nonneg hδ₀ (by positivity)) (by norm_num)

/-- Below the explicit threshold at least one actual exit test holds. -/
theorem halvingAccepts_of_radius_le (A : FormalMultilinearSeries ℝ E ℝ)
    {j p : ℕ} (hj : 0 < j) (hjp : j ≤ p) {B σ ζ ε δ₀ : ℝ}
    (hB : 0 < B) (hσ : 0 ≤ σ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hA : ∀ a, j < a → a ≤ p → ‖A a‖ ≤ B)
    (d : ℕ → E) (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) {t : ℕ}
    (ht : BacktrackingGradient.step δ₀ t ≤ ζ * ε / (8 * max B σ)) :
    HalvingAccepts A j p σ ζ ε δ₀ d t := by
  by_cases htest : TaylorModel.jetDecrement A j (d t) ≤
      ζ / 2 * ε * BacktrackingGradient.step δ₀ t ^ j / j.factorial
  · exact Or.inl htest
  · right
    have hmodel := TaylorModel.penalized_decrement_ge_half A hj hjp hB hσ
      (halving_radius_pos hδ₀ t)
      ((halving_radius_antitone hδ₀.le (Nat.zero_le t)).trans (by simpa))
      (show BacktrackingGradient.step δ₀ t ≤ (ζ / 2 * ε) / (4 * max B σ) by
        convert ht using 1; ring) hA (d t) (hd t) (le_of_not_ge htest)
    convert hmodel using 1; ring

/-- Every sequence of feasible computed directions exits the halving loop finitely. -/
theorem exists_halvingAccepts (A : FormalMultilinearSeries ℝ E ℝ)
    {j p : ℕ} (hj : 0 < j) (hjp : j ≤ p) {B σ ζ ε δ₀ : ℝ}
    (hB : 0 < B) (hσ : 0 ≤ σ) (hζ : 0 < ζ) (hε : 0 < ε)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hA : ∀ a, j < a → a ≤ p → ‖A a‖ ≤ B)
    (d : ℕ → E) (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) :
    ∃ t, HalvingAccepts A j p σ ζ ε δ₀ d t := by
  obtain ⟨t, ht⟩ := BacktrackingGradient.exists_step_le δ₀
    (show 0 < ζ * ε / (8 * max B σ) by positivity)
  exact ⟨t, halvingAccepts_of_radius_le A hj hjp hB hσ hδ₀ hδ₀1 hA d hd ht⟩

/-- A rejected prefix prevents the accepted radius from falling below half of
the sufficient threshold, with the initial radius covering the zero-halving case. -/
theorem halving_radius_lower (A : FormalMultilinearSeries ℝ E ℝ)
    {j p : ℕ} (hj : 0 < j) (hjp : j ≤ p) {B σ ζ ε δ₀ : ℝ}
    (hB : 0 < B) (hσ : 0 ≤ σ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hA : ∀ a, j < a → a ≤ p → ‖A a‖ ≤ B)
    (d : ℕ → E) (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) {N : ℕ}
    (hreject : ∀ t < N, ¬ HalvingAccepts A j p σ ζ ε δ₀ d t) :
    min (ζ * ε / (16 * max B σ)) δ₀ ≤ BacktrackingGradient.step δ₀ N := by
  cases N with
  | zero => simp
  | succ N =>
    have hprev : ζ * ε / (8 * max B σ) < BacktrackingGradient.step δ₀ N := by
      apply lt_of_not_ge
      intro hh
      exact hreject N (by omega)
        (halvingAccepts_of_radius_le A hj hjp hB hσ hδ₀ hδ₀1 hA d hd hh)
    rw [BacktrackingGradient.step_succ]
    apply (min_le_left _ _).trans
    have he : ζ * ε / (16 * max B σ) = (ζ * ε / (8 * max B σ)) / 2 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right hprev.le (by norm_num)

/-- A completed optimality-radius loop records the actual exit and the earlier
failed exit tests, exactly as prescribed by the halving program. -/
structure HalvingRun (A : FormalMultilinearSeries ℝ E ℝ) (j p : ℕ)
    (σ ζ ε δ₀ : ℝ) (d : ℕ → E) (N : ℕ) : Prop where
  exits : HalvingAccepts A j p σ ζ ε δ₀ d N
  rejected : ∀ t < N, ¬ HalvingAccepts A j p σ ζ ε δ₀ d t

/-- The first passing pair of exit tests defines a finite run and gives all
intermediate and final radius bounds simultaneously. -/
theorem exists_halvingRun (A : FormalMultilinearSeries ℝ E ℝ)
    {j p : ℕ} (hj : 0 < j) (hjp : j ≤ p) {B σ ζ ε δ₀ : ℝ}
    (hB : 0 < B) (hσ : 0 ≤ σ) (hζ : 0 < ζ) (hε : 0 < ε)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hA : ∀ a, j < a → a ≤ p → ‖A a‖ ≤ B)
    (d : ℕ → E) (hd : ∀ t, ‖d t‖ ≤ BacktrackingGradient.step δ₀ t) :
    ∃ N, HalvingRun A j p σ ζ ε δ₀ d N ∧
      min (ζ * ε / (16 * max B σ)) δ₀ ≤ BacktrackingGradient.step δ₀ N ∧
      ∀ t ≤ N, BacktrackingGradient.step δ₀ N ≤ BacktrackingGradient.step δ₀ t ∧
        BacktrackingGradient.step δ₀ t ≤ δ₀ := by
  classical
  have hex := exists_halvingAccepts A hj hjp hB hσ hζ hε hδ₀ hδ₀1 hA d hd
  let N := Nat.find hex
  have hr : HalvingRun A j p σ ζ ε δ₀ d N :=
    ⟨Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩
  refine ⟨N, hr, halving_radius_lower A hj hjp hB hσ hδ₀ hδ₀1 hA d hd hr.rejected, ?_⟩
  intro t ht
  exact ⟨halving_radius_antitone hδ₀.le ht,
    (halving_radius_antitone hδ₀.le (Nat.zero_le t)).trans (by simp)⟩

end InexactRegularization
