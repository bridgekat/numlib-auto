import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Optimization.HighOrder.ModelDecrease
import Mathlib.Tactic

/-!
# Selected Taylor trials with inexact derivative tensors

The selection component records the actual approximate Taylor polynomial,
selected failing computed test and comparison step on every trial iteration.
Accuracy-improving iterations are excluded from the trial set. No conclusion
about scaled gaps or model decrease is a field of this component specification.
-/

open Set
namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive model order, indexed by `Fin q`. -/
def modelOrder {q : ℕ} (j : Fin q) : ℕ := j.val + 1

/-- The inexact Taylor decrement, computed from the supplied continuous
multilinear derivative tensors with the actual factorial normalization. -/
noncomputable def decrement (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (s : E) : ℝ :=
  TaylorModel.ofJet A p 0 - TaylorModel.ofJet A p s

/-- The minimum of the requested accuracies over positive orders. -/
noncomputable def minimumAccuracy {q : ℕ} (hq : 0 < q) (ε : Fin q → ℝ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hq⟩, Finset.mem_univ _⟩ ε

/-- The minimum accuracy is no greater than any requested component. -/
theorem minimumAccuracy_le {q : ℕ} (hq : 0 < q) (ε : Fin q → ℝ) (j : Fin q) :
    minimumAccuracy hq ε ≤ ε j := Finset.inf'_le _ (Finset.mem_univ _)

/-- The minimum of finitely many positive requested accuracies is positive. -/
theorem minimumAccuracy_pos {q : ℕ} (hq : 0 < q) {ε : Fin q → ℝ}
    (hε : ∀ j, 0 < ε j) : 0 < minimumAccuracy hq ε :=
  (Finset.lt_inf'_iff _).mpr (fun j _ => hε j)

/-- The optimality radius is the smaller of the trust radius and its fixed cap. -/
def optimalityRadius (θ Δ : ℝ) : ℝ := min θ Δ

/-- The failed computed test and selected model comparison of TRqIDA on its trial set.
Other accuracy updates, objective ratios and radius updates are separate components.
No derivative accuracy bound is needed for this purely computed-model statement. -/
structure SelectedTrials {q : ℕ} (A : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d s : ℕ → E)
    (ε : Fin q → ℝ) (ζ θ : ℝ) : Prop where
  order_pos : 0 < q
  zeta_pos : 0 < ζ
  zeta_le_one : ζ ≤ 1
  cap_pos : 0 < θ
  cap_le_one : θ ≤ 1
  accuracy_pos : ∀ a, 0 < ε a
  accuracy_le_one : ∀ a, ε a ≤ 1
  radius_pos : ∀ i ∈ T, 0 < Δ i
  direction_feasible : ∀ i ∈ T, ‖d i‖ ≤ optimalityRadius θ (Δ i)
  failed_test : ∀ i ∈ T,
    ζ / 2 * ε (j i) * optimalityRadius θ (Δ i) ^ modelOrder (j i) /
      (modelOrder (j i)).factorial < decrement (A i) (modelOrder (j i)) (d i)
  step_feasible : ∀ i ∈ T, ‖s i‖ ≤ Δ i
  model_comparison : ∀ i ∈ T,
    TaylorModel.ofJet (A i) (modelOrder (j i)) (s i) ≤
      TaylorModel.ofJet (A i) (modelOrder (j i)) (d i)

/-- The scaled actual computed gap in equation (13.1.25). -/
noncomputable def scaledGap {q : ℕ} (A : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d : ℕ → E) (θ : ℝ) (i : ℕ) : ℝ :=
  ModelDecrease.scaled (decrement (A i) (modelOrder (j i)) (d i))
    (optimalityRadius θ (Δ i)) (modelOrder (j i))

/-- Trial indices through an inclusive iteration endpoint. -/
noncomputable def trialPrefix (T : Set ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (k + 1)).filter (· ∈ T)

/-- Prefix membership means both being a trial and being no later than the endpoint. -/
@[simp] theorem mem_trialPrefix {T : Set ℕ} {k i : ℕ} :
    i ∈ trialPrefix T k ↔ i ≤ k ∧ i ∈ T := by
  classical
  simp only [trialPrefix, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- The inclusive trial prefix is nonempty when its endpoint is a trial. -/
theorem trialPrefix_nonempty {T : Set ℕ} {k : ℕ} (hk : k ∈ T) :
    (trialPrefix T k).Nonempty := ⟨k, mem_trialPrefix.mpr ⟨le_rfl, hk⟩⟩

/-- The true finite minimum of computed scaled gaps over the trial prefix. -/
noncomputable def prefixGap {q : ℕ} (A : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (T : Set ℕ) (j : ℕ → Fin q) (Δ : ℕ → ℝ) (d : ℕ → E) (θ : ℝ)
    (k : ℕ) (hk : k ∈ T) : ℝ :=
  (trialPrefix T k).inf' (trialPrefix_nonempty hk) (scaledGap A j Δ d θ)

namespace SelectedTrials
variable {q : ℕ} {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {j : ℕ → Fin q} {Δ : ℕ → ℝ} {d s : ℕ → E} {ε : Fin q → ℝ} {ζ θ : ℝ}

/-- A positive trust radius and cap give a positive optimality radius. -/
theorem optimalityRadius_pos (h : SelectedTrials A T j Δ d s ε ζ θ) {i : ℕ} (hi : i ∈ T) :
    0 < optimalityRadius θ (Δ i) := lt_min h.cap_pos (h.radius_pos i hi)

/-- The actual failed computed test bounds its normalized scaled gap. -/
theorem scaledGap_lower (h : SelectedTrials A T j Δ d s ε ζ θ) {i : ℕ} (hi : i ∈ T) :
    ζ / 2 * minimumAccuracy h.order_pos ε ≤ scaledGap A j Δ d θ i := by
  have hl := ModelDecrease.le_scaled_of_test (modelOrder (j i))
    (h.optimalityRadius_pos hi) (h.failed_test i hi)
  exact (mul_le_mul_of_nonneg_left (minimumAccuracy_le h.order_pos ε (j i))
    (div_nonneg h.zeta_pos.le (by norm_num))).trans hl

/-- The minimum over actual trial indices satisfies the source's lower bound. -/
theorem prefixGap_lower (h : SelectedTrials A T j Δ d s ε ζ θ) {k : ℕ} (hk : k ∈ T) :
    ζ / 2 * minimumAccuracy h.order_pos ε ≤ prefixGap A T j Δ d θ k hk := by
  apply Finset.le_inf'
  intro i hi
  exact h.scaledGap_lower (mem_trialPrefix.mp hi).2

/-- The selected comparison step attains at least the original computed decrement. -/
theorem model_decrease (h : SelectedTrials A T j Δ d s ε ζ θ) {i : ℕ} (hi : i ∈ T) :
    scaledGap A j Δ d θ i * optimalityRadius θ (Δ i) ^ modelOrder (j i) /
        (modelOrder (j i)).factorial ≤ decrement (A i) (modelOrder (j i)) (s i) := by
  rw [scaledGap, ModelDecrease.scaled_mul_radius _ (h.optimalityRadius_pos hi)]
  exact sub_le_sub_left (h.model_comparison i hi) _

end SelectedTrials
end InexactTrustRegion
