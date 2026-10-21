import Numlib.Optimization.InexactTaylorModels
import Numlib.Optimization.HigherOrderApproximateRegularizationInnerReturn

/-!
# Inspecting inexact regularization models

A radius search records the actual displacement at every halving. Passing the computed
fractional test uses a non-strict inequality; model decrease is tested separately. The
polynomial tail bound gives finite progress for every legal choice of these displacements.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The supplied positive-order tensors used by an inexact polynomial. -/
abbrev Coefficients (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ

/-- A selected feasible displacement capturing a fraction of the actual polynomial gap. -/
structure CoefficientWitness (A : Coefficients E) (j : ℕ) (δ v : ℝ) (d : E) : Prop where
  feasible : ‖d‖ ≤ δ
  fraction_le : v * gapOn (decrement A j) (Metric.closedBall 0 δ) ≤ decrement A j d

/-- Compact coefficient polynomials always admit feasible fraction witnesses, including
an exact maximizer. No approximate-gap oracle contract is assumed. -/
theorem exists_coefficientWitness [ProperSpace E] (A : Coefficients E) (j : ℕ)
    {δ v : ℝ} (hδ : 0 ≤ δ) (hv : v ≤ 1) : ∃ d : E, CoefficientWitness A j δ v d := by
  have hz : (0 : E) ∈ Metric.closedBall 0 δ := by simpa using hδ
  obtain ⟨d, hd, he⟩ := exists_eq_gapOn (isCompact_closedBall 0 δ)
    ⟨0, hz⟩ (continuous_decrement A j).continuousOn
  have hzero : decrement A j (0 : E) = 0 := by
    rw [decrement_eq 0, polynomial_zero, sub_self]
  have hgap := gapOn_nonneg (isCompact_closedBall 0 δ)
    (continuous_decrement A j).continuousOn hz hzero
  exact ⟨d, ⟨by simpa using hd, by rw [he]; exact mul_le_of_le_one_left hgap hv⟩⟩

/-- The radius after a specified number of literal halvings. -/
def halvedRadius (δ : ℝ) (k : ℕ) : ℝ := δ * (1 / 2 : ℝ) ^ k

/-- No halving changes the initial radius. -/
@[simp] theorem halvedRadius_zero (δ : ℝ) : halvedRadius δ 0 = δ := by
  simp [halvedRadius]

/-- A further halving divides the radius by two. -/
theorem halvedRadius_succ (δ : ℝ) (k : ℕ) :
    halvedRadius δ (k + 1) = halvedRadius δ k / 2 := by
  simp [halvedRadius, pow_succ]; ring

/-- Positive initial radii remain positive. -/
theorem halvedRadius_pos {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : 0 < halvedRadius δ k := by
  unfold halvedRadius; positivity

/-- Every later radius is bounded by every earlier radius. -/
theorem halvedRadius_antitone {δ : ℝ} (hδ : 0 ≤ δ) : Antitone (halvedRadius δ) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [halvedRadius_succ]
  have : 0 ≤ halvedRadius δ k := by unfold halvedRadius; positivity
  linarith

/-- A legal search prefix contains actual witnesses; every nonfinal attempt failed both
its non-strict computed pass and its regularized model decrease test. -/
structure RadiusSearch (c : ℝ) (A : Coefficients E) (p j : ℕ)
    (σ δ v ε : ℝ) (N : ℕ) where
  direction : ℕ → E
  witness : ∀ k, k ≤ N → CoefficientWitness A j (halvedRadius δ k) v (direction k)
  failed : ∀ k, k < N →
    v * ε * halvedRadius δ k ^ j / (2 * (j ! : ℝ)) < decrement A j (direction k) ∧
    c - regularizedPolynomial c A p σ (direction k) <
      v * ε * halvedRadius δ k ^ j / (4 * (j ! : ℝ))

/-- The tested terminal outcome is either a computed pass or sufficient actual model decrease. -/
def RadiusSearch.Finished {c : ℝ} {A : Coefficients E} {p j : ℕ}
    {σ δ v ε : ℝ} {N : ℕ} (s : RadiusSearch c A p j σ δ v ε N) : Prop :=
  decrement A j (s.direction N) ≤ v * ε * halvedRadius δ N ^ j / (2 * (j ! : ℝ)) ∨
    v * ε * halvedRadius δ N ^ j / (4 * (j ! : ℝ)) ≤
      c - regularizedPolynomial c A p σ (s.direction N)

/-- Below the explicit radius threshold every inspected displacement either passes or
provides the required regularized-model decrease. The same selected witness is retained. -/
theorem inspection_finished_of_small_radius (c : ℝ) (A : Coefficients E)
    {p j : ℕ} (hjp : j ≤ p) {L σ δ v ε : ℝ}
    (hL : 0 < L) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : δ ≤ v * ε / (8 * max L σ)) (d : E) (hd : ‖d‖ ≤ δ)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L) :
    decrement A j d ≤ v * ε * δ ^ j / (2 * (j ! : ℝ)) ∨
      v * ε * δ ^ j / (4 * (j ! : ℝ)) ≤ c - regularizedPolynomial c A p σ d := by
  by_cases hpass : decrement A j d ≤ v * ε * δ ^ j / (2 * (j ! : ℝ))
  · exact Or.inl hpass
  · apply Or.inr
    have hden : 0 < 8 * max L σ := by positivity
    have hs := (le_div_iff₀ hden).mp hsmall
    have hh := half_decrease_of_small_radius c A hjp hL.le hδ d hd hA
      (α := v * ε / 2) (by calc
        _ = (δ * (8 * max L σ)) / 2 := by ring
        _ ≤ (v * ε) / 2 := div_le_div_of_nonneg_right hs (by norm_num)) (by
        have ht := (lt_of_not_ge hpass).le
        convert ht using 1; ring)
    convert hh using 1; ring

/-- Every actual halving occurs strictly above the eventual success threshold. -/
theorem RadiusSearch.threshold_lt {c : ℝ} {A : Coefficients E} {p j : ℕ}
    {L σ δ v ε : ℝ} {N : ℕ} (s : RadiusSearch c A p j σ δ v ε N)
    (hjp : j ≤ p) (hL : 0 < L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L) {k : ℕ} (hk : k < N) :
    v * ε / (8 * max L σ) < halvedRadius δ k := by
  by_contra hn
  have hfinished := inspection_finished_of_small_radius c A hjp hL
    ⟨(halvedRadius_pos hδ.1 k).le, (show halvedRadius δ k ≤ δ by
        simpa using halvedRadius_antitone hδ.1.le (Nat.zero_le k)).trans hδ.2⟩
    (le_of_not_gt hn) (s.direction k) (s.witness k hk.le).feasible hA
  rcases hfinished with hp | hm
  · exact (not_lt_of_ge hp (s.failed k hk).1)
  · exact (not_lt_of_ge hm (s.failed k hk).2)

/-- Every search prefix retains at least half the success threshold, or its initial radius
when no halving was necessary. This includes all intermediate radii. -/
theorem RadiusSearch.radius_bounds {c : ℝ} {A : Coefficients E} {p j : ℕ}
    {L σ δ v ε : ℝ} {N : ℕ} (s : RadiusSearch c A p j σ δ v ε N)
    (hjp : j ≤ p) (hL : 0 < L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L) {k : ℕ} (hk : k ≤ N) :
    δ ≥ halvedRadius δ k ∧ halvedRadius δ k ≥ halvedRadius δ N ∧
      min (v * ε / (16 * max L σ)) δ ≤ halvedRadius δ N := by
  refine ⟨by simpa using halvedRadius_antitone hδ.1.le (Nat.zero_le k),
    halvedRadius_antitone hδ.1.le hk, ?_⟩
  cases N with
  | zero => simp
  | succ N =>
    have ht := s.threshold_lt hjp hL hδ hA (Nat.lt_succ_self N)
    rw [halvedRadius_succ]
    have he : v * ε / (16 * max L σ) = (v * ε / (8 * max L σ)) / 2 := by ring
    rw [he]
    exact (min_le_left _ _).trans (by linarith)

/-- The halving countdown bounds every legal prefix, independently of its witness choices. -/
theorem RadiusSearch.length_le {c : ℝ} {A : Coefficients E} {p j : ℕ}
    {L σ δ v ε : ℝ} {N : ℕ} (s : RadiusSearch c A p j σ δ v ε N)
    (hjp : j ≤ p) (hL : 0 < L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hv : 0 < v) (hε : 0 < ε)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L) :
    N ≤ HigherOrderApproximateRegularization.geometricCountdown (v * ε / (8 * max L σ)) δ := by
  by_contra hn
  have hcnt : HigherOrderApproximateRegularization.geometricCountdown
      (v * ε / (8 * max L σ)) δ < N := by omega
  have hη : 0 < v * ε / (8 * max L σ) := by positivity
  have hsmall := HigherOrderApproximateRegularization.geometricCountdown_spec hη δ
  exact (not_lt_of_ge hsmall (s.threshold_lt hjp hL hδ hA hcnt))

/-- Every sequence of actual feasible witness choices has a first finished inspection.
No eventual success premise is required: the polynomial-tail threshold supplies it. -/
theorem exists_finished_search (c : ℝ) (A : Coefficients E) {p j : ℕ}
    (hjp : j ≤ p) {L σ δ v ε : ℝ} (hL : 0 < L)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hv : 0 < v) (hε : 0 < ε)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L)
    (d : ℕ → E) (hd : ∀ k, CoefficientWitness A j (halvedRadius δ k) v (d k)) :
    ∃ N : ℕ, N ≤ HigherOrderApproximateRegularization.geometricCountdown
      (v * ε / (8 * max L σ)) δ ∧
      ∃ s : RadiusSearch c A p j σ δ v ε N, s.direction = d ∧ s.Finished := by
  let finish (k : ℕ) : Prop :=
    decrement A j (d k) ≤ v * ε * halvedRadius δ k ^ j / (2 * (j ! : ℝ)) ∨
      v * ε * halvedRadius δ k ^ j / (4 * (j ! : ℝ)) ≤
        c - regularizedPolynomial c A p σ (d k)
  have hex : ∃ k, finish k := by
    refine ⟨HigherOrderApproximateRegularization.geometricCountdown
      (v * ε / (8 * max L σ)) δ, ?_⟩
    apply inspection_finished_of_small_radius c A hjp hL
      ⟨(halvedRadius_pos hδ.1 _).le, ?_⟩
      (HigherOrderApproximateRegularization.geometricCountdown_spec (by positivity) δ)
      _ (hd _).feasible hA
    exact (show halvedRadius δ _ ≤ δ by
      simpa using halvedRadius_antitone hδ.1.le (Nat.zero_le _)).trans hδ.2
  let N := Nat.find hex
  have hN : finish N := Nat.find_spec hex
  have hf : ∀ k, k < N → ¬finish k := fun k hk => Nat.find_min hex hk
  let s : RadiusSearch c A p j σ δ v ε N := {
    direction := d
    witness := fun k _ => hd k
    failed := by
      intro k hk
      have hn := hf k hk
      exact ⟨lt_of_not_ge (fun hh => hn (Or.inl hh)),
        lt_of_not_ge (fun hh => hn (Or.inr hh))⟩ }
  exact ⟨N, s.length_le hjp hL hδ hv hε hA, s, rfl, hN⟩

/-- Cancelling the positive witness fraction gives half-tolerance control of the actual
approximate gap. Equality in the computed test is allowed. -/
theorem CoefficientWitness.gap_le_half {A : Coefficients E} {j : ℕ} {δ v ε : ℝ} {d : E}
    (w : CoefficientWitness A j δ v d) (hv : 0 < v)
    (hpass : decrement A j d ≤ v * ε * δ ^ j / (2 * (j ! : ℝ))) :
    gapOn (decrement A j) (Metric.closedBall 0 δ) ≤ ε * δ ^ j / (2 * (j ! : ℝ)) := by
  have hh : v * gapOn (decrement A j) (Metric.closedBall 0 δ) ≤
      v * (ε * δ ^ j / (2 * (j ! : ℝ))) := by
    calc
      _ ≤ decrement A j d := w.fraction_le
      _ ≤ _ := by convert hpass using 1; ring
  exact le_of_mul_le_mul_left hh hv

end Optimization.InexactRegularization
