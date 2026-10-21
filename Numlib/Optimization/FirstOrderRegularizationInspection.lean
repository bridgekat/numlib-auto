import Numlib.Optimization.InexactRegularization

/-!
# Complete first-order regularization inspections

A finite coefficient sum supplies the radius-search bound. Actual feasible fractional
witnesses at every dyadic radius produce a complete inspection without an assumed terminal
search outcome. Compactness supplies these witnesses when no particular choices are prescribed.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive finite bound on all coefficients beyond the inspected first order. -/
def firstOrderCoefficientBound (A : Coefficients E) (p : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.Icc 2 p, ‖A i‖

/-- The explicit finite coefficient bound is strictly positive. -/
theorem firstOrderCoefficientBound_pos (A : Coefficients E) (p : ℕ) :
    0 < firstOrderCoefficientBound A p := by
  unfold firstOrderCoefficientBound
  positivity

/-- Every higher coefficient is bounded by the explicit finite sum. -/
theorem norm_le_firstOrderCoefficientBound (A : Coefficients E) (p i : ℕ)
    (hi : i ∈ Finset.Icc 2 p) : ‖A i‖ ≤ firstOrderCoefficientBound A p := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.Icc 2 p) => norm_nonneg (A j)) hi
  unfold firstOrderCoefficientBound
  linarith

private def firstOrderSearch (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ)
    (s : RadiusSearch c A P.p 1 σ (δ 1) P.fraction (P.epsilon 1) N)
    (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    RadiusSearch c A P.p j σ (δ j) P.fraction (P.epsilon j) N := by
  have hj1 : j = 1 := by omega
  subst j
  exact s

private theorem firstOrderSearch_one (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ)
    (s : RadiusSearch c A P.p 1 σ (δ 1) P.fraction (P.epsilon 1) N)
    (hj : 1 ≤ 1) (hjq : 1 ≤ P.q) :
    firstOrderSearch P hq c A σ δ N s 1 hj hjq = s := rfl

private def inspectionWithFirstOrderDirection (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ)
    (s : RadiusSearch c A P.p 1 σ (δ 1) P.fraction (P.epsilon 1) N)
    (hs : s.Finished) :
    { I : Inspection P c A σ δ //
      (I.search 1 le_rfl (by omega) I.order_pos).direction = s.direction } := by
  let pass : Prop := decrement A 1 (s.direction N) ≤
    P.fraction * P.epsilon 1 * halvedRadius (δ 1) N ^ 1 / (2 * (1 ! : ℝ))
  classical
  by_cases hp : pass
  · exact ⟨{
      order := 2
      order_pos := by omega
      order_le := by omega
      halvings := fun _ => N
      search := fun j hj hjq _ => firstOrderSearch P hq c A σ δ N s j hj hjq
      earlier := by
        intro j hj hjq _
        have hj1 : j = 1 := by omega
        subst j
        simpa only [firstOrderSearch_one] using hp
      failed := by intro ho; omega
      retained := by intro ho; omega }, rfl⟩
  · exact ⟨{
      order := 1
      order_pos := le_rfl
      order_le := by omega
      halvings := fun _ => N
      search := fun j hj hjq _ => firstOrderSearch P hq c A σ δ N s j hj hjq
      earlier := by intro j hj _ ho; omega
      failed := by
        intro ho
        simpa only [firstOrderSearch_one] using lt_of_not_ge hp
      retained := by
        intro ho
        simpa only [firstOrderSearch_one] using hs.resolve_left hp }, rfl⟩

private def inspectionFromFirstOrderSearch (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ)
    (s : RadiusSearch c A P.p 1 σ (δ 1) P.fraction (P.epsilon 1) N)
    (hs : s.Finished) : Inspection P c A σ δ :=
  (inspectionWithFirstOrderDirection P hq c A σ δ N s hs).val

private theorem inspectionFromFirstOrderSearch_direction (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (N : ℕ)
    (s : RadiusSearch c A P.p 1 σ (δ 1) P.fraction (P.epsilon 1) N)
    (hs : s.Finished) :
    let I := inspectionFromFirstOrderSearch P hq c A σ δ N s hs
    (I.search 1 le_rfl (by omega) I.order_pos).direction = s.direction :=
  (inspectionWithFirstOrderDirection P hq c A σ δ N s hs).property

/-- A complete first-order inspection preserves the entire prescribed sequence of actual
fractional-witness directions, including the terminal direction selected by its search. -/
theorem exists_firstOrderInspection_with_directions (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ)
    (hδ : δ 1 ∈ Set.Ioc (0 : ℝ) 1) (d : ℕ → E)
    (hd : ∀ k, CoefficientWitness A 1 (halvedRadius (δ 1) k) P.fraction (d k)) :
    ∃ I : Inspection P c A σ δ,
      (I.search 1 le_rfl (by omega) I.order_pos).direction = d := by
  have hp : 1 ≤ P.p := by have := P.order_le; omega
  obtain ⟨N, _, s, he, hs⟩ := exists_finished_search c A hp
    (firstOrderCoefficientBound_pos A P.p) hδ P.fraction_pos
    (P.epsilon_pos 1 le_rfl (by omega))
    (fun i hi => norm_le_firstOrderCoefficientBound A P.p i hi) d hd
  refine ⟨inspectionFromFirstOrderSearch P hq c A σ δ N s hs, ?_⟩
  exact (inspectionFromFirstOrderSearch_direction P hq c A σ δ N s hs).trans he

/-- Prescribed actual fractional witnesses produce a complete order-one inspection.
The search theorem proves its terminal outcome using the actual finite coefficient bound. -/
theorem exists_firstOrderInspection_of_witnesses (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ)
    (hδ : δ 1 ∈ Set.Ioc (0 : ℝ) 1) (d : ℕ → E)
    (hd : ∀ k, CoefficientWitness A 1 (halvedRadius (δ 1) k) P.fraction (d k)) :
    Nonempty (Inspection P c A σ δ) := by
  obtain ⟨I, _⟩ := exists_firstOrderInspection_with_directions P hq c A σ δ hδ d hd
  exact ⟨I⟩

/-- Compact coefficient polynomials admit a complete first-order inspection at every
positive incoming radius at most one, without any supplied search or inspection certificate. -/
theorem exists_firstOrderInspection [ProperSpace E] (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ)
    (hδ : δ 1 ∈ Set.Ioc (0 : ℝ) 1) : Nonempty (Inspection P c A σ δ) := by
  have hw : ∀ k, ∃ d : E,
      CoefficientWitness A 1 (halvedRadius (δ 1) k) P.fraction d := fun k =>
    exists_coefficientWitness A 1 (halvedRadius_pos hδ.1 k).le P.fraction_le_one
  exact exists_firstOrderInspection_of_witnesses P hq c A σ δ hδ
    (fun k => Classical.choose (hw k)) (fun k => Classical.choose_spec (hw k))

end Optimization.InexactRegularization
