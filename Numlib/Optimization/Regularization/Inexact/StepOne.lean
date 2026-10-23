import Numlib.Optimization.Regularization.Inexact.Parameter
import Numlib.Optimization.Regularization.Inexact.RadiusLoop
import Numlib.Optimization.Regularization.Inexact.VerifiedOptimality
import Numlib.Optimization.LineSearch.Backtracking.Radii

/-!
# Actual ordered optimality checks for inexact regularization

Every computed direction satisfies the actual relative jet-criticality test.
The radius-reduction prefix records both rejected exit tests. The first failing
order either supplies an actual positive reference decrease or all computed
optimality tests pass. Radius floors and verified true optimality are derived.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A complete Step1 check, including its sequential stopping order, actual
halving tests and computed directions. Unprocessed later orders never halve.
No radius floor, true criticality or positive-decrease conclusion is assumed. -/
structure StepOneComputation {q : ℕ} (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    (σ ζ : ℝ) (ε initial reduced : Fin q → ℝ) (reference : E)
    (direction : Fin q → ℕ → E) (count : Fin q → ℕ)
    (selected : Option (Fin q)) : Prop where
  radius_eq : ∀ a, reduced a = BacktrackingGradient.step (initial a) (count a)
  feasible : ∀ a t, ‖direction a t‖ ≤ BacktrackingGradient.step (initial a) t
  approximation : ∀ a t, ζ * TaylorModel.jetCriticality A (modelOrder a)
    (BacktrackingGradient.step (initial a) t) ≤
      TaylorModel.jetDecrement A (modelOrder a) (direction a t)
  rejected : ∀ a t, t < count a → ¬HalvingAccepts A (modelOrder a) p
    σ ζ (ε a) (initial a) (direction a) t
  outcome : match selected with
    | none => ∀ a, TaylorModel.jetDecrement A (modelOrder a) (direction a (count a)) ≤
        ζ / 2 * ε a * reduced a ^ modelOrder a / (modelOrder a).factorial
    | some a => reference = direction a (count a) ∧
        ζ / 2 * ε a * reduced a ^ modelOrder a / (modelOrder a).factorial <
          TaylorModel.jetDecrement A (modelOrder a) reference ∧
        ζ / 4 * ε a * reduced a ^ modelOrder a / (modelOrder a).factorial ≤
          model A p σ 0 - model A p σ reference ∧
        (∀ b, b < a → TaylorModel.jetDecrement A (modelOrder b) (direction b (count b)) ≤
          ζ / 2 * ε b * reduced b ^ modelOrder b / (modelOrder b).factorial) ∧
        (∀ b, a < b → count b = 0)

/-- Every Step1 radius is positive, no larger than its inherited value, and
at most one. These properties follow from the actual geometric reductions. -/
theorem StepOneComputation.radius_bounds {q : ℕ} {A : FormalMultilinearSeries ℝ E ℝ}
    {p : ℕ} {σ ζ : ℝ} {ε initial reduced : Fin q → ℝ} {reference : E}
    {direction : Fin q → ℕ → E} {count : Fin q → ℕ} {selected : Option (Fin q)}
    (h : StepOneComputation A p σ ζ ε initial reduced reference direction count selected)
    (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1) (a : Fin q) :
    0 < reduced a ∧ reduced a ≤ initial a ∧ reduced a ≤ 1 := by
  rw [h.radius_eq a]
  have hu := BacktrackingGradient.step_antitone (hinit a).1.le (Nat.zero_le (count a))
  simp only [BacktrackingGradient.step, pow_zero, div_one] at hu
  exact ⟨BacktrackingGradient.step_pos (hinit a).1 _, hu, hu.trans (hinit a).2⟩

/-- Actual rejected exit tests force the full Step1 radius floor, including
orders that are not processed because an earlier order was selected. -/
theorem StepOneComputation.radius_lower {q : ℕ} {A : FormalMultilinearSeries ℝ E ℝ}
    {p : ℕ} {σ ζ B : ℝ} {ε initial reduced : Fin q → ℝ} {reference : E}
    {direction : Fin q → ℕ → E} {count : Fin q → ℕ} {selected : Option (Fin q)}
    (h : StepOneComputation A p σ ζ ε initial reduced reference direction count selected)
    (hqp : q ≤ p) (hB : 0 < B) (hσ : 0 ≤ σ)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ B)
    (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1) (a : Fin q) :
    min (ζ * ε a / (16 * max B σ)) (initial a) ≤ reduced a := by
  rw [h.radius_eq a]
  exact halving_radius_lower A (by unfold modelOrder; omega)
    (by unfold modelOrder; omega) hB hσ (hinit a).1 (hinit a).2
    (fun i hi hip => hA i (by unfold modelOrder at hi; omega) hip)
    (direction a) (h.feasible a) (h.rejected a)

/-- A selected order supplies strict actual reference improvement. Its
nonzero positive decrease follows from the primitive check and positive data. -/
theorem StepOneComputation.reference_improvement {q : ℕ}
    {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ ζ : ℝ}
    {ε initial reduced : Fin q → ℝ} {reference : E}
    {direction : Fin q → ℕ → E} {count : Fin q → ℕ} {a : Fin q}
    (h : StepOneComputation A p σ ζ ε initial reduced reference direction count (some a))
    (hζ : 0 < ζ) (hε : 0 < ε a) (hinit : ∀ b, 0 < initial b ∧ initial b ≤ 1) :
    model A p σ reference < model A p σ 0 := by
  have hδ := (h.radius_bounds hinit a).1
  have hp : 0 < ζ / 4 * ε a * reduced a ^ modelOrder a / (modelOrder a).factorial :=
    div_pos (mul_pos (mul_pos (div_pos hζ (by norm_num)) hε) (pow_pos hδ _)) (by positivity)
  have hd := h.outcome.2.2.1
  linarith

variable [ProperSpace E]

/-- When all Step1 tests pass, verified actual tensor-error budgets certify
true Taylor criticality in every order at the computed reduced radii. -/
theorem StepOneComputation.true_optimality {q : ℕ}
    {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ ζ : ℝ}
    {ε initial reduced : Fin q → ℝ} {reference : E}
    {direction : Fin q → ℕ → E} {count : Fin q → ℕ}
    (h : StepOneComputation A p σ ζ ε initial reduced reference direction count none)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : ∀ a, 0 < ε a)
    (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1)
    (e : ℕ → ℝ) (hbudget : ∀ a, tensorErrorBudget e (modelOrder a) (reduced a) ≤
      ζ / 2 * ε a * reduced a ^ modelOrder a / (modelOrder a).factorial)
    (f : E → ℝ) (x : E)
    (horacle : ∀ i, 1 ≤ i → i ≤ q → ‖A i - iteratedFDeriv ℝ i f x‖ ≤ e i)
    (a : Fin q) : TaylorModel.criticality f (modelOrder a) x (reduced a) ≤
      ε a * reduced a ^ modelOrder a / (modelOrder a).factorial := by
  have hcheck : VectorTerminationCheck A reduced ζ ε (fun b => direction b (count b)) e := {
    radius_nonneg := fun b => (h.radius_bounds hinit b).1.le
    zeta_pos := hζ
    zeta_le_one := hζ1
    accuracy_pos := hε
    approximation := fun b => by rw [h.radius_eq b]; exact h.approximation b _
    computed_passes := h.outcome
    verified := hbudget }
  exact hcheck.true_optimality f x horacle a

/-- Compactness constructs genuine relative computed directions. Every order's
actual radius loop has a finite first exit. Selecting the first failed
optimality test constructs a complete sequential Step1 computation, leaving
all later unprocessed radii unchanged. -/
theorem exists_stepOneComputation {q p : ℕ} (hqp : q ≤ p)
    (A : FormalMultilinearSeries ℝ E ℝ) {B σ ζ : ℝ}
    (hB : 0 < B) (hσ : 0 ≤ σ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ B)
    (ε initial : Fin q → ℝ) (hε : ∀ a, 0 < ε a)
    (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1) :
    ∃ (reduced : Fin q → ℝ) (reference : E) (direction : Fin q → ℕ → E)
      (count : Fin q → ℕ) (selected : Option (Fin q)),
      StepOneComputation A p σ ζ ε initial reduced reference direction count selected := by
  classical
  have hex : ∀ (a : Fin q) (t : ℕ), ∃ d : E,
      ‖d‖ ≤ BacktrackingGradient.step (initial a) t ∧
      TaylorModel.jetDecrement A (modelOrder a) d =
        TaylorModel.jetCriticality A (modelOrder a) (BacktrackingGradient.step (initial a) t) :=
    fun a t => TaylorModel.exists_jetDecrement_eq_jetCriticality A (modelOrder a)
      (BacktrackingGradient.step_pos (hinit a).1 t).le
  choose direction hd heq using hex
  have happrox : ∀ a t, ζ * TaylorModel.jetCriticality A (modelOrder a)
      (BacktrackingGradient.step (initial a) t) ≤
        TaylorModel.jetDecrement A (modelOrder a) (direction a t) := by
    intro a t
    rw [heq a t]
    exact mul_le_of_le_one_left (TaylorModel.jetCriticality_nonneg A (modelOrder a)
      (BacktrackingGradient.step_pos (hinit a).1 t).le) hζ1
  have hloop : ∀ a : Fin q, ∃ N,
      HalvingRun A (modelOrder a) p σ ζ (ε a) (initial a) (direction a) N := by
    intro a
    obtain ⟨N, hrun, _, _⟩ := exists_halvingRun A (j := modelOrder a) (p := p)
      (by unfold modelOrder; omega)
      (by unfold modelOrder; omega) hB hσ hζ (hε a) (hinit a).1 (hinit a).2
      (fun i hi hip => hA i (by unfold modelOrder at hi; omega) hip) (direction a) (hd a)
    exact ⟨N, hrun⟩
  choose count hr using hloop
  let reduced := fun a => BacktrackingGradient.step (initial a) (count a)
  let Pass := fun a => TaylorModel.jetDecrement A (modelOrder a) (direction a (count a)) ≤
    ζ / 2 * ε a * reduced a ^ modelOrder a / (modelOrder a).factorial
  by_cases hbad : ∃ a, ¬Pass a
  · let bad := Finset.univ.filter fun a => ¬Pass a
    have hne : bad.Nonempty := by
      obtain ⟨a, ha⟩ := hbad
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    let a := bad.min' hne
    have ha : ¬Pass a := (Finset.mem_filter.mp (Finset.min'_mem bad hne)).2
    have hprior : ∀ b, b < a → Pass b := by
      intro b hba
      by_contra hb
      have hbmem : b ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
      exact (not_le_of_gt hba) (Finset.min'_le bad b hbmem)
    let count' := fun b => if b ≤ a then count b else 0
    let reduced' := fun b => BacktrackingGradient.step (initial b) (count' b)
    refine ⟨reduced', direction a (count a), direction, count', some a,
      ⟨fun _ => rfl, hd, happrox, ?_, ?_⟩⟩
    · intro b t ht
      by_cases hba : b ≤ a
      · exact (hr b).rejected t (by simpa only [count', ite_eq_left hba] using ht)
      · simp only [count', ite_eq_right hba, Nat.not_lt_zero] at ht
    · have hcounta : count' a = count a := by simp only [count', le_refl, ite_true]
      have hdrop := (hr a).exits.resolve_left ha
      refine ⟨by rw [hcounta], ?_, ?_, ?_, ?_⟩
      · simpa only [reduced', hcounta, reduced] using lt_of_not_ge ha
      · simpa only [reduced', hcounta, reduced, model] using hdrop
      · intro b hba
        have hcountb : count' b = count b := by simp only [count', ite_eq_left hba.le]
        simpa only [reduced', hcountb, reduced] using hprior b hba
      · intro b hab
        exact ite_eq_right (not_le.mpr hab)
  · have hpass : ∀ a, Pass a := by simpa only [not_exists, not_not] using hbad
    exact ⟨reduced, 0, direction, count, none,
      ⟨fun _ => rfl, hd, happrox, fun a => (hr a).rejected, hpass⟩⟩

end InexactRegularization
