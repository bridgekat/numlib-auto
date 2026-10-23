import Numlib.Optimization.HighOrder.ModelSolve.Reductions
import Numlib.Optimization.HighOrder.ModelSolve.Uniform
import Numlib.Optimization.Regularization.Inexact.Parameter

/-!
# Actual step calculations with inexact regularized tensor models

The step component records the model comparison, large-step exit or actual
criticality tests, and the actual tests behind every radius reduction. Candidate
points may change during approximate global minimization. No radius floor,
nonzero-step conclusion or objective decrease is a field of the component.
-/

namespace InexactRegularization
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The Step2 component records the actual comparison, computed criticality
checks and radius reductions. Candidate points may vary; orders one and two
never halve. The remaining steps of an outer execution are separate. -/
structure StepTwoComputation (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    (order : ι → ℕ) (σ θ ζ : ℝ) (ε : ι → ℝ) (reference : E)
    (initial : ι → ℝ) (s : E) (δ : ι → ℝ) : Prop where
  comparison : model A p σ s ≤ model A p σ reference
  result : (1 ≤ ‖s‖ ∧ δ = initial) ∨ (‖s‖ < 1 ∧
    ∃ (point direction : ι → ℕ → E) (count : ι → ℕ) (last : ι → E), ∀ a,
      (∀ t < count a, ‖point a t‖ ≤ 1) ∧
      ModelSolve.RadiusReductions (model A p σ) (order a) (ζ * θ * ε a) 1
        (point a) (direction a) (count a) ∧
      (order a ≤ 2 → count a = 0) ∧ δ a = BacktrackingGradient.step 1 (count a) ∧
      ‖last a‖ ≤ δ a ∧
      ζ * TaylorModel.criticality (model A p σ) (order a) s (δ a) ≤
        TaylorModel.decrement (model A p σ) (order a) s (last a) ∧
      TaylorModel.decrement (model A p σ) (order a) s (last a) ≤
        ζ * θ * ε a * δ a ^ order a / (order a).factorial)

/-- Every actual Step2 radius is positive and at most one when the inherited
large-step radii are, by positivity and monotonicity of geometric candidates. -/
theorem StepTwoComputation.radius_mem {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ}
    {order : ι → ℕ} {σ θ ζ : ℝ} {ε initial δ : ι → ℝ} {reference s : E}
    (h : StepTwoComputation A p order σ θ ζ ε reference initial s δ)
    (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1) (a : ι) :
    0 < δ a ∧ δ a ≤ 1 := by
  rcases h.result with ⟨_, rfl⟩ | ⟨_, point, direction, count, last, hr⟩
  · exact hinit a
  · rw [(hr a).2.2.2.1]
    exact ⟨BacktrackingGradient.step_pos zero_lt_one _,
      (BacktrackingGradient.step_antitone zero_le_one (Nat.zero_le _)).trans (by simp)⟩

/-- A genuinely improving reference and the actual comparison make a Step2
return nonzero. This conclusion is not a field of the component. -/
theorem StepTwoComputation.nonzero {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ}
    {order : ι → ℕ} {σ θ ζ : ℝ} {ε initial δ : ι → ℝ} {reference s : E}
    (h : StepTwoComputation A p order σ θ ζ ε reference initial s δ)
    (href : model A p σ reference < model A p σ 0) : s ≠ 0 := by
  intro hs
  exact (not_lt_of_ge (hs ▸ h.comparison)) href

/-- An actual small Step2 return satisfies normalized criticality after its
positive relative factor cancels from the two computed tests. -/
theorem StepTwoComputation.criticality {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ}
    {order : ι → ℕ} {σ θ ζ : ℝ} {ε initial δ : ι → ℝ} {reference s : E}
    (h : StepTwoComputation A p order σ θ ζ ε reference initial s δ)
    (hζ : 0 < ζ) (hs : ‖s‖ < 1) (a : ι) :
    TaylorModel.criticality (model A p σ) (order a) s (δ a) ≤
      θ * ε a * δ a ^ order a / (order a).factorial := by
  rcases h.result with ⟨hlarge, _⟩ | ⟨_, point, direction, count, last, hr⟩
  · exact (not_lt_of_ge hlarge hs).elim
  · have ha := hr a
    apply le_of_mul_le_mul_left (a := ζ) _ hζ
    calc _ ≤ TaylorModel.decrement (model A p σ) (order a) s (last a) := ha.2.2.2.2.2.1
      _ ≤ ζ * θ * ε a * δ a ^ order a / (order a).factorial := ha.2.2.2.2.2.2
      _ = _ := by ring

/-- Actual radius-reduction tests and analytic model bounds imply a radius
floor for every small Step2 computation, even with changing candidates. -/
theorem StepTwoComputation.radius_lower {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ}
    {order : ι → ℕ} {σ θ ζ B : ℝ} {ε initial δ : ι → ℝ} {reference s : E}
    (h : StepTwoComputation A p order σ θ ζ ε reference initial s δ)
    (hB : 0 < B) (hf : ContDiff ℝ p (model A p σ))
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p (model A p σ) u -
      iteratedFDeriv ℝ p (model A p σ) v‖ ≤ B * ‖u - v‖)
    (hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (model A p σ) x‖ ≤ B)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p) (hs : ‖s‖ < 1) (a : ι) :
    min (ζ * θ * ε a / (8 * B)) 1 ≤ δ a ∧
      (order a ≤ 2 → δ a = 1) := by
  rcases h.result with ⟨hlarge, _⟩ | ⟨_, point, direction, count, last, hr⟩
  · exact (not_lt_of_ge hlarge hs).elim
  · obtain ⟨hpoint, hred, hlow, hδ, _⟩ := hr a
    constructor
    · rw [hδ]
      exact hred.radius_lower (horder a).1 (horder a).2 hf hB.le hB le_rfl hlip
        (fun t ht n hn hnp => hder n (by have := (horder a).1; omega) hnp
          (point a t) (hpoint t ht)) zero_lt_one le_rfl
    · intro hj
      rw [hδ, hlow hj]
      simp

end General

section Existence
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- Exact global minimization is an allowed approximate solve. Coercivity,
compact attaining directions and finite actual Taylor tests construct its
Step2 component, including every radius-reduction test. -/
theorem exists_stepTwoComputation (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    {σ θ ζ D : ℝ} (hσ : 0 < σ) (hD : 0 ≤ D)
    (hA : ∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (reference : E) (initial : ι → ℝ) :
    ∃ (s : E) (δ : ι → ℝ),
      StepTwoComputation A p order σ θ ζ ε reference initial s δ := by
  obtain ⟨κ, hκ, hκ1, hsolve⟩ :=
    ModelSolve.exists_uniform_regularized_solve (E := E) (ι := ι) p hσ.le hD
  obtain ⟨s, hs, _, hcase⟩ := hsolve σ hσ le_rfl A hA θ ζ hθ hθ1 hζ hζ1
    order horder ε hε
  by_cases hlarge : 1 ≤ ‖s‖
  · exact ⟨s, initial, ⟨hs reference, Or.inl ⟨hlarge, rfl⟩⟩⟩
  · have hsmall : ‖s‖ < 1 := not_le.mp hlarge
    rcases hcase with hbad | ⟨d, N, hr⟩
    · exact (not_lt_of_ge hbad.le hsmall).elim
    · refine ⟨s, fun a => BacktrackingGradient.step 1 (N a),
        ⟨hs reference, Or.inr ⟨hsmall, (fun _ _ => s), d, N,
          (fun a => d a (N a)), ?_⟩⟩⟩
      intro a
      obtain ⟨hd, hrun, _, _, hlow⟩ := hr a
      exact ⟨fun _ _ => hsmall.le,
        hrun.toRadiusReductions (mul_pos (mul_pos hζ hθ) (hε a).1) zero_lt_one
          (fun t => (hd t).1) hs,
        hlow, rfl, (hd _).1, (hd _).2, hrun.passes⟩

/-- The radius floor for every permitted Step2 computation has a common
positive coefficient fixed before the model jet, bounded penalty parameter,
relative factors and requested accuracies. It is derived from the actual
radius-reduction tests, without assuming exact minimization in the execution. -/
theorem exists_uniform_stepTwo_radius_floor (p : ℕ) {S D : ℝ}
    (hS : 0 ≤ S) (hD : 0 ≤ D) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ σ : ℝ, 0 ≤ σ → σ ≤ S →
      ∀ A : FormalMultilinearSeries ℝ E ℝ,
        (∀ i, 2 ≤ i → i ≤ p → ‖A i‖ ≤ D) →
      ∀ (order : ι → ℕ), (∀ a, 0 < order a ∧ order a ≤ p) →
      ∀ θ ζ : ℝ, 0 < θ → θ ≤ 1 → 0 < ζ → ζ ≤ 1 →
      ∀ (ε initial δ : ι → ℝ), (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∀ reference s : E,
      StepTwoComputation A p order σ θ ζ ε reference initial s δ →
      ‖s‖ < 1 → ∀ a, κ * (ζ * θ * ε a) ≤ δ a ∧
        (order a ≤ 2 → δ a = 1) := by
  obtain ⟨B, hB, hbound⟩ :=
    ModelDecrease.exists_uniform_penalized_derivative_bound (E := E) p hS hD
  let κ := min (1 / (8 * B)) 1
  refine ⟨κ, lt_min (by positivity) zero_lt_one, min_le_right _ _, ?_⟩
  intro σ hσ hσS A hA order horder θ ζ hθ hθ1 hζ hζ1 ε initial δ hε reference s h hs a
  obtain ⟨hder, hlip⟩ := hbound σ hσ hσS A hA
  have hh := h.radius_lower hB (ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ)
    hlip hder horder hs a
  refine ⟨le_trans ?_ hh.1, hh.2⟩
  have hα : 0 ≤ ζ * θ * ε a := mul_nonneg (mul_nonneg hζ.le hθ.le) (hε a).1.le
  apply le_min
  · have hk := mul_le_mul_of_nonneg_right (min_le_left (1 / (8 * B)) 1) hα
    simpa only [div_mul_eq_mul_div, one_mul] using hk
  · apply (mul_le_of_le_one_left hα (min_le_right (1 / (8 * B)) 1)).trans
    have hzθ : ζ * θ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hζ1 hθ1 hθ.le zero_le_one
    simpa only [one_mul] using mul_le_mul hzθ (hε a).2 (hε a).1.le zero_le_one

end Existence

end InexactRegularization
