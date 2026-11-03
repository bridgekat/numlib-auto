import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import NumlibSurface.ConnGouldToint.Chapter15.Section05

/-! # State transitions for the SQP filter algorithms -/

open ConnGouldToint.Chapter06 Optimization
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Parameters shared by the composite and single-step filter algorithms.
The contraction factor is strictly below one on rejected trials. -/
structure FilterSQPParams where
  γ₀ : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  η₁ : ℝ
  η₂ : ℝ
  margin : ℝ
  switchFactor : ℝ
  lower_pos : 0 < γ₀
  lower_lt_upper : γ₀ < γ₁
  rejection_contracts : γ₁ < 1
  expansion : 1 ≤ γ₂
  acceptance_pos : 0 < η₁
  acceptance_order : η₁ ≤ η₂
  acceptance_lt_one : η₂ < 1
  margin_range : margin ∈ Set.Ioo 0 1
  switch_range : switchFactor ∈ Set.Ioo 0 1

/-- The primal iterate, radius, model data, and filter kept between iterations. -/
structure FilterSQPState (E ι : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  x : E
  radius : ℝ
  multiplier : ι → ℝ
  B : E →L[ℝ] E
  W : ι → E →L[ℝ] E
  entries : Set (ℝ × ℝ)

/-- Step 0 starts with an empty filter. -/
def FilterSQPState.initial (x : E) (Δ : ℝ) (y : ι → ℝ)
    (B : E →L[ℝ] E) (W : ι → E →L[ℝ] E) : FilterSQPState E ι :=
  ⟨x, Δ, y, B, W, ∅⟩

/-- The filter chapter uses the plus-multiplier Lagrangian convention. -/
noncomputable def filterSQPModel [Fintype ι] [CompleteSpace E] (f : E → ℝ)
    (state : FilterSQPState E ι) (s : E) : ℝ :=
  let H := state.B + ∑ i, state.multiplier i • state.W i
  quadraticModel (f state.x) (gradient f state.x) H.toLinearMap s

/-- The trust-region and linearized-constraint tests of TRQP. -/
def filterSQPFeasible [CompleteSpace E] (eq : ι → Bool) (c : ι → E → ℝ)
    (state : FilterSQPState E ι) (s : E) : Prop :=
  ‖s‖ ≤ state.radius ∧
    sqpFilterLinearFeasible eq (fun i ↦ c i state.x) (fun i ↦ gradient (c i) state.x) s

/-- A trial must pass the filter and current-pair tests. When the
switching test holds it must also have a valid acceptable ratio. -/
def filterSQPAccepted (P : FilterSQPParams) (F : Set (ℝ × ℝ))
    (current trial : ℝ × ℝ) (pred ratio : ℝ) : Prop :=
  sqpFilterAccepts P.margin F trial ∧ sqpFilterAcceptsPair P.margin trial current ∧
    (sqpFilterSwitching P.switchFactor current.1 pred → 0 < pred ∧ P.η₁ ≤ ratio)

private noncomputable def filterSQPRatio (pair : E → ℝ × ℝ) (x s : E) (pred : ℝ) : ℝ :=
  if 0 < pred then ((pair x).2 - (pair (x + s)).2) / pred else 0

private def filterSQPModelDataValid (state : FilterSQPState E ι) : Prop :=
  state.B.toLinearMap.IsSymmetric ∧ ∀ i, (state.W i).toLinearMap.IsSymmetric

/-- The shared restoration, rejection, and acceptance transitions. A zero
or negative prediction cannot certify an objective step. An accepted
feasibility step below the ratio threshold uses the shrink interval. -/
inductive FilterSQPStep (P : FilterSQPParams) (pair : E → ℝ × ℝ)
    (compatible : FilterSQPState E ι → Prop)
    (trial : FilterSQPState E ι → E → Prop) (prediction : FilterSQPState E ι → E → ℝ)
    (state : FilterSQPState E ι) : Option (FilterSQPState E ι) → Prop
  | restored (next : FilterSQPState E ι)
      (incompatible : ¬ compatible state)
      (entries : next.entries = sqpFilterInsert state.entries (pair state.x))
      (acceptable : sqpFilterAccepts P.margin next.entries (pair next.x))
      (radius_pos : 0 < next.radius) (ready : compatible next)
      (model_data : filterSQPModelDataValid next) :
      FilterSQPStep P pair compatible trial prediction state (some next)
  | restoration_failed
      (incompatible : ¬ compatible state)
      (impossible : ¬ ∃ next, next.entries = sqpFilterInsert state.entries (pair state.x) ∧
        sqpFilterAccepts P.margin next.entries (pair next.x) ∧
        0 < next.radius ∧ compatible next ∧ filterSQPModelDataValid next) :
      FilterSQPStep P pair compatible trial prediction state none
  | rejected (s : E) (Δ' : ℝ)
      (ready : compatible state) (feasible_trial : trial state s)
      (rejected : ¬ filterSQPAccepted P state.entries (pair state.x) (pair (state.x + s))
        (prediction state s) (filterSQPRatio pair state.x s (prediction state s)))
      (radius_update : sqpFilterRadiusUpdate P.γ₀ P.γ₁ P.γ₂ P.η₁ P.η₂
        (filterSQPRatio pair state.x s (prediction state s)) state.radius Δ' false) :
      FilterSQPStep P pair compatible trial prediction state (some { state with radius := Δ' })
  | accepted (s : E) (next : FilterSQPState E ι)
      (ready : compatible state) (feasible_trial : trial state s)
      (accepted : filterSQPAccepted P state.entries (pair state.x) (pair (state.x + s))
        (prediction state s) (filterSQPRatio pair state.x s (prediction state s)))
      (iterate_update : next.x = state.x + s)
      (entries : next.entries =
        open Classical in
        if sqpFilterSwitching P.switchFactor (pair state.x).1 (prediction state s) then
          state.entries else sqpFilterInsert state.entries (pair state.x))
      (radius_update : sqpFilterRadiusUpdate P.γ₀ P.γ₁ P.γ₂ P.η₁ P.η₂
        (filterSQPRatio pair state.x s (prediction state s)) state.radius next.radius true)
      (model_data : filterSQPModelDataValid next) :
      FilterSQPStep P pair compatible trial prediction state (some next)

private noncomputable def filterSQPPair [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ)
    (eq : ι → Bool) (x : E) : ℝ × ℝ :=
  (sqpFilterViolation eq (fun i ↦ c i x), f x)

private def filterSQPNormal [CompleteSpace E] (eq : ι → Bool) (c : ι → E → ℝ)
    (κΔ κμ μ : ℝ) (state : FilterSQPState E ι) (n : E) : Prop :=
  sqpFilterCompatible eq (fun i ↦ c i state.x) (fun i ↦ gradient (c i) state.x)
    n κΔ κμ state.radius μ

/-- Algorithm 15.5.1 uses a compatible normal step and the
tangential model-decrease requirement AA.1m. -/
def compositeFilterSQPStep [Fintype ι] [CompleteSpace E]
    (P : FilterSQPParams) (f : E → ℝ) (c : ι → E → ℝ) (eq : ι → Bool)
    (κΔ κμ μ κT : ℝ) (state : FilterSQPState E ι) (next : Option (FilterSQPState E ι)) : Prop :=
  FilterSQPStep P (filterSQPPair f c eq)
    (fun a ↦ ∃ n, filterSQPNormal eq c κΔ κμ μ a n)
    (fun a s ↦ filterSQPFeasible eq c a s ∧ ∃ n, filterSQPNormal eq c κΔ κμ μ a n ∧
      let χ := sqpFilterCriticality eq (fun i ↦ c i a.x) (fun i ↦ gradient (c i) a.x)
        (gradient f (a.x + n)) n
      let H := a.B + ∑ i, a.multiplier i • a.W i
      κT * χ * min (χ / (1 + ‖H‖)) a.radius ≤ filterSQPModel f a n - filterSQPModel f a s)
    (fun a s ↦ filterSQPModel f a 0 - filterSQPModel f a s) state next

/-- Algorithm 15.5.2 replaces normal-step compatibility by feasibility
of the full subproblem, and uses (15.5.45) for the chosen trial. -/
def singleFilterSQPStep [Fintype ι] [CompleteSpace E]
    (P : FilterSQPParams) (f : E → ℝ) (c : ι → E → ℝ) (eq : ι → Bool)
    (π : E → ℝ) (ε : ℝ) (state : FilterSQPState E ι) (next : Option (FilterSQPState E ι)) : Prop :=
  FilterSQPStep P (filterSQPPair f c eq)
    (fun a ↦ ∃ s, filterSQPFeasible eq c a s)
    (fun a s ↦ filterSQPFeasible eq c a s ∧
      ε * min (π a.x) a.radius ≤ filterSQPModel f a 0 - filterSQPModel f a s)
    (fun a s ↦ filterSQPModel f a 0 - filterSQPModel f a s) state next

/-- A continued iteration leaves an iterate that passes the filter at
the start of its next iteration. -/
theorem FilterSQPStep.accepts_next {P : FilterSQPParams} {pair : E → ℝ × ℝ}
    {compatible : FilterSQPState E ι → Prop} {trial : FilterSQPState E ι → E → Prop}
    {prediction : FilterSQPState E ι → E → ℝ} {state next : FilterSQPState E ι}
    (hstep : FilterSQPStep P pair compatible trial prediction state (some next))
    (hstate : sqpFilterAccepts P.margin state.entries (pair state.x)) :
    sqpFilterAccepts P.margin next.entries (pair next.x) := by
  cases hstep with
  | restored next _ _ h _ _ _ => exact h
  | rejected => exact hstate
  | accepted s next _ _ ha hx hF _ _ =>
    rw [hx, hF]
    split
    · exact ha.1
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with he | hz
      · exact he.symm ▸ ha.2.1
      · exact ha.1 z hz.1

/-- A transition from an incompatible iterate must be restoration.
A continued restoration cannot be followed by another restoration. -/
theorem FilterSQPStep.compatible_of_restored {P : FilterSQPParams} {pair : E → ℝ × ℝ}
    {compatible : FilterSQPState E ι → Prop} {trial : FilterSQPState E ι → E → Prop}
    {prediction : FilterSQPState E ι → E → ℝ} {state next : FilterSQPState E ι}
    (hstep : FilterSQPStep P pair compatible trial prediction state (some next))
    (h : ¬ compatible state) : compatible next := by
  cases hstep with
  | restored next _ _ _ _ hr _ => exact hr
  | rejected _ _ hr => exact (h hr).elim
  | accepted _ _ hr => exact (h hr).elim

end ConnGouldToint.Chapter15
