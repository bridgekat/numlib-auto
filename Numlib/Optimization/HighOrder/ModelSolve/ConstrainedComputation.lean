import Numlib.Optimization.HighOrder.ModelSolve.ConstrainedHalving
import Numlib.Optimization.Regularization.Constrained.ModelMinimum

/-!
# Primitive finite constrained model computations

Actual feasible changing candidates, halving guards, relative Taylor directions
and accepted decrement tests specify each radius calculation. A positive
fraction of the genuine feasible global gap specifies the model step. Radius
floors and true model criticality bounds are derived from those primitive tests.
-/

namespace ModelSolve
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- A completed finite feasible radius calculation. All inequalities describe
actual computed tests; no radius floor or derived criticality bound is a field. -/
structure FeasibleRadiusCalculation (m : E → ℝ) (C : Set E) (j : ℕ)
    (α ζ : ℝ) (s : E) (δ : ℝ) where
  point : ℕ → E
  direction : ℕ → E
  count : ℕ
  last : E
  point_norm : ∀ t < count, ‖point t‖ ≤ 1
  reductions : FeasibleRadiusReductions m C j α 1 point direction count
  first_order : j = 1 → count = 0
  final_radius : δ = BacktrackingGradient.step 1 count
  last_feasible : s + last ∈ C
  last_norm : ‖last‖ ≤ δ
  approximation : ζ * TaylorModel.constrainedCriticality m j C s δ ≤
    TaylorModel.decrement m j s last
  passes : TaylorModel.decrement m j s last ≤ α * δ ^ j / j.factorial

/-- Actual halving guards bound the returned radius below by the normalized
Taylor remainder threshold, even when intermediate candidates change. -/
theorem FeasibleRadiusCalculation.radius_lower {m : E → ℝ} {C : Set E}
    {p j : ℕ} {α ζ δ B : ℝ} {s : E}
    (r : FeasibleRadiusCalculation m C j α ζ s δ)
    (hj : 0 < j) (hjp : j ≤ p) (hB : 0 < B) (hf : ContDiff ℝ p m)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p m u - iteratedFDeriv ℝ p m v‖ ≤ B * ‖u - v‖)
    (hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n m x‖ ≤ B) : min (α / (8 * B)) 1 ≤ δ := by
  rw [r.final_radius]
  exact r.reductions.toRadiusReductions.radius_lower hj hjp hf hB.le hB le_rfl hlip
    (fun t ht n hn hnp => hder n (by omega) hnp (r.point t) (r.point_norm t ht))
    zero_lt_one le_rfl

/-- A primitive constrained detailed model step: positive feasible global gap
and either a strict large-step exit or actual finite per-order radius tests. -/
structure ConstrainedStepComputation (m : E → ℝ) (C : Set E) (order : ι → ℕ)
    (θ ζ : ℝ) (ε : ι → ℝ) (s : E) (δ : ι → ℝ) : Prop where
  fraction : ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ModelDecrease.ApproximateGlobalStepOn m C μ s
  result : (1 < ‖s‖ ∧ ∀ a, δ a = 1) ∨ (‖s‖ ≤ 1 ∧
    Nonempty (∀ a, FeasibleRadiusCalculation m C (order a) (ζ * θ * ε a) ζ s (δ a)))

/-- The positive feasible global-gap rule returns an actual feasible step. -/
theorem ConstrainedStepComputation.feasible {m : E → ℝ} {C : Set E} {order : ι → ℕ}
    {θ ζ : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : ConstrainedStepComputation m C order θ ζ ε s δ) : s ∈ C := by
  obtain ⟨μ, _, _, hm⟩ := h.fraction
  exact hm.1

/-- A primitive feasible global-gap return cannot increase the model when
zero is feasible. -/
theorem ConstrainedStepComputation.nonincrease {m : E → ℝ} {C : Set E} {order : ι → ℕ}
    {θ ζ : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : ConstrainedStepComputation m C order θ ζ ε s δ) (hzero : (0 : E) ∈ C) :
    m s ≤ m 0 := by
  obtain ⟨μ, _, _, hm⟩ := h.fraction
  exact hm.nonincrease hzero

/-- Every actual returned radius is positive and no larger than one. -/
theorem ConstrainedStepComputation.radius_mem {m : E → ℝ} {C : Set E} {order : ι → ℕ}
    {θ ζ : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : ConstrainedStepComputation m C order θ ζ ε s δ) (a : ι) :
    0 < δ a ∧ δ a ≤ 1 := by
  rcases h.result with ⟨_, hδ⟩ | ⟨_, ⟨r⟩⟩
  · rw [hδ a]
    exact ⟨zero_lt_one, le_rfl⟩
  · rw [(r a).final_radius]
    exact ⟨BacktrackingGradient.step_pos zero_lt_one _,
      (BacktrackingGradient.step_antitone zero_le_one (Nat.zero_le _)).trans (by simp)⟩

/-- The actual first-order no-halving policy retains the unit radius.
Higher orders are allowed genuinely adaptive radii. -/
theorem ConstrainedStepComputation.unit_radius {m : E → ℝ} {C : Set E} {order : ι → ℕ}
    {θ ζ : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : ConstrainedStepComputation m C order θ ζ ε s δ) (a : ι) (ha : order a = 1) :
    δ a = 1 := by
  rcases h.result with ⟨_, hδ⟩ | ⟨_, ⟨r⟩⟩
  · exact hδ a
  · rw [(r a).final_radius, (r a).first_order ha]
    simp

/-- Actual relative Taylor approximation and the final passing decrement test
imply normalized constrained model criticality on every short return. -/
theorem ConstrainedStepComputation.criticality {m : E → ℝ} {C : Set E} {order : ι → ℕ}
    {θ ζ : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : ConstrainedStepComputation m C order θ ζ ε s δ)
    (hζ : 0 < ζ) (hs : ‖s‖ ≤ 1) (a : ι) :
    TaylorModel.constrainedCriticality m (order a) C s (δ a) ≤
      θ * ε a * δ a ^ order a / (order a).factorial := by
  rcases h.result with ⟨hlarge, _⟩ | ⟨_, ⟨r⟩⟩
  · exact (not_lt_of_ge hs hlarge).elim
  · apply le_of_mul_le_mul_left (a := ζ) _ hζ
    convert (r a).approximation.trans (r a).passes using 1
    ring

/-- Every actual finite constrained computation retains its normalized radius
floor, from the genuine failed-test and insufficient-decrease guards. -/
theorem ConstrainedStepComputation.radius_lower {m : E → ℝ} {C : Set E}
    {p : ℕ} {order : ι → ℕ} {θ ζ B : ℝ} {ε δ : ι → ℝ} {s : E}
    (h : ConstrainedStepComputation m C order θ ζ ε s δ)
    (hB : 0 < B) (hf : ContDiff ℝ p m)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p m u - iteratedFDeriv ℝ p m v‖ ≤ B * ‖u - v‖)
    (hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n m x‖ ≤ B)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p) (hs : ‖s‖ ≤ 1) (a : ι) :
    min (ζ * θ * ε a / (8 * B)) 1 ≤ δ a := by
  rcases h.result with ⟨hlarge, _⟩ | ⟨_, ⟨r⟩⟩
  · exact (not_lt_of_ge hs hlarge).elim
  · exact (r a).radius_lower (horder a).1 (horder a).2 hB hf hlip hder

end ModelSolve

namespace ModelSolve
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

/-- A genuine constrained global minimum and finite feasible first-passing
Taylor loops construct every field of a detailed model computation. -/
theorem exists_constrained_stepComputation_of_isMinOn {m : E → ℝ} {p : ℕ}
    (hf : ContDiff ℝ p m) {B : ℝ} (hB : 0 < B)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p m u - iteratedFDeriv ℝ p m v‖ ≤ B * ‖u - v‖)
    (hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n m x‖ ≤ B)
    {C : Set E} (hC : IsClosed C) (hconv : Convex ℝ C)
    (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    {θ ζ : ℝ} (hθ : 0 < θ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) (s : E) (hsC : s ∈ C) (hmin : IsMinOn m C s) :
    ∃ δ : ι → ℝ, ConstrainedStepComputation m C order θ ζ ε s δ := by
  classical
  have hfrac : ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ModelDecrease.ApproximateGlobalStepOn m C μ s := by
    refine ⟨1, zero_lt_one, le_rfl, hsC, fun t ht => ?_⟩
    simpa only [one_mul] using sub_le_sub_left (hmin ht) (m 0)
  by_cases hs : 1 < ‖s‖
  · exact ⟨fun _ => 1, hfrac, Or.inl ⟨hs, fun _ => rfl⟩⟩
  · have hs1 : ‖s‖ ≤ 1 := not_lt.mp hs
    have hall := fun a => exists_attaining_constrained_criticalHalvingRun
      (horder a).1 (horder a).2 hf hB.le hB le_rfl
      (mul_pos (mul_pos hζ hθ) (hε a)) hζ1 hlip hC hconv s hsC hmin
      (fun n hn hnp => hder n (by have := (horder a).1; omega) hnp s hs1)
      zero_lt_one le_rfl
    choose d N hd using hall
    refine ⟨fun a => BacktrackingGradient.step 1 (N a), hfrac, Or.inr ⟨hs1, ⟨?_⟩⟩⟩
    intro a
    obtain ⟨hdir, hr, _, _, hlow⟩ := hd a
    exact {
      point := fun _ => s
      direction := d a
      count := N a
      last := d a (N a)
      point_norm := fun _ _ => hs1
      reductions := hr.toFeasibleRadiusReductions (mul_pos (mul_pos hζ hθ) (hε a))
        zero_lt_one (fun t => (hdir t).2.1) (fun t => (hdir t).1) hsC hmin
      first_order := hlow
      final_radius := rfl
      last_feasible := (hdir _).1
      last_norm := (hdir _).2.1
      approximation := (hdir _).2.2
      passes := hr.passes }

end ModelSolve
