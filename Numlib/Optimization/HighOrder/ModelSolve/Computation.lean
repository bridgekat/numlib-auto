import Numlib.Optimization.HighOrder.ModelSolve.Reductions
import Numlib.Optimization.Regularization.GlobalStep

/-!
# Primitive finite high-order model computations

Approximate global model minimization, actual computed Taylor tests and the
actual tests permitting each radius halving define this component. Candidate
points may change. Radius floors, model decrease and true objective criticality
are consequences rather than fields of the computation.
-/

namespace ModelSolve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The actual model-solve and radius-loop component of a high-order method.
The strict large-step exit retains all criticality checks at norm exactly one.
First- and second-order radii never halve. -/
structure StepComputation (m : E → ℝ) (order : ι → ℕ) (θ ζ : ℝ)
    (ε : ι → ℝ) (s : E) (δ : ι → ℝ) : Prop where
  fraction : ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ModelDecrease.ApproximateGlobalStep m μ s
  result : (1 < ‖s‖ ∧ ∀ a, δ a = 1) ∨ (‖s‖ ≤ 1 ∧
    ∃ (point direction : ι → ℕ → E) (count : ι → ℕ) (last : ι → E), ∀ a,
      (∀ t < count a, ‖point a t‖ ≤ 1) ∧
      RadiusReductions m (order a) (ζ * θ * ε a) 1
        (point a) (direction a) (count a) ∧
      (order a ≤ 2 → count a = 0) ∧ δ a = BacktrackingGradient.step 1 (count a) ∧
      ‖last a‖ ≤ δ a ∧
      ζ * TaylorModel.criticality m (order a) s (δ a) ≤
        TaylorModel.decrement m (order a) s (last a) ∧
      TaylorModel.decrement m (order a) s (last a) ≤
        ζ * θ * ε a * δ a ^ order a / (order a).factorial)

/-- Every actual positive-fraction approximate global solve has nonpositive
model change, by comparison with the zero displacement. -/
theorem StepComputation.nonincrease {m : E → ℝ} {order : ι → ℕ} {θ ζ : ℝ}
    {ε δ : ι → ℝ} {s : E} (h : StepComputation m order θ ζ ε s δ) : m s ≤ m 0 := by
  obtain ⟨μ, _, _, hm⟩ := h.fraction
  have hh := hm 0
  simpa only [sub_self, mul_zero, sub_nonneg] using hh

/-- Every actual returned radius is positive and at most one. -/
theorem StepComputation.radius_mem {m : E → ℝ} {order : ι → ℕ} {θ ζ : ℝ}
    {ε δ : ι → ℝ} {s : E} (h : StepComputation m order θ ζ ε s δ) (a : ι) :
    0 < δ a ∧ δ a ≤ 1 := by
  rcases h.result with ⟨_, hlarge⟩ | ⟨_, point, direction, count, last, hr⟩
  · rw [hlarge a]
    exact ⟨zero_lt_one, le_rfl⟩
  · rw [(hr a).2.2.2.1]
    exact ⟨BacktrackingGradient.step_pos zero_lt_one _,
      (BacktrackingGradient.step_antitone zero_le_one (Nat.zero_le _)).trans (by simp)⟩

/-- First- and second-order radii equal one on both return branches. -/
theorem StepComputation.unit_radius {m : E → ℝ} {order : ι → ℕ} {θ ζ : ℝ}
    {ε δ : ι → ℝ} {s : E} (h : StepComputation m order θ ζ ε s δ)
    (a : ι) (ha : order a ≤ 2) : δ a = 1 := by
  rcases h.result with ⟨_, hlarge⟩ | ⟨_, point, direction, count, last, hr⟩
  · exact hlarge a
  · rw [(hr a).2.2.2.1, (hr a).2.2.1 ha]
    simp

/-- The two actual computed Taylor tests imply normalized model criticality
on every short-step return, after cancellation of the positive relative factor. -/
theorem StepComputation.criticality {m : E → ℝ} {order : ι → ℕ} {θ ζ : ℝ}
    {ε δ : ι → ℝ} {s : E} (h : StepComputation m order θ ζ ε s δ)
    (hζ : 0 < ζ) (hs : ‖s‖ ≤ 1) (a : ι) :
    TaylorModel.criticality m (order a) s (δ a) ≤
      θ * ε a * δ a ^ order a / (order a).factorial := by
  rcases h.result with ⟨hlarge, _⟩ | ⟨_, point, direction, count, last, hr⟩
  · exact (not_lt_of_ge hs hlarge).elim
  · apply le_of_mul_le_mul_left (a := ζ) _ hζ
    have hh := (hr a).2.2.2.2.2.1.trans (hr a).2.2.2.2.2.2
    convert hh using 1
    ring

/-- The actual failed-test and insufficient-decrease guards derive the radius
floor even when successive model candidates differ. -/
theorem StepComputation.radius_lower {m : E → ℝ} {p : ℕ} {order : ι → ℕ} {θ ζ B : ℝ}
    {ε δ : ι → ℝ} {s : E} (h : StepComputation m order θ ζ ε s δ)
    (hB : 0 < B) (hf : ContDiff ℝ p m)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p m u - iteratedFDeriv ℝ p m v‖ ≤ B * ‖u - v‖)
    (hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n m x‖ ≤ B)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p) (hs : ‖s‖ ≤ 1) (a : ι) :
    min (ζ * θ * ε a / (8 * B)) 1 ≤ δ a := by
  rcases h.result with ⟨hlarge, _⟩ | ⟨_, point, direction, count, last, hr⟩
  · exact (not_lt_of_ge hs hlarge).elim
  · rw [(hr a).2.2.2.1]
    exact (hr a).2.1.radius_lower (horder a).1 (horder a).2 hf hB.le hB le_rfl hlip
      (fun t ht n hn hnp => hder n (by have := (horder a).1; omega) hnp
        (point a t) ((hr a).1 t ht)) zero_lt_one le_rfl

/-- An actual global model minimum and finite first-passing criticality
loops construct every primitive field of a model computation. -/
theorem exists_stepComputation_of_isMin {m : E → ℝ} {p : ℕ}
    (hf : ContDiff ℝ p m) {B : ℝ} (hB : 0 < B)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p m u - iteratedFDeriv ℝ p m v‖ ≤ B * ‖u - v‖)
    (hder : ∀ n, 2 ≤ n → n ≤ p → ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n m x‖ ≤ B)
    (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    {θ ζ : ℝ} (hθ : 0 < θ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) (s : E) (hmin : ∀ t, m s ≤ m t)
    [FiniteDimensional ℝ E] :
    ∃ δ : ι → ℝ, StepComputation m order θ ζ ε s δ := by
  classical
  have hfrac : ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ModelDecrease.ApproximateGlobalStep m μ s := by
    refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro t
    simpa only [one_mul] using sub_le_sub_left (hmin t) (m 0)
  by_cases hs : 1 < ‖s‖
  · exact ⟨fun _ => 1, hfrac, Or.inl ⟨hs, fun _ => rfl⟩⟩
  · have hs1 : ‖s‖ ≤ 1 := not_lt.mp hs
    have hall := fun a => exists_attaining_criticalHalvingRun (horder a).1 (horder a).2
      hf hB.le hB le_rfl (mul_pos (mul_pos hζ hθ) (hε a)) hζ1 hlip s hmin
      (fun n hn hnp => hder n (by have := (horder a).1; omega) hnp s hs1)
      zero_lt_one le_rfl
    choose d N hd using hall
    refine ⟨fun a => BacktrackingGradient.step 1 (N a), hfrac,
      Or.inr ⟨hs1, (fun _ _ => s), d, N, (fun a => d a (N a)), ?_⟩⟩
    intro a
    obtain ⟨hdir, hrun, _, _, hlow⟩ := hd a
    exact ⟨fun _ _ => hs1, hrun.toRadiusReductions
      (mul_pos (mul_pos hζ hθ) (hε a)) zero_lt_one (fun t => (hdir t).1) hmin,
      hlow, rfl, (hdir _).1, (hdir _).2, hrun.passes⟩

end ModelSolve
