import Numlib.Optimization.Composite.Origin
import Numlib.Optimization.Regularization.HighOrder.CriticalityRun

/-!
# Primitive composite adaptive regularization executions

The computation uses actual generalized Taylor directions, a positive fraction
of the global model gap, actual objective ratios and accepted point and radius
updates. True approximate optimality and the literal zero-decrease return are
separate targets. No decrease floor or evaluation budget is an execution field.
-/

namespace Composite
open InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composite computations share the exact high-order regularization settings. -/
abbrev Settings := HighOrderRegularization.Settings

/-- Actual scalar, residual and model direction data for a composite execution. -/
structure ExecutionData (E : Type*) (q : ℕ) extends
    HighOrderRegularization.ExecutionData E q where
  fraction : ℕ → ℝ
  modelDirection : ℕ → Fin q → E

/-- The actual generalized Taylor tests used to select a failing order. -/
structure OptimalityCheck (f : E → ℝ) (c : E → F) (h : F → ℝ)
    {q : ℕ} (ζ : ℝ) (ε δ : Fin q → ℝ) (x : E)
    (direction : Fin q → E) (selected : Option (Fin q)) : Prop where
  feasible : ∀ a, ‖direction a‖ ≤ δ a
  approximation : ∀ a, ζ * criticality f c h (modelOrder a) x (δ a) ≤
    decrement f c h (modelOrder a) x (direction a)
  passed : selected = none → ∀ a, decrement f c h (modelOrder a) x (direction a) ≤
    ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial
  failed : ∀ a, selected = some a →
    ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial <
      decrement f c h (modelOrder a) x (direction a)

/-- A returned detailed model solve satisfies the primitive global-gap rule and
actual computed model tests when its step norm is strictly less than one. -/
structure StepOutput (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ)
    {q : ℕ} (θ ζ : ℝ) (ε : Fin q → ℝ) (x s : E) (σ μ : ℝ)
    (δ : Fin q → ℝ) (direction : Fin q → E) : Prop where
  fraction_pos : 0 < μ
  fraction_le_one : μ ≤ 1
  global_gap : ModelDecrease.ApproximateGlobalStep (regularizedModel f c h p x σ) μ s
  radius_mem : ∀ a, 0 < δ a ∧ δ a ≤ 1
  tests : ‖s‖ < 1 → ∀ a, ‖direction a‖ ≤ δ a ∧
    ζ * criticality (smoothModel f p x σ) (residualModel c p x) h
      (modelOrder a) s (δ a) ≤
        decrement (smoothModel f p x σ) (residualModel c p x) h
          (modelOrder a) s (direction a) ∧
    decrement (smoothModel f p x σ) (residualModel c p x) h
      (modelOrder a) s (direction a) ≤
        ζ * θ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial

/-- True generalized approximate optimality at a vector of legal radii. -/
def OptimalityAt {q : ℕ} (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (ε : Fin q → ℝ) (x : E) (δ : Fin q → ℝ) : Prop :=
  (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧ ∀ a,
    criticality f c h (modelOrder a) x (δ a) ≤
      ε a * δ a ^ modelOrder a / (modelOrder a).factorial

/-- A target is true approximate optimality at inherited radii, or the literal
zero-decrease model return, whose true optimality is proved separately. -/
def TargetAt {p q : ℕ} (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (_P : Settings p q) (ε : Fin q → ℝ) (D : ExecutionData E q) (k : ℕ) : Prop :=
  OptimalityAt f c h ε (D.point k) (D.radius k) ∨
    (D.selected k ≠ none ∧ regularizedModel f c h p (D.point k) (D.parameter k) 0 =
      regularizedModel f c h p (D.point k) (D.parameter k) (D.step k))

/-- A finite actual detailed composite execution prefix, including its endpoint
check. Continuing trials strictly improve the model and use actual ratios. -/
structure Run {p q : ℕ} (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (P : Settings p q) (ε : Fin q → ℝ) (D : ExecutionData E q) (N : ℕ) : Prop where
  accuracy_pos : ∀ a, 0 < ε a
  accuracy_le_one : ∀ a, ε a ≤ 1
  initial_parameter : D.parameter 0 = P.sigmaInitial
  initial_radii : ∀ a, 0 < D.radius 0 a ∧ D.radius 0 a ≤ 1
  modelTrace : ModelTrace f c h p D.point D.step D.parameter D.ratio P.eta1 P.eta2
    P.gamma1 P.gamma2 P.gamma3 P.sigmaMin N
  check : ∀ k ≤ N, OptimalityCheck f c h P.zeta ε (D.radius k) (D.point k)
    (D.direction k) (D.selected k)
  step_two : ∀ k ≤ N, D.selected k ≠ none → StepOutput f c h p P.theta P.zeta ε
    (D.point k) (D.step k) (D.parameter k) (D.fraction k)
    (D.solvedRadius k) (D.modelDirection k)
  continues : ∀ k < N, D.selected k ≠ none
  point_update : ∀ k < N, D.point (k + 1) =
    if P.eta1 ≤ D.ratio k then D.point k + D.step k else D.point k
  radius_update : ∀ k < N, D.radius (k + 1) =
    if P.eta1 ≤ D.ratio k then D.solvedRadius k else D.radius k

/-- A passed computed objective check implies true generalized optimality. -/
theorem OptimalityCheck.optimality_of_none {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {q : ℕ} {ζ : ℝ} {ε δ : Fin q → ℝ} {x : E} {direction : Fin q → E}
    {selected : Option (Fin q)} (hc : OptimalityCheck f c h ζ ε δ x direction selected)
    (hζ : 0 < ζ) (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1) (hs : selected = none) :
    OptimalityAt f c h ε x δ := by
  refine ⟨hδ, fun a => ?_⟩
  have hh := (hc.approximation a).trans (hc.passed hs a)
  apply le_of_mul_le_mul_left (a := ζ) _ hζ
  convert hh using 1
  ring

/-- Primitive global-gap comparison implies nonincrease of the actual model. -/
theorem StepOutput.nonincrease {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p q : ℕ} {θ ζ σ μ : ℝ} {ε δ : Fin q → ℝ} {x s : E} {d : Fin q → E}
    (ho : StepOutput f c h p θ ζ ε x s σ μ δ d) :
    regularizedModel f c h p x σ s ≤ regularizedModel f c h p x σ 0 := by
  have hh := ho.global_gap 0
  simpa only [sub_self, mul_zero, sub_nonneg] using hh

/-- The two actual computed model inequalities imply normalized model criticality. -/
theorem StepOutput.criticality_le {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p q : ℕ} {θ ζ σ μ : ℝ} {ε δ : Fin q → ℝ} {x s : E} {d : Fin q → E}
    (ho : StepOutput f c h p θ ζ ε x s σ μ δ d) (hζ : 0 < ζ)
    (hs : ‖s‖ < 1) (a : Fin q) :
    criticality (smoothModel f p x σ) (residualModel c p x) h (modelOrder a) s (δ a) ≤
      θ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by
  have hh := (ho.tests hs a).2.1.trans (ho.tests hs a).2.2
  apply le_of_mul_le_mul_left (a := ζ) _ hζ
  convert hh using 1
  ring

/-- Genuine global model minimizers construct permitted detailed returns with
unit first-order convex radii and the fixed source radius floor. -/
theorem exists_stepOutput [FiniteDimensional ℝ E] (f : E → ℝ) (c : E → F)
    {h : F → ℝ} {p q : ℕ} (hqp : q ≤ p) {Df Dc σ θ ζ : ℝ} {K : NNReal}
    (hDf : 1 ≤ Df) (hDc : 0 ≤ Dc) (hσ : 0 < σ) (hh : LipschitzWith K h)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (x : E) (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (hAf : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Df)
    (hAc : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Dc) :
    ∃ (s : E) (μ : ℝ) (δ : Fin q → ℝ) (d : Fin q → E),
      StepOutput f c h p θ ζ ε x s σ μ δ d ∧
      (∀ a, modelOrder a = 1 → ConvexOn ℝ Set.univ h → δ a = 1) ∧
      ∀ a, ζ * θ / (8 * (3 * (Df + (K : ℝ) * Dc) + σ)) * ε a ≤ δ a := by
  obtain ⟨s, δ, d, hmin, hδ, hone, hfloor, htest⟩ :=
    exists_minimizer_with_criticality f c p modelOrder
      (fun a => ⟨by unfold modelOrder; omega,
        (Nat.succ_le_of_lt a.isLt).trans hqp⟩)
      hDf hDc hσ hh hθ hθ1 hζ hζ1 x ε hε hAf hAc
  refine ⟨s, 1, δ, d, ⟨by norm_num, le_rfl, ?_, hδ, fun hs => htest hs.le⟩,
    hone, hfloor⟩
  intro t
  simpa only [one_mul] using sub_le_sub_left (hmin t) _

namespace Run
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
  {P : Settings p q} {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- A shorter prefix retains all actual computation and update rules. -/
theorem restrict (hr : Run f c h P ε D N) {M : ℕ} (hM : M ≤ N) :
    Run f c h P ε D M where
  accuracy_pos := hr.accuracy_pos
  accuracy_le_one := hr.accuracy_le_one
  initial_parameter := hr.initial_parameter
  initial_radii := hr.initial_radii
  modelTrace := {
    updates := { hr.modelTrace.updates with
      update := fun k hk => hr.modelTrace.updates.update k (hk.trans_le hM) }
    improvement := fun k hk => hr.modelTrace.improvement k (hk.trans_le hM)
    ratio := fun k hk => hr.modelTrace.ratio k (hk.trans_le hM) }
  check := fun k hk => hr.check k (hk.trans hM)
  step_two := fun k hk => hr.step_two k (hk.trans hM)
  continues := fun k hk => hr.continues k (hk.trans_le hM)
  point_update := fun k hk => hr.point_update k (hk.trans_le hM)
  radius_update := fun k hk => hr.radius_update k (hk.trans_le hM)

/-- Every inherited actual radius remains positive and at most one. -/
theorem radius_mem (hr : Run f c h P ε D N) {k : ℕ} (hk : k ≤ N) (a : Fin q) :
    0 < D.radius k a ∧ D.radius k a ≤ 1 := by
  induction k with
  | zero => exact hr.initial_radii a
  | succ k ih =>
    have hkN : k < N := by omega
    rw [hr.radius_update k hkN]
    split_ifs
    · exact (hr.step_two k hkN.le (hr.continues k hkN)).radius_mem a
    · exact ih hkN.le

/-- A passed computed endpoint check supplies a true inherited-radius target. -/
theorem target_of_none (hr : Run f c h P ε D N) {k : ℕ} (hk : k ≤ N)
    (hs : D.selected k = none) : TargetAt f c h P ε D k :=
  Or.inl ((hr.check k hk).optimality_of_none P.zeta_pos (hr.radius_mem hk) hs)

end Run
end Composite
