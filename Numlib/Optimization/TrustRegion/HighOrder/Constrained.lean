import Numlib.Optimization.TrustRegion.HighOrder.Radius
import Numlib.Optimization.Constrained.FirstOrderCriticality
import Numlib.Optimization.EvaluationComplexity.Updates

/-!
# Trust-region trials on simple feasible sets

The Taylor criticality computations optimize over actual feasible displacement
balls. Directions, trial points, ratios and radius updates are checked directly.
An unrestricted trial whose testing balls and selected step are feasible induces
one of these constrained trials.
-/

namespace HighOrderTrustRegion
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One nonterminal constrained trust-region trial, with genuine constrained
Taylor criticality and actual objective acceptance and radius updates. -/
structure ConstrainedTrial {q : ℕ} (f : E → ℝ) (X : Set E) (P : Parameters q)
    (x : E) (Δ : ℝ) (d : Fin q → E) (j : Fin q) (s xnext : E)
    (Δnext ρ : ℝ) : Prop where
  current_feasible : x ∈ X
  radius_pos : 0 < Δ
  direction_norm : ∀ a, a ≤ j → ‖d a‖ ≤ optimalityRadius P Δ
  direction_feasible : ∀ a, a ≤ j → x + d a ∈ X
  approximation : ∀ a, a ≤ j → P.zeta *
    TaylorModel.constrainedCriticality f (modelOrder a) X x (optimalityRadius P Δ) ≤
      TaylorModel.decrement f (modelOrder a) x (d a)
  earlier_tests : ∀ a, a < j → TaylorModel.decrement f (modelOrder a) x (d a) ≤
    P.zeta * P.accuracy a * optimalityRadius P Δ ^ modelOrder a /
      (modelOrder a).factorial
  failed_test : P.zeta * P.accuracy j * optimalityRadius P Δ ^ modelOrder j /
    (modelOrder j).factorial < TaylorModel.decrement f (modelOrder j) x (d j)
  step_norm : ‖s‖ ≤ Δ
  step_feasible : x + s ∈ X
  model_comparison : TaylorModel.decrement f (modelOrder j) x (d j) ≤
    TaylorModel.decrement f (modelOrder j) x s
  ratio : ρ = (f x - f (x + s)) / TaylorModel.decrement f (modelOrder j) x s
  point_update : xnext = if P.eta1 ≤ ρ then x + s else x
  radius_update :
    if P.eta2 ≤ ρ then Δnext ∈ Icc Δ (min P.radiusMax (P.gamma3 * Δ))
    else if P.eta1 ≤ ρ then Δnext ∈ Icc (P.gamma2 * Δ) Δ
    else Δnext ∈ Icc (P.gamma1 * Δ) (P.gamma2 * Δ)

/-- Feasibility of an entire testing ball transfers an actual unrestricted
trial to the constrained algorithm without changing any numerical checks. -/
theorem Trial.constrained_of_ball {q : ℕ} {f : E → ℝ} {X : Set E}
    {P : Parameters q} {x s xnext : E} {Δ Δnext ρ : ℝ}
    {d : Fin q → E} {j : Fin q}
    (h : Trial f P x Δ d j s xnext Δnext ρ) (hx : x ∈ X)
    (hb : ∀ v, ‖v‖ ≤ optimalityRadius P Δ → x + v ∈ X)
    (hs : x + s ∈ X) : ConstrainedTrial f X P x Δ d j s xnext Δnext ρ where
  current_feasible := hx
  radius_pos := h.radius_pos
  direction_norm := h.direction_feasible
  direction_feasible := fun a ha => hb _ (h.direction_feasible a ha)
  approximation := by
    intro a ha
    rw [TaylorModel.constrainedCriticality_eq_of_ball hb]
    exact h.approximation a ha
  earlier_tests := h.earlier_tests
  failed_test := h.failed_test
  step_norm := h.step_feasible
  step_feasible := hs
  model_comparison := h.model_comparison
  ratio := h.ratio
  point_update := h.point_update
  radius_update := h.radius_update

/-- A finite nonterminal constrained trust-region execution. All fields are
initialization or individual operational trial checks. -/
structure ConstrainedRun {q : ℕ} (f : E → ℝ) (X : Set E) (P : Parameters q)
    (x s : ℕ → E) (d : ℕ → Fin q → E) (j : ℕ → Fin q)
    (Δ ρ : ℕ → ℝ) (N : ℕ) : Prop where
  initial_radius_pos : 0 < Δ 0
  initial_radius_le_max : Δ 0 ≤ P.radiusMax
  trials : ∀ i < N, ConstrainedTrial f X P (x i) (Δ i) (d i) (j i)
    (s i) (x (i + 1)) (Δ (i + 1)) (ρ i)

namespace ConstrainedRun
variable {q : ℕ} {f : E → ℝ} {X : Set E} {P : Parameters q}
  {x s : ℕ → E} {d : ℕ → Fin q → E} {j : ℕ → Fin q}
  {Δ ρ : ℕ → ℝ} {N : ℕ}

/-- Positivity of every radius, including the final endpoint, follows from
initialization and the actual three-case update intervals. -/
theorem radius_pos (h : ConstrainedRun f X P x s d j Δ ρ N) {i : ℕ} (hi : i ≤ N) :
    0 < Δ i := by
  induction i with
  | zero => exact h.initial_radius_pos
  | succ i ih =>
    have hp := ih (by omega)
    have hu := (h.trials i (by omega)).radius_update
    split_ifs at hu with hv hs
    · exact hp.trans_le hu.1
    · exact (mul_pos (P.gamma1_pos.trans_le P.gamma1_le_gamma2) hp).trans_le hu.1
    · exact (mul_pos P.gamma1_pos hp).trans_le hu.1

/-- A successful constrained trial enlarges its radius by at most `gamma3`. -/
theorem successful_radius_le (h : ConstrainedRun f X P x s d j Δ ρ N)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ ρ i) : Δ (i + 1) ≤ P.gamma3 * Δ i := by
  have ht := h.trials i hi
  have hu := ht.radius_update
  split_ifs at hu with hv
  · exact hu.2.trans (min_le_right _ _)
  · exact hu.2.trans (le_mul_of_one_le_left ht.radius_pos.le P.one_le_gamma3)

/-- Every unsuccessful constrained trial contracts by at least `gamma2`. -/
theorem unsuccessful_radius_le (h : ConstrainedRun f X P x s d j Δ ρ N)
    {i : ℕ} (hi : i < N) (hu : ¬P.eta1 ≤ ρ i) : Δ (i + 1) ≤ P.gamma2 * Δ i := by
  have hv : ¬P.eta2 ≤ ρ i := fun hh => hu (P.eta1_le_eta2.trans hh)
  have ht := (h.trials i hi).radius_update
  rw [ite_eq_right hv, ite_eq_right hu] at ht
  exact ht.2

/-- The valid trial-count estimate retains the logarithm of an actual
positive endpoint-radius lower bound. In general that lower bound depends on
the requested accuracies; it cannot be absorbed in a uniform additive constant. -/
theorem iterations_le_of_radius_lower (h : ConstrainedRun f X P x s d j Δ ρ N)
    {δmin : ℝ} (hδ : 0 < δmin) (hlow : δmin ≤ Δ N) :
    (N : ℝ) ≤ (EvaluationComplexity.successfulIterations
      {i | P.eta1 ≤ ρ i} N).card *
        (1 + Real.log P.gamma3 / |Real.log P.gamma2|) +
      |Real.log (δmin / Δ 0)| / |Real.log P.gamma2| :=
  EvaluationComplexity.iteration_bound_of_parameter_lower
    (fun _ hi => h.radius_pos hi) (zero_lt_one.trans_le P.one_le_gamma3)
    (P.gamma1_pos.trans_le P.gamma1_le_gamma2) P.gamma2_lt_one hlow hδ
    (fun _ hi hs => h.successful_radius_le hi hs)
    (fun _ hi hu => h.unsuccessful_radius_le hi hu)

end ConstrainedRun
end HighOrderTrustRegion
