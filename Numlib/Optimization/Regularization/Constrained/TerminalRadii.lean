import Numlib.Optimization.Regularization.Constrained.Execution

/-!
# Quantitative constrained terminal radii

Inherited radii have the actual finite-solver floor. A zero model return makes
zero a true model minimum, at which finite feasible halvings construct another
certificate with a quantitative floor. Actual origin jets transfer it to f.
-/

namespace ConstrainedRegularization
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap parameterCap_pos)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A zero global-gap return has actual true Taylor certificates at uniformly
positive quantitative radii, obtained from finite model halvings at zero. -/
theorem zero_step_optimality_with_radius_floor {f : E → ℝ} {p q : ℕ} {x s : E}
    (hqp : q ≤ p) (hf : ContDiffAt ℝ p f x) {X : Set E} (hX : IsClosed X)
    (hconv : Convex ℝ X) (hx : x ∈ X) {σ μ L : ℝ} (hσ : 0 ≤ σ) (hμ : 0 < μ)
    (hL : 1 ≤ L) (hA : ∀ i, 2 ≤ i → i ≤ p → ‖ftaylorSeries ℝ f x i‖ ≤ L)
    (hsolve : ModelDecrease.ApproximateGlobalStepOn (HighOrderRegularization.model f p x σ)
      (TaylorModel.feasibleDisplacements X x) μ s)
    (hzero : HighOrderRegularization.model f p x σ 0 =
      HighOrderRegularization.model f p x σ s)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) :
    ∃ δ : Fin q → ℝ, OptimalityAt f X ε x δ ∧
      ∀ a, 1 / (8 * (3 * L + σ)) * ε a ≤ δ a := by
  let A := ftaylorSeries ℝ f x
  let m := HighOrderRegularization.model f p x σ
  let C := TaylorModel.feasibleDisplacements X x
  let B := 3 * L + σ
  have hB : 0 < B := by dsimp [B]; linarith
  have hm : ContDiff ℝ p m := ModelDecrease.contDiff_penalized_ofJet A p p le_rfl σ
  have hlip : ∀ u v,
      ‖iteratedFDeriv ℝ p m u - iteratedFDeriv ℝ p m v‖ ≤ B * ‖u - v‖ := by
    intro u v
    have hh := ModelDecrease.norm_sub_iteratedFDeriv_penalized_ofJet_le A p hσ u v
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _))
  have hder : ∀ n, 2 ≤ n → n ≤ p → ∀ y : E, ‖y‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n m y‖ ≤ B :=
    fun n hn hnp y hy => ModelDecrease.norm_iteratedFDeriv_penalized_ofJet_le_three_mul_add
      A hnp hσ (zero_le_one.trans hL) (fun i hni hip => hA i (hn.trans hni) hip) hy
  have hC : IsClosed C := hX.preimage (continuous_const.add continuous_id)
  have hCv : Convex ℝ C := hconv.translate_preimage_right x
  have h0 : (0 : E) ∈ C := by simpa [C] using hx
  have hmin := hsolve.isMinOn_zero hμ hzero
  have horder : ∀ a : Fin q, 0 < modelOrder a ∧ modelOrder a ≤ p := by
    intro a
    have := a.isLt
    unfold modelOrder
    omega
  obtain ⟨δ, hd⟩ := ModelSolve.exists_constrained_stepComputation_of_isMinOn hm hB hlip hder
    hC hCv modelOrder horder zero_lt_one zero_lt_one le_rfl ε (fun a => (hε a).1) 0 h0 hmin
  refine ⟨δ, ⟨hx, hd.radius_mem, ?_⟩, ?_⟩
  · intro a
    have hh := hd.criticality zero_lt_one (by simp : ‖(0 : E)‖ ≤ 1) a
    rw [HighOrderRegularization.constrainedCriticality_model_zero_order hf (horder a).2] at hh
    simpa only [one_mul] using hh
  · intro a
    have hh := hd.radius_lower_penalized A hσ hL hA horder zero_lt_one le_rfl le_rfl hε
      (by simp : ‖(0 : E)‖ ≤ 1) a
    simpa only [one_mul] using hh

end ConstrainedRegularization

namespace ConstrainedRegularization
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap parameterCap_pos)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {X : Set E} {P : Settings p q}
  {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- Initial unit radii, actual finite model solves and radius inheritance give
a uniform positive floor at every actual endpoint. -/
theorem radius_floor (h : Run f X P ε D N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hinit : ∀ a, D.radius 0 a = 1) {k : ℕ} (hk : k ≤ N) (a : Fin q) :
    radiusCoefficient P L (parameterCap P L) * ε a ≤ D.radius k a := by
  let κ := radiusCoefficient P L (parameterCap P L)
  have hκ := radiusCoefficient_mem P hL (parameterCap_pos P L).le
  have he1 : κ * ε a ≤ 1 := by
    have hh := mul_le_mul hκ.2 (h.accuracy_le_one a) (h.accuracy_pos a).le zero_le_one
    simpa only [one_mul] using hh
  induction k with
  | zero => simpa only [hinit a] using he1
  | succ k ih =>
    have hkN : k < N := by omega
    rw [h.radius_update k hkN]
    split_ifs
    · have hm := h.step_two k hkN.le (h.continues k hkN)
      by_cases hs : ‖D.step k‖ ≤ 1
      · have hh := h.solved_radius_floor hf hL hlip hkN.le (h.continues k hkN) hs a
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (h.accuracy_pos a).le).trans hh
      · have hδ : D.solvedRadius k a = 1 := by
          rcases hm.result with ⟨_, hδ⟩ | ⟨hs', _⟩
          · exact hδ a
          · exact (hs hs').elim
        simpa only [hδ] using he1
    · exact ih (by omega)

/-- Both terminal branches produce true constrained Taylor certificates with
an explicit accuracy-independent radius coefficient. Even zero model returns
use genuinely constructed finite feasible halving certificates. -/
theorem target_optimality_with_radius_floor (h : Run f X P ε D N) (hX : IsClosed X)
    (hconv : Convex ℝ X) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hinit : ∀ a, D.radius 0 a = 1) (htarget : TargetAt f X P ε D N) :
    ∃ δ : Fin q → ℝ, OptimalityAt f X ε (D.point N) δ ∧
      ∀ a, radiusCoefficient P L (parameterCap P L) * ε a ≤ δ a := by
  rcases htarget with ht | ⟨hselected, hzero⟩
  · exact ⟨D.radius N, ht, h.radius_floor hf hL hlip hinit le_rfl⟩
  · obtain ⟨μ, hμ, _, hsolve⟩ := (h.step_two N le_rfl hselected).fraction
    have hA := HighOrderRegularization.tensor_bound_of_derivative_lipschitz f
      (zero_le_one.trans hL) (fun i hi hip => hlip i hi hip.le) (D.point N)
    obtain ⟨δ, hopt, hfloor⟩ := zero_step_optimality_with_radius_floor P.order_le
      hf.contDiffAt hX hconv (h.point_mem le_rfl) (h.modelTrace.updates.pos le_rfl).le hμ hL hA
      hsolve hzero ε (fun a => ⟨h.accuracy_pos a, h.accuracy_le_one a⟩)
    refine ⟨δ, hopt, fun a => ?_⟩
    have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
    have hcap := h.parameter_le hf hL (hlip p hp le_rfl) le_rfl
    have hden : 0 < 8 * (3 * L + parameterCap P L) := by
      have := parameterCap_pos P L
      positivity
    have hnum : P.zeta * P.theta ≤ 1 := by
      simpa only [one_mul] using
        mul_le_mul P.zeta_le_one P.theta_lt_one.le P.theta_pos.le zero_le_one
    have hκ : radiusCoefficient P L (parameterCap P L) ≤
        1 / (8 * (3 * L + D.parameter N)) := by
      apply (min_le_left _ _).trans
      apply le_trans (div_le_div_of_nonneg_right hnum hden.le)
      exact div_le_div_of_nonneg_left zero_le_one (by
        have := h.modelTrace.updates.pos le_rfl
        positivity) (by linarith)
    exact (mul_le_mul_of_nonneg_right hκ (h.accuracy_pos a).le).trans (hfloor a)

end Run
end ConstrainedRegularization

namespace ConstrainedRegularization
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Constructed actual first-target executions have the full initialized
budgets and a true terminal certificate with explicit uniform radius floors.
The radius coefficient depends only on fixed settings and the common derivative
Lipschitz constant, before the objective, initial point and accuracies. -/
theorem certified_execution_with_radius_floor {p q : ℕ} (f : E → ℝ) (X : Set E)
    (hX : IsClosed X) (hconv : Convex ℝ X) (P : Settings p q)
    (x₀ : E) (hx₀ : x₀ ∈ X) (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) :
    ∃ κs > 0, ∃ κa > 0, ∃ κc > 0,
      ∀ (ε : Fin q → ℝ), (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ (D : ExecutionData E q) (K : ℕ) (δ : Fin q → ℝ),
        D.point 0 = x₀ ∧ D.parameter 0 = P.sigmaInitial ∧ (∀ a, D.radius 0 a = 1) ∧
        Run f X P ε D K ∧ TargetAt f X P ε D K ∧
        (∀ k < K, ¬TargetAt f X P ε D k) ∧ OptimalityAt f X ε (D.point K) δ ∧
        (∀ a, radiusCoefficient P L (parameterCap P L) * ε a ≤ δ a) ∧
        (∀ a, modelOrder a = 1 → TaylorModel.constrainedCriticality f 1 X (D.point K) 1 ≤
          ε a) ∧
        ((K + 1 : ℕ) : ℝ) ≤ κa * (f x₀ - flow) / accuracyFactor P ε + κc ∧
        (((EvaluationComplexity.successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 :
          ℕ) : ℝ) ≤ κs * (f x₀ - flow) / accuracyFactor P ε + 2 := by
  obtain ⟨κs, hs, κa, ha, κc, hc, hall⟩ :=
    exists_certified_execution f X hX hconv P x₀ hx₀ hf hL hlip hlow
  refine ⟨κs, hs, κa, ha, κc, hc, ?_⟩
  intro ε hε
  obtain ⟨D, K, _, hx, hσ, hδ, hr, ht, hfirst, _, hunit, hF, hD⟩ := hall ε hε
  obtain ⟨δ, hopt, hfloor⟩ := hr.target_optimality_with_radius_floor hX hconv hf hL hlip hδ ht
  exact ⟨D, K, δ, hx, hσ, hδ, hr, ht, hfirst, hopt, hfloor, hunit, hF, hD⟩

end ConstrainedRegularization
