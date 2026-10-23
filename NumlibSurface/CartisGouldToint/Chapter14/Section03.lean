import Numlib.Optimization.Constrained.LagrangianStability
import Numlib.Optimization.LeastNorm.Counterexample
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Equality constraints and local Lagrangian stability

The restricted criticality is the supremum of actual Lagrangian Taylor decrements
on the specified allowed displacements. The augmented multiplier norm is exactly
the Euclidean norm of `(1,y)`. Local smoothness is required on an open set containing
the radius ball; this resolves the source's ambiguous use of “diameter”. The final
constraint equalities refer to the same displacement `d` as the conclusion.
When both Lipschitz constants vanish, the entire radius ball is allowed, as in footnote 111.
-/

namespace CartisGouldToint

/-- **Theorem 14.3.2.** Actual approximate Lagrangian Taylor criticality implies
both printed objective stability bounds, with the exact feasibility loss, factorial,
augmented multiplier factor and square-root-two stability radius. All assumptions
are local, and the allowed displacement set need not be closed or convex. -/
theorem theorem_14_3_2 {n m j : ℕ} (hj : 1 ≤ j) (_hj3 : j ≤ 3)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X D V : Set (EuclideanSpace ℝ (Fin n))) (_hX : IsClosed X) (_hXne : X.Nonempty)
    (x : EuclideanSpace ℝ (Fin n)) (_hx : x ∈ X) (hD : IsOpen D)
    (_hV : V ⊆ TaylorModel.feasibleDisplacements X x)
    (hf : ContDiffOn ℝ j f D) (hc : ContDiffOn ℝ j c D)
    (y : EuclideanSpace ℝ (Fin m)) {δ ε₀ ε η Lf Lc : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (_hη : 0 ≤ η) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hball : Metric.closedBall x δ ⊆ D)
    (hlf : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ Lf * ‖u - v‖)
    (hlc : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j c u - iteratedFDeriv ℝ j c v‖ ≤ Lc * ‖u - v‖)
    (hfeas : ‖c x‖ ≤ ε₀)
    (hcrit : TaylorModel.restrictedCriticality (Constrained.vectorLagrangian f c y) j V x δ ≤
      ε * Constrained.multiplierNorm y * δ ^ j / j.factorial + η) :
    ∀ d : EuclideanSpace ℝ (Fin n), d ∈ V → ‖c (x + d)‖ ≤ ε₀ →
      (‖d‖ ≤ δ ∧ (max Lf Lc = 0 ∨
        ‖d‖ ≤ (j + 1 : ℕ) * ε / (Real.sqrt 2 * max Lf Lc))) →
      (f x - 2 * ε₀ * ‖y‖ - 2 * ε * Constrained.multiplierNorm y * δ ^ j / j.factorial - η ≤
        f (x + d)) ∧
      ((c (x + d) = 0 ∧ inner ℝ y (c x) ≤ 0) ∨ c (x + d) = c x →
        f x - 2 * ε * Constrained.multiplierNorm y * δ ^ j / j.factorial - η ≤ f (x + d)) := by
  intro d hdV hcd hd
  have hL := Constrained.value_ge_of_lagrangian_criticality hj hD hf hc x y hδ.le
    hε hLf hLc hball hlf hlc hcrit hdV hd
  let b := 2 * ε * Constrained.multiplierNorm y * δ ^ j / (j.factorial : ℝ) + η
  have hb : Constrained.vectorLagrangian f c y x - b ≤
      Constrained.vectorLagrangian f c y (x + d) := by
    dsimp [b]
    linarith only [hL]
  constructor
  · have hh := Constrained.objective_bound_of_lagrangian_bound f c x d y hfeas hcd hb
    dsimp [b] at hh
    linarith only [hh]
  · intro he
    have hh := Constrained.objective_bound_of_lagrangian_bound_no_loss f c x d y hb he
    dsimp [b] at hh
    linarith only [hh]
/-- The genuine least-squares merit for any residual map, including the
constraint violation and the explicit-target residual maps. -/
noncomputable abbrev leastSquaresMerit {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (r : E → F) (x : E) : ℝ := LeastNorm.merit r x

/-- Algorithm14.3.1 with an explicit inner execution relation and actual
function/derivative call counters. Inner soundness and complexity are separate
hypotheses of the convergence and evaluation theorems. -/
abbrev lenqscRun {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] {q : ℕ} (r : E → F) (X : Set E)
    (call : E → (Fin q → ℝ) → E → (Fin q → ℝ) → ℕ → ℕ → Prop)
    (ε₀ β : ℝ) (ε : Fin q → ℝ) (x : ℕ → E) (δ : ℕ → Fin q → ℝ)
    (nf nd : ℕ → ℕ) (N : ℕ) : Prop := LeastNorm.Run r X call ε₀ β ε x δ nf nd N

/-- **Theorem 14.3.3 with integer rounding.** The actual first least-norm
termination point satisfies (14.3.18) within the ceiling of the printed real
logarithmic expression. The initial primal test and every actual inner call are
retained. A constant-residual example below requires one call although the
unrounded expression equals one half. -/
theorem theorem_14_3_3_corrected {n m q : ℕ}
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (call : EuclideanSpace ℝ (Fin n) → (Fin q → ℝ) → EuclideanSpace ℝ (Fin n) →
      (Fin q → ℝ) → ℕ → ℕ → Prop) (hsound : LeastNorm.InnerSound r X call)
    (ε₀ β : ℝ) (ε : Fin q → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (δ : ℕ → Fin q → ℝ) (nf nd : ℕ → ℕ)
    (hprefix : ∀ N, (∀ k < N, ¬LeastNorm.TargetAt r X ε₀ ε x δ k) →
      lenqscRun r X call ε₀ β ε x δ nf nd N) :
    ∃ (K : ℕ) (radii : Fin q → ℝ), x K ∈ X ∧
      (∀ a, 0 < radii a ∧ radii a ≤ 1) ∧
      (‖r (x K)‖ ≤ ε₀ ∨ ∀ a, TaylorModel.constrainedCriticality
        (leastSquaresMerit r) (InexactTrustRegion.modelOrder a) X (x K) (radii a) ≤
          ε a * ‖r (x K)‖ * radii a ^ InexactTrustRegion.modelOrder a /
            (InexactTrustRegion.modelOrder a).factorial) ∧
      lenqscRun r X call ε₀ β ε x δ nf nd K ∧
      (∀ k < K, ¬LeastNorm.TargetAt r X ε₀ ε x δ k) ∧
      K ≤ ⌈max 0 (Real.log (ε₀ / ‖r (x 0)‖) / Real.log β)⌉₊ := by
  obtain ⟨K, htarget, hrun, hfirst, hbound⟩ := LeastNorm.exists_first_target hsound hprefix
  have he : Real.log (‖r (x 0)‖ / ε₀) / Real.log β⁻¹ =
      Real.log (ε₀ / ‖r (x 0)‖) / Real.log β := by
    rw [show ‖r (x 0)‖ / ε₀ = (ε₀ / ‖r (x 0)‖)⁻¹ by rw [inv_div],
      Real.log_inv, Real.log_inv, neg_div_neg_eq]
  have hcount : K ≤ ⌈max 0 (Real.log (ε₀ / ‖r (x 0)‖) / Real.log β)⌉₊ := by
    dsimp [GeometricDecay.budget] at hbound
    rw [he] at hbound
    exact hbound.trans (Nat.ceil_mono (le_max_right _ _))
  cases K with
  | zero =>
    refine ⟨0, fun _ => 1, hrun.initial_feasible, fun _ => ⟨zero_lt_one, le_rfl⟩,
      Or.inl ?_, hrun, hfirst, hcount⟩
    simpa only [LeastNorm.TargetAt, ite_true] using htarget
  | succ k =>
    obtain ⟨hfeas, hδ, _⟩ := hsound _ _ _ _ _ _ (hrun.inner k (Nat.lt_succ_self k))
    refine ⟨k + 1, δ (k + 1), hfeas, hδ, ?_, hrun, hfirst, hcount⟩
    simpa only [LeastNorm.TargetAt, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false] using htarget

/-- A genuine constant-residual execution refutes the unrounded real count in
**Theorem14.3.3**: the initial primal test fails, the first inner call finds zero
true criticality, and one call is greater than the printed bound one half. -/
theorem theorem_14_3_3_counterexample :
    LeastNorm.InnerSound LeastNorm.Counterexample.residual Set.univ
      LeastNorm.Counterexample.innerCall ∧
    LeastNorm.Run LeastNorm.Counterexample.residual Set.univ
      LeastNorm.Counterexample.innerCall (1 / 4) (1 / 4) (fun _ => 1 / 2)
        (fun _ => 0) (fun _ _ => 1) (fun _ => 1) (fun _ => 1) 1 ∧
    LeastNorm.TargetAt (q := 1) LeastNorm.Counterexample.residual Set.univ
      (1 / 4) (fun _ => 1 / 2) (fun _ => 0) (fun _ _ => 1) 1 ∧
    ¬LeastNorm.TargetAt (q := 1) LeastNorm.Counterexample.residual Set.univ
      (1 / 4) (fun _ => 1 / 2) (fun _ => 0) (fun _ _ => 1) 0 ∧
    ¬(1 : ℝ) ≤ max 0 (Real.log ((1 / 4 : ℝ) / (1 / 2)) / Real.log (1 / 4)) :=
  ⟨LeastNorm.Counterexample.inner_sound, LeastNorm.Counterexample.one_iteration,
    LeastNorm.Counterexample.first_target_one.1, LeastNorm.Counterexample.first_target_one.2,
    LeastNorm.Counterexample.printed_iteration_bound_false⟩

end CartisGouldToint
