import Numlib.Optimization.Constrained.TargetCounterexample.TwoPhase
import Numlib.Optimization.LeastNorm.ComponentRegularity
import Numlib.Optimization.Constrained.TargetRegularity
import Numlib.Optimization.Constrained.LagrangianStability
import Numlib.Optimization.Constrained.TargetCounterexample
import Numlib.Optimization.LeastNorm.Counterexample
import Numlib.Optimization.LeastNorm.Budget
import Numlib.Optimization.LeastNorm.EvaluationCounterexample
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

/-- **Theorem14.3.4 with a uniform geometric coefficient.** Actual per-call
least-squares evaluation bounds give simultaneous function and derivative
budgets at the genuine first outer termination point. The accuracy exponents
are unchanged. This companion uses the coefficient `β^(-π)/(1-β)` instead of
interchanging a finite sum and a maximum as in the printed proof. -/
theorem theorem_14_3_4_corrected {n m q : ℕ} (hq : 0 < q)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (call : EuclideanSpace ℝ (Fin n) → (Fin q → ℝ) → EuclideanSpace ℝ (Fin n) →
      (Fin q → ℝ) → ℕ → ℕ → Prop) (hsound : LeastNorm.InnerSound r X call)
    (π : Fin q → ℝ) (hπ : ∀ a, 1 < π a) {κF κD : ℝ}
    (hκF : 0 ≤ κF) (hκD : 0 ≤ κD)
    (hcounts : LeastNorm.InnerCounts r call hq π κF κD)
    (ε₀ β : ℝ) (ε : Fin q → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (δ : ℕ → Fin q → ℝ) (nf nd : ℕ → ℕ)
    (hprefix : ∀ N, (∀ k < N, ¬LeastNorm.TargetAt r X ε₀ ε x δ k) →
      lenqscRun r X call ε₀ β ε x δ nf nd N) :
    ∃ K : ℕ, LeastNorm.TargetAt r X ε₀ ε x δ K ∧
      lenqscRun r X call ε₀ β ε x δ nf nd K ∧
      (∀ k < K, ¬LeastNorm.TargetAt r X ε₀ ε x δ k) ∧
      K ≤ GeometricDecay.budget ‖r (x 0)‖ ε₀ β ∧
      (∑ k ∈ Finset.range K, (nf k : ℝ)) ≤ κF / 2 * ‖r (x 0)‖ / (1 - β) *
        LeastNorm.maximumWeight hq
          (fun a => β ^ (-π a) * ε₀ ^ (1 - π a) * ε a ^ (-π a)) ∧
      (∑ k ∈ Finset.range K, (nd k : ℝ)) ≤ κD / 2 * ‖r (x 0)‖ / (1 - β) *
        LeastNorm.maximumWeight hq
          (fun a => β ^ (-π a) * ε₀ ^ (1 - π a) * ε a ^ (-π a)) := by
  obtain ⟨K, ht, hr, hf, hb⟩ := LeastNorm.exists_first_target hsound hprefix
  exact ⟨K, ht, hr, hf, hb,
    hr.evaluations_le hsound hq π hπ hκF nf
      (fun k hk => (hcounts _ _ _ _ _ _ (hr.inner k hk)).1),
    hr.evaluations_le hsound hq π hπ hκD nd
      (fun k hk => (hcounts _ _ _ _ _ _ (hr.inner k hk)).2)⟩

open LeastNorm.EvaluationCounterexample in
/-- **Theorem14.3.4 is false with the displayed constants for arbitrary
allowed exponents.** This actual smooth affine-residual execution satisfies
all inner criticality tests, both per-call evaluation bounds with constants one,
and all source global Lipschitz and initial-level tensor bounds. Its first outer
target requires two calls totaling 34203 evaluations, while the printed bound
is less than that total. The invalid maximum/sum interchange cannot be used. -/
theorem theorem_14_3_4_counterexample :
    ContDiff ℝ 2 (LeastNorm.merit residual) ∧
    (∀ j, 1 ≤ j → j ≤ 2 → ∀ x y : ℝ,
      ‖iteratedFDeriv ℝ j (LeastNorm.merit residual) x -
        iteratedFDeriv ℝ j (LeastNorm.merit residual) y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x : ℝ, LeastNorm.merit residual x ≤ LeastNorm.merit residual (point 0) →
      ∀ j, 1 ≤ j → j ≤ 2 → ‖iteratedFDeriv ℝ j (LeastNorm.merit residual) x‖ ≤ 1) ∧
    (∀ a, 1 < exponent a) ∧
    LeastNorm.InnerSound residual Set.univ innerCall ∧
    LeastNorm.InnerCounts residual innerCall (by norm_num : 0 < 2) exponent 1 1 ∧
    LeastNorm.Run residual Set.univ innerCall (898 / 1000) (9 / 10) accuracy point
      (fun _ _ => 1) count count 2 ∧
    LeastNorm.TargetAt residual Set.univ (898 / 1000) accuracy point (fun _ _ => 1) 2 ∧
    (∀ k < 2, ¬LeastNorm.TargetAt residual Set.univ (898 / 1000)
      accuracy point (fun _ _ => 1) k) ∧
    ¬(∑ k ∈ Finset.range 2, (count k : ℝ)) ≤ 1 / 2 * ‖residual (point 0)‖ *
      LeastNorm.maximumWeight (by norm_num : 0 < 2) printedWeight := by
  refine ⟨merit_regularity.1, merit_regularity.2.1, merit_regularity.2.2, ?_,
    inner_sound, inner_counts, two_iterations, first_target_two.1, first_target_two.2,
    printed_evaluation_bound_false⟩
  intro a
  fin_cases a <;> norm_num [exponent]

/-- **Counterexample to Lemma14.3.5.** A bounded smooth objective and linear
equality constraint admit an actual feasible phase-one return and one exact
phase-two inner call. The genuine target reset terminates with all requested
merit criticalities satisfied, but no multiplier satisfies both printed first-
and second-order Lagrangian conclusions. The first bound forces the multiplier
to zero, and a feasible tangent displacement refutes the second bound. -/
alias lemma_14_3_5_counterexample := Constrained.TargetCounterexample.verified_counterexample

/-- **Lemma 14.3.6.** Both actual least-squares merits have the source regularity
on the same open convex domain. Four constants for the feasibility merit are
fixed before the initial residual level and all derivative orders. The target
merit constants are fixed before every target, with both actual merit derivative
norms bounded on its unit residual level.

The printed equation (14.3.63) names the feasibility merit `ν`; this statement
retains that bound and also proves the intended target merit `μ` bound. Uniform
component derivative bounds and Lipschitz constants give the exact Euclidean
square-root dimension conversion. -/
theorem lemma_14_3_6 {n m p : ℕ}
    {X S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hXS : X ⊆ S)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hc : ∀ i, ContDiffOn ℝ p (fun z => c z i) S) {Bc Lc : ℝ} (hBc : 0 ≤ Bc) (hLc : 0 ≤ Lc)
    (hbc : ∀ i j, 1 ≤ j → j ≤ p → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ j (fun z => c z i) x‖ ≤ Bc)
    (hlc : ∀ i j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j (fun z => c z i) x -
        iteratedFDeriv ℝ j (fun z => c z i) y‖ ≤ Lc * ‖x - y‖) :
    (∃ LA ≥ 1, ∃ LB ≥ 1, ∃ BA ≥ 1, ∃ BB ≥ 1,
      ContDiffOn ℝ p (LeastNorm.merit c) S ∧
      ∀ x₀ ∈ X, ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ X,
        ‖c x‖ ≤ ‖c x₀‖ →
        (∀ y ∈ S, ‖iteratedFDeriv ℝ j (LeastNorm.merit c) x -
          iteratedFDeriv ℝ j (LeastNorm.merit c) y‖ ≤
            (LA + LB * ‖c x₀‖) * ‖x - y‖) ∧
        ‖iteratedFDeriv ℝ j (LeastNorm.merit c) x‖ ≤ BA + BB * ‖c x₀‖) ∧
    (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (Bf Lf : ℝ),
      ContDiffOn ℝ p f S → 0 ≤ Bf → 0 ≤ Lf →
      (∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ Bf) →
      (∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ Lf * ‖x - y‖) →
      ∃ L ≥ 1, ∃ B ≥ 1, ∀ t : ℝ, ContDiffOn ℝ p (Constrained.targetMerit f c t) S ∧
        ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ X,
          Constrained.targetMerit f c t x ≤ (1 / 2 : ℝ) →
          (∀ y ∈ S, ‖iteratedFDeriv ℝ j (Constrained.targetMerit f c t) x -
            iteratedFDeriv ℝ j (Constrained.targetMerit f c t) y‖ ≤ L * ‖x - y‖) ∧
          ‖iteratedFDeriv ℝ j (Constrained.targetMerit f c t) x‖ ≤ B ∧
          ‖iteratedFDeriv ℝ j (LeastNorm.merit c) x‖ ≤ B) := by
  have hcv : ContDiffOn ℝ p c S := (contDiffOn_piLp 2).mpr hc
  have hBc' : 0 ≤ Real.sqrt m * Bc := mul_nonneg (Real.sqrt_nonneg _) hBc
  have hLc' : 0 ≤ Real.sqrt m * Lc := mul_nonneg (Real.sqrt_nonneg _) hLc
  have hbcv : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ j c x‖ ≤ Real.sqrt m * Bc := by
    intro j hj hjp x hx
    exact LeastNorm.norm_iteratedFDeriv_le_components_on hcv hS hjp hBc
      (fun i z hz => hbc i j hj hjp z hz) hx
  have hlcv : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j c x - iteratedFDeriv ℝ j c y‖ ≤
        (Real.sqrt m * Lc) * ‖x - y‖ := by
    intro j hj hjp x hx y hy
    exact LeastNorm.norm_iteratedFDeriv_sub_le_components_on hcv hS hjp hLc
      (fun i z hz w hw => hlc i j hj hjp z hz w hw) hx hy
  obtain ⟨LA, hLA, LB, hLB, BA, hBA, BB, hBB, hcont, hlevels⟩ :=
    LeastNorm.merit_regularity_on_residual_levels hcv hS hconv hBc' hLc' hbcv hlcv
  constructor
  · refine ⟨LA, hLA, LB, hLB, BA, hBA, BB, hBB, hcont, ?_⟩
    intro x₀ _hx₀ j hj hjp x hx hlevel
    exact hlevels ‖c x₀‖ (norm_nonneg _) j hj hjp x (hXS hx) hlevel
  · intro f Bf Lf hf hBf hLf hbf hlf
    obtain ⟨L, hL, B, hB, htargets⟩ := Constrained.targetMerit_uniform_regularity
      hf hcv hS hconv hBf hLf hBc' hLc' hbf hlf hbcv hlcv
    refine ⟨L, hL, max B (BA + BB), hB.trans (le_max_left _ _), ?_⟩
    intro t
    refine ⟨(htargets t).1, ?_⟩
    intro j hj hjp x hx hlevel
    have hm := (htargets t).2 j hj hjp x (hXS hx) hlevel
    have hr := Constrained.targetMerit_residual_bounds hlevel
    have hn := (hlevels 1 zero_le_one j hj hjp x (hXS hx) hr.1).2
    refine ⟨hm.1, hm.2.trans (le_max_left _ _), ?_⟩
    have hn' : ‖iteratedFDeriv ℝ j (LeastNorm.merit c) x‖ ≤ BA + BB := by
      simpa only [mul_one] using hn
    exact hn'.trans (le_max_right B (BA + BB))

end CartisGouldToint

namespace CartisGouldToint

/-- **Counterexample to Theorem 14.3.9's output guarantee.** For `p=q=2`,
all source regularity and objective bounds hold globally. Phase one is an
actual zero-call feasible return. Phase two uses a genuine one-trial AR22 run:
its initial ordered Taylor check selects order two, its step is a proved global
minimum of the actual cubic model, its actual ratio lies between the legal
acceptance thresholds, and its endpoint passes both true Taylor checks. The
actual target-reset branch then terminates at zero with unit radii, although
no multiplier satisfies even the first two printed Lagrangian bounds. This
refutes the stated output conclusion independently of the numerical counts. -/
alias theorem_14_3_9_counterexample :=
  Constrained.TargetCounterexample.InnerRegularization.verified_regularized_counterexample

end CartisGouldToint
