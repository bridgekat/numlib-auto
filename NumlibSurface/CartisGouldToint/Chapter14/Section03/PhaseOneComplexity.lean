import NumlibSurface.CartisGouldToint.Chapter14.Section03.TwoPhase
import Numlib.Optimization.ResidualLeastSquares.SeparatedCostBounds

/-!
# Chapter 14, Section 3: direct Phase-1 evaluation estimates

The component regularity assumption supplies the actual anchored level-set hypotheses
for the feasibility objective. The separated maxima of Lemma 14.3.7 can be bounded directly,
without the single-maximum estimate of Theorem 14.3.4. All INNER terminal queries and the
initial residual query are counted. At positive initial residual the latter is absorbed
into one coefficient selected before every primal and dual tolerance. The literal
unconditional beta input implies positive initial residual, closing Lemma 14.3.7 with
full counts. The broader operational zero-residual extension retains its explicit initial query.
-/

noncomputable section
namespace CartisGouldToint.Chapter14.Section03
open Set Metric Optimization ConstrainedTaylorCriticality ResidualLeastSquares
variable {n m p q : ℕ} {S : Type}

/-- The constraint assumptions of Lemma 14.3.6(i) yield the actual Chapter-14 anchored
level-set interface for the feasibility objective. All coefficient families are chosen
before the initial point and the resulting bounds depend only on its residual norm. -/
theorem constraintJetsOnInitialLevel
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hc : ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (LA LB BA BB : ℕ → ℝ),
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j) ∧
      ∀ x₀ ∈ X, Section02.SmoothBoundedJetsOnLevelSet (squaredResidual c) X x₀ p false U
        (fun j => LA j + LB j * ‖c x₀‖) (fun j => BA j + BB j * ‖c x₀‖) := by
  obtain ⟨U, LA, LB, BA, BB, hX, ho, hv, hs, hconst, hj⟩ :=
    lemma_14_3_6_constraint hc
  refine ⟨U, LA, LB, BA, BB, hconst, ?_⟩
  intro x₀ hx₀
  have hL : ∀ j, 1 ≤ LA j + LB j * ‖c x₀‖ := by
    intro j
    exact (hconst j).1.trans (le_add_of_nonneg_right
      (mul_nonneg (zero_le_one.trans (hconst j).2.1) (norm_nonneg _)))
  have hB : ∀ j, 1 ≤ BA j + BB j * ‖c x₀‖ := by
    intro j
    exact (hconst j).2.2.1.trans (le_add_of_nonneg_right
      (mul_nonneg (zero_le_one.trans (hconst j).2.2.2) (norm_nonneg _)))
  have hlevel : ∀ x ∈ Section02.feasibleSublevelSet (squaredResidual c) X x₀,
      x ∈ X ∧ ‖c x‖ ≤ ‖c x₀‖ := by
    intro x hx
    obtain ⟨hx, hf⟩ := mem_feasibleSublevelSet.mp hx
    refine ⟨hx, ?_⟩
    simp only [squaredResidual] at hf
    nlinarith [norm_nonneg (c x), norm_nonneg (c x₀)]
  refine {
    isOpen := ho
    convex := hv
    centers_subset := fun x hx => hX (hlevel x hx).1
    contDiffOn := hs
    lipschitz_nonneg := fun j _ _ => zero_le_one.trans (hL j)
    bound_nonneg := fun j _ _ => zero_le_one.trans (hB j)
    bound := ?_
    lipschitz := ?_
    initial_feasible := hx₀
    feasible_subset := hX
    lipschitz_one_le := fun j _ _ => hL j
    bound_one_le := fun j _ _ => hB j }
  · intro j hj1 hjp x hx d
    have hb := (hj x₀ hx₀ j (Finset.mem_Icc.mpr ⟨hj1, hjp⟩) x
      (hlevel x hx).1 (hlevel x hx).2).1
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (squaredResidual c) x‖ * ‖d‖ ^ j := by
        simpa using (iteratedFDeriv ℝ j (squaredResidual c) x).le_opNorm (fun _ => d)
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg d) j)
  · intro j hj1 hjp x hx y hy d
    have hj1 : 1 ≤ j := hj1.resolve_right (by decide)
    have hl := (hj x₀ hx₀ j (Finset.mem_Icc.mpr ⟨hj1, hjp⟩) x
      (hlevel x hx).1 (hlevel x hx).2).2 y hy
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (squaredResidual c) y -
          iteratedFDeriv ℝ j (squaredResidual c) x‖ * ‖d‖ ^ j := by
        simpa using (iteratedFDeriv ℝ j (squaredResidual c) y -
          iteratedFDeriv ℝ j (squaredResidual c) x).le_opNorm (fun _ => d)
      _ ≤ _ := mul_le_mul_of_nonneg_right hl (pow_nonneg (norm_nonneg d) j)

variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
  {X : Set (EuclideanSpace ℝ (Fin n))} {θ ε₀ β : ℝ} {ε π : ℕ → ℝ}
  {κ : EvaluationKind → ℝ}
  {step : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
    EuclideanSpace ℝ (Fin n) × S → List EvaluationKind → Prop}
  {terminal : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S → List EvaluationKind → Prop}
  {t : Trace (EuclideanSpace ℝ (Fin n)) S}

/-- Actual Phase-1 LEN calls reach the weak residual-or-all-gaps test (14.3.64), with
feasible output and bounded positive radii. The cost uses the source's separated maxima,
with a tolerance-independent inflation of each INNER coefficient by `1 / (1 - β)`.
The initial residual query is explicit, also in the initially feasible branch. -/
theorem phase_one_evaluation_bound
    (h : algorithm_14_3_1_closedDual X c q (θ * ε₀) β ε π κ step terminal t)
    (hθ : 0 < θ) (hε₀ : 0 < ε₀) (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) :
    ∃ K ≤ MeasureDomination.geometricIterationCount ‖c (t.point 0)‖ β⁻¹ (θ * ε₀),
      Stops X c q (θ * ε₀) ε t K ∧
      (∀ k < K, ¬Stops X c q (θ * ε₀) ε t k) ∧ t.point K ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q,
        0 < twoPhasePhaseOneRadii t K j ∧ twoPhasePhaseOneRadii t K j ≤ 1) ∧
      twoPhasePhaseOneTest X c q θ ε₀ ε (twoPhasePhaseOneRadii t K) (t.point K) ∧
      ∀ a, (totalEvaluations t a K : ℝ) ≤ (if a = .function then 1 else 0) +
        (κ a / (1 - β)) / 2 * ‖c (t.point 0)‖ *
          geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  obtain ⟨K, hK, hs, hb⟩ := h.terminates
  refine ⟨K, hK, hs, hb, ?_, ?_, ?_,
    fun a => h.totalEvaluations_le_separated hθ hε₀ hπ hb a⟩
  · cases K with
    | zero => exact h.initial_feasible
    | succ k =>
      have hi := (h.solve k (hb k (by omega))).feasible _ le_rfl
      simpa only [h.finish] using hi
  · intro j hj
    cases K with
    | zero => simp
    | succ k =>
      rw [twoPhasePhaseOneRadii_of_pos t (by omega)]
      exact (h.solve k (hb k (by omega))).radius j hj
  · by_cases hr : ‖c (t.point K)‖ ≤ θ * ε₀
    · exact Or.inl hr
    · right
      have hpos : 0 < K := by
        rcases hs with hs | ⟨hk, _⟩
        · exact (hr hs).elim
        · exact hk
      rw [twoPhasePhaseOneRadii_of_pos t hpos]
      intro j hj
      exact (((h.stops_iff_certificate K).mp hs).resolve_left hr j hj).2

/-- At positive initial constraint norm, one coefficient works before *every* choice
of primal and dual tolerances, including their closed upper endpoints. It counts the
initial constraint query and every terminal INNER event. This is the exact separated
shape (14.3.65–66) on positive initial norm. The literal source beta input implies this
positivity; the broader operational extension also permits zero initial norm. -/
theorem phase_one_evaluation_bound_of_initial_pos
    {x₀ : EuclideanSpace ℝ (Fin n)} (hR : 0 < ‖c x₀‖)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ1 : β < 1)
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) (hκ : ∀ a, 0 ≤ κ a) :
    ∃ κν : EvaluationKind → ℝ, (∀ a, 0 ≤ κν a) ∧
      ∀ (ε₀ : ℝ) (ε : ℕ → ℝ), 0 < ε₀ → ε₀ ≤ 1 →
      ∀ (t : Trace (EuclideanSpace ℝ (Fin n)) S), t.point 0 = x₀ →
      algorithm_14_3_1_closedDual X c q (θ * ε₀) β ε π κ step terminal t →
      ∃ K ≤ MeasureDomination.geometricIterationCount ‖c x₀‖ β⁻¹ (θ * ε₀),
        Stops X c q (θ * ε₀) ε t K ∧
        (∀ k < K, ¬Stops X c q (θ * ε₀) ε t k) ∧ t.point K ∈ X ∧
        (∀ j ∈ Finset.Icc 1 q,
          0 < twoPhasePhaseOneRadii t K j ∧ twoPhasePhaseOneRadii t K j ≤ 1) ∧
        twoPhasePhaseOneTest X c q θ ε₀ ε (twoPhasePhaseOneRadii t K) (t.point K) ∧
        ∀ a, (totalEvaluations t a K : ℝ) ≤ κν a / 2 * ‖c x₀‖ *
          geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  refine ⟨fun a => κ a / (1 - β) + 2 / ‖c x₀‖, ?_, ?_⟩
  · intro a
    exact add_nonneg (div_nonneg (hκ a) (sub_pos.mpr hβ1).le) (by positivity)
  · intro ε₀ ε hε₀ hε₀1 t ht h
    obtain ⟨K, hK, hs, hb, hx, hrad, htest, _⟩ :=
      phase_one_evaluation_bound h hθ hε₀ hπ
    refine ⟨K, ?_, hs, hb, hx, hrad, htest, ?_⟩
    · simpa only [ht] using hK
    · intro a
      have he := h.totalEvaluations_le_separated_of_initial_pos
        hθ hθ1 hε₀ hε₀1 hπ (by simpa only [ht] using hR) hb a
      simpa only [ht] using he

/-- The actual Phase-1 component of a full TPqp-GC execution satisfies the separated
bound for every counted channel. This uses its complete LEN traces and its genuine
first stopping index, including the zero-call initialization branch. -/
theorem algorithm_14_3_2.phase_one_evaluation_bound
    {S₂ : Type} {f : EuclideanSpace ℝ (Fin n) → ℝ} {β₂ : ℝ}
    {κ₂ : EvaluationKind → ℝ}
    {step₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      EuclideanSpace ℝ (Fin n) × S₂ → List EvaluationKind → Prop}
    {terminal₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      List EvaluationKind → Prop}
    {K N : ℕ} {phaseTwo : TwoPhaseTargets.TargetTrace (EuclideanSpace ℝ (Fin n)) S₂}
    (h : algorithm_14_3_2 f c X q θ ε₀ β β₂ ε π κ κ₂ step terminal step₂ terminal₂
      t K phaseTwo N) (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) (a : EvaluationKind) :
    (totalEvaluations t a K : ℝ) ≤ (if a = .function then 1 else 0) +
      (κ a / (1 - β)) / 2 * ‖c (t.point 0)‖ *
        geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π :=
  h.phase_one.totalEvaluations_le_separated h.fraction.1 h.primal.1 hπ h.phase_one_first a

/-- Lemma 14.3.7: literal Phase 1 terminates with (14.3.64), and both full evaluation
channels satisfy (14.3.65–66). The coefficient is selected before every tolerance and
actual trace, and may depend on the fixed initial residual norm. Positive initial norm
is derived from the unconditional printed beta input, not added as a new assumption.
The constraint assumptions also supply the genuine anchored regularity of `ν` on its
whole feasible initial level set. As in (14.3.19–21), actual INNER contracts with fixed
exponents and coefficients are explicit execution context. This proof uses the direct
separated-maxima estimate and does not use the false single maximum of Theorem 14.3.4. -/
theorem lemma_14_3_7
    (hc : ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ X)
    (hinput : LiteralLENInput c x₀ β) (hθ : θ ∈ Ioo 0 1)
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) (hκ : ∀ a, 0 ≤ κ a) :
    ∃ κν : EvaluationKind → ℝ, (∀ a, 0 ≤ κν a) ∧
      (∃ (U : Set (EuclideanSpace ℝ (Fin n))) (L B : ℕ → ℝ),
        Section02.SmoothBoundedJetsOnLevelSet (squaredResidual c) X x₀ p false U L B) ∧
      ∀ (ε₀ : ℝ) (ε : ℕ → ℝ), 0 < ε₀ → ε₀ ≤ 1 →
      ∀ (t : Trace (EuclideanSpace ℝ (Fin n)) S), t.point 0 = x₀ →
      algorithm_14_3_1_closedDual X c q (θ * ε₀) β ε π κ step terminal t →
      ∃ K ≤ MeasureDomination.geometricIterationCount ‖c x₀‖ β⁻¹ (θ * ε₀),
        Stops X c q (θ * ε₀) ε t K ∧
        (∀ k < K, ¬Stops X c q (θ * ε₀) ε t k) ∧ t.point K ∈ X ∧
        (∀ j ∈ Finset.Icc 1 q,
          0 < twoPhasePhaseOneRadii t K j ∧ twoPhasePhaseOneRadii t K j ≤ 1) ∧
        twoPhasePhaseOneTest X c q θ ε₀ ε (twoPhasePhaseOneRadii t K) (t.point K) ∧
        ∀ a, (totalEvaluations t a K : ℝ) ≤ κν a / 2 * ‖c x₀‖ *
          geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  obtain ⟨κν, hκν, hbound⟩ :=
    phase_one_evaluation_bound_of_initial_pos (S := S) (X := X)
      (step := step) (terminal := terminal) hinput.initial_norm_pos hθ.1 hθ.2.le
      hinput.factor_lt_one hπ hκ
  obtain ⟨U, LA, LB, BA, BB, _, hreg⟩ := constraintJetsOnInitialLevel hc
  exact ⟨κν, hκν, ⟨U, _, _, hreg x₀ hx₀⟩, hbound⟩

/-- The unconditional printed Phase-1 input of an actual TPqp-GC run implies positive
initial constraint norm, regardless of whether its initial residual test succeeds. -/
theorem algorithm_14_3_2.phase_one_initial_norm_pos
    {S₂ : Type} {f : EuclideanSpace ℝ (Fin n) → ℝ} {β₂ : ℝ}
    {κ₂ : EvaluationKind → ℝ}
    {step₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      EuclideanSpace ℝ (Fin n) × S₂ → List EvaluationKind → Prop}
    {terminal₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      List EvaluationKind → Prop}
    {K N : ℕ} {phaseTwo : TwoPhaseTargets.TargetTrace (EuclideanSpace ℝ (Fin n)) S₂}
    (h : algorithm_14_3_2 f c X q θ ε₀ β β₂ ε π κ κ₂ step terminal step₂ terminal₂
      t K phaseTwo N) : 0 < ‖c (t.point 0)‖ :=
  h.phase_one_input.initial_norm_pos

/-- Lemma 14.3.7 applies at the genuine first Phase-1 stopping index of the actual
TPqp-GC algorithm. One coefficient works before all primal and dual tolerances and all
executions; both closed upper endpoints are retained. Every terminal INNER query and
the initial constraint query are counted. The fixed coefficient is exactly
`κ a / (1 - β) + 2 / ‖c x₀‖`; this depends on no tolerance or trace. -/
theorem algorithm_14_3_2.phase_one_literal_evaluation_bound
    {S₂ : Type} {f : EuclideanSpace ℝ (Fin n) → ℝ} {β₂ : ℝ}
    {κ₂ : EvaluationKind → ℝ}
    {step₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      EuclideanSpace ℝ (Fin n) × S₂ → List EvaluationKind → Prop}
    {terminal₂ : ℝ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S₂ →
      List EvaluationKind → Prop}
    (hc : ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ X)
    (hinput : LiteralLENInput c x₀ β) (hθ : θ ∈ Ioo 0 1)
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) (hκ : ∀ a, 0 ≤ κ a) :
    ∃ κν : EvaluationKind → ℝ, (∀ a, 0 ≤ κν a) ∧
      ∀ (ε₀ : ℝ) (ε : ℕ → ℝ)
      (t : Trace (EuclideanSpace ℝ (Fin n)) S) (K : ℕ)
      (phaseTwo : TwoPhaseTargets.TargetTrace (EuclideanSpace ℝ (Fin n)) S₂) (N : ℕ),
      t.point 0 = x₀ →
      algorithm_14_3_2 f c X q θ ε₀ β β₂ ε π κ κ₂ step terminal step₂ terminal₂
        t K phaseTwo N →
      K ≤ MeasureDomination.geometricIterationCount ‖c x₀‖ β⁻¹ (θ * ε₀) ∧
      t.point K ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q,
        0 < twoPhasePhaseOneRadii t K j ∧ twoPhasePhaseOneRadii t K j ≤ 1) ∧
      twoPhasePhaseOneTest X c q θ ε₀ ε (twoPhasePhaseOneRadii t K) (t.point K) ∧
      ∀ a, (totalEvaluations t a K : ℝ) ≤ κν a / 2 * ‖c x₀‖ *
        geometricCostWeight q β θ π * primalDualCostWeight q ε₀ ε π := by
  obtain ⟨κν, hκν, _, hbound⟩ :=
    lemma_14_3_7 (S := S) (step := step) (terminal := terminal)
      hc hx₀ hinput hθ hπ hκ
  refine ⟨κν, hκν, ?_⟩
  intro ε₀ ε t K phaseTwo N ht h
  obtain ⟨J, hJ, hs, hb, hx, hr, htest, he⟩ :=
    hbound ε₀ ε h.primal.1 h.primal.2 t ht h.phase_one
  have hJK : J = K := by
    apply le_antisymm
    · by_contra hn
      exact hb K (lt_of_not_ge hn) h.phase_one_stop
    · by_contra hn
      exact h.phase_one_first J (lt_of_not_ge hn) hs
  subst J
  exact ⟨hJ, hx, hr, htest, he⟩

end CartisGouldToint.Chapter14.Section03
