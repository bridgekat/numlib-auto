import Numlib.Optimization.CompositeModelCoercivity
import Numlib.Optimization.HigherOrderApproximateRegularizationTermination

/-!
# Finite returned composite inner executions

For existence, permitted minimization choices may select an attained global model minimum.
Failed inspections there can only halve unprotected radii, and the actual small-radius
decrease estimate forbids infinitely many halvings. A natural rank constructs the complete
finite history. This proves existence of a legal execution, rather than termination for every
possible approximate minimization choice.
-/

noncomputable section
open scoped Nat NNReal
open Set Metric
namespace Optimization.CompositeRegularization
open CompositeTaylorModels
open HigherOrderApproximateRegularization (Parameters ValidRadii InnerState InnerPhase
  InnerInitial accuracyTarget accuracyTarget_bounds radiusFloor radiusFloor_bounds
  geometricCountdown geometricCountdown_halve_lt phaseCost)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Small-radius generalized Taylor decrement gives actual decrease of the composite
objective. This analytic property does not assume any algorithmic return or criticality. -/
def SmallRadiusDecrease (P : Parameters) (g : E → ℝ) (v : E → F) (h : F → ℝ) (M : ℝ) : Prop :=
  ∀ s : E, ‖s‖ ≤ 1 → ∀ j, 1 ≤ j → j ≤ P.q → ∀ δ : ℝ,
    0 < δ → δ ≤ 1 → 4 * M * δ ≤ accuracyTarget P j → ∀ d : E, ‖d‖ ≤ δ →
      accuracyTarget P j * δ ^ j / (j ! : ℝ) ≤ decrement g v h j s d →
      accuracyTarget P j * δ ^ j / (2 * (j ! : ℝ)) ≤
        objective g v h s - objective g v h (s + d)

/-- A genuine halving starts above twice the eventual radius floor. -/
theorem radius_gt_of_small_actual_decrease {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {M : ℝ} (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P g v h M)
    {s d : E} {j : ℕ} {δ : ℝ} (hs : ‖s‖ ≤ 1) (hj : 1 ≤ j) (hjq : j ≤ P.q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ)
    (hfail : accuracyTarget P j * δ ^ j / (j ! : ℝ) < decrement g v h j s d)
    (hsmall : objective g v h s - objective g v h (s + d) <
      (1 / 2 : ℝ) * accuracyTarget P j * δ ^ j / (j ! : ℝ)) :
    2 * radiusFloor P M j < δ := by
  have hM0 : 0 < M := by linarith
  by_contra hn
  have hδsmall : 4 * M * δ ≤ accuracyTarget P j := by
    have hh : δ ≤ 2 * radiusFloor P M j := le_of_not_gt hn
    dsimp [radiusFloor] at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 8 * M)).mp
      (show δ / 2 ≤ accuracyTarget P j / (8 * M) by linarith only [hh])
    nlinarith only [hh']
  have hh := hdec s hs j hj hjq δ hδ hδ1 hδsmall d hd hfail.le
  have he : accuracyTarget P j * δ ^ j / (2 * (j ! : ℝ)) =
      (1 / 2 : ℝ) * accuracyTarget P j * δ ^ j / (j ! : ℝ) := by ring
  linarith only [hh, hsmall, he]

/-- Radius validity and the exact source floors hold through all actual inner transitions. -/
structure InnerBounds (P : Parameters) (M : ℝ) (a : InnerState E) : Prop where
  radii_valid : ValidRadii P a.radii
  radii_floor : ∀ j, 1 ≤ j → j ≤ P.q → radiusFloor P M j ≤ a.radii j
  inspect : ∀ j, a.phase = .inspect j → 1 ≤ j ∧ j ≤ P.q ∧ ‖a.step‖ < 1

omit [NormedSpace ℝ E] in
/-- Unit initialization satisfies every positive quantitative radius floor. -/
theorem initial_bounds {P : Parameters} {M : ℝ} (hM : 1 ≤ M)
    {a : InnerState E} (ha : InnerInitial a) : InnerBounds P M a where
  radii_valid := by intro j _ _; rw [ha.2.2.1]; norm_num
  radii_floor := by
    intro j hj hjq
    rw [ha.2.2.1]
    exact (radiusFloor_bounds P hM hj hjq).2
  inspect := by intro j hj; rw [ha.2.2.2] at hj; contradiction

/-- Every actual composite inner transition preserves validity, floors and inspection norms. -/
theorem InnerTransition.bounds {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P g v h M) {a b : InnerState E}
    (ht : InnerTransition P g v h convex hconv z a b) (ha : InnerBounds P M a) :
    InnerBounds P M b := by
  classical
  cases ht with
  | minimize hphase s hfrac =>
    refine ⟨ha.radii_valid, ha.radii_floor, ?_⟩
    intro j hj
    dsimp at hj
    by_cases hs : 1 ≤ ‖s‖
    · simp [hs] at hj
    · simp only [ite_eq_right hs] at hj
      have he : j = 1 := (InnerPhase.inspect.inj hj).symm
      subst j
      exact ⟨le_rfl, P.order_pos, lt_of_not_ge hs⟩
  | pass j hphase hj hjq d hw htest =>
    refine ⟨ha.radii_valid, ha.radii_floor, ?_⟩
    intro i hi
    dsimp at hi
    by_cases he : j = P.q
    · simp [he] at hi
    · simp only [ite_eq_right he] at hi
      have hei : i = j + 1 := (InnerPhase.inspect.inj hi).symm
      subst i
      exact ⟨by omega, by omega, (ha.inspect j hphase).2.2⟩
  | halve j hphase hj hjq hbranch d hw hfail hsmall =>
    have hδ := ha.radii_valid j hj hjq
    have hlarge := radius_gt_of_small_actual_decrease hM hdec
      (ha.inspect j hphase).2.2.le hj hjq hδ.1 hδ.2 hw.feasible hfail
      (by simpa only [accuracyTarget, mul_assoc] using hsmall)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi hiq
      change 0 < Function.update a.radii j (a.radii j / 2) i ∧
        Function.update a.radii j (a.radii j / 2) i ≤ 1
      by_cases he : i = j
      · subst i
        simp only [Function.update_self]
        exact ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
      · rw [Function.update_of_ne he]
        exact ha.radii_valid i hi hiq
    · intro i hi hiq
      change radiusFloor P M i ≤ Function.update a.radii j (a.radii j / 2) i
      by_cases he : i = j
      · subst i
        simp only [Function.update_self]
        linarith only [hlarge]
      · rw [Function.update_of_ne he]
        exact ha.radii_floor i hi hiq
    · intro i hi
      exact ha.inspect i (hphase.trans hi)
  | improve => exact ⟨ha.radii_valid, ha.radii_floor, fun i hi => by contradiction⟩

/-- Every finite actual inner history retains positive valid radii and all source floors. -/
theorem InnerExecution.bounds {P : Parameters} {g : E → ℝ} {v : E → F} {h : F → ℝ}
    {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P g v h M) {N : ℕ}
    (run : InnerExecution P g v h convex hconv z N) {k : ℕ} (hk : k ≤ N) :
    InnerBounds P M (run.state k) := by
  induction k with
  | zero => exact initial_bounds hM run.initial
  | succ k ih => exact (run.transition k (by omega)).bounds hM hdec (ih (by omega))

/-- The rank of an exact-minimum inspection epoch counts radius halvings and pending tests. -/
def minimumInspectionRank (P : Parameters) (M : ℝ) (a : InnerState E) : ℕ :=
  if a.phase = .returned then 0 else
    ((∑ j ∈ Finset.Icc 1 P.q,
      geometricCountdown (2 * radiusFloor P M j) (a.radii j)) + 1) * (P.q + 2) +
        phaseCost P.q a.phase

private theorem radius_count_lt {P : Parameters} {M : ℝ} (hM : 1 ≤ M)
    {δ : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q)
    (hδ : 2 * radiusFloor P M j < δ j) :
    (∑ i ∈ Finset.Icc 1 P.q,
      geometricCountdown (2 * radiusFloor P M i) (Function.update δ j (δ j / 2) i)) <
    ∑ i ∈ Finset.Icc 1 P.q, geometricCountdown (2 * radiusFloor P M i) (δ i) := by
  have hstrict := geometricCountdown_halve_lt
    (mul_pos (by norm_num) (radiusFloor_bounds P hM hj hjq).1) hδ
  apply Finset.sum_lt_sum
  · intro i _
    by_cases he : i = j
    · subst i
      simpa using hstrict.le
    · simp only [Function.update_of_ne he, le_refl]
  · exact ⟨j, Finset.mem_Icc.mpr ⟨hj, hjq⟩, by simpa using hstrict⟩

/-- An actual transition that does not improve the minimization fraction strictly decreases
its inspection rank. No correctness or termination conclusion is an algorithm field. -/
theorem InnerTransition.minimumInspectionRank_lt {P : Parameters} {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {convex : Bool} {hconv : convex = true → ConvexOn ℝ univ h} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P g v h M) {a b : InnerState E}
    (ht : InnerTransition P g v h convex hconv z a b) (ha : InnerBounds P M a)
    (hb : b.phase ≠ .minimize) : minimumInspectionRank P M b < minimumInspectionRank P M a := by
  classical
  cases ht with
  | minimize hphase s hfrac =>
    by_cases hs : 1 ≤ ‖s‖
    · simp [minimumInspectionRank, phaseCost, hphase, hs]
    · simp [minimumInspectionRank, phaseCost, hphase, hs]
  | pass j hphase hj hjq d hw htest =>
    by_cases he : j = P.q
    · simp [minimumInspectionRank, phaseCost, hphase, he]
    · simp only [minimumInspectionRank, phaseCost, hphase, ite_eq_right he]
      simp only [reduceCtorEq, ite_false]
      omega
  | halve j hphase hj hjq hbranch d hw hfail hsmall =>
    have hδ := ha.radii_valid j hj hjq
    have hlarge := radius_gt_of_small_actual_decrease hM hdec
      (ha.inspect j hphase).2.2.le hj hjq hδ.1 hδ.2 hw.feasible hfail
      (by simpa only [accuracyTarget, mul_assoc] using hsmall)
    have hcnt := radius_count_lt hM hj hjq hlarge
    simp only [minimumInspectionRank, hphase, reduceCtorEq, ite_false, phaseCost]
    nlinarith
  | improve => exact (hb rfl).elim

/-- A strict unit-norm minimizer admits a legal fractional step just outside the unit ball.
This keeps the strict source long-step conclusion compatible with the literal weak-boundary
return instruction. -/
theorem exists_fraction_long_step {w : E → ℝ} (hw : Continuous w) {z : E} {μ : ℝ}
    (hμ : μ < 1) (hz : ‖z‖ = 1) (hstrict : w z < w 0) :
    ∃ s : E, 1 < ‖s‖ ∧ μ * (w 0 - w z) ≤ w 0 - w s := by
  have hval : w z < w 0 - μ * (w 0 - w z) := by nlinarith
  have hcont : Continuous (fun t : ℝ => w (t • z)) :=
    hw.comp (continuous_id.smul continuous_const)
  have hevent : ∀ᶠ t : ℝ in nhds (1 : ℝ),
      w (t • z) < w 0 - μ * (w 0 - w z) :=
    (hcont.tendsto 1).eventually (eventually_lt_nhds (by simpa only [one_smul] using hval))
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hevent
  have ht : dist (1 + ε / 2) (1 : ℝ) < ε := by
    rw [Real.dist_eq]
    have he : 1 + ε / 2 - 1 = ε / 2 := by ring
    rw [he, abs_of_pos (by positivity)]
    linarith
  refine ⟨(1 + ε / 2) • z, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hz, mul_one]
    linarith
  · have := hb ht
    linarith

/-- At a composite global minimum, any failed inspection at a protected convex first order
is impossible. This is the first-order necessary condition, with the outer map undifferentiated. -/
theorem not_failed_first_of_minimum {g : E → ℝ} {v : E → F} {h : F → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {z d : E} (hg : DifferentiableAt ℝ g z)
    (hv : DifferentiableAt ℝ v z) (hconv : ConvexOn ℝ univ h)
    (hmin : ∀ t, objective g v h z ≤ objective g v h t) :
    decrement g v h 1 z d ≤ 0 := by
  have he := first_model_min_of_convex_localMin hg hv hh hconv
    (Filter.Eventually.of_forall hmin) d
  dsimp [decrement]
  linarith only [he]

/-- An attained composite model minimum yields an actual initialized finite inner history.
The exact-minimum inspections terminate by a natural radius-halving rank. A strict unit
boundary minimum uses an outward fractional step, so the final norm is never exactly one.
The initial accuracy fraction is retained exactly. -/
theorem exists_inner_return_execution [ProperSpace E] (P : Parameters)
    {g : E → ℝ} {v : E → F} {h : F → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h)
    (hw : Continuous (objective g v h)) {z : E} (hg : DifferentiableAt ℝ g z)
    (hv : DifferentiableAt ℝ v z) (hmin : ∀ t, objective g v h z ≤ objective g v h t)
    (hboundary : ‖z‖ = 1 → objective g v h z < objective g v h 0)
    {convex : Bool} (hconv : convex = true → ConvexOn ℝ univ h)
    {M : ℝ} (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P g v h M)
    {a : InnerState E} (hinit : InnerInitial a) (hμ : a.mu < 1) :
    ∃ N, ∃ run : InnerExecution P g v h convex hconv z N,
      run.state 0 = a ∧ (run.state N).phase = .returned ∧ ‖(run.state N).step‖ ≠ 1 := by
  classical
  let good : InnerState E → Prop := fun b => InnerBounds P M b ∧ b.mu = a.mu ∧
    (∀ j, b.phase = .inspect j → b.step = z) ∧
    (b.phase ≠ .minimize → ‖b.step‖ ≠ 1)
  let R : InnerState E → InnerState E → Prop := fun b c =>
    InnerTransition P g v h convex hconv z b c ∧ good c ∧ c.phase ≠ .minimize
  have ha : good a := ⟨initial_bounds hM hinit, rfl,
    fun j hj => by rw [hinit.2.2.2] at hj; contradiction,
    fun hp => (hp hinit.2.2.2).elim⟩
  have hnext : ∀ b, good b → b.phase ≠ .returned → ∃ c, R b c := by
    intro b hb hnot
    cases hp : b.phase with
    | minimize =>
      by_cases hz : ‖z‖ = 1
      · obtain ⟨s, hs, hfrac⟩ := exists_fraction_long_step hw hμ hz (hboundary hz)
        have ht := InnerTransition.minimize (P := P) (convex_correct := hconv) b hp s
          (by simpa only [hb.2.1] using hfrac)
        refine ⟨_, ht, ?_, ?_⟩
        · refine ⟨ht.bounds hM hdec hb.1, hb.2.1, ?_, ?_⟩
          · simp [hs.le]
          · simpa [hs.le] using ne_of_gt hs
        · simp [hs.le]
      · have hfrac : b.mu * (objective g v h 0 - objective g v h z) ≤
            objective g v h 0 - objective g v h z :=
          mul_le_of_le_one_left (sub_nonneg.mpr (hmin 0)) (by rw [hb.2.1]; exact hμ.le)
        have ht := InnerTransition.minimize (P := P) (convex_correct := hconv) b hp z hfrac
        refine ⟨_, ht, ?_, ?_⟩
        · refine ⟨ht.bounds hM hdec hb.1, hb.2.1, ?_, ?_⟩
          · intro j hj
            rfl
          · intro _
            exact hz
        · dsimp
          split_ifs <;> decide
    | inspect j =>
      obtain ⟨hj, hjq, hs⟩ := hb.1.inspect j hp
      have hδ := hb.1.radii_valid j hj hjq
      obtain ⟨d, hd, _⟩ := exists_fraction_gapWitness g v hh j b.step hδ.1.le
        P.fraction_pos.le P.fraction_le_one
      by_cases htest : decrement g v h j b.step d ≤
          P.fraction * P.theta * P.epsilon j * b.radii j ^ j / (j ! : ℝ)
      · have ht := InnerTransition.pass (convex_correct := hconv) (minimizer := z)
          b j hp hj hjq d hd htest
        refine ⟨_, ht, ?_, ?_⟩
        · exact ⟨ht.bounds hM hdec hb.1, hb.2.1,
            fun i hi => hb.2.2.1 j hp, fun _ => ne_of_lt hs⟩
        · dsimp
          split_ifs <;> decide
      · have hfail := lt_of_not_ge htest
        have hbranch : 2 ≤ j ∨ convex = false := by
          by_contra hn
          have hj1 : j = 1 := by omega
          have htrue : convex = true := by cases convex <;> simp_all
          have hz := hb.2.2.1 j hp
          have he := not_failed_first_of_minimum hh hg hv (hconv htrue) hmin (d := d)
          rw [hz, hj1] at hfail
          have hpos : 0 < P.fraction * P.theta * P.epsilon 1 * b.radii 1 ^ 1 / (1 ! : ℝ) := by
            have hε := P.epsilon_pos 1 le_rfl P.order_pos
            have hδ' := (hb.1.radii_valid 1 le_rfl P.order_pos).1
            have hf := P.fraction_pos
            have ht := P.theta_pos
            positivity
          linarith only [he, hfail, hpos]
        have hsmall : objective g v h b.step - objective g v h (b.step + d) <
            (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * b.radii j ^ j / (j ! : ℝ) := by
          have hnonpos : objective g v h b.step - objective g v h (b.step + d) ≤ 0 := by
            rw [hb.2.2.1 j hp]
            exact sub_nonpos.mpr (hmin (z + d))
          have hpos : 0 < (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j *
              b.radii j ^ j / (j ! : ℝ) := by
            have hε := P.epsilon_pos j hj hjq
            have hδ0 := hδ.1
            have hf := P.fraction_pos
            have ht := P.theta_pos
            positivity
          exact hnonpos.trans_lt hpos
        have ht := InnerTransition.halve (convex_correct := hconv) (minimizer := z) b j hp hj hjq
          hbranch d hd hfail hsmall
        refine ⟨_, ht, ?_, by simp⟩
        exact ⟨ht.bounds hM hdec hb.1, hb.2.1,
          fun i hi => hb.2.2.1 j hp, fun _ => ne_of_lt hs⟩
    | returned => exact (hnot hp).elim
  have hpres : ∀ b c, good b → R b c → good c := fun _ _ _ ht => ht.2.1
  have hdrop : ∀ b c, good b → R b c →
      minimumInspectionRank P M c < minimumInspectionRank P M b := by
    intro b c hb ht
    exact ht.1.minimumInspectionRank_lt hM hdec hb.1 ht.2.2
  obtain ⟨N, state, hzero, hstop, htrans⟩ := Relation.exists_finite_stopped_chain_of_rank R
    (minimumInspectionRank P M) (fun b => b.phase = .returned) good hnext hpres hdrop ha
  have hgood : ∀ k, k ≤ N → good (state k) := by
    intro k hk
    induction k with
    | zero => simpa only [hzero] using ha
    | succ k ih => exact (htrans k (by omega)).2.1
  exact ⟨N, ⟨state, hmin, by simpa only [hzero] using hinit,
    fun k hk => (htrans k hk).1⟩, hzero, hstop,
      (hgood N le_rfl).2.2.2 (by rw [hstop]; decide)⟩

end Optimization.CompositeRegularization
