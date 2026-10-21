import Numlib.Order.WellFounded.FiniteChain
import Numlib.Optimization.HigherOrderApproximateRegularizationInner
import Numlib.Topology.Order.NearMinimum
import Numlib.Optimization.TaylorGapContinuity

/-!
# Finite progress of the actual inner regularization procedure

Positive Taylor decrease at small radii prevents unbounded radius halving. Compactness of
the model sublevel excludes failed low-order tests near its global minimum. A geometric
countdown combines the remaining accuracy and radius refinements with the program phase.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.HigherOrderApproximateRegularization
open TaylorCriticality

private theorem exists_geometric_threshold {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ∃ n : ℕ, x * (1 / 2 : ℝ) ^ n ≤ η := by
  by_cases hx : x ≤ 0
  · exact ⟨0, by simpa using hx.trans hη.le⟩
  · have hx' : 0 < x := lt_of_not_ge hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hη hx')
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    have := (lt_div_iff₀ hx').mp hn
    nlinarith

/-- The least number of halvings needed to meet a positive real threshold. -/
def geometricCountdown (η x : ℝ) : ℕ :=
  if hη : 0 < η then Nat.find (exists_geometric_threshold hη x) else 0

/-- The countdown's defining threshold is attained. -/
theorem geometricCountdown_spec {η : ℝ} (hη : 0 < η) (x : ℝ) :
    x * (1 / 2 : ℝ) ^ geometricCountdown η x ≤ η := by
  rw [geometricCountdown, dite_eq_left hη]
  exact Nat.find_spec (exists_geometric_threshold hη x)

/-- Any successful number of halvings bounds the least countdown. -/
theorem geometricCountdown_le {η x : ℝ} (hη : 0 < η) {n : ℕ}
    (hn : x * (1 / 2 : ℝ) ^ n ≤ η) : geometricCountdown η x ≤ n := by
  rw [geometricCountdown, dite_eq_left hη]
  exact Nat.find_min' (exists_geometric_threshold hη x) hn

/-- Halving a value still above the threshold strictly decreases its countdown. -/
theorem geometricCountdown_halve_lt {η x : ℝ} (hη : 0 < η) (hx : η < x) :
    geometricCountdown η (x / 2) < geometricCountdown η x := by
  have hn : 0 < geometricCountdown η x := by
    by_contra hn
    have he : geometricCountdown η x = 0 := by omega
    have hs := geometricCountdown_spec hη x
    rw [he, pow_zero, mul_one] at hs
    linarith
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hs := geometricCountdown_spec hη x
  rw [he, pow_succ] at hs
  have hh : x / 2 * (1 / 2 : ℝ) ^ n ≤ η := by nlinarith only [hs]
  have := geometricCountdown_le hη hh
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniformly near its minimum value on a compact initial sublevel, all low-order gaps
are below their fixed positive stopping thresholds. -/
theorem exists_model_gap_threshold [ProperSpace E] (P : Parameters) {m : E → ℝ} {z : E}
    (hm : ContDiff ℝ P.q m) (hcompact : IsCompact {s | m s ≤ m 0})
    (hmin : ∀ s, m z ≤ m s) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : E, m s ≤ m 0 → m s ≤ m z + η →
      ∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 →
      gapOn (taylorDecrement m j s) (closedBall 0 1) <
        P.fraction * P.theta * P.epsilon j / (j ! : ℝ) := by
  classical
  have hex : ∀ j : Fin (P.q + 1), ∃ η : ℝ, 0 < η ∧
      ∀ s : E, m s ≤ m 0 → m s ≤ m z + η →
      1 ≤ (j : ℕ) → (j : ℕ) ≤ 2 →
      gapOn (taylorDecrement m j s) (closedBall 0 1) <
        P.fraction * P.theta * P.epsilon j / ((j : ℕ) ! : ℝ) := by
    intro j
    by_cases hj : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 2
    · have hjq : (j : ℕ) ≤ P.q := Nat.le_of_lt_succ j.isLt
      have hmj : ContDiff ℝ (j : ℕ) m := hm.of_le (by exact_mod_cast hjq)
      obtain ⟨η, hη, hb⟩ := hcompact.exists_pos_forall_lt_of_near_minimum hm.continuous
        (continuous_gapOn_taylorDecrement hmj 1) (fun s _ => hmin s)
        (fun s _ hs => gapOn_taylorDecrement_eq_zero_of_isLocalMin
          (by omega : (j : ℕ) = 1 ∨ (j : ℕ) = 2) hmj
          (Filter.Eventually.of_forall fun t => hs ▸ hmin t) (by norm_num))
        (div_pos (mul_pos (mul_pos P.fraction_pos P.theta_pos)
          (P.epsilon_pos j hj.1 hjq)) (by positivity : (0 : ℝ) < ((j : ℕ) ! : ℝ)))
      exact ⟨η, hη, fun s hs hsη _ _ => hb s hs hsη⟩
    · exact ⟨1, by norm_num, fun _ _ _ h1 h2 => (hj ⟨h1, h2⟩).elim⟩
  choose η hη using hex
  let ηmin := (Finset.univ.image η).min' (by simp)
  have hηmin : 0 < ηmin := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hη j).1
  refine ⟨ηmin, hηmin, fun s hs hsη j hj hjq hj2 => ?_⟩
  have hle : ηmin ≤ η ⟨j, by omega⟩ := Finset.min'_le _ _ (Finset.mem_image_of_mem _ (by simp))
  exact (hη ⟨j, by omega⟩).2 s hs (hsη.trans (by linarith)) hj hj2

/-- The positive coefficient of the model stopping threshold at a requested order. -/
def accuracyTarget (P : Parameters) (j : ℕ) : ℝ := P.fraction * P.theta * P.epsilon j

/-- Every requested stopping coefficient is positive and at most one. -/
theorem accuracyTarget_bounds (P : Parameters) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    0 < accuracyTarget P j ∧ accuracyTarget P j ≤ 1 := by
  refine ⟨mul_pos (mul_pos P.fraction_pos P.theta_pos) (P.epsilon_pos j hj hjq), ?_⟩
  have hf : P.fraction * P.theta ≤ 1 :=
    (mul_le_mul_of_nonneg_right P.fraction_le_one P.theta_pos.le).trans
      (by simpa using P.theta_lt_one.le)
  exact (mul_le_mul_of_nonneg_right hf (P.epsilon_pos j hj hjq).le).trans
    (by simpa using (P.epsilon_lt_one j hj hjq).le)

/-- The radius floor forced by the small-radius actual-decrease estimate. -/
def radiusFloor (P : Parameters) (M : ℝ) (j : ℕ) : ℝ := accuracyTarget P j / (8 * M)

/-- The floor is positive and no greater than one. -/
theorem radiusFloor_bounds (P : Parameters) {M : ℝ} (hM : 1 ≤ M) {j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    0 < radiusFloor P M j ∧ radiusFloor P M j ≤ 1 := by
  have hM0 : 0 < M := by linarith
  obtain ⟨hα, hα1⟩ := accuracyTarget_bounds P hj hjq
  refine ⟨div_pos hα (by positivity), ?_⟩
  exact (div_le_iff₀ (by positivity : 0 < 8 * M)).mpr (by linarith)

/-- A local Taylor decrement at a small radius guarantees half its target as actual decrease.
This property follows from the usual Lipschitz model derivative estimates. -/
def SmallRadiusDecrease (P : Parameters) (m : E → ℝ) (M : ℝ) : Prop :=
  ∀ s : E, ‖s‖ ≤ 1 → ∀ j, 1 ≤ j → j ≤ P.q → ∀ δ : ℝ,
    0 < δ → δ ≤ 1 → 4 * M * δ ≤ accuracyTarget P j → ∀ d : E, ‖d‖ ≤ δ →
      accuracyTarget P j * δ ^ j / (j ! : ℝ) ≤ taylorDecrement m j s d →
      accuracyTarget P j * δ ^ j / (2 * (j ! : ℝ)) ≤ m s - m (s + d)

/-- State bounds proved from the initialization and the literal transitions. They include
no convergence or termination assumption. -/
structure InnerBounds (P : Parameters) (M : ℝ) (a : InnerState E) : Prop where
  radii_valid : ValidRadii P a.radii
  radii_low : ∀ j, j ≤ 2 → a.radii j = 1
  radii_floor : ∀ j, 3 ≤ j → j ≤ P.q → radiusFloor P M j ≤ a.radii j
  inspect : ∀ j, a.phase = .inspect j → 1 ≤ j ∧ j ≤ P.q ∧ ‖a.step‖ ≤ 1

omit [NormedSpace ℝ E] in
/-- Initial unit radii satisfy every required radius floor. -/
theorem InnerInitial.bounds {P : Parameters} {M : ℝ} (hM : 1 ≤ M)
    {a : InnerState E} (ha : InnerInitial a) : InnerBounds P M a where
  radii_valid := by intro j _ _; rw [ha.2.2.1]; norm_num
  radii_low := by intro j _; rw [ha.2.2.1]
  radii_floor := by
    intro j hj hjq
    rw [ha.2.2.1]
    exact (radiusFloor_bounds P hM (by omega) hjq).2
  inspect := by intro j hj; rw [ha.2.2.2] at hj; contradiction

/-- A legal halving must start above twice the eventual radius floor. -/
theorem radius_gt_of_small_actual_decrease {P : Parameters} {m : E → ℝ} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P m M) {s d : E} {j : ℕ} {δ : ℝ}
    (hs : ‖s‖ ≤ 1) (hj : 3 ≤ j) (hjq : j ≤ P.q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : ‖d‖ ≤ δ)
    (hfail : accuracyTarget P j * δ ^ j / (j ! : ℝ) < taylorDecrement m j s d)
    (hsmall : m s - m (s + d) <
      (1 / 2 : ℝ) * accuracyTarget P j * δ ^ j / (j ! : ℝ)) :
    2 * radiusFloor P M j < δ := by
  have hM0 : 0 < M := by linarith
  by_contra h
  have hδsmall : 4 * M * δ ≤ accuracyTarget P j := by
    have hh : δ ≤ 2 * radiusFloor P M j := le_of_not_gt h
    dsimp [radiusFloor] at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 8 * M)).mp
      (show δ / 2 ≤ accuracyTarget P j / (8 * M) by linarith only [hh])
    nlinarith only [hh']
  have hh := hdec s hs j (by omega) hjq δ hδ hδ1 hδsmall d hd hfail.le
  have he : accuracyTarget P j * δ ^ j / (2 * (j ! : ℝ)) =
      (1 / 2 : ℝ) * accuracyTarget P j * δ ^ j / (j ! : ℝ) := by ring
  linarith only [hh, hsmall, he]

/-- Every literal inner transition preserves the derived radius and inspection bounds. -/
theorem InnerTransition.bounds {P : Parameters} {m : E → ℝ} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P m M) {a b : InnerState E}
    (h : InnerTransition P m z a b) (ha : InnerBounds P M a) : InnerBounds P M b := by
  classical
  cases h with
  | minimize hphase s hfrac =>
    refine ⟨ha.radii_valid, ha.radii_low, ha.radii_floor, ?_⟩
    intro j hj
    dsimp at hj
    by_cases hs : 1 ≤ ‖s‖
    · simp [hs] at hj
    · simp only [ite_eq_right hs] at hj
      have he : j = 1 := (InnerPhase.inspect.inj hj).symm
      subst j
      exact ⟨le_rfl, P.order_pos, (lt_of_not_ge hs).le⟩
  | pass j hphase hj hjq d hw htest =>
    refine ⟨ha.radii_valid, ha.radii_low, ha.radii_floor, ?_⟩
    intro i hi
    dsimp at hi
    by_cases he : j = P.q
    · simp [he] at hi
    · simp only [ite_eq_right he] at hi
      have hei : i = j + 1 := (InnerPhase.inspect.inj hi).symm
      subst i
      exact ⟨by omega, by omega, (ha.inspect j hphase).2.2⟩
  | halve j hphase hj hjq d hw hfail hsmall =>
    have hδ := ha.radii_valid j (by omega) hjq
    have hlarge := radius_gt_of_small_actual_decrease hM hdec
      (ha.inspect j hphase).2.2 hj hjq hδ.1 hδ.2 hw.feasible hfail
      (by simpa only [accuracyTarget, mul_assoc] using hsmall)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi hiq
      change 0 < Function.update a.radii j (a.radii j / 2) i ∧
        Function.update a.radii j (a.radii j / 2) i ≤ 1
      by_cases he : i = j
      · subst i
        simp only [Function.update_self]
        exact ⟨div_pos hδ.1 (by norm_num), by linarith [hδ.2]⟩
      · rw [Function.update_of_ne he]
        exact ha.radii_valid i hi hiq
    · intro i hi
      change Function.update a.radii j (a.radii j / 2) i = 1
      rw [Function.update_of_ne (by omega : i ≠ j)]
      exact ha.radii_low i hi
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
  | improve j hphase hj hjq d hw hfail hother =>
    exact ⟨ha.radii_valid, ha.radii_low, ha.radii_floor, fun i hi => by contradiction⟩

/-- Every literal finite prefix satisfies the derived radius floors and inspection bounds. -/
theorem InnerExecution.bounds {P : Parameters} {m : E → ℝ} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P m M) {N : ℕ}
    (h : InnerExecution P m z N) {k : ℕ} (hk : k ≤ N) : InnerBounds P M (h.state k) := by
  induction k with
  | zero => exact h.initial.bounds hM
  | succ k ih => exact (h.transition k (by omega)).bounds hM hdec (ih (by omega))

/-- An accuracy threshold forces every failed improving inspection to occur while the
remaining fraction-of-global-decrease error is above that threshold. -/
def AccuracyThreshold (P : Parameters) (m : E → ℝ) (z : E) (M η : ℝ) : Prop :=
  ∀ a : InnerState E, InnerBounds P M a → 0 ≤ a.mu →
    a.mu * (m 0 - m z) ≤ m 0 - m a.step → ∀ j, a.phase = .inspect j →
      1 ≤ j → j ≤ P.q → ∀ d : E,
        GapWitness m j a.step (a.radii j) P.fraction d →
        accuracyTarget P j * a.radii j ^ j / (j ! : ℝ) < taylorDecrement m j a.step d →
        (j ≤ 2 ∨ (1 / 2 : ℝ) * accuracyTarget P j * a.radii j ^ j / (j ! : ℝ) ≤
          m a.step - m (a.step + d)) → η < (1 - a.mu) * (m 0 - m z)

/-- Compactness and smoothness give a positive accuracy threshold uniformly over all legal
inspection points and all feasible fraction witnesses. -/
theorem exists_accuracyThreshold [ProperSpace E] (P : Parameters) {m : E → ℝ} {z : E}
    {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s) :
    ∃ η : ℝ, 0 < η ∧ AccuracyThreshold P m z M η := by
  classical
  obtain ⟨ηlow, hηlow, hlow⟩ := exists_model_gap_threshold P hm hcompact hmin
  let c : Fin (P.q + 1) → ℝ := fun j => if 3 ≤ (j : ℕ) then
    accuracyTarget P j * radiusFloor P M j ^ (j : ℕ) / (2 * ((j : ℕ) ! : ℝ)) else 1
  have hc : ∀ j, 0 < c j := by
    intro j
    dsimp [c]
    split_ifs with hj
    · exact div_pos (mul_pos (accuracyTarget_bounds P (by omega)
        (Nat.le_of_lt_succ j.isLt)).1 (pow_pos (radiusFloor_bounds P hM (by omega)
          (Nat.le_of_lt_succ j.isLt)).1 _)) (by positivity)
    · norm_num
  let cmin := (Finset.univ.image c).min' (by simp)
  have hcmin : 0 < cmin := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hc j
  refine ⟨min ηlow (cmin / 2), lt_min hηlow (by positivity), ?_⟩
  intro a ha hμ hfrac j hphase hj hjq d hw hfail hother
  by_contra hnot
  have herr : (1 - a.mu) * (m 0 - m z) ≤ min ηlow (cmin / 2) := le_of_not_gt hnot
  have hnear : m a.step ≤ m z + ηlow := by
    have hη := min_le_left ηlow (cmin / 2)
    nlinarith only [herr, hfrac, hη]
  have hnonincrease : m a.step ≤ m 0 := model_nonincrease_of_fraction hmin hμ hfrac
  by_cases hjlow : j ≤ 2
  · have hg := hlow a.step hnonincrease hnear j hj hjq hjlow
    have hd : d ∈ closedBall (0 : E) 1 := by
      rw [← ha.radii_low j hjlow]
      simpa using hw.feasible
    have hupper := le_gapOn (isCompact_closedBall (0 : E) 1)
      (continuous_taylorDecrement m j a.step).continuousOn hd
    rw [ha.radii_low j hjlow, one_pow, mul_one] at hfail
    dsimp [accuracyTarget] at hfail
    linarith only [hg, hupper, hfail]
  · have hjhigh : 3 ≤ j := by omega
    have hdecrease := hother.resolve_left hjlow
    have hfloor := ha.radii_floor j hjhigh hjq
    have hfloor0 := (radiusFloor_bounds P hM hj hjq).1
    have hα := (accuracyTarget_bounds P hj hjq).1
    have hpower := pow_le_pow_left₀ hfloor0.le hfloor j
    have hdiv : accuracyTarget P j * radiusFloor P M j ^ j / (2 * (j ! : ℝ)) ≤
        accuracyTarget P j * a.radii j ^ j / (2 * (j ! : ℝ)) := by gcongr
    have hcj : cmin ≤ accuracyTarget P j * radiusFloor P M j ^ j / (2 * (j ! : ℝ)) := by
      have hh : cmin ≤ c ⟨j, by omega⟩ :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem _ (by simp))
      simpa only [c, ite_eq_left hjhigh] using hh
    have heq : accuracyTarget P j * a.radii j ^ j / (2 * (j ! : ℝ)) =
        (1 / 2 : ℝ) * accuracyTarget P j * a.radii j ^ j / (j ! : ℝ) := by ring
    have hη := min_le_right ηlow (cmin / 2)
    have hglob := hmin (a.step + d)
    nlinarith only [herr, hfrac, hdecrease, hdiv, hcj, heq, hη, hglob, hcmin]

/-- Remaining geometric refinements of the accuracy fraction and higher-order radii. -/
def refinementCount (P : Parameters) (m : E → ℝ) (z : E) (M η : ℝ)
    (a : InnerState E) : ℕ :=
  geometricCountdown η ((1 - a.mu) * (m 0 - m z)) +
    ∑ j ∈ Finset.Icc 3 P.q, geometricCountdown (2 * radiusFloor P M j) (a.radii j)

/-- The remaining inspections within a single minimization pass. -/
def phaseCost (q : ℕ) : InnerPhase → ℕ
  | .minimize => q + 1
  | .inspect j => q + 1 - j
  | .returned => 0

/-- A natural-valued progress measure; a returned state has rank zero. -/
def progressRank (P : Parameters) (m : E → ℝ) (z : E) (M η : ℝ)
    (a : InnerState E) : ℕ :=
  if a.phase = .returned then 0 else
    (refinementCount P m z M η a + 1) * (P.q + 2) + phaseCost P.q a.phase

omit [NormedSpace ℝ E] in
/-- Rank zero is exactly the returned phase. -/
theorem progressRank_eq_zero_iff (P : Parameters) (m : E → ℝ) (z : E) (M η : ℝ)
    (a : InnerState E) : progressRank P m z M η a = 0 ↔ a.phase = .returned := by
  unfold progressRank
  split_ifs with h
  · simp [h]
  · have : 0 < (refinementCount P m z M η a + 1) * (P.q + 2) := by positivity
    constructor
    · omega
    · exact fun he => (h he).elim

private theorem radius_count_lt {P : Parameters} {M : ℝ} (hM : 1 ≤ M)
    {δ : ℕ → ℝ} {j : ℕ} (hj : 3 ≤ j) (hjq : j ≤ P.q)
    (hδ : 2 * radiusFloor P M j < δ j) :
    (∑ i ∈ Finset.Icc 3 P.q,
      geometricCountdown (2 * radiusFloor P M i) (Function.update δ j (δ j / 2) i)) <
    ∑ i ∈ Finset.Icc 3 P.q, geometricCountdown (2 * radiusFloor P M i) (δ i) := by
  have hstrict := geometricCountdown_halve_lt
    (mul_pos (by norm_num) (radiusFloor_bounds P hM (by omega) hjq).1) hδ
  apply Finset.sum_lt_sum
  · intro i _
    by_cases he : i = j
    · subst i
      simpa using hstrict.le
    · simp only [Function.update_of_ne he, le_refl]
  · exact ⟨j, Finset.mem_Icc.mpr ⟨hj, hjq⟩, by simpa using hstrict⟩

/-- Every literal legal transition strictly decreases a natural-valued progress measure.
The accuracy threshold and radius floors were obtained from the actual model estimates. -/
theorem InnerTransition.progressRank_lt {P : Parameters} {m : E → ℝ} {z : E} {M η : ℝ}
    (hM : 1 ≤ M) (hη : 0 < η) (hguard : AccuracyThreshold P m z M η)
    (hdec : SmallRadiusDecrease P m M) {a b : InnerState E}
    (h : InnerTransition P m z a b) (ha : InnerBounds P M a) (hμ : 0 ≤ a.mu)
    (hfrac : a.phase ≠ .minimize → a.mu * (m 0 - m z) ≤ m 0 - m a.step) :
    progressRank P m z M η b < progressRank P m z M η a := by
  classical
  cases h with
  | minimize hphase s hf =>
    by_cases hs : 1 ≤ ‖s‖
    · simp [progressRank, phaseCost, hphase, hs]
    · simp [progressRank, refinementCount, phaseCost, hphase, hs]
  | pass j hphase hj hjq d hw htest =>
    by_cases he : j = P.q
    · simp [progressRank, phaseCost, hphase, he]
    · simp only [progressRank, refinementCount, phaseCost, hphase,
        ite_eq_right he]
      simp only [reduceCtorEq, ite_false]
      omega
  | halve j hphase hj hjq d hw hfail hsmall =>
    have hδ := ha.radii_valid j (by omega) hjq
    have hlarge := radius_gt_of_small_actual_decrease hM hdec
      (ha.inspect j hphase).2.2 hj hjq hδ.1 hδ.2 hw.feasible hfail
      (by simpa only [accuracyTarget, mul_assoc] using hsmall)
    have hcnt := radius_count_lt hM hj hjq hlarge
    simp only [progressRank, refinementCount, hphase, reduceCtorEq, ite_false, phaseCost]
    nlinarith
  | improve j hphase hj hjq d hw hfail hother =>
    have herr := hguard a ha hμ (hfrac (by simp [hphase])) j hphase hj hjq d hw hfail
      (by simpa only [accuracyTarget, mul_assoc] using hother)
    have hcnt := geometricCountdown_halve_lt hη herr
    have he : (1 - (1 + a.mu) / 2) * (m 0 - m z) =
        ((1 - a.mu) * (m 0 - m z)) / 2 := by ring
    simp only [progressRank, refinementCount, hphase, reduceCtorEq, ite_false, phaseCost, he]
    nlinarith

/-- Every finite literal execution consumes at most its initial progress rank. -/
theorem InnerExecution.length_add_rank_le {P : Parameters} {m : E → ℝ} {z : E} {M η : ℝ}
    (hM : 1 ≤ M) (hη : 0 < η) (hguard : AccuracyThreshold P m z M η)
    (hdec : SmallRadiusDecrease P m M) {N : ℕ} (h : InnerExecution P m z N) :
    N + progressRank P m z M η (h.state N) ≤ progressRank P m z M η (h.state 0) := by
  have hall : ∀ k, k ≤ N →
      k + progressRank P m z M η (h.state k) ≤ progressRank P m z M η (h.state 0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hi := ih (by omega)
      have hdrop := (h.transition k (by omega)).progressRank_lt hM hη hguard hdec
        (h.bounds hM hdec (by omega)) (h.mu_bounds (by omega)).1.le
        (h.fraction_of_ne_minimize (by omega))
      omega
  exact hall N le_rfl

/-- Increasing the initial value cannot shorten the required countdown. -/
theorem geometricCountdown_mono {η x y : ℝ} (hη : 0 < η) (hxy : x ≤ y) :
    geometricCountdown η x ≤ geometricCountdown η y := by
  apply geometricCountdown_le hη
  exact (mul_le_mul_of_nonneg_right hxy (by positivity)).trans (geometricCountdown_spec hη y)

/-- Any nonreturned valid state has a legal next transition. Neither an exact minimizer
choice nor a particular fraction witness is imposed on subsequent transitions. -/
theorem InnerTransition.exists_next [ProperSpace E] {P : Parameters} {m : E → ℝ} {z : E} {M : ℝ}
    (hmin : ∀ s, m z ≤ m s) {a : InnerState E} (ha : InnerBounds P M a)
    (hμ : a.mu ≤ 1) (hphase : a.phase ≠ .returned) :
    ∃ b, InnerTransition P m z a b := by
  classical
  cases hp : a.phase with
  | minimize =>
    exact ⟨_, InnerTransition.minimize a hp z
      (mul_le_of_le_one_left (sub_nonneg.mpr (hmin 0)) hμ)⟩
  | inspect j =>
    obtain ⟨hj, hjq, _⟩ := ha.inspect j hp
    obtain ⟨d, hw⟩ := exists_gapWitness m j a.step
      (ha.radii_valid j hj hjq).1.le P.fraction_le_one
    by_cases htest : taylorDecrement m j a.step d ≤
        P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)
    · exact ⟨_, InnerTransition.pass a j hp hj hjq d hw htest⟩
    · have hfail := lt_of_not_ge htest
      by_cases hjlow : j ≤ 2
      · exact ⟨_, InnerTransition.improve a j hp hj hjq d hw hfail (Or.inl hjlow)⟩
      · by_cases hsmall : m a.step - m (a.step + d) <
          (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)
        · exact ⟨_, InnerTransition.halve a j hp (by omega) hjq d hw hfail hsmall⟩
        · exact ⟨_, InnerTransition.improve a j hp hj hjq d hw hfail
            (Or.inr (le_of_not_gt hsmall))⟩
  | returned => exact (hphase hp).elim

/-- A compact smooth model with the small-radius decrease estimate admits one common bound
on all legal prefix lengths, uniformly over every allowed initial accuracy fraction. -/
theorem exists_inner_length_bound [ProperSpace E] (P : Parameters) {m : E → ℝ} {z : E}
    {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s)
    (hdec : SmallRadiusDecrease P m M) :
    ∃ B : ℕ, ∀ N, ∀ run : InnerExecution P m z N,
      N ≤ B ∧ (N = B → (run.state N).phase = .returned) := by
  obtain ⟨η, hη, hguard⟩ := exists_accuracyThreshold P hM hm hcompact hmin
  let C := geometricCountdown η (m 0 - m z) +
    ∑ j ∈ Finset.Icc 3 P.q, geometricCountdown (2 * radiusFloor P M j) 1
  let B := (C + 1) * (P.q + 2) + (P.q + 1)
  refine ⟨B, fun N run => ?_⟩
  have hrank := run.length_add_rank_le hM hη hguard hdec
  have hD : 0 ≤ m 0 - m z := sub_nonneg.mpr (hmin 0)
  have hμ := run.initial.1
  have herror : (1 - (run.state 0).mu) * (m 0 - m z) ≤ m 0 - m z := by
    nlinarith only [hD, hμ]
  have hcnt := geometricCountdown_mono hη herror
  have hstart : progressRank P m z M η (run.state 0) ≤ B := by
    simp only [progressRank, refinementCount, run.initial.2.2.1, run.initial.2.2.2,
      reduceCtorEq, ite_false, phaseCost]
    dsimp [B, C]
    nlinarith
  refine ⟨by omega, fun he => ?_⟩
  apply (progressRank_eq_zero_iff P m z M η (run.state N)).1
  omega

/-- Every choice of legal transitions from a valid initialization reaches the returned
phase within a common finite bound. The choices may depend arbitrarily on the history. -/
theorem eventually_return_of_transition [ProperSpace E] (P : Parameters)
    {m : E → ℝ} {z : E} {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s)
    (hdec : SmallRadiusDecrease P m M) :
    ∃ B : ℕ, ∀ state : ℕ → InnerState E, InnerInitial (state 0) →
      (∀ k, (state k).phase ≠ .returned → InnerTransition P m z (state k) (state (k + 1))) →
      ∃ N ≤ B, (state N).phase = .returned := by
  obtain ⟨B, hB⟩ := exists_inner_length_bound P hM hm hcompact hmin hdec
  refine ⟨B, fun state hinit htrans => ?_⟩
  by_contra hnot
  have hn : ∀ k, k ≤ B → (state k).phase ≠ .returned := by
    intro k hk he
    exact hnot ⟨k, hk, he⟩
  let run : InnerExecution P m z B := {
    state := state
    is_minimizer := hmin
    initial := hinit
    transition := fun k hk => htrans k (hn k (Nat.le_of_lt hk)) }
  exact hn B le_rfl ((hB B run).2 rfl)

/-- A finite prefix of the strict-boundary inner procedure. Orthogonality, convergence,
radius floors, and termination are consequences of the transitions, not fields. -/
structure CorrectedInnerExecution (P : Parameters) (m : E → ℝ) (minimizer : E)
    (inherited : ℕ → ℝ) (N : ℕ) where
  state : ℕ → InnerState E
  is_minimizer : ∀ t, m minimizer ≤ m t
  initial : InnerInitial (state 0)
  transition : ∀ k, k < N → CorrectedInnerTransition P m minimizer inherited
    (state k) (state (k + 1))

/-- A corrected transition cannot continue from a returned state. -/
theorem CorrectedInnerTransition.source_ne_returned {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {a b : InnerState E}
    (h : CorrectedInnerTransition P m z inherited a b) : a.phase ≠ .returned := by
  intro he
  simp only [CorrectedInnerTransition, he, reduceCtorEq, ite_false] at h
  cases h <;> simp_all

/-- Correcting the long-step boundary preserves positive bounded accuracy fractions. -/
theorem CorrectedInnerTransition.mu_bounds {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {a b : InnerState E}
    (h : CorrectedInnerTransition P m z inherited a b) (hμ : 0 < a.mu) (hμ1 : a.mu ≤ 1) :
    0 < b.mu ∧ b.mu ≤ 1 ∧ a.mu ≤ b.mu := by
  by_cases hp : a.phase = .minimize
  · simp only [CorrectedInnerTransition, ite_eq_left hp] at h
    obtain ⟨s, _, rfl⟩ := h
    exact ⟨hμ, hμ1, le_rfl⟩
  · simp only [CorrectedInnerTransition, ite_eq_right hp] at h
    exact h.mu_bounds hμ hμ1

/-- Every corrected inspected or returned state retains its actual fraction certificate. -/
theorem CorrectedInnerTransition.fraction_of_ne_minimize {P : Parameters} {m : E → ℝ}
    {z : E} {inherited : ℕ → ℝ} {a b : InnerState E}
    (h : CorrectedInnerTransition P m z inherited a b)
    (ha : a.phase ≠ .minimize → a.mu * (m 0 - m z) ≤ m 0 - m a.step)
    (hb : b.phase ≠ .minimize) : b.mu * (m 0 - m z) ≤ m 0 - m b.step := by
  by_cases hp : a.phase = .minimize
  · simp only [CorrectedInnerTransition, ite_eq_left hp] at h
    obtain ⟨s, hf, rfl⟩ := h
    exact hf
  · simp only [CorrectedInnerTransition, ite_eq_right hp] at h
    exact h.fraction_of_ne_minimize ha hb

/-- Before return, corrected transitions preserve the same radius floors and unit low
radii as the literal process. A long return may copy arbitrary inherited radii. -/
theorem CorrectedInnerTransition.bounds {P : Parameters} {m : E → ℝ} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P m M) {inherited : ℕ → ℝ}
    {a b : InnerState E} (h : CorrectedInnerTransition P m z inherited a b)
    (ha : InnerBounds P M a) (hb : b.phase ≠ .returned) : InnerBounds P M b := by
  by_cases hp : a.phase = .minimize
  · simp only [CorrectedInnerTransition, ite_eq_left hp] at h
    obtain ⟨s, _, rfl⟩ := h
    by_cases hs : 1 < ‖s‖
    · simp [hs] at hb
    · simp only [ite_eq_right hs]
      refine ⟨ha.radii_valid, ha.radii_low, ha.radii_floor, ?_⟩
      intro j hj
      have he : j = 1 := (InnerPhase.inspect.inj hj).symm
      subst j
      exact ⟨le_rfl, P.order_pos, le_of_not_gt hs⟩
  · simp only [CorrectedInnerTransition, ite_eq_right hp] at h
    exact h.bounds hM hdec ha

/-- The strict boundary correction also strictly decreases the actual natural rank. -/
theorem CorrectedInnerTransition.progressRank_lt {P : Parameters} {m : E → ℝ} {z : E}
    {M η : ℝ} (hM : 1 ≤ M) (hη : 0 < η) (hguard : AccuracyThreshold P m z M η)
    (hdec : SmallRadiusDecrease P m M) {inherited : ℕ → ℝ} {a b : InnerState E}
    (h : CorrectedInnerTransition P m z inherited a b) (ha : InnerBounds P M a)
    (hμ : 0 ≤ a.mu)
    (hfrac : a.phase ≠ .minimize → a.mu * (m 0 - m z) ≤ m 0 - m a.step) :
    progressRank P m z M η b < progressRank P m z M η a := by
  by_cases hp : a.phase = .minimize
  · simp only [CorrectedInnerTransition, ite_eq_left hp] at h
    obtain ⟨s, _, rfl⟩ := h
    by_cases hs : 1 < ‖s‖
    · simp [progressRank, hp, phaseCost, hs]
    · simp [progressRank, refinementCount, hp, phaseCost, hs]
  · simp only [CorrectedInnerTransition, ite_eq_right hp] at h
    exact h.progressRank_lt hM hη hguard hdec ha hμ hfrac

/-- Every nonreturned corrected state has a legal next transition. -/
theorem CorrectedInnerTransition.exists_next [ProperSpace E] {P : Parameters}
    {m : E → ℝ} {z : E} {M : ℝ} (hmin : ∀ s, m z ≤ m s) {inherited : ℕ → ℝ}
    {a : InnerState E} (ha : InnerBounds P M a) (hμ : a.mu ≤ 1)
    (hphase : a.phase ≠ .returned) : ∃ b, CorrectedInnerTransition P m z inherited a b := by
  by_cases hp : a.phase = .minimize
  · refine ⟨⟨a.mu, if 1 < ‖z‖ then inherited else a.radii, z,
        if 1 < ‖z‖ then .returned else .inspect 1⟩, ?_⟩
    simp only [CorrectedInnerTransition, ite_eq_left hp]
    exact ⟨z, mul_le_of_le_one_left (sub_nonneg.mpr (hmin 0)) hμ, rfl⟩
  · obtain ⟨b, hb⟩ := InnerTransition.exists_next hmin ha hμ hphase
    exact ⟨b, by simpa only [CorrectedInnerTransition, ite_eq_right hp] using hb⟩

/-- Accuracy remains positive and bounded throughout a corrected prefix. -/
theorem CorrectedInnerExecution.mu_bounds {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {N : ℕ} (h : CorrectedInnerExecution P m z inherited N)
    {k : ℕ} (hk : k ≤ N) : 0 < (h.state k).mu ∧ (h.state k).mu ≤ 1 := by
  induction k with
  | zero => exact ⟨h.initial.1, h.initial.2.1⟩
  | succ k ih =>
    have hi := ih (by omega)
    exact ((h.transition k (by omega)).mu_bounds hi.1 hi.2).imp_right And.left

/-- Every inspected or returned corrected state has actual fraction provenance. -/
theorem CorrectedInnerExecution.fraction_of_ne_minimize {P : Parameters} {m : E → ℝ}
    {z : E} {inherited : ℕ → ℝ} {N : ℕ} (h : CorrectedInnerExecution P m z inherited N)
    {k : ℕ} (hk : k ≤ N) (hp : (h.state k).phase ≠ .minimize) :
    (h.state k).mu * (m 0 - m z) ≤ m 0 - m (h.state k).step := by
  induction k with
  | zero => exact (hp h.initial.2.2.2).elim
  | succ k ih =>
    exact (h.transition k (by omega)).fraction_of_ne_minimize
      (fun hp => ih (by omega) hp) hp

/-- Before a corrected prefix returns, its radii and inspection points satisfy all derived
bounds. The return branch may instead copy the inherited outer radii. -/
theorem CorrectedInnerExecution.bounds {P : Parameters} {m : E → ℝ} {z : E} {M : ℝ}
    (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P m M) {inherited : ℕ → ℝ} {N : ℕ}
    (h : CorrectedInnerExecution P m z inherited N) {k : ℕ} (hk : k ≤ N)
    (hp : (h.state k).phase ≠ .returned) : InnerBounds P M (h.state k) := by
  induction k with
  | zero => exact h.initial.bounds hM
  | succ k ih =>
    have ht := h.transition k (by omega)
    exact ht.bounds hM hdec (ih (by omega) ht.source_ne_returned) hp

/-- Every corrected prefix consumes at most its initial natural progress rank. -/
theorem CorrectedInnerExecution.length_add_rank_le {P : Parameters} {m : E → ℝ} {z : E}
    {M η : ℝ} (hM : 1 ≤ M) (hη : 0 < η) (hguard : AccuracyThreshold P m z M η)
    (hdec : SmallRadiusDecrease P m M) {inherited : ℕ → ℝ} {N : ℕ}
    (h : CorrectedInnerExecution P m z inherited N) :
    N + progressRank P m z M η (h.state N) ≤ progressRank P m z M η (h.state 0) := by
  have hall : ∀ k, k ≤ N →
      k + progressRank P m z M η (h.state k) ≤ progressRank P m z M η (h.state 0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hi := ih (by omega)
      have ht := h.transition k (by omega)
      have hdrop := ht.progressRank_lt hM hη hguard hdec
        (h.bounds hM hdec (by omega) ht.source_ne_returned)
        (h.mu_bounds (by omega)).1.le (h.fraction_of_ne_minimize (by omega))
      omega
  exact hall N le_rfl

/-- A common finite bound applies to all strict-boundary corrected prefixes, regardless of
initial accuracy fraction and arbitrary inherited radii on the return branch. -/
theorem exists_corrected_inner_length_bound [ProperSpace E] (P : Parameters)
    {m : E → ℝ} {z : E} {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s)
    (hdec : SmallRadiusDecrease P m M) :
    ∃ B : ℕ, ∀ inherited N, ∀ run : CorrectedInnerExecution P m z inherited N,
      N ≤ B ∧ (N = B → (run.state N).phase = .returned) := by
  obtain ⟨η, hη, hguard⟩ := exists_accuracyThreshold P hM hm hcompact hmin
  let C := geometricCountdown η (m 0 - m z) +
    ∑ j ∈ Finset.Icc 3 P.q, geometricCountdown (2 * radiusFloor P M j) 1
  let B := (C + 1) * (P.q + 2) + (P.q + 1)
  refine ⟨B, fun inherited N run => ?_⟩
  have hrank := run.length_add_rank_le hM hη hguard hdec
  have hD : 0 ≤ m 0 - m z := sub_nonneg.mpr (hmin 0)
  have hμ := run.initial.1
  have herror : (1 - (run.state 0).mu) * (m 0 - m z) ≤ m 0 - m z := by
    nlinarith only [hD, hμ]
  have hcnt := geometricCountdown_mono hη herror
  have hstart : progressRank P m z M η (run.state 0) ≤ B := by
    simp only [progressRank, refinementCount, run.initial.2.2.1, run.initial.2.2.2,
      reduceCtorEq, ite_false, phaseCost]
    dsimp [B, C]
    nlinarith
  refine ⟨by omega, fun he => ?_⟩
  apply (progressRank_eq_zero_iff P m z M η (run.state N)).1
  omega

/-- Any legal history of corrected choices reaches return within a common finite bound. -/
theorem eventually_corrected_return_of_transition [ProperSpace E] (P : Parameters)
    {m : E → ℝ} {z : E} {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s)
    (hdec : SmallRadiusDecrease P m M) :
    ∃ B : ℕ, ∀ inherited (state : ℕ → InnerState E), InnerInitial (state 0) →
      (∀ k, (state k).phase ≠ .returned →
        CorrectedInnerTransition P m z inherited (state k) (state (k + 1))) →
      ∃ N ≤ B, (state N).phase = .returned := by
  obtain ⟨B, hB⟩ := exists_corrected_inner_length_bound P hM hm hcompact hmin hdec
  refine ⟨B, fun inherited state hinit htrans => ?_⟩
  by_contra hnot
  have hn : ∀ k, k ≤ B → (state k).phase ≠ .returned := by
    intro k hk he
    exact hnot ⟨k, hk, he⟩
  let run : CorrectedInnerExecution P m z inherited B := {
    state := state
    is_minimizer := hmin
    initial := hinit
    transition := fun k hk => htrans k (hn k (Nat.le_of_lt hk)) }
  exact hn B le_rfl ((hB inherited B run).2 rfl)

/-- The literal procedure cannot continue from its returned phase. -/
theorem InnerTransition.source_ne_returned {P : Parameters} {m : E → ℝ} {z : E}
    {a b : InnerState E} (h : InnerTransition P m z a b) : a.phase ≠ .returned := by
  intro he
  cases h <;> simp_all

/-- The literal procedure has an actual finite returned execution from every allowed
initial state, including every initial fraction in `(0,1]`. -/
theorem exists_inner_return_execution [ProperSpace E] (P : Parameters)
    {m : E → ℝ} {z : E} {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s)
    (hdec : SmallRadiusDecrease P m M) {a : InnerState E} (hinit : InnerInitial a) :
    ∃ N, ∃ run : InnerExecution P m z N,
      run.state 0 = a ∧ (run.state N).phase = .returned := by
  obtain ⟨η, hη, hguard⟩ := exists_accuracyThreshold P hM hm hcompact hmin
  let good : InnerState E → Prop := fun a =>
    (a.phase ≠ .returned → InnerBounds P M a) ∧ 0 < a.mu ∧ a.mu ≤ 1 ∧
      (a.phase ≠ .minimize → a.mu * (m 0 - m z) ≤ m 0 - m a.step)
  have ha : good a := ⟨fun _ => hinit.bounds hM, hinit.1, hinit.2.1,
    fun hp => (hp hinit.2.2.2).elim⟩
  have hnext : ∀ a, good a → a.phase ≠ .returned → ∃ b, InnerTransition P m z a b := by
    intro a ha hp
    exact InnerTransition.exists_next hmin (ha.1 hp) ha.2.2.1 hp
  have hpres : ∀ a b, good a → InnerTransition P m z a b → good b := by
    intro a b ha ht
    have hbound := ha.1 ht.source_ne_returned
    have hμ := ht.mu_bounds ha.2.1 ha.2.2.1
    exact ⟨fun _ => ht.bounds hM hdec hbound, hμ.1, hμ.2.1,
      ht.fraction_of_ne_minimize ha.2.2.2⟩
  have hdrop : ∀ a b, good a → InnerTransition P m z a b →
      progressRank P m z M η b < progressRank P m z M η a := by
    intro a b ha ht
    exact ht.progressRank_lt hM hη hguard hdec (ha.1 ht.source_ne_returned)
      ha.2.1.le ha.2.2.2
  obtain ⟨N, state, hzero, hstop, htrans⟩ := Relation.exists_finite_stopped_chain_of_rank
    (InnerTransition P m z) (progressRank P m z M η) (fun a => a.phase = .returned)
    good hnext hpres hdrop ha
  exact ⟨N, ⟨state, hmin, by simpa only [hzero] using hinit, htrans⟩, hzero, hstop⟩

/-- The corrected procedure has an actual finite returned execution from every allowed
initial state, for arbitrary inherited radii on a possible long-step return. -/
theorem exists_corrected_inner_return_execution [ProperSpace E] (P : Parameters)
    {m : E → ℝ} {z : E} {M : ℝ} (hM : 1 ≤ M) (hm : ContDiff ℝ P.q m)
    (hcompact : IsCompact {s | m s ≤ m 0}) (hmin : ∀ s, m z ≤ m s)
    (hdec : SmallRadiusDecrease P m M) (inherited : ℕ → ℝ)
    {a : InnerState E} (hinit : InnerInitial a) :
    ∃ N, ∃ run : CorrectedInnerExecution P m z inherited N,
      run.state 0 = a ∧ (run.state N).phase = .returned := by
  obtain ⟨η, hη, hguard⟩ := exists_accuracyThreshold P hM hm hcompact hmin
  let good : InnerState E → Prop := fun a =>
    (a.phase ≠ .returned → InnerBounds P M a) ∧ 0 < a.mu ∧ a.mu ≤ 1 ∧
      (a.phase ≠ .minimize → a.mu * (m 0 - m z) ≤ m 0 - m a.step)
  have ha : good a := ⟨fun _ => hinit.bounds hM, hinit.1, hinit.2.1,
    fun hp => (hp hinit.2.2.2).elim⟩
  have hnext : ∀ a, good a → a.phase ≠ .returned →
      ∃ b, CorrectedInnerTransition P m z inherited a b := by
    intro a ha hp
    exact CorrectedInnerTransition.exists_next hmin (ha.1 hp) ha.2.2.1 hp
  have hpres : ∀ a b, good a → CorrectedInnerTransition P m z inherited a b → good b := by
    intro a b ha ht
    have hbound := ha.1 ht.source_ne_returned
    have hμ := ht.mu_bounds ha.2.1 ha.2.2.1
    exact ⟨fun hp => ht.bounds hM hdec hbound hp, hμ.1, hμ.2.1,
      ht.fraction_of_ne_minimize ha.2.2.2⟩
  have hdrop : ∀ a b, good a → CorrectedInnerTransition P m z inherited a b →
      progressRank P m z M η b < progressRank P m z M η a := by
    intro a b ha ht
    exact ht.progressRank_lt hM hη hguard hdec (ha.1 ht.source_ne_returned)
      ha.2.1.le ha.2.2.2
  obtain ⟨N, state, hzero, hstop, htrans⟩ := Relation.exists_finite_stopped_chain_of_rank
    (CorrectedInnerTransition P m z inherited) (progressRank P m z M η)
    (fun a => a.phase = .returned) good hnext hpres hdrop ha
  exact ⟨N, ⟨state, hmin, by simpa only [hzero] using hinit, htrans⟩, hzero, hstop⟩

/-- Every sublevel of a positive actual regularized Taylor model is compact. -/
theorem isCompact_model_sublevel [ProperSpace E] (f : E → ℝ) (p : ℕ) (x : E)
    {σ : ℝ} (hσ : 0 < σ) (b : ℝ) : IsCompact {s | model f p x σ s ≤ b} := by
  have hm : Continuous (model f p x σ) :=
    (RegularizedTaylorModel.contDiff_taylorModel f p x 0).continuous.add
      (continuous_const.mul (continuous_norm.pow _))
  exact isCompact_of_isClosed_isBounded (isClosed_le hm continuous_const)
    (model_sublevel_isBounded f p x hσ b)

section Model
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The actual regularized Taylor model supplies the small-radius decrease estimate used
in the finite-progress proof. -/
theorem smallRadiusDecrease_model (P : Parameters) {f : F → ℝ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f P.p L) (x : F) {σ : ℝ} (hσ : 0 ≤ σ) :
    SmallRadiusDecrease P (model f P.p x σ)
      (3 * HigherOrderDerivativeFamily.maxConstant P.p L + σ) := by
  intro s hs j hj hjq δ hδ hδ1 hsmall d hd htarget
  have hm := HigherOrderRegularization.diagonalLipschitz_model (x := x) hf.smooth.contDiffAt hσ
  apply hm.half_decrease_of_small_radius (P.order_pos.trans P.order_le)
    (hjq.trans P.order_le) (by linarith [hf.maxConstant_nonneg])
    (by linarith [hf.maxConstant_nonneg]) ⟨hδ.le, hδ1⟩ s d hd ?_ hsmall htarget
  intro i hi
  exact hf.norm_iteratedFDeriv_model_le (by have := (Finset.mem_Icc.mp hi).1; omega)
    (Finset.mem_Icc.mp hi).2 x s hσ hs

/-- Every legal inner execution for an actual regularized Taylor model terminates, for
any positive initial fraction at most one and any choices allowed by the literal algorithm. -/
theorem InnerExecution.terminates (P : Parameters) {f : F → ℝ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f P.p L)
    (hL : 1 ≤ HigherOrderDerivativeFamily.maxConstant P.p L) (x : F) {σ : ℝ}
    (hσ : 0 < σ) {z : F} (hmin : ∀ s, model f P.p x σ z ≤ model f P.p x σ s) :
    ∃ B : ℕ, ∀ N, ∀ run : InnerExecution P (model f P.p x σ) z N,
      N ≤ B ∧ (N = B → (run.state N).phase = .returned) := by
  have hm := contDiff_model f P.p x σ
  have hcompact := isCompact_model_sublevel f P.p x hσ (model f P.p x σ 0)
  exact exists_inner_length_bound P (by linarith) (hm.of_le (by exact_mod_cast P.order_le))
    hcompact hmin (smallRadiusDecrease_model P hf x hσ.le)

/-- Corrected legal inner executions of the actual model have the same uniform finite
termination guarantee, including the strict unit boundary and inherited long-return radii. -/
theorem CorrectedInnerExecution.terminates (P : Parameters) {f : F → ℝ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f P.p L)
    (hL : 1 ≤ HigherOrderDerivativeFamily.maxConstant P.p L) (x : F) {σ : ℝ}
    (hσ : 0 < σ) {z : F} (hmin : ∀ s, model f P.p x σ z ≤ model f P.p x σ s) :
    ∃ B : ℕ, ∀ inherited N, ∀ run : CorrectedInnerExecution P (model f P.p x σ) z inherited N,
      N ≤ B ∧ (N = B → (run.state N).phase = .returned) := by
  have hm := contDiff_model f P.p x σ
  have hcompact := isCompact_model_sublevel f P.p x hσ (model f P.p x σ 0)
  exact exists_corrected_inner_length_bound P (by linarith)
    (hm.of_le (by exact_mod_cast P.order_le)) hcompact hmin
    (smallRadiusDecrease_model P hf x hσ.le)

/-- The actual literal algorithm has a finite returned execution from every permitted
initial state, with the initial accuracy fraction preserved exactly. -/
theorem exists_model_inner_return_execution (P : Parameters) {f : F → ℝ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f P.p L)
    (hL : 1 ≤ HigherOrderDerivativeFamily.maxConstant P.p L) (x : F) {σ : ℝ}
    (hσ : 0 < σ) {z : F} (hmin : ∀ s, model f P.p x σ z ≤ model f P.p x σ s)
    {a : InnerState F} (hinit : InnerInitial a) :
    ∃ N, ∃ run : InnerExecution P (model f P.p x σ) z N,
      run.state 0 = a ∧ (run.state N).phase = .returned := by
  exact exists_inner_return_execution P (by linarith)
    ((contDiff_model f P.p x σ).of_le (by exact_mod_cast P.order_le))
    (isCompact_model_sublevel f P.p x hσ (model f P.p x σ 0)) hmin
    (smallRadiusDecrease_model P hf x hσ.le) hinit

/-- The actual strict-boundary algorithm has a finite returned execution from every
permitted initial state, for arbitrary inherited radii. -/
theorem exists_model_corrected_inner_return_execution (P : Parameters)
    {f : F → ℝ} {L : ℕ → ℝ} (hf : HigherOrderDerivativeFamily f P.p L)
    (hL : 1 ≤ HigherOrderDerivativeFamily.maxConstant P.p L) (x : F) {σ : ℝ}
    (hσ : 0 < σ) {z : F} (hmin : ∀ s, model f P.p x σ z ≤ model f P.p x σ s)
    (inherited : ℕ → ℝ) {a : InnerState F} (hinit : InnerInitial a) :
    ∃ N, ∃ run : CorrectedInnerExecution P (model f P.p x σ) z inherited N,
      run.state 0 = a ∧ (run.state N).phase = .returned := by
  exact exists_corrected_inner_return_execution P (by linarith)
    ((contDiff_model f P.p x σ).of_le (by exact_mod_cast P.order_le))
    (isCompact_model_sublevel f P.p x hσ (model f P.p x σ 0)) hmin
    (smallRadiusDecrease_model P hf x hσ.le) inherited hinit

end Model

end Optimization.HigherOrderApproximateRegularization
