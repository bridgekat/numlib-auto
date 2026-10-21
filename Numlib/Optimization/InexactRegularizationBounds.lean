import Numlib.Optimization.InexactRegularization
import Numlib.Optimization.AdaptiveRegularizationFiniteComplexity
import Numlib.Optimization.HigherOrderApproximateRegularizationBounds

/-!
# Certificates and scalar invariants of implicit regularization

Computed witnesses certify half-tolerance approximate gaps. A separate coefficient-error
budget then certifies true objective gaps. Parameter counting includes only trial iterations;
accuracy refinements have zero logarithmic contribution. Neither computed failures nor
computed passes are identified with unscaled true objective tests.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {checked : ℕ}

/-- The complete inspection shrinks valid radii only and preserves their positivity. -/
theorem Inspection.valid_radii {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ) :
    HigherOrderApproximateRegularization.ValidRadii P.toParameters I.radii := by
  intro j hj hjq
  unfold Inspection.radii
  split_ifs
  · exact ⟨halvedRadius_pos (hδ j hj hjq).1 _,
      (show halvedRadius (δ j) (I.halvings j) ≤ δ j by
        simpa using halvedRadius_antitone (hδ j hj hjq).1.le
          (Nat.zero_le (I.halvings j))).trans (hδ j hj hjq).2⟩
  · exact hδ j hj hjq

/-- Every raw inner prefix retains valid active radii, by induction over its actual updates. -/
theorem InnerResult.valid_radii {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} {d : E} (s : InnerResult P c A σ δ d)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ) :
    HigherOrderApproximateRegularization.ValidRadii P.toParameters s.radii := by
  have hall : ∀ k, k ≤ s.length →
      HigherOrderApproximateRegularization.ValidRadii P.toParameters
        (s.execution.state k).radii := by
    intro k hk
    induction k with
    | zero =>
      rw [s.execution.initial.2.2.1]
      exact fun _ _ _ => ⟨by norm_num, le_rfl⟩
    | succ k ih =>
      exact (s.execution.transition k (by omega)).radii_valid (ih (by omega))
  unfold InnerResult.radii
  split_ifs
  · exact hδ
  · exact hall _ le_rfl

/-- A complete all-pass inspection certifies actual approximate gaps at its post-loop radii. -/
theorem Inspection.passed_gap {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hall : I.order = P.q + 1)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    gapOn (decrement A j) (Metric.closedBall 0 (I.radii j)) ≤
      P.epsilon j * I.radii j ^ j / (2 * (j ! : ℝ)) := by
  have hjo : j < I.order := by omega
  have h := ((I.search j hj hjq hjo.le).witness (I.halvings j) le_rfl).gap_le_half
    P.fraction_pos (I.earlier j hj hjq hjo)
  simpa only [Inspection.radii, ite_eq_left hjo.le] using h

/-- At each visited order the complete search obeys the finite halving bound and radius floor. -/
theorem Inspection.search_bounds {P : Parameters} {c : ℝ} {A : Coefficients E} {σ L : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ)
    (hL : 0 < L) (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    (hA : ∀ i ∈ Finset.Icc 1 P.p, ‖A i‖ ≤ L)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j ≤ I.order) :
    I.halvings j ≤ HigherOrderApproximateRegularization.geometricCountdown
        (P.fraction * P.epsilon j / (8 * max L σ)) (δ j) ∧
      min (P.fraction * P.epsilon j / (16 * max L σ)) (δ j) ≤ I.radii j ∧
      I.radii j ≤ δ j := by
  have htail (i : ℕ) (hi : i ∈ Finset.Icc (j + 1) P.p) : ‖A i‖ ≤ L :=
    hA i (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hi).1; omega, (Finset.mem_Icc.mp hi).2⟩)
  have hs := I.search j hj hjq hjo
  have hb := hs.radius_bounds (hjq.trans P.order_le) hL (hδ j hj hjq) htail le_rfl
  refine ⟨hs.length_le (hjq.trans P.order_le) hL (hδ j hj hjq)
    P.fraction_pos (P.epsilon_pos j hj hjq) htail, ?_, ?_⟩
  · simpa only [Inspection.radii, ite_eq_left hjo] using hb.2.2
  · simpa only [Inspection.radii, ite_eq_left hjo] using hb.1

/-- The detailed inner return supplies actual passing model witnesses, or the weak long
branch with inherited radii. This retains the selected witnesses at equality. -/
theorem InnerResult.quality {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} {d : E} (s : InnerResult P c A σ δ d) :
    (1 ≤ ‖s.step‖ ∧ s.radii = δ) ∨ ∀ j, 1 ≤ j → j ≤ P.q → ∃ w : E,
      HigherOrderApproximateRegularization.GapWitness (regularizedPolynomial c A P.p σ)
        j s.step (s.radii j) P.fraction w ∧
      taylorDecrement (regularizedPolynomial c A P.p σ) j s.step w ≤
        P.fraction * P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ) := by
  by_cases hl : 1 ≤ ‖s.step‖
  · exact Or.inl ⟨hl, by simp only [InnerResult.radii, ite_eq_left hl]⟩
  · apply Or.inr
    have h := s.execution.return_quality s.returned
    rcases h with h | h
    · exact (hl h).elim
    · have he : s.radii = (s.execution.state s.length).radii := ite_eq_right hl
      rw [he]
      exact h

/-- The positive retained inspection witness makes every actual Step 2 output nonzero
and its approximate Taylor decrement strictly positive. -/
theorem InnerResult.decrement_pos {P : Parameters} {c : ℝ} {A : Coefficients E} {σ : ℝ}
    {δ : ℕ → ℝ} (I : Inspection P c A σ δ) (hq : I.order ≤ P.q)
    (s : InnerResult P c A σ I.radii (I.direction hq)) (hσ : 0 ≤ σ)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ) :
    σ * ‖s.step‖ ^ (P.p + 1) / ((P.p + 1)! : ℝ) ≤ decrement A P.p s.step ∧
      0 < decrement A P.p s.step ∧ s.step ≠ 0 := by
  apply decrement_pos_of_retained_model_decrease c A P.p hσ (hs := s.retained)
  have hret := I.retained hq
  have hpos : 0 < P.fraction * P.epsilon I.order *
      halvedRadius (δ I.order) (I.halvings I.order) ^ I.order /
        (4 * (I.order ! : ℝ)) := by
    have := P.fraction_pos
    have := P.epsilon_pos I.order I.order_pos hq
    have := halvedRadius_pos (hδ I.order I.order_pos hq).1 (I.halvings I.order)
    positivity
  change _ ≤ c - regularizedPolynomial c A P.p σ (I.direction hq) at hret
  linarith

/-- A computed all-pass inspection and independent coefficient errors certify the actual
objective gaps. The error budget handles zero error multipliers without division. -/
theorem Inspection.true_quality [ProperSpace E] {P : Parameters} {f : E → ℝ} {x : E}
    {A : Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} (I : Inspection P (f x) A σ δ)
    (hall : I.order = P.q + 1)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    (e : ℕ → ℝ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p, ‖A i - iteratedFDeriv ℝ i f x‖ ≤ e i)
    (herr : ∀ j, 1 ≤ j → j ≤ P.q →
      (∑ i ∈ Finset.Icc 1 j, e i * I.radii j ^ i / (i ! : ℝ)) ≤
        P.epsilon j * I.radii j ^ j / (2 * (j ! : ℝ))) :
    ∀ j, 1 ≤ j → j ≤ P.q →
      gapOn (taylorDecrement f j x) (Metric.closedBall 0 (I.radii j)) ≤
        P.epsilon j * I.radii j ^ j / (j ! : ℝ) := by
  intro j hj hjq
  have hv := I.valid_radii hδ j hj hjq
  have hh := approximate_gap_certifies A (fun i => iteratedFDeriv ℝ i f x) e
    (isCompact_closedBall (0 : E) (I.radii j))
    ⟨0, by simpa using hv.1.le⟩ hv.1.le (Set.Subset.refl _)
    (fun i hi => hcoeff i (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (hjq.trans P.order_le)⟩))
    (I.passed_gap hall hj hjq) (herr j hj hjq)
  have he : decrement (fun i => iteratedFDeriv ℝ i f x) j = taylorDecrement f j x :=
    funext (decrement_iteratedFDeriv f x j)
  rw [he] at hh
  exact hh

/-- Every legal transition preserves the strictly positive regularization floor. -/
theorem Transition.sigma_floor {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (ha : P.sigmaMin ≤ a.sigma) :
    P.sigmaMin ≤ b.sigma := by
  cases t with
  | refineInspection => exact ha
  | refineStep => exact ha
  | trial I hq s hacc next hu =>
    have hh := hu.floor_le ha
    split_ifs <;> exact hh

/-- The regularization floor holds at every state of a legal finite prefix. -/
theorem Execution.sigma_floor {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k : ℕ} (hk : k ≤ N) : P.sigmaMin ≤ (r.state k).sigma := by
  induction k with
  | zero => exact r.initial_sigma
  | succ k ih => exact (r.transition k (by omega)).sigma_floor (ih (by omega))

/-- Accuracy-only iterations leave the parameter and pre-inspection radii unchanged. -/
theorem Transition.accuracy_only {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {accepted : Bool}
    (t : Transition P checked f oracle a b false accepted) :
    b.sigma = a.sigma ∧ b.radii = a.radii ∧ b.point = a.point ∧
      b.request = (fun i => P.gammaAccuracy * a.request i) := by
  cases t <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A rejected trial retains the oracle's exact point/request key and marks its tensors
cached, so the next inspection performs no duplicate tensor query. -/
theorem Transition.rejected_cache {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (ht : trial = true)
    (ha : accepted = false) :
    b.point = a.point ∧ b.request = a.request ∧ b.fresh = false := by
  cases t with
  | refineInspection => cases ht
  | refineStep => cases ht
  | trial I hq s hacc next hu =>
    have hn : ¬P.eta1 ≤ ratio P f oracle a s.step := by simpa using ha
    simp [hn]

/-- The literal outer update preserves valid radii, including restoration after refinement. -/
theorem Transition.valid_radii {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted)
    (ha : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii) :
    HigherOrderApproximateRegularization.ValidRadii P.toParameters b.radii := by
  cases t with
  | refineInspection => exact ha
  | refineStep => exact ha
  | trial I hq s hacc next hu =>
    have hi := I.valid_radii ha
    split_ifs
    · exact s.valid_radii hi
    · exact hi

/-- Every state in an actual legal prefix has positive radii at most one. -/
theorem Execution.valid_radii {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k : ℕ} (hk : k ≤ N) :
    HigherOrderApproximateRegularization.ValidRadii P.toParameters (r.state k).radii := by
  induction k with
  | zero => exact r.initial_radii
  | succ k ih => exact (r.transition k (by omega)).valid_radii (ih (by omega))

/-- Every legal accepted trial decreases the actual objective; all other branches retain it. -/
theorem Transition.objective_nonincrease {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (hσ : 0 ≤ a.sigma)
    (ha : HigherOrderApproximateRegularization.ValidRadii P.toParameters a.radii) :
    f b.point ≤ f a.point := by
  cases t with
  | refineInspection => exact le_rfl
  | refineStep => exact le_rfl
  | trial I hq s hacc next hu =>
    have hpos := (InnerResult.decrement_pos I hq s hσ ha).2.1
    split_ifs with hs
    · have hdec := (le_div_iff₀ hpos).mp hs
      have hh : 0 ≤ P.eta1 * decrement (oracle a.point a.request) P.p s.step :=
        mul_nonneg P.eta1_pos.le hpos.le
      change _ ≤ f a.point
      change P.eta1 * decrement (oracle a.point a.request) P.p s.step ≤
        f a.point - f (a.point + s.step) at hdec
      linarith
    · exact le_rfl

/-- Requested accuracies remain positive and never increase at any active derivative order. -/
theorem Transition.request_bounds {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) {i : ℕ} (hi : 0 < a.request i) :
    0 < b.request i ∧ b.request i ≤ a.request i := by
  cases t with
  | refineInspection =>
    exact ⟨mul_pos P.gammaAccuracy_pos hi,
      mul_le_of_le_one_left hi.le P.gammaAccuracy_lt_one.le⟩
  | refineStep =>
    exact ⟨mul_pos P.gammaAccuracy_pos hi,
      mul_le_of_le_one_left hi.le P.gammaAccuracy_lt_one.le⟩
  | trial => split_ifs <;> exact ⟨hi, le_rfl⟩

/-- All active requests obey their initial bound throughout the legal prefix. -/
theorem Execution.request_bounds {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {k i : ℕ} (hk : k ≤ N) (hi : i ∈ Finset.Icc 1 P.p) :
    0 < (r.state k).request i ∧ (r.state k).request i ≤ (r.state 0).request i := by
  induction k with
  | zero => exact ⟨r.initial_request i hi, le_rfl⟩
  | succ k ih =>
    have hi' := ih (by omega)
    have hb := (r.transition k (by omega)).request_bounds hi'.1
    exact ⟨hb.1, hb.2.trans hi'.2⟩

/-- Every accepted iteration is a trial, independently of its model and oracle. -/
theorem Transition.accepted_is_trial {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (ha : accepted = true) :
    trial = true := by
  cases t <;> simp_all

/-- The literal parameter intervals imply the per-trial logarithmic lower bound. -/
theorem parameter_update_log_lower (P : Parameters) {ρ σ next : ℝ}
    (hσ : 0 < σ)
    (h : HigherOrderApproximateRegularization.ParameterUpdate P.toParameters ρ σ next) :
    (if P.eta1 ≤ ρ then Real.log P.gamma1 else Real.log P.gamma2) ≤
      Real.log next - Real.log σ := by
  have hmul : (if P.eta1 ≤ ρ then P.gamma1 else P.gamma2) * σ ≤ next := by
    unfold HigherOrderApproximateRegularization.ParameterUpdate at h
    by_cases h1 : P.eta1 ≤ ρ
    · simp only [ite_eq_left h1]
      by_cases h2 : P.eta2 ≤ ρ
      · simp only [ite_eq_left h2] at h
        exact (le_max_right _ _).trans h.1
      · simp only [ite_eq_right h2, ite_eq_left h1] at h
        exact (mul_le_of_le_one_left hσ.le P.gamma1_lt_one.le).trans h.1
    · have h2 : ¬P.eta2 ≤ ρ := fun hh => h1 (P.eta_le.trans hh)
      simp only [ite_eq_right h2, ite_eq_right h1] at h ⊢
      exact h.1
  have hγ : 0 < (if P.eta1 ≤ ρ then P.gamma1 else P.gamma2) := by
    split_ifs
    · exact P.gamma1_pos
    · exact zero_lt_one.trans P.one_lt_gamma2
  have hh := Real.log_le_log (mul_pos hγ hσ) hmul
  rw [Real.log_mul hγ.ne' hσ.ne'] at hh
  split_ifs at hh ⊢ <;> linarith

/-- Accuracy refinements contribute zero; accepted trials contribute `log γ₁`, and rejected
trials contribute `log γ₂`. This is an inequality derived from actual legal transitions. -/
theorem Transition.log_step {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {a b : State E} {trial accepted : Bool}
    (t : Transition P checked f oracle a b trial accepted) (hσ : 0 < a.sigma) :
    (if accepted then Real.log P.gamma1 - Real.log P.gamma2 else 0) +
      (if trial then Real.log P.gamma2 else 0) ≤ Real.log b.sigma - Real.log a.sigma := by
  cases t with
  | refineInspection => simp [refine]
  | refineStep => simp [refine]
  | trial I hq s hacc next hu =>
    have hh := parameter_update_log_lower P hσ hu
    by_cases hs : P.eta1 ≤ ratio P f oracle a s.step
    · simpa [hs] using hh
    · simpa [hs] using hh

/-- Actual trial count before the finite endpoint. -/
def Execution.trialCount {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) : ℕ :=
  ((Finset.range N).filter fun k => r.trial k).card

/-- Actual accepted-trial count before the finite endpoint. -/
def Execution.acceptedCount {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) : ℕ :=
  ((Finset.range N).filter fun k => r.accepted k).card

/-- Telescoping only the actual parameter changes yields the trial-count logarithmic budget. -/
theorem Execution.log_budget {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ}
    (r : Execution P checked f oracle N) :
    (r.acceptedCount : ℝ) * (Real.log P.gamma1 - Real.log P.gamma2) +
      (r.trialCount : ℝ) * Real.log P.gamma2 ≤
        Real.log ((r.state N).sigma / (r.state 0).sigma) := by
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun k hk =>
    (r.transition k (Finset.mem_range.mp hk)).log_step
      (P.sigmaMin_pos.trans_le (r.sigma_floor (Finset.mem_range.mp hk).le)))
  rw [show (∑ k ∈ Finset.range N, (Real.log (r.state (k + 1)).sigma -
      Real.log (r.state k).sigma)) = Real.log (r.state N).sigma - Real.log (r.state 0).sigma
    from Finset.sum_range_sub (fun k => Real.log (r.state k).sigma) N] at hh
  rw [Real.log_div (P.sigmaMin_pos.trans_le (r.sigma_floor le_rfl)).ne'
    (P.sigmaMin_pos.trans_le (r.sigma_floor (Nat.zero_le N))).ne']
  simpa [Execution.acceptedCount, Execution.trialCount, Finset.sum_add_distrib,
    Finset.sum_ite, mul_sub] using hh

/-- A terminal parameter upper bound controls every actual trial; refinements create no
spurious trial count and need no contraction or expansion assumption. -/
theorem Execution.trial_count_le {P : Parameters} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} {N : ℕ} (r : Execution P checked f oracle N)
    {M : ℝ} (hM : (r.state N).sigma ≤ M) :
    (r.trialCount : ℝ) ≤ (r.acceptedCount : ℝ) *
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (M / (r.state 0).sigma) / Real.log P.gamma2 :=
  ParameterUpdates.trial_budget_of_log_budget P.toParameters.toRegularizationParameters
    (P.sigmaMin_pos.trans_le (r.sigma_floor (Nat.zero_le N)))
    (P.sigmaMin_pos.trans_le (r.sigma_floor le_rfl)) hM r.log_budget

end Optimization.InexactRegularization
