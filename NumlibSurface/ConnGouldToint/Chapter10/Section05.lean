import NumlibSurface.ConnGouldToint.Chapter06.Section03
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Alternative trust-region management

A terminating inner loop of Algorithm 10.5.1 yields one basic trust-region
iteration at its stored radius. Expansion can be incorporated into the
preceding radius update because the preceding iteration must be very successful.
-/

namespace ConnGouldToint.Chapter10

open Chapter06

/-- The extra parameter of Algorithm 10.5.1 is a growth factor strictly above one. -/
structure InternalDoublingParams extends BTRParams where
  γ₃ : ℝ
  one_lt_gamma₃ : 1 < γ₃

section Doubling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A terminating trace of the inner loop of Algorithm 10.5.1. Index zero
is the initial trial from Step 2. A budget of `some N` allows `N + 1`
enlarged probes. The model and norm are held fixed for every
probe, and the model is evaluated on the enlarged regions. Continuation uses
`η₂` as in Step 3c. If the final probe is rejected, the preceding probe is retained. -/
structure InternalDoublingTrace (P : InternalDoublingParams) (f m : E → ℝ)
    (x : E) (p : Seminorm ℝ E) (previousRatio : ℝ) (sufficient : ℝ → E → Prop)
    (budget : Option ℕ := none) where
  last : ℕ
  radius : ℕ → ℝ
  step : ℕ → E
  initial_radius_pos : 0 < radius 0
  enter : 0 < last ↔ P.η₂ ≤ previousRatio ∧ P.η₂ ≤ btrRatio f m x (step 0)
  feasible : ∀ j ≤ last, x + step j ∈ trustRegion p x (radius j)
  sufficient_decrease : ∀ j ≤ last, sufficient (radius j) (step j)
  predicted_pos : ∀ j ≤ last, 0 < m x - m (x + step j)
  enlarge : ∀ j < last, P.γ₃ * radius j ≤ radius (j + 1)
  continue_loop : ∀ j, 0 < j → j < last →
    P.η₂ ≤ btrRatio f m x (step j) ∧ ‖step (j - 1)‖ < ‖step j‖
  within_budget : ∀ N, budget = some N → last ≤ N + 1
  stop : 0 < last → (∃ N, budget = some N ∧ last = N + 1) ∨
    ¬ (P.η₂ ≤ btrRatio f m x (step last) ∧ ‖step (last - 1)‖ < ‖step last‖)

namespace InternalDoublingTrace

variable {P : InternalDoublingParams} {f m : E → ℝ} {x : E} {p : Seminorm ℝ E}
  {previousRatio : ℝ} {sufficient : ℝ → E → Prop} {budget : Option ℕ}

/-- The index of the stored trial after Step 3c. If there is no inner loop,
the initial trial is retained even if it fails the acceptance test. -/
noncomputable def storedIndex
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : ℕ :=
  if P.η₁ ≤ btrRatio f m x (trace.step trace.last) then trace.last else trace.last - 1

/-- The radius retained together with the stored trial in Step 3c. -/
noncomputable def storedRadius
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : ℝ :=
  trace.radius trace.storedIndex

/-- The step retained for Step 4. -/
noncomputable def storedStep
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : E :=
  trace.step trace.storedIndex

/-- The achieved-to-predicted reduction ratio at the stored step. -/
noncomputable def storedRatio
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) : ℝ :=
  btrRatio f m x trace.storedStep

private theorem storedIndex_le_last
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) :
    trace.storedIndex ≤ trace.last := by
  unfold storedIndex
  split
  · exact le_rfl
  · exact Nat.sub_le _ _

/-- Internal doubling never reduces the stored radius below the initial radius. -/
theorem storedRadius_ge_initial
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) :
    trace.radius 0 ≤ trace.storedRadius := by
  have h (j : ℕ) (hj : j ≤ trace.last) : trace.radius 0 ≤ trace.radius j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      have hj' : j < trace.last := Nat.lt_of_succ_le hj
      have hprev := ih hj'.le
      exact hprev.trans ((le_mul_of_one_le_left
        (trace.initial_radius_pos.le.trans hprev) P.one_lt_gamma₃.le).trans
        (trace.enlarge j hj'))
  exact h _ trace.storedIndex_le_last

/-- If the preceding iteration was not very successful, there is no inner loop. -/
theorem storedRadius_eq_initial_of_previous_not_very_successful
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget)
    (h : previousRatio < P.η₂) : trace.storedRadius = trace.radius 0 := by
  have hlast : trace.last = 0 :=
    Nat.eq_zero_of_not_pos fun hpos ↦ h.not_ge (trace.enter.mp hpos).1
  simp [storedRadius, storedIndex, hlast]

/-- If the inner loop runs, Step 3c retains the latest acceptable probe.
If the final probe fails, all earlier probes were very successful. -/
theorem storedIndex_is_latest_acceptable
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient budget) (h : 0 < trace.last) :
    P.η₁ ≤ trace.storedRatio ∧
      ∀ j ≤ trace.last, P.η₁ ≤ btrRatio f m x (trace.step j) → j ≤ trace.storedIndex := by
  by_cases hfinal : P.η₁ ≤ btrRatio f m x (trace.step trace.last)
  · have hi : trace.storedIndex = trace.last := ite_eq_left hfinal
    exact ⟨by simpa only [storedRatio, storedStep, hi] using hfinal,
      fun j hj _ ↦ hi ▸ hj⟩
  · have hi : trace.storedIndex = trace.last - 1 := ite_eq_right hfinal
    constructor
    · have hprev : P.η₂ ≤ btrRatio f m x (trace.step (trace.last - 1)) := by
        by_cases hzero : trace.last - 1 = 0
        · rw [hzero]
          exact (trace.enter.mp h).2
        · exact (trace.continue_loop _ (Nat.pos_of_ne_zero hzero) (by omega)).1
      simpa only [storedRatio, storedStep, hi] using P.eta₁_le_eta₂.trans hprev
    · intro j hj hgood
      have hj' : j ≠ trace.last := fun he ↦ hfinal (he ▸ hgood)
      rw [hi]
      omega

/-- An always very successful sequence of strictly lengthening probes
cannot be the probes of any terminating inner trace. -/
theorem no_termination_of_always_continue
    (trace : InternalDoublingTrace P f m x p previousRatio sufficient)
    (hprevious : P.η₂ ≤ previousRatio) (trials : ℕ → E)
    (hmatch : ∀ j ≤ trace.last, trace.step j = trials j)
    (hratio : ∀ j, P.η₂ ≤ btrRatio f m x (trials j))
    (hlength : ∀ j, ‖trials j‖ < ‖trials (j + 1)‖) : False := by
  have hstart : 0 < trace.last := trace.enter.mpr
    ⟨hprevious, by simpa only [hmatch 0 (Nat.zero_le _)] using hratio 0⟩
  have hstop := trace.stop hstart
  rcases hstop with ⟨N, hnone, _⟩ | hstop
  · simp at hnone
  apply hstop
  rw [hmatch _ le_rfl, hmatch _ (Nat.sub_le _ _)]
  exact ⟨hratio _, by simpa only [Nat.sub_add_cancel hstart] using hlength (trace.last - 1)⟩

end InternalDoublingTrace

/-- An infinite outer run of Algorithm 10.5.1, with a terminating inner trace
at each iteration. Step 5 updates the stored radius into the next initial
radius, with a strict upper endpoint for a successful but not very successful
iteration. -/
structure InternalDoublingRun (f : E → ℝ) (P : InternalDoublingParams)
    (sufficient : ℕ → (E → ℝ) → E → ℝ → E → Prop)
    (budget : Option ℕ := none) where
  x : ℕ → E
  p : ℕ → Seminorm ℝ E
  norm_separates : ∀ k v, p k v = 0 → v = 0
  model : ℕ → E → ℝ
  previousRatio : ℕ → ℝ
  trace : ∀ k, InternalDoublingTrace P f (model k) (x k) (p k) (previousRatio k)
    (sufficient k (model k) (x k)) budget
  initial_previous_ratio : previousRatio 0 = 1
  previous_ratio_update : ∀ k, previousRatio (k + 1) = (trace k).storedRatio
  iterate_update : ∀ k, x (k + 1) =
    Optimization.acceptStep P.η₁ f (x k) (trace k).storedStep
      (model k (x k) - model k (x k + (trace k).storedStep))
  radius_update : ∀ k, BTRRadiusUpdate P.toBTRParams (trace k).storedRatio
    (trace k).storedRadius ((trace (k + 1)).radius 0)
  successful_radius_strict : ∀ k,
    P.η₁ ≤ (trace k).storedRatio → (trace k).storedRatio < P.η₂ →
      (trace (k + 1)).radius 0 < (trace k).storedRadius

/-- The outer iterates, stored steps, and stored radii of internal doubling
form a run of Algorithm BTR. The enlargement at iteration `k + 1` can be
absorbed into the update at iteration `k`, because it only occurs when that
update follows a very successful trial. -/
noncomputable def InternalDoublingRun.toBTRRun {f : E → ℝ} {P : InternalDoublingParams}
    {sufficient : ℕ → (E → ℝ) → E → ℝ → E → Prop} {budget : Option ℕ}
    (run : InternalDoublingRun f P sufficient budget) :
    BTRRun f P.toBTRParams (fun k m x s ↦ sufficient k m x (run.trace k).storedRadius s) where
  x := run.x
  p := run.p
  norm_separates := run.norm_separates
  model := run.model
  s := fun k ↦ (run.trace k).storedStep
  Δ := fun k ↦ (run.trace k).storedRadius
  delta_initial_pos :=
    (run.trace 0).initial_radius_pos.trans_le (run.trace 0).storedRadius_ge_initial
  feasible := fun k ↦ (run.trace k).feasible _ (run.trace k).storedIndex_le_last
  sufficient_decrease := fun k ↦
    (run.trace k).sufficient_decrease _ (run.trace k).storedIndex_le_last
  predicted_pos := fun k ↦ (run.trace k).predicted_pos _ (run.trace k).storedIndex_le_last
  iterate_update := run.iterate_update
  radius_update := by
    intro k
    change BTRRadiusUpdate P.toBTRParams (run.trace k).storedRatio
      (run.trace k).storedRadius (run.trace (k + 1)).storedRadius
    have hupdate := run.radius_update k
    by_cases h : P.η₂ ≤ (run.trace k).storedRatio
    · refine ⟨fun _ ↦ (hupdate.very_successful h).trans
        (run.trace (k + 1)).storedRadius_ge_initial, ?_, ?_⟩
      · exact fun _ hlt ↦ (hlt.not_ge h).elim
      · exact fun hlt ↦ (hlt.not_ge (P.eta₁_le_eta₂.trans h)).elim
    · have hprevious : run.previousRatio (k + 1) < P.η₂ := by
        rw [run.previous_ratio_update]
        exact lt_of_not_ge h
      rw [(run.trace (k + 1)).storedRadius_eq_initial_of_previous_not_very_successful hprevious]
      exact hupdate

/-- A finite budget makes the internal loop terminate whenever the
prescribed probes can be computed. The retained trial still satisfies the
same acceptance rule, so the capped outer run has the BTR representation. -/
theorem exists_cappedInternalDoublingTrace {P : InternalDoublingParams} {f m : E → ℝ}
    {x : E} {p : Seminorm ℝ E} {previousRatio : ℝ} {sufficient : ℝ → E → Prop}
    (N : ℕ) (radius : ℕ → ℝ) (step : ℕ → E) (hpos : 0 < radius 0)
    (hfeas : ∀ j ≤ N + 1, x + step j ∈ trustRegion p x (radius j))
    (hsuff : ∀ j ≤ N + 1, sufficient (radius j) (step j))
    (hpred : ∀ j ≤ N + 1, 0 < m x - m (x + step j))
    (hgrowth : ∀ j < N + 1, P.γ₃ * radius j ≤ radius (j + 1)) :
    ∃ trace : InternalDoublingTrace P f m x p previousRatio sufficient (some N),
      trace.radius = radius ∧ trace.step = step := by
  classical
  by_cases henter : P.η₂ ≤ previousRatio ∧ P.η₂ ≤ btrRatio f m x (step 0)
  · let good (j : ℕ) := P.η₂ ≤ btrRatio f m x (step j) ∧ ‖step (j - 1)‖ < ‖step j‖
    have hex : ∃ j, 0 < j ∧ (j = N + 1 ∨ ¬ good j) := ⟨N + 1, by omega, Or.inl rfl⟩
    let j := Nat.find hex
    have hj : 0 < j ∧ (j = N + 1 ∨ ¬ good j) := Nat.find_spec hex
    have hjN : j ≤ N + 1 := Nat.find_min' hex ⟨by omega, Or.inl rfl⟩
    refine ⟨{
      last := j
      radius := radius
      step := step
      initial_radius_pos := hpos
      enter := ⟨fun _ ↦ henter, fun _ ↦ hj.1⟩
      feasible i hi := hfeas i (hi.trans hjN)
      sufficient_decrease i hi := hsuff i (hi.trans hjN)
      predicted_pos i hi := hpred i (hi.trans hjN)
      enlarge i hi := hgrowth i (hi.trans_le hjN)
      continue_loop i hi hij := ?_
      within_budget := ?_
      stop := fun _ ↦ hj.2.imp_left (fun h ↦ ⟨N, rfl, h⟩)
    }, rfl, rfl⟩
    · by_contra hn
      exact (Nat.find_min hex hij) ⟨hi, Or.inr hn⟩
    · intro M h
      cases Option.some.inj h
      exact hjN
  · refine ⟨{
      last := 0
      radius := radius
      step := step
      initial_radius_pos := hpos
      enter := by simp [henter]
      feasible i hi := hfeas i (by omega)
      sufficient_decrease i hi := hsuff i (by omega)
      predicted_pos i hi := hpred i (by omega)
      enlarge _ h := (Nat.not_lt_zero _ h).elim
      continue_loop _ _ h := (Nat.not_lt_zero _ h).elim
      within_budget := fun _ _ ↦ Nat.zero_le _
      stop := fun h ↦ (Nat.not_lt_zero _ h).elim
    }, rfl, rfl⟩

end Doubling

section StepLength

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rejection update (10.5.2) uses the length of the trial step in the
current trust-region norm. -/
def StepLengthRejection (γ₁bar γ₂bar : ℝ) (p : Seminorm ℝ E) (s : E) (Δ' : ℝ) : Prop :=
  γ₁bar * p s ≤ Δ' ∧ Δ' ≤ γ₂bar * p s

/-- If the next norm assigns the old step at least as much length as in (10.5.3),
the rejected trial is infeasible after the step-length contraction. -/
theorem rejected_trial_not_feasible_after_step_contraction
    {p p' : Seminorm ℝ E} {x s : E} {γ₁bar γ₂bar Δ' : ℝ}
    (hΔ : StepLengthRejection γ₁bar γ₂bar p s Δ') (hγ : γ₂bar < 1)
    (hs : 0 < p s) (hnorm : p s ≤ p' s) :
    x + s ∉ trustRegion p' x Δ' := by
  rw [mem_trustRegion, add_sub_cancel_left]
  exact not_le.mpr (hΔ.2.trans_lt ((mul_lt_of_lt_one_left hs hγ).trans_le hnorm))

/-- Reusing a rejected trial at a smaller radius preserves its sufficient model
decrease, provided the step still satisfies the feasibility test (10.5.4). -/
theorem rejected_trial_reusable {f m : E → ℝ} {x s g : E} {p : Seminorm ℝ E}
    {β κ Δ γ₂ η₁ : ℝ} {j : ℕ}
    (hκ : 0 ≤ κ) (hΔ : 0 ≤ Δ) (hγ₀ : 0 ≤ γ₂) (hγ₁ : γ₂ ≤ 1)
    (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (hfit : p s ≤ γ₂ ^ j * Δ) (hreject : btrRatio f m x s < η₁) :
    x + s ∈ trustRegion p x (γ₂ ^ j * Δ) ∧
      HasSufficientModelDecrease m x s g β (γ₂ ^ j * Δ) κ ∧
      Optimization.acceptStep η₁ f x s (m x - m (x + s)) = x := by
  refine ⟨?_, ⟨hdec.1, ?_⟩, Optimization.acceptStep_of_lt hreject⟩
  · rwa [mem_trustRegion, add_sub_cancel_left]
  · have hrad : γ₂ ^ j * Δ ≤ Δ :=
      mul_le_of_le_one_left hΔ (pow_le_one₀ hγ₀ hγ₁)
    exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hrad)
      (mul_nonneg hκ (norm_nonneg _))).trans hdec.2

/-- The last feasible radius in the geometric sequence (10.5.4) is followed
by an infeasible radius when the rejected step has positive length. -/
theorem exists_last_feasible_rejection {γ Δ a : ℝ}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) (ha : 0 < a) (hinit : a ≤ Δ) :
    ∃ j : ℕ, a ≤ γ ^ j * Δ ∧ γ ^ (j + 1) * Δ < a ∧
      ∀ i ≤ j, a ≤ γ ^ i * Δ := by
  classical
  have hlim : Filter.Tendsto (fun k : ℕ ↦ γ ^ k * Δ) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ₀ hγ₁).mul_const Δ
  have hfail : ∃ j : ℕ, γ ^ j * Δ < a := (hlim.eventually (gt_mem_nhds ha)).exists
  let n := Nat.find hfail
  have hn : γ ^ n * Δ < a := Nat.find_spec hfail
  have hn₀ : n ≠ 0 := by
    intro hz
    simp only [hz, pow_zero, one_mul] at hn
    exact hn.not_ge hinit
  let j := n - 1
  have hj : j + 1 = n := by omega
  have hprior (i : ℕ) (hi : i ≤ j) : a ≤ γ ^ i * Δ :=
    le_of_not_gt (Nat.find_min hfail (by omega : i < n))
  exact ⟨j, hprior j le_rfl, by simpa only [hj] using hn, hprior⟩

/-- The interval in (10.5.2) is contained in a BTR rejection interval
(10.5.1) at the last feasible geometric radius. The two endpoint comparisons
in (10.5.5) suffice for this containment. -/
theorem step_length_rejection_simulated {P : BTRParams} {p : Seminorm ℝ E}
    {s : E} {R Δ' γ₁bar γ₂bar : ℝ}
    (hlower : P.γ₁ / P.γ₂ ≤ γ₁bar) (hupper : γ₂bar ≤ P.γ₂)
    (hfit : p s ≤ R) (hfail : P.γ₂ * R < p s)
    (hΔ : StepLengthRejection γ₁bar γ₂bar p s Δ') :
    P.γ₁ * R ≤ Δ' ∧ Δ' ≤ P.γ₂ * R := by
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have hs : 0 ≤ p s := apply_nonneg _ _
  constructor
  · have hdiv : R ≤ p s / P.γ₂ := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hfail.le)
    calc
      _ ≤ P.γ₁ * (p s / P.γ₂) := mul_le_mul_of_nonneg_left hdiv P.gamma₁_pos.le
      _ = (P.γ₁ / P.γ₂) * p s := by ring
      _ ≤ γ₁bar * p s := mul_le_mul_of_nonneg_right hlower hs
      _ ≤ _ := hΔ.1
  · exact hΔ.2.trans ((mul_le_mul_of_nonneg_right hupper hs).trans
      (mul_le_mul_of_nonneg_left hfit hγ.le))

/-- The two step-length factors in (10.5.5) can lie in the prescribed
interval only when the basic contraction factors satisfy `γ₁ ≤ γ₂²`. -/
theorem step_length_rejection_compatible {P : BTRParams} {γ₁bar γ₂bar : ℝ}
    (hlower : P.γ₁ / P.γ₂ ≤ γ₁bar) (hbars : γ₁bar < γ₂bar)
    (hupper : γ₂bar ≤ P.γ₂) : P.γ₁ ≤ P.γ₂ ^ 2 := by
  have hγ : 0 < P.γ₂ := P.gamma₁_pos.trans_le P.gamma₁_le_gamma₂
  have h := (div_le_iff₀ hγ).mp (hlower.trans (hbars.le.trans hupper))
  simpa only [pow_two] using h

/-- The three-case update (10.5.6) uses step length in place of radius. -/
abbrev StepLengthRadiusUpdate (P : BTRParams) (ρ : ℝ)
    (p : Seminorm ℝ E) (s : E) (Δ' : ℝ) : Prop :=
  BTRRadiusUpdate P ρ (p s) Δ'

/-- The Cauchy step-length safeguard (10.5.7). -/
def CauchyStepLengthSafeguard (p : Seminorm ℝ E) (s sC : E) : Prop :=
  p sC ≤ p s

/-- The boundary version of the safeguard, (10.5.8). -/
def CauchyBoundarySafeguard (p : Seminorm ℝ E) (s sC : E) (Δ : ℝ) : Prop :=
  p sC = Δ → p s = Δ

/-- For a feasible trial the length safeguard (10.5.7) implies (10.5.8). -/
theorem CauchyStepLengthSafeguard.boundary {p : Seminorm ℝ E} {s sC : E} {Δ : ℝ}
    (h : CauchyStepLengthSafeguard p s sC) (hfit : p s ≤ Δ) :
    CauchyBoundarySafeguard p s sC Δ := by
  intro hC
  exact le_antisymm hfit (hC ▸ h)

/-- If the Cauchy point is on the boundary, (10.5.8) restores the very
successful noncontraction property of the ordinary BTR radius update. -/
theorem StepLengthRadiusUpdate.noncontract_of_cauchy_boundary
    {P : BTRParams} {p : Seminorm ℝ E} {s sC : E} {ρ Δ Δ' : ℝ}
    (hu : StepLengthRadiusUpdate P ρ p s Δ')
    (h : CauchyBoundarySafeguard p s sC Δ) (hC : p sC = Δ) (hρ : P.η₂ ≤ ρ) :
    Δ ≤ Δ' :=
  h hC ▸ hu.very_successful hρ

end StepLength

/-- Without an inner limit, the printed stopping rule can continue forever
even for a smooth bounded-below objective and exact models. The probes
`sⱼ = Δⱼ = 2^j` are all feasible and satisfy AA.1. Every ratio is one and
every step is strictly longer than the preceding one. -/
theorem internalDoubling_unbounded_inner_counterexample :
    let f : ℝ → ℝ := fun x ↦ Real.exp (-x)
    let r : ℕ → ℝ := fun j ↦ 2 ^ j
    let p : Seminorm ℝ ℝ := normSeminorm ℝ ℝ
    ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧
      (∀ j, r j ∈ trustRegion p 0 (r j) ∧
        2 * r j = r (j + 1) ∧
        0 < f 0 - f (0 + r j) ∧
        btrRatio f f 0 (r j) = 1 ∧ ‖r j‖ < ‖r (j + 1)‖) ∧
      (∀ (P : InternalDoublingParams) (sufficient : ℝ → ℝ → Prop)
          (trace : InternalDoublingTrace P f f 0 p 1 sufficient),
        (∀ j ≤ trace.last, trace.step j = r j) → False) ∧
      ∃ κ : ℝ, ∀ j β, 1 ≤ β →
        HasSufficientModelDecrease f 0 (r j) (gradient f 0) β (r j) κ := by
  dsimp only
  let f : ℝ → ℝ := fun x ↦ Real.exp (-x)
  let r : ℕ → ℝ := fun j ↦ 2 ^ j
  have hr (j : ℕ) : 1 ≤ r j := one_le_pow₀ (by norm_num)
  have hpos (j : ℕ) : 0 < r j := zero_lt_one.trans_le (hr j)
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hdrop (j : ℕ) : 1 - Real.exp (-1) ≤ f 0 - f (0 + r j) := by
    simp only [f, neg_zero, Real.exp_zero, zero_add]
    exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (hr j))) _
  have hprobes (j : ℕ) : r j ∈ trustRegion (normSeminorm ℝ ℝ) 0 (r j) ∧
      2 * r j = r (j + 1) ∧ 0 < f 0 - f (0 + r j) ∧
      btrRatio f f 0 (r j) = 1 ∧ ‖r j‖ < ‖r (j + 1)‖ := by
    have hpow : 2 * r j = r (j + 1) := by simp [r, pow_succ, mul_comm]
    have hpred : 0 < f 0 - f (0 + r j) := (sub_pos.mpr hexp).trans_le (hdrop j)
    refine ⟨?_, hpow, hpred, ?_, ?_⟩
    · rw [mem_trustRegion, sub_zero, coe_normSeminorm, Real.norm_eq_abs, abs_of_pos (hpos j)]
    · change (f 0 - f (0 + r j)) / (f 0 - f (0 + r j)) = 1
      exact div_self hpred.ne'
    · rw [Real.norm_of_nonneg (hpos j).le, Real.norm_of_nonneg (hpos (j + 1)).le, ← hpow]
      linarith [hpos j]
  refine ⟨Real.contDiff_exp.comp contDiff_id.neg, ⟨0, ?_⟩, hprobes, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (Real.exp_pos (-x)).le
  · intro P sufficient trace hmatch
    exact trace.no_termination_of_always_continue P.eta₂_lt_one.le r hmatch
      (fun j ↦ (hprobes j).2.2.2.1 ▸ P.eta₂_lt_one.le) (fun j ↦ (hprobes j).2.2.2.2)
  · let κ := (1 - Real.exp (-1)) / 2
    have hκ : 0 < κ := half_pos (sub_pos.mpr hexp)
    have hg : gradient f 0 = -1 := by
      rw [gradient_eq_deriv']
      have h := (Real.hasDerivAt_exp (- (0 : ℝ))).comp 0 ((hasDerivAt_id (0 : ℝ)).neg)
      change deriv (Real.exp ∘ Neg.neg) 0 = -1
      simpa only [id_eq, neg_zero, Real.exp_zero, one_mul] using h.deriv
    refine ⟨κ, fun j β hβ ↦ ⟨⟨hκ, ?_⟩, ?_⟩⟩
    · dsimp [κ]
      linarith [Real.exp_pos (-1)]
    · rw [hg, norm_neg, norm_one, mul_one]
      have hmin : min (1 / β) (r j) ≤ 1 :=
        (min_le_left _ _).trans (div_le_one (zero_lt_one.trans_le hβ) |>.mpr hβ)
      calc
        _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hmin hκ.le
        _ ≤ 1 - Real.exp (-1) := by dsimp [κ]; linarith
        _ ≤ _ := hdrop j

/-- The quadratic example after (10.5.6). Updating from the step length
can force geometric contraction at every iteration despite exact models and
very successful ratios. The iterates converge to the noncritical point one. -/
theorem stepLengthRadiusUpdate_counterexample (P : BTRParams) :
    let f : ℝ → ℝ := fun x ↦ x ^ 2
    let Δ : ℕ → ℝ := fun k ↦ (1 / 2) ^ k
    let x : ℕ → ℝ := fun k ↦ 1 + Δ k
    let s : ℕ → ℝ := fun k ↦ -(Δ k / 2)
    (∀ k, x k + s k ∈ trustRegion (normSeminorm ℝ ℝ) (x k) (Δ k) ∧
      0 < f (x k) - f (x k + s k) ∧
      HasSufficientModelDecrease f (x k) (s k) (gradient f (x k)) 3 (Δ k) (1 / 4) ∧
      btrRatio f f (x k) (s k) = 1 ∧
      StepLengthRadiusUpdate P 1 (normSeminorm ℝ ℝ) (s k) (Δ (k + 1)) ∧
      x (k + 1) = x k + s k) ∧
      Filter.Tendsto x Filter.atTop (nhds 1) ∧ gradient f 1 ≠ 0 := by
  dsimp only
  let f : ℝ → ℝ := fun x ↦ x ^ 2
  let Δ : ℕ → ℝ := fun k ↦ (1 / 2) ^ k
  let x : ℕ → ℝ := fun k ↦ 1 + Δ k
  let s : ℕ → ℝ := fun k ↦ -(Δ k / 2)
  have hgrad (z : ℝ) : gradient f z = 2 * z := by
    rw [gradient_eq_deriv']
    change deriv (fun x : ℝ ↦ x ^ 2) z = _
    rw [deriv_pow_field]
    norm_num
  have hpos (k : ℕ) : 0 < Δ k := pow_pos (by norm_num) _
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hsucc : Δ (k + 1) = Δ k / 2 := by dsimp [Δ]; rw [pow_succ]; ring
    have hlen : ‖s k‖ = Δ k / 2 := by
      change |-(Δ k / 2)| = Δ k / 2
      rw [abs_neg, abs_of_nonneg (by positivity [hpos k])]
    have hx : Δ k ≤ x k := by dsimp [x]; linarith
    have hx₀ : 0 < x k := (hpos k).trans_le hx
    have hsq : (Δ k) ^ 2 ≤ x k * Δ k := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hx (hpos k).le
    have hpred : x k * Δ k / 2 ≤ f (x k) - f (x k + s k) := by
      change x k * Δ k / 2 ≤ (x k) ^ 2 - (x k + -(Δ k / 2)) ^ 2
      nlinarith only [hsq, mul_nonneg hx₀.le (hpos k).le]
    have hpred₀ : 0 < f (x k) - f (x k + s k) :=
      (half_pos (mul_pos hx₀ (hpos k))).trans_le hpred
    refine ⟨?_, hpred₀, ?_, ?_, ?_, ?_⟩
    · rw [mem_trustRegion, add_sub_cancel_left, coe_normSeminorm, hlen]
      linarith [hpos k]
    · refine ⟨by norm_num, ?_⟩
      rw [hgrad, Real.norm_of_nonneg (by positivity [hx₀])]
      calc
        _ ≤ (1 / 4 : ℝ) * (2 * x k) * Δ k :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity [hx₀])
        _ = x k * Δ k / 2 := by ring
        _ ≤ _ := hpred
    · change (f (x k) - f (x k + s k)) / (f (x k) - f (x k + s k)) = 1
      exact div_self hpred₀.ne'
    · refine ⟨?_, ?_, ?_⟩
      · intro _
        change normSeminorm ℝ ℝ (s k) ≤ Δ (k + 1)
        rw [coe_normSeminorm, hlen, hsucc]
      · intro _ hlt
        exact (hlt.not_ge P.eta₂_lt_one.le).elim
      · intro hlt
        exact (hlt.not_ge (P.eta₁_le_eta₂.trans P.eta₂_lt_one.le)).elim
    · change 1 + Δ (k + 1) = 1 + Δ k + -(Δ k / 2)
      rw [hsucc]
      ring
  · have ht : Filter.Tendsto Δ Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [x, add_zero] using ht.const_add 1
  · rw [hgrad]
    norm_num

end ConnGouldToint.Chapter10
