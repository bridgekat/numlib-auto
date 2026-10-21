import Numlib.Optimization.InnerInspectionCertificates
import Numlib.Optimization.HigherOrderApproximateRegularizationTermination

/-!
# Gap witnesses at returned inner states

Each inspection epoch starts at order one. Passing an order stores its actual witness;
halving changes only the currently inspected radius, and improving the minimizing accuracy
resets the epoch. Thus an inspection return certifies every order at the final point and radii.
The raw norm boundary remains distinct from the corrected strict outer boundary.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderApproximateRegularization
open TaylorCriticality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def certificate (P : Parameters) (m : E → ℝ) (i : ℕ) (s : E) (δ : ℝ) : Prop :=
  ∃ d : E, GapWitness m i s δ P.fraction d ∧
    taylorDecrement m i s d ≤ P.fraction * P.theta * P.epsilon i * δ ^ i / (i ! : ℝ)

private abbrev passedOrders (P : Parameters) (m : E → ℝ) :=
  HigherOrderApproximateRegularization.InnerCertificates.PassedOrders (certificate P m)

private abbrev epochInvariant (P : Parameters) (m : E → ℝ) :=
  HigherOrderApproximateRegularization.InnerCertificates.EpochInvariant P.q (certificate P m)

private theorem epoch_pass {P : Parameters} {m : E → ℝ}
    {long : InnerState E → Prop} {a : InnerState E} {j : ℕ}
    (ha : passedOrders P m a j) (d : E)
    (hw : GapWitness m j a.step (a.radii j) P.fraction d)
    (htest : taylorDecrement m j a.step d ≤
      P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
    epochInvariant P m long
      ⟨a.mu, a.radii, a.step, if j = P.q then .returned else .inspect (j + 1)⟩ :=
  HigherOrderApproximateRegularization.InnerCertificates.pass ha ⟨d, hw, htest⟩

private theorem epoch_halve {P : Parameters} {m : E → ℝ}
    {a : InnerState E} {j : ℕ} (ha : passedOrders P m a j) :
    passedOrders P m
      ⟨a.mu, Function.update a.radii j (a.radii j / 2), a.step, .inspect j⟩ j :=
  HigherOrderApproximateRegularization.InnerCertificates.halve ha

private theorem epoch_of_ne_minimize {P : Parameters} {m : E → ℝ} {long : InnerState E → Prop}
    {z : E} {a b : InnerState E} (h : InnerTransition P m z a b)
    (hne : a.phase ≠ .minimize) (ha : epochInvariant P m long a) :
    epochInvariant P m long b := by
  cases h with
  | minimize hphase s hfrac => exact (hne hphase).elim
  | pass j hphase hj hjq d hw htest =>
    apply epoch_pass (d := d) (hw := hw) (htest := htest)
    simpa only [epochInvariant, InnerCertificates.EpochInvariant, hphase] using ha
  | halve j hphase hj hjq d hw hfail hsmall =>
    apply epoch_halve
    simpa only [epochInvariant, InnerCertificates.EpochInvariant, hphase] using ha
  | improve => trivial

private theorem epoch_raw {P : Parameters} {m : E → ℝ} {z : E} {a b : InnerState E}
    (h : InnerTransition P m z a b)
    (ha : epochInvariant P m (fun a => 1 ≤ ‖a.step‖) a) :
    epochInvariant P m (fun a => 1 ≤ ‖a.step‖) b := by
  by_cases hphase : a.phase = .minimize
  · cases h with
    | minimize hp s hfrac =>
      by_cases hs : 1 ≤ ‖s‖
      · simp only [hs, ite_true, epochInvariant, InnerCertificates.EpochInvariant]
        exact Or.inl trivial
      · simp only [ite_eq_right hs, epochInvariant, InnerCertificates.EpochInvariant,
          InnerCertificates.PassedOrders]
        intro i hi hij
        omega
    | pass => simp_all
    | halve => simp_all
    | improve => trivial
  · exact epoch_of_ne_minimize h hphase ha

/-- A raw returned state is either on the source's weak norm boundary or has actual witnesses
passing every model Taylor-gap test at its final point and radii. -/
theorem InnerExecution.return_quality {P : Parameters} {m : E → ℝ} {z : E} {N : ℕ}
    (h : InnerExecution P m z N) (hreturn : (h.state N).phase = .returned) :
    1 ≤ ‖(h.state N).step‖ ∨ ∀ j, 1 ≤ j → j ≤ P.q → ∃ d : E,
      GapWitness m j (h.state N).step ((h.state N).radii j) P.fraction d ∧
      taylorDecrement m j (h.state N).step d ≤
        P.fraction * P.theta * P.epsilon j * (h.state N).radii j ^ j / (j ! : ℝ) := by
  have hi : ∀ k, k ≤ N → epochInvariant P m (fun a => 1 ≤ ‖a.step‖) (h.state k) := by
    intro k hk
    induction k with
    | zero => simp only [epochInvariant, InnerCertificates.EpochInvariant, h.initial.2.2.2]
    | succ k ih => exact epoch_raw (h.transition k (by omega)) (ih (by omega))
  have hf := hi N le_rfl
  simp only [epochInvariant, InnerCertificates.EpochInvariant, hreturn,
    InnerCertificates.PassedOrders, certificate] at hf
  exact hf.imp_right (fun hp j hj hjq => hp j hj (by omega))

private theorem epoch_corrected {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {a b : InnerState E}
    (h : CorrectedInnerTransition P m z inherited a b)
    (ha : epochInvariant P m (fun a => 1 < ‖a.step‖ ∧ a.radii = inherited) a) :
    epochInvariant P m (fun a => 1 < ‖a.step‖ ∧ a.radii = inherited) b := by
  by_cases hp : a.phase = .minimize
  · simp only [CorrectedInnerTransition, ite_eq_left hp] at h
    obtain ⟨s, _, rfl⟩ := h
    by_cases hs : 1 < ‖s‖
    · simp only [ite_eq_left hs, epochInvariant, InnerCertificates.EpochInvariant]
      exact Or.inl ⟨hs, trivial⟩
    · simp only [ite_eq_right hs, epochInvariant, InnerCertificates.EpochInvariant,
          InnerCertificates.PassedOrders]
      intro i hi hij
      omega
  · exact epoch_of_ne_minimize
      (by simpa only [CorrectedInnerTransition, ite_eq_right hp] using h) hp ha

/-- A strict-boundary inner return either has a genuine long step and inherited radii,
or actual witnesses passing every requested gap test at the final point and radii. -/
theorem CorrectedInnerExecution.return_quality {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {N : ℕ} (h : CorrectedInnerExecution P m z inherited N)
    (hreturn : (h.state N).phase = .returned) :
    (1 < ‖(h.state N).step‖ ∧ (h.state N).radii = inherited) ∨
      ∀ j, 1 ≤ j → j ≤ P.q → ∃ d : E,
        GapWitness m j (h.state N).step ((h.state N).radii j) P.fraction d ∧
        taylorDecrement m j (h.state N).step d ≤
          P.fraction * P.theta * P.epsilon j * (h.state N).radii j ^ j / (j ! : ℝ) := by
  have hi : ∀ k, k ≤ N → epochInvariant P m
      (fun a => 1 < ‖a.step‖ ∧ a.radii = inherited) (h.state k) := by
    intro k hk
    induction k with
    | zero => simp only [epochInvariant, InnerCertificates.EpochInvariant, h.initial.2.2.2]
    | succ k ih => exact epoch_corrected (h.transition k (by omega)) (ih (by omega))
  have hf := hi N le_rfl
  simp only [epochInvariant, InnerCertificates.EpochInvariant, hreturn,
    InnerCertificates.PassedOrders, certificate] at hf
  exact hf.imp_right (fun hp j hj hjq => hp j hj (by omega))

/-- Every raw transition preserves positive radii bounded by one at all active orders. -/
theorem InnerTransition.radii_valid {P : Parameters} {m : E → ℝ} {z : E}
    {a b : InnerState E} (h : InnerTransition P m z a b) (ha : ValidRadii P a.radii) :
    ValidRadii P b.radii := by
  cases h with
  | minimize => exact ha
  | pass => exact ha
  | improve => exact ha
  | halve j hphase hj hjq d hw hfail hsmall =>
    intro i hi hiq
    change 0 < Function.update a.radii j (a.radii j / 2) i ∧
      Function.update a.radii j (a.radii j / 2) i ≤ 1
    by_cases hij : i = j
    · subst i
      rw [Function.update_self]
      have hjr := ha j (by omega) hjq
      exact ⟨by linarith [hjr.1], by linarith [hjr.2]⟩
    · rw [Function.update_of_ne hij]
      exact ha i hi hiq

/-- Copying valid inherited radii at a strict long return preserves validity. -/
theorem CorrectedInnerTransition.radii_valid {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {a b : InnerState E}
    (h : CorrectedInnerTransition P m z inherited a b)
    (hinherited : ValidRadii P inherited) (ha : ValidRadii P a.radii) :
    ValidRadii P b.radii := by
  by_cases hp : a.phase = .minimize
  · simp only [CorrectedInnerTransition, ite_eq_left hp] at h
    obtain ⟨s, _, rfl⟩ := h
    dsimp
    split_ifs
    · exact hinherited
    · exact ha
  · exact (show InnerTransition P m z a b by
      simpa only [CorrectedInnerTransition, ite_eq_right hp] using h).radii_valid ha

/-- Valid inherited radii give valid radii at every corrected state, including long returns. -/
theorem CorrectedInnerExecution.radii_valid {P : Parameters} {m : E → ℝ} {z : E}
    {inherited : ℕ → ℝ} {N : ℕ} (h : CorrectedInnerExecution P m z inherited N)
    (hinherited : ValidRadii P inherited) {k : ℕ} (hk : k ≤ N) :
    ValidRadii P (h.state k).radii := by
  induction k with
  | zero =>
    rw [h.initial.2.2.1]
    intro j hj hjq
    exact ⟨by norm_num, le_rfl⟩
  | succ k ih => exact (h.transition k (by omega)).radii_valid hinherited (ih (by omega))

/-- A returned strict-boundary inner execution constructs an actual outer model step.
Every direction is extracted from its final inspection epoch. -/
theorem CorrectedInnerExecution.exists_modelStep {P : Parameters} {f : E → ℝ} {x : E}
    {σ : ℝ} {z : E} {inherited : ℕ → ℝ} {N : ℕ}
    (h : CorrectedInnerExecution P (model f P.p x σ) z inherited N)
    (hinherited : ValidRadii P inherited) (hreturn : (h.state N).phase = .returned) :
    ∃ trial : ModelStep P f x σ inherited,
      trial.step = (h.state N).step ∧ trial.radii = (h.state N).radii := by
  classical
  have hnonincrease : model f P.p x σ (h.state N).step ≤ model f P.p x σ 0 :=
    model_nonincrease_of_fraction h.is_minimizer (h.mu_bounds le_rfl).1.le
      (h.fraction_of_ne_minimize le_rfl (by rw [hreturn]; decide))
  have hquality := h.return_quality hreturn
  have hex : ∃ d : ℕ → E,
      (1 < ‖(h.state N).step‖ ∧ (h.state N).radii = inherited) ∨
      ∀ j, 1 ≤ j → j ≤ P.q →
        GapWitness (model f P.p x σ) j (h.state N).step ((h.state N).radii j) P.fraction (d j) ∧
        taylorDecrement (model f P.p x σ) j (h.state N).step (d j) ≤
          P.fraction * P.theta * P.epsilon j * (h.state N).radii j ^ j / (j ! : ℝ) := by
    rcases hquality with hl | hg
    · exact ⟨fun _ => 0, Or.inl hl⟩
    · have he : ∀ j, ∃ d : E, 1 ≤ j → j ≤ P.q →
          GapWitness (model f P.p x σ) j (h.state N).step ((h.state N).radii j) P.fraction d ∧
          taylorDecrement (model f P.p x σ) j (h.state N).step d ≤
            P.fraction * P.theta * P.epsilon j * (h.state N).radii j ^ j / (j ! : ℝ) := by
        intro j
        by_cases hj : 1 ≤ j ∧ j ≤ P.q
        · obtain ⟨d, hd⟩ := hg j hj.1 hj.2
          exact ⟨d, fun _ _ => hd⟩
        · exact ⟨0, fun h1 hq => (hj ⟨h1, hq⟩).elim⟩
      choose d hd using he
      exact ⟨d, Or.inr hd⟩
  obtain ⟨d, hd⟩ := hex
  exact ⟨{
    step := (h.state N).step
    radii := (h.state N).radii
    radii_valid := h.radii_valid hinherited le_rfl
    nonincrease := hnonincrease
    direction := d
    quality := hd }, rfl, rfl⟩

/-- A corrected return of norm at most one retains unit low-order radii and every quantitative
higher-order floor. Such a return comes from inspection, never from the strict long branch. -/
theorem CorrectedInnerExecution.radii_of_return_small {P : Parameters} {m : E → ℝ} {z : E}
    {M : ℝ} (hM : 1 ≤ M) (hdec : SmallRadiusDecrease P m M)
    {inherited : ℕ → ℝ} {N : ℕ} (h : CorrectedInnerExecution P m z inherited N)
    (hreturn : (h.state N).phase = .returned) (hs : ‖(h.state N).step‖ ≤ 1) :
    (∀ j, j ≤ 2 → (h.state N).radii j = 1) ∧
      ∀ j, 3 ≤ j → j ≤ P.q → radiusFloor P M j ≤ (h.state N).radii j := by
  have hstep : ∀ {a b : InnerState E}, CorrectedInnerTransition P m z inherited a b →
      InnerBounds P M a → b.phase = .returned → ‖b.step‖ ≤ 1 →
      (∀ j, j ≤ 2 → b.radii j = 1) ∧
        ∀ j, 3 ≤ j → j ≤ P.q → radiusFloor P M j ≤ b.radii j := by
    intro a b ht ha hb hs
    by_cases hp : a.phase = .minimize
    · simp only [CorrectedInnerTransition, ite_eq_left hp] at ht
      obtain ⟨s, _, rfl⟩ := ht
      have hsn : ¬1 < ‖s‖ := not_lt_of_ge hs
      simp only [ite_eq_right hsn] at hb
      cases hb
    · have hr : InnerTransition P m z a b := by
        simpa only [CorrectedInnerTransition, ite_eq_right hp] using ht
      cases hr with
      | minimize hphase s hfrac => exact (hp hphase).elim
      | pass => exact ⟨ha.radii_low, ha.radii_floor⟩
      | halve => cases hb
      | improve => cases hb
  cases N with
  | zero => rw [h.initial.2.2.2] at hreturn; cases hreturn
  | succ k =>
    have ht := h.transition k (Nat.lt_succ_self k)
    exact hstep ht (h.bounds hM hdec (Nat.le_succ k) ht.source_ne_returned) hreturn hs

end Optimization.HigherOrderApproximateRegularization
