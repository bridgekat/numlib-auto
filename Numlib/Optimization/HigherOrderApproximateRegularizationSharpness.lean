import Numlib.Optimization.HigherOrderTrustRegionSharpness
import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Optimization.TaylorCriticalityLocalMinimum

/-!
# Sharp approximate-regularization executions

Sparse actual objective jets generate accepted regularization trials. Model optimality radii
are an explicit premise, independently of objective interpolation. This distinguishes the
unit-radius good case from smaller-radius constructions.
-/
noncomputable section
open scoped Nat NNReal
namespace Optimization.HigherOrderApproximateRegularizationSharpness
open HigherOrderApproximateRegularization HigherOrderSharpness TaylorCriticality
open RegularizedTaylorModel Metric Set

/-- Fixed admissible regularization parameters with common accuracy and exact witnesses. -/
def parameters (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p)
    (ε σ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hσ : 0 < σ) : Parameters where
  p := p
  q := q
  order_pos := hq
  order_le := hqp
  epsilon := fun _ => ε
  epsilon_pos := fun _ _ _ => hε
  epsilon_lt_one := fun _ _ _ => hε1
  theta := 1 / 2
  fraction := 1
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := σ
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := hσ
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  fraction_pos := by norm_num
  fraction_le_one := le_rfl

/-- Actual scalar Taylor decrements from a sparse objective jet, at every truncation order. -/
theorem decrement_sparse {N p q k : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    (hq : 1 ≤ q)
    (hjet : ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) = sparseJet N q G h k j)
    {j : ℕ} (hj : j ≤ p) (d : ℝ) :
    taylorDecrement f j ((k : ℝ) * h) d =
      if q ≤ j ∧ k < N then G / q.factorial * d ^ q else 0 := by
  induction j with
  | zero => simp [show ¬q ≤ 0 by omega]
  | succ j ih =>
    rw [taylorDecrement_succ, ih (by omega),
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hjet (j + 1) hj]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    simp only [sparseJet, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    by_cases he : j + 1 = q
    · subst q
      simp only [show ¬j + 1 ≤ j by omega, false_and, ite_false, le_refl, true_and]
      split_ifs <;> ring
    · have hi : q ≤ j + 1 ↔ q ≤ j := by omega
      simp only [he, ite_false, mul_zero, sub_zero, hi]

/-- Exact maximization of a nonnegative monomial decrement on a scalar ball. -/
theorem gap_sparse {N p q k : ℕ} {f : ℝ → ℝ} {G h δ : ℝ}
    (hq : 1 ≤ q) (hG : 0 ≤ G) (hδ : 0 ≤ δ)
    (hjet : ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) = sparseJet N q G h k j)
    {j : ℕ} (hj : j ≤ p) :
    gapOn (taylorDecrement f j ((k : ℝ) * h)) (closedBall 0 δ) =
      taylorDecrement f j ((k : ℝ) * h) δ := by
  apply le_antisymm
  · apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    rw [decrement_sparse hq hjet hj, decrement_sparse hq hjet hj]
    split_ifs
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hd' : |d| ≤ δ := by simpa [Real.dist_eq] using hd
      exact (le_abs_self _).trans (by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hd' _)
    · exact le_rfl
  · exact le_gapOn (isCompact_closedBall 0 δ)
      (continuous_taylorDecrement f j ((k : ℝ) * h)).continuousOn
      (by simp [abs_of_nonneg hδ])

/-- Explicit actual model-gap requirement for a selected step and testing radius. -/
def ModelQuality (P : Parameters) (f : ℝ → ℝ) (x h σ δ : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ P.q →
    gapOn (taylorDecrement (model f P.p x σ) j h) (closedBall 0 δ) ≤
      P.theta * P.epsilon j * δ ^ j / (j.factorial : ℝ)

/-- The states of an accepted constant-spacing execution, with the cache cleared after each
successful trial. -/
def state (σ δ h : ℝ) (k : ℕ) : OuterState ℝ :=
  ⟨(k : ℝ) * h, σ, fun _ => δ, 0, true⟩

/-- Accepted local trials and an actual final passed test assemble into a complete legal
execution, with exact objective and derivative-cache costs. -/
theorem execution_of_accepted {N : ℕ} {P : Parameters} {f : ℝ → ℝ} {h σ δ : ℝ}
    (hσ : P.sigmaMin ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hfrac : P.fraction = 1)
    (hfailed : ∀ k < N, Nonempty (FailedTest P f ((k : ℝ) * h) (fun _ => δ)))
    (hpassed : PassedTest P f ((N : ℝ) * h) (fun _ => δ))
    (hmodel : ∀ k < N, model f P.p ((k : ℝ) * h) σ h <
      model f P.p ((k : ℝ) * h) σ 0)
    (hquality : ∀ k < N, ModelQuality P f ((k : ℝ) * h) h σ δ)
    (hratio : ∀ k < N, (f ((k : ℝ) * h) - f ((k : ℝ) * h + h)) /
      taylorDecrement f P.p ((k : ℝ) * h) h = 1) :
    ∃ run : OuterExecution P f 0 σ (fun _ => δ) N,
      run.state = state σ δ h ∧ run.last = .stopTest (run.state N) ∧
      (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
      run.functionCount = N + 1 ∧ run.derivativeCount = N * P.p + P.q := by
  classical
  have hv : ValidRadii P (fun _ => δ) := fun _ _ _ => ⟨hδ, hδ1⟩
  have htrial (k : ℕ) (hk : k < N) : ∃ t : ModelStep P f ((k : ℝ) * h) σ (fun _ => δ),
      t.step = h ∧ t.radii = (fun _ => δ) := by
    choose d hd using fun j : ℕ => exists_gapWitness (model f P.p ((k : ℝ) * h) σ) j h
      hδ.le P.fraction_le_one
    refine ⟨⟨h, fun _ => δ, hv, (hmodel k hk).le, d, Or.inr ?_⟩, rfl, rfl⟩
    intro j hj hjq
    refine ⟨hd j, ?_⟩
    rw [hfrac, one_mul]
    exact (le_gapOn (isCompact_closedBall (0 : ℝ) δ)
      (continuous_taylorDecrement (model f P.p ((k : ℝ) * h) σ) j h).continuousOn
      (show d j ∈ closedBall 0 δ by simpa using (hd j).feasible)).trans (hquality k hk j hj hjq)
  choose trial hstep hradii using htrial
  let run : OuterExecution P f 0 σ (fun _ => δ) N := {
    state := state σ δ h
    functionCalls := fun k => if k < N then 1 else 0
    derivativeCalls := fun k => if k < N then P.p else P.q
    last := .stopTest (state σ δ h N)
    initial := ⟨hσ, hv, by simp [state]⟩
    valid := fun _ _ => ⟨hσ, hv, Nat.zero_le _, by simp [state]⟩
    transition := by
      intro k hk
      have hu : ParameterUpdate P 1 σ σ := by
        rw [ParameterUpdate, ite_eq_left P.eta2_lt_one.le]
        exact ⟨max_le hσ (mul_le_of_le_one_left
          (P.sigmaMin_pos.le.trans hσ) P.gamma1_lt_one.le), le_rfl⟩
      have ht := OuterTransition.trial (state σ δ h k) (fun _ => hfailed k hk)
        (show 0 ≤ P.p by omega) (trial k hk)
        (by simpa only [state, hstep] using hmodel k hk) σ
        (by simpa only [state, hstep, hratio k hk] using hu)
      have hη : P.eta1 ≤ 1 := P.eta_le.trans P.eta2_lt_one.le
      simpa only [state, hstep, hradii, hratio k hk, ite_eq_left hη, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, ite_eq_left hk, Nat.sub_zero] using ht
    final := by
      simpa [state] using OuterTransition.stop (state σ δ h N) rfl
        (show 0 ≤ P.q by omega) hpassed }
  refine ⟨run, rfl, rfl, ?_, ?_, ?_⟩
  · intro k hk ⟨hs⟩
    obtain ⟨ht⟩ := hfailed k hk
    have hl := (hs.witness ht.order ht.order_pos ht.order_le).fraction_le
    have hu := hs.passes ht.order ht.order_pos ht.order_le
    have hb := le_gapOn (isCompact_closedBall (0 : ℝ) δ)
      (continuous_taylorDecrement f ht.order ((k : ℝ) * h)).continuousOn
      (show ht.direction ht.order ∈ closedBall 0 δ by
        simpa using (ht.witness ht.order ht.order_pos le_rfl).feasible)
    have hff := ht.fails
    simp only [hfrac, one_mul] at hl hu hff
    change gapOn (taylorDecrement f ht.order ((k : ℝ) * h)) (closedBall 0 δ) ≤
      taylorDecrement f ht.order ((k : ℝ) * h) (hs.direction ht.order) at hl
    exact (not_lt_of_ge (hff.trans (hb.trans hl))) hu
  · change 1 + ∑ k ∈ Finset.range (N + 1), (if k < N then 1 else 0) = N + 1
    rw [Finset.sum_range_succ]
    have hh : ∑ k ∈ Finset.range N, (if k < N then 1 else 0) = N := by
      rw [Finset.sum_congr rfl (fun k hk => ite_eq_left (Finset.mem_range.mp hk))]
      simp
    rw [hh]
    simp [Nat.add_comm]
  · change (∑ k ∈ Finset.range (N + 1), (if k < N then P.p else P.q)) = N * P.p + P.q
    rw [Finset.sum_range_succ]
    have hh : ∑ k ∈ Finset.range N, (if k < N then P.p else P.q) = N * P.p := by
      rw [Finset.sum_congr rfl (fun k hk => ite_eq_left (Finset.mem_range.mp hk))]
      simp
    rw [hh]
    simp

/-- Sparse objective jets produce an actual legal outer execution, its first stopping test,
and the precise oracle costs. Model quality is expressed using actual Taylor gaps. -/
theorem run_of_sparseJet {N : ℕ} {P : Parameters} {f : ℝ → ℝ} {G h σ δ : ℝ}
    (hσ : P.sigmaMin ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hG : 0 < G)
    (hfail : P.epsilon P.q < G) (hfrac : P.fraction = 1)
    (hjet : ∀ k ≤ N, ∀ j ≤ P.p,
      iteratedDeriv j f ((k : ℝ) * h) = sparseJet N P.q G h k j)
    (hmodel : ∀ k < N, model f P.p ((k : ℝ) * h) σ h <
      model f P.p ((k : ℝ) * h) σ 0)
    (hquality : ∀ k < N, ModelQuality P f ((k : ℝ) * h) h σ δ)
    (hratio : ∀ k < N, (f ((k : ℝ) * h) - f ((k : ℝ) * h + h)) /
      taylorDecrement f P.p ((k : ℝ) * h) h = 1) :
    ∃ run : OuterExecution P f 0 σ (fun _ => δ) N,
      run.state = state σ δ h ∧ run.last = .stopTest (run.state N) ∧
      (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
      run.functionCount = N + 1 ∧ run.derivativeCount = N * P.p + P.q := by
  have hdec (k : ℕ) (hk : k ≤ N) (j : ℕ) (hj : j ≤ P.p) (d : ℝ) :=
    decrement_sparse P.order_pos (hjet k hk) hj d
  have hw (k : ℕ) (hk : k ≤ N) (j : ℕ) (hj : j ≤ P.p) :
      GapWitness f j ((k : ℝ) * h) δ P.fraction δ := by
    refine ⟨by simp [Real.norm_eq_abs, abs_of_pos hδ], ?_⟩
    rw [hfrac, one_mul, gap_sparse P.order_pos hG.le hδ.le (hjet k hk) hj]
  have hfailed (k : ℕ) (hk : k < N) : Nonempty (FailedTest P f ((k : ℝ) * h) (fun _ => δ)) := by
    refine ⟨⟨P.q, P.order_pos, le_rfl, fun _ => δ,
      fun j _ hj => hw k hk.le j (hj.trans P.order_le), ?_, ?_⟩⟩
    · intro j hj hjq
      rw [hdec k hk.le j (hjq.le.trans P.order_le),
        ite_eq_right (by omega : ¬(P.q ≤ j ∧ k < N))]
      have hpε := P.epsilon_pos j hj hjq.le
      positivity
    · rw [hdec k hk.le P.q P.order_le, ite_eq_left ⟨le_rfl, hk⟩, hfrac]
      have : 0 < δ ^ P.q / (P.q.factorial : ℝ) := by positivity
      calc
        _ = P.epsilon P.q * (δ ^ P.q / (P.q.factorial : ℝ)) := by ring
        _ ≤ G * (δ ^ P.q / (P.q.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hfail.le this.le
        _ = _ := by ring
  have hpassed : PassedTest P f ((N : ℝ) * h) (fun _ => δ) := by
    refine ⟨fun _ => δ, fun j _ hj => hw N le_rfl j (hj.trans P.order_le), ?_⟩
    intro j hj hjq
    rw [hdec N le_rfl j (hjq.trans P.order_le), ite_eq_right (by omega)]
    have hpε := P.epsilon_pos j hj hjq
    positivity
  exact execution_of_accepted hσ hδ hδ1 hfrac hfailed hpassed hmodel hquality hratio

/-- The positive minimizer of a sparse power model is global, for arbitrary active order.
The proof factors its derivative into the difference of two natural powers. -/
theorem power_model_minimum {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p)
    {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    -(p + 1 : ℝ) * h ^ (p - q + 1) * h ^ q + (q : ℝ) * h ^ (p + 1) ≤
      -(p + 1 : ℝ) * h ^ (p - q + 1) * t ^ q + (q : ℝ) * |t| ^ (p + 1) := by
  let g : ℝ → ℝ := fun x => -(p + 1 : ℝ) * h ^ (p - q + 1) * x ^ q +
    (q : ℝ) * x ^ (p + 1)
  have hd (x : ℝ) : HasDerivAt g
      ((q : ℝ) * (p + 1 : ℝ) * x ^ (q - 1) * (x ^ (p - q + 1) - h ^ (p - q + 1))) x := by
    convert (((hasDerivAt_id x).pow q).const_mul (-(p + 1 : ℝ) * h ^ (p - q + 1))).add
      (((hasDerivAt_id x).pow (p + 1)).const_mul (q : ℝ)) using 1
    · rfl
    dsimp
    have he : x ^ (q - 1) * x ^ (p - q + 1) = x ^ p := by
      rw [← pow_add, show q - 1 + (p - q + 1) = p by omega]
    push_cast
    linear_combination (q : ℝ) * (p + 1 : ℝ) * he
  have hm : MonotoneOn g (Ici h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici h) (by fun_prop)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x).deriv]
    have hhx : h ≤ x := (interior_subset hx)
    have hpow := pow_le_pow_left₀ hh hhx (p - q + 1)
    have hx0 : 0 ≤ x := hh.trans hhx
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hpow)
  have ha : AntitoneOn g (Icc 0 h) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 h) (by fun_prop)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) h := interior_subset hx
    rw [(hd x).deriv]
    have hpow := pow_le_pow_left₀ hx'.1 hx'.2 (p - q + 1)
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hx'.1 _))
      (sub_nonpos.mpr hpow)
  have hab : g h ≤ g |t| := by
    by_cases ht : |t| ≤ h
    · exact ha ⟨abs_nonneg _, ht⟩ ⟨hh, le_rfl⟩ ht
    · exact hm (show h ∈ Ici h from le_refl h)
        (le_of_lt (lt_of_not_ge ht)) (le_of_lt (lt_of_not_ge ht))
  change _ ≤ g |t| at hab
  apply hab.trans
  dsimp [g]
  have hp : t ^ q ≤ |t| ^ q := by rw [← abs_pow]; exact le_abs_self _
  have hn : -(p + 1 : ℝ) * h ^ (p - q + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (pow_nonneg hh _)
  exact add_le_add (mul_le_mul_of_nonpos_left hp hn) le_rfl

/-- A fixed regularization parameter matching the sparse step normalization. -/
def sigma (p q : ℕ) : ℝ := 2 * p.factorial / (q - 1).factorial

/-- The normalized regularization parameter is positive. -/
theorem sigma_pos (p q : ℕ) : 0 < sigma p q := by unfold sigma; positivity

/-- The actual sparse-jet model is a positive multiple of its power-model shape. -/
theorem model_sparse_shape {N p q k : ℕ} {f : ℝ → ℝ} {h t : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N)
    (hjet : ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) =
      sparseJet N q (2 * h ^ (p - q + 1)) h k j) :
    model f p ((k : ℝ) * h) (sigma p q) t =
      f ((k : ℝ) * h) + 2 / (((p : ℝ) + 1) * q.factorial) *
        (-((p : ℝ) + 1) * h ^ (p - q + 1) * t ^ q + (q : ℝ) * |t| ^ (p + 1)) := by
  have hqfac : (q.factorial : ℝ) = (q : ℝ) * (q - 1).factorial := by
    have he := Nat.factorial_succ (q - 1)
    rw [Nat.sub_add_cancel hq] at he
    exact_mod_cast he
  have hv : f ((k : ℝ) * h) = -(k : ℝ) * (2 * h ^ (p - q + 1)) *
      h ^ q / q.factorial := by simpa [sparseJet] using hjet 0 (by omega)
  change HigherOrderRegularization.model f p ((k : ℝ) * h) (sigma p q) t = _
  rw [model_of_sparseJet hq hqp hk hjet, hv, sigma, Nat.factorial_succ]
  push_cast
  rw [hqfac]
  field_simp
  ring

/-- The chosen sparse step is a global minimizer of the actual regularized Taylor model. -/
theorem model_sparse_minimum {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hh : 0 ≤ h)
    (hjet : ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) =
      sparseJet N q (2 * h ^ (p - q + 1)) h k j) (t : ℝ) :
    model f p ((k : ℝ) * h) (sigma p q) h ≤
      model f p ((k : ℝ) * h) (sigma p q) t := by
  rw [model_sparse_shape hq hqp hk hjet, model_sparse_shape hq hqp hk hjet,
    abs_of_nonneg hh]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (power_model_minimum hq hqp hh t) (by positivity))

/-- The normalized sparse step strictly reduces the actual regularized Taylor model. -/
theorem model_sparse_strict {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) =
      sparseJet N q (2 * h ^ (p - q + 1)) h k j) :
    model f p ((k : ℝ) * h) (sigma p q) h <
      model f p ((k : ℝ) * h) (sigma p q) 0 := by
  rw [model_sparse_shape hq hqp hk hjet, model_zero, abs_of_pos hh]
  have he : h ^ (p - q + 1) * h ^ q = h ^ (p + 1) := by
    rw [← pow_add, show p - q + 1 + q = p + 1 by omega]
  have hneg : -((p : ℝ) + 1) * h ^ (p - q + 1) * h ^ q +
      (q : ℝ) * h ^ (p + 1) < 0 := by
    rw [mul_assoc, he]
    have hqr : (q : ℝ) < p + 1 := by exact_mod_cast (show q < p + 1 by omega)
    nlinarith [pow_pos hh (p + 1)]
  have hc : 0 < 2 / (((p : ℝ) + 1) * q.factorial) := by positivity
  linarith [mul_neg_of_pos_of_neg hc hneg]

/-- On a sparse chain the true-to-predicted ratio is exactly one. -/
theorem ratio_sparse {N p q k : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hG : 0 < G) (hh : 0 < h)
    (hjet : ∀ i ≤ N, ∀ j ≤ p,
      iteratedDeriv j f ((i : ℝ) * h) = sparseJet N q G h i j) :
    (f ((k : ℝ) * h) - f ((k : ℝ) * h + h)) /
      taylorDecrement f p ((k : ℝ) * h) h = 1 := by
  have hv (i : ℕ) (hi : i ≤ N) : f ((i : ℝ) * h) =
      -(i : ℝ) * G * h ^ q / q.factorial := by
    simpa [sparseJet] using hjet i hi 0 (by omega)
  have hx : (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
  rw [decrement_sparse hq (hjet k hk.le) le_rfl, ite_eq_left ⟨hqp, hk⟩,
    hx, hv k hk.le, hv (k + 1) hk]
  push_cast
  have hp : G / (q.factorial : ℝ) * h ^ q ≠ 0 := by positivity
  apply (div_eq_one_iff_eq hp).mpr
  ring

/-- Uniform derivative bounds promote the top scalar Lipschitz estimate to all tensor orders. -/
theorem all_derivatives_lipschitz {p : ℕ} {f : ℝ → ℝ} {L B : ℝ≥0}
    (hf : ContDiff ℝ p f) (hL : LipschitzWith L (iteratedDeriv p f))
    (hb : ∀ j ≤ p, ∀ x, |iteratedDeriv j f x| ≤ B) :
    ∀ j ≤ p, LipschitzWith (max L B) (iteratedFDeriv ℝ j f) := by
  intro j hj
  apply HigherOrderSharpness.iteratedFDeriv_lipschitz
  by_cases he : j = p
  · subst j
    exact hL.weaken (le_max_left _ _)
  · apply LipschitzWith.weaken (K := B) _ (le_max_right _ _)
    apply lipschitzWith_of_nnnorm_deriv_le
      (hf.differentiable_iteratedDeriv j (by exact_mod_cast (show j < p by omega)))
    intro x
    change ‖deriv (iteratedDeriv j f) x‖ ≤ (B : ℝ)
    simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hb (j + 1) (by omega) x

/-- Uniform smooth bounded good-case Hermite objectives. The selected steps are actual global
model minimizers. The only remaining premise for the legal execution is the explicit unit
model-radius criterion, as assumed in the good-case sharpness statement. -/
theorem exists_good_family (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p q hq hqp ε (sigma p q) hε (by linarith) (sigma_pos p q)
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ),
        ContDiff ℝ p f ∧ (∀ j ≤ p, LipschitzWith L (iteratedFDeriv ℝ j f)) ∧
        (∀ x, |f x| ≤ B) ∧ f 0 = 0 ∧ 0 < h ∧ h ≤ 1 ∧
        N = ⌈1 / ε ^ sharpExponent p q⌉₊ ∧
        (∀ k < N, ∀ t, model f p ((k : ℝ) * h) (sigma p q) h ≤
          model f p ((k : ℝ) * h) (sigma p q) t) ∧
        (∀ k < N, ε / (q.factorial : ℝ) <
          gapOn (taylorDecrement f q ((k : ℝ) * h)) (closedBall 0 1)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j ((N : ℝ) * h)) (closedBall 0 1) = 0) ∧
        ((∀ k < N, ModelQuality P f ((k : ℝ) * h) h (sigma p q) 1) →
          ∃ run : OuterExecution P f 0 (sigma p q) (fun _ => 1) N,
            run.state = state (sigma p q) 1 h ∧
            run.last = .stopTest (run.state N) ∧
            (∀ k < N,
              ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
            run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q) := by
  obtain ⟨L, B, hc⟩ := exists_sparseJet_chain p q hq hqp 4 (by norm_num)
  refine ⟨max L B, B, ?_⟩
  intro ε hε hεsmall
  dsimp only
  let h := ε ^ (((p - q + 1 : ℕ) : ℝ)⁻¹)
  have hh : 0 < h := Real.rpow_pos_of_pos hε _
  have hh1 : h ≤ 1 := Real.rpow_le_one hε.le (by linarith) (by positivity)
  have he : h ^ (p - q + 1) = ε :=
    Real.rpow_inv_natCast_pow hε.le (by omega)
  have hpn : h ^ (p + 1) = ε ^ sharpExponent p q := by
    dsimp [h, sharpExponent]
    rw [← Real.rpow_mul_natCast hε.le]
    congr 1
    ring
  let N : ℕ := ⌈1 / ε ^ sharpExponent p q⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hn : (N : ℝ) * h ^ (p + 1) ≤ 2 := by
    have hu := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ sharpExponent p q by positivity)).le
      (pow_nonneg hh.le (p + 1))
    have hcanc : (1 / ε ^ sharpExponent p q + 1) * h ^ (p + 1) =
        1 + h ^ (p + 1) := by rw [hpn]; field_simp
    rw [hcanc] at hu
    exact hu.trans (by linarith [pow_le_one₀ hh.le hh1 (n := p + 1)])
  have hdrop : (N : ℝ) * (2 * h ^ (p - q + 1)) * h ^ q ≤ 4 := by
    have hexp : h ^ (p - q + 1) * h ^ q = h ^ (p + 1) := by
      rw [← pow_add, show p - q + 1 + q = p + 1 by omega]
    nlinarith [hn]
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hc N hN (2 * h ^ (p - q + 1)) h
    (by positivity) hh (by nlinarith [pow_nonneg hh.le (p - q + 1)]) hdrop
    (by rw [he]; linarith) (by linarith)
  refine ⟨f, N, h, hf, all_derivatives_lipschitz hf hLip hb, ?_, ?_, hh, hh1,
    rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa using hb 0 (by omega) x
  · simpa [sparseJet] using hjet 0 (by omega) 0 (by omega)
  · intro k hk t
    exact model_sparse_minimum hq hqp hk hh.le (hjet k hk.le) t
  · intro k hk
    rw [gap_sparse hq (show 0 ≤ 2 * h ^ (p - q + 1) by positivity) (by norm_num)
      (hjet k hk.le) hqp, decrement_sparse hq (hjet k hk.le) hqp,
      ite_eq_left ⟨le_rfl, hk⟩, one_pow, mul_one, he]
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith)
  · intro j _ hj
    rw [gap_sparse hq (show 0 ≤ 2 * h ^ (p - q + 1) by positivity) (by norm_num)
      (hjet N le_rfl) (hj.trans hqp),
      decrement_sparse hq (hjet N le_rfl) (hj.trans hqp), ite_eq_right (by omega)]
  · intro hquality
    exact run_of_sparseJet le_rfl (by norm_num) le_rfl (by positivity)
      (by dsimp [parameters]; rw [he]; linarith) rfl hjet
      (fun k hk => model_sparse_strict hq hqp hk hh (hjet k hk.le))
      hquality (fun k hk => ratio_sparse hq hqp hk (by positivity) hh hjet)

/-- At a genuine global minimizer every first- and second-order Taylor gap vanishes.
This conclusion holds at every positive radius. -/
theorem gap_low_at_minimum {m : ℝ → ℝ} {h δ : ℝ} {p j : ℕ}
    (hf : ContDiff ℝ p m) (hδ : 0 < δ) (hj : 1 ≤ j) (hj2 : j ≤ 2) (hjp : j ≤ p)
    (hmin : ∀ t, m h ≤ m t) : gapOn (taylorDecrement m j h) (closedBall 0 δ) = 0 := by
  exact gapOn_taylorDecrement_eq_zero_of_isLocalMin (by omega : j = 1 ∨ j = 2)
    (hf.of_le (by exact_mod_cast hjp)) (Filter.Eventually.of_forall hmin) hδ

/-- For orders one and two, unit model radii require no additional premise. Every member
has an actual legal outer execution and an exact ceiling iteration lower bound. -/
theorem exists_low_family (p q : ℕ) (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p q hq hqp ε (sigma p q) hε (by linarith) (sigma_pos p q)
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ)
        (run : OuterExecution P f 0 (sigma p q) (fun _ => 1) N),
        ContDiff ℝ p f ∧ (∀ j ≤ p, LipschitzWith L (iteratedFDeriv ℝ j f)) ∧
        (∀ x, |f x| ≤ B) ∧ f 0 = 0 ∧ 0 < h ∧ h ≤ 1 ∧
        N = ⌈1 / ε ^ sharpExponent p q⌉₊ ∧
        (∀ k < N, ε / (q.factorial : ℝ) <
          gapOn (taylorDecrement f q ((k : ℝ) * h)) (closedBall 0 1)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j ((N : ℝ) * h)) (closedBall 0 1) = 0) ∧
        run.state = state (sigma p q) 1 h ∧ run.last = .stopTest (run.state N) ∧
        (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
        run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q := by
  obtain ⟨L, B, hc⟩ := exists_good_family p q hq hqp
  refine ⟨L, B, ?_⟩
  intro ε hε hεsmall
  obtain ⟨f, N, h, hf, hL, hb, hf0, hh, hh1, hN, hmin, hgap, hend, hrun⟩ :=
    hc ε hε hεsmall
  obtain ⟨run, hstate, hlast, hnot, hfun, hder⟩ := hrun (by
    intro k hk j hj hjq
    change gapOn (taylorDecrement (model f p ((k : ℝ) * h) (sigma p q)) j h)
      (closedBall 0 1) ≤ (1 / 2 : ℝ) * ε * 1 ^ j / (j.factorial : ℝ)
    rw [gap_low_at_minimum (contDiff_model f p ((k : ℝ) * h) (sigma p q))
      (by norm_num) hj (hjq.trans hq2) (hjq.trans hqp) (hmin k hk)]
    positivity)
  exact ⟨f, N, h, run, hf, hL, hb, hf0, hh, hh1, hN, hgap, hend,
    hstate, hlast, hnot, hfun, hder⟩

end Optimization.HigherOrderApproximateRegularizationSharpness
