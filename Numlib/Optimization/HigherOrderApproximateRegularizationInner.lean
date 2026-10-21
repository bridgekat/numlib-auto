import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Optimization.HigherOrderRegularizationModelBounds
import Numlib.Optimization.HigherOrderModelDecrease
import Numlib.Optimization.TaylorCriticalityLocalMinimum

/-!
# Existence and stopping certificates for regularized model steps

The regularized model attains its global minimum. Sharp model remainder bounds control
higher Taylor gaps there, while its first two gaps vanish at every radius. An actual
fraction-of-global-decrease step with zero decrease certifies that zero is a global minimum;
model nonincrease alone does not supply this certificate.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization
section TaylorJets
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every Taylor-model jet through its degree agrees with the original jet at the origin. -/
theorem RegularizedTaylorModel.iteratedFDeriv_taylorModel_zero {f : E → ℝ} {p j : ℕ}
    {x : E} (hf : ContDiffAt ℝ p f x) (hj : j ≤ p) :
    iteratedFDeriv ℝ j (taylorModel f p x) 0 = iteratedFDeriv ℝ j f x := by
  classical
  ext v
  rw [iteratedFDeriv_taylorModel_contraction hf]
  rw [Finset.sum_eq_single j]
  · simp only [le_refl, dite_eq_left, Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
      inv_one, one_smul]
    congr 1
    funext l
    simp only [l.isLt, dite_eq_left]
  · intro k _ hkj
    by_cases hjk : j ≤ k
    · rw [dite_eq_left hjk]
      have hjk' : j < k := by omega
      rw [(iteratedFDeriv ℝ k f x).map_coord_zero ⟨j, hjk'⟩ (by simp)]
      simp
    · rw [dite_eq_right hjk]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).elim

end TaylorJets

namespace HigherOrderApproximateRegularization
open TaylorCriticality

/-- An actual positive fraction of global decrease, together with zero decrease, certifies
that zero itself is globally minimizing. -/
theorem isMin_zero_of_fraction_eq {F : Type*} [Zero F]
    {m : F → ℝ} {s minimizer : F} {μ : ℝ}
    (hmin : ∀ t, m minimizer ≤ m t) (hμ : 0 < μ)
    (hfrac : μ * (m 0 - m minimizer) ≤ m 0 - m s) (heq : m s = m 0) :
    ∀ t, m 0 ≤ m t := by
  have hzero := hmin 0
  have he : m 0 = m minimizer := by nlinarith
  intro t
  rw [he]
  exact hmin t

section TraceFractions
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Outside the minimization phase, every transition preserves the actual fraction-of-global-
decrease certificate obtained at the last minimization. -/
theorem InnerTransition.fraction_of_ne_minimize {P : Parameters} {m : F → ℝ} {z : F}
    {a b : InnerState F} (h : InnerTransition P m z a b)
    (ha : a.phase ≠ .minimize → a.mu * (m 0 - m z) ≤ m 0 - m a.step)
    (hb : b.phase ≠ .minimize) : b.mu * (m 0 - m z) ≤ m 0 - m b.step := by
  cases h <;> simp_all

/-- Every finite inner prefix retains a positive accuracy fraction bounded by one. -/
theorem InnerExecution.mu_bounds {P : Parameters} {m : F → ℝ} {z : F} {N : ℕ}
    (h : InnerExecution P m z N) {k : ℕ} (hk : k ≤ N) :
    0 < (h.state k).mu ∧ (h.state k).mu ≤ 1 := by
  induction k with
  | zero => exact ⟨h.initial.1, h.initial.2.1⟩
  | succ k ih =>
    have hi := ih (by omega)
    exact ((h.transition k (by omega)).mu_bounds hi.1 hi.2).imp_right And.left

/-- Every inspected or returned inner state has its actual fraction-of-global-decrease
certificate; no certificate is required while a new minimization is pending. -/
theorem InnerExecution.fraction_of_ne_minimize {P : Parameters} {m : F → ℝ} {z : F} {N : ℕ}
    (h : InnerExecution P m z N) {k : ℕ} (hk : k ≤ N)
    (hphase : (h.state k).phase ≠ .minimize) :
    (h.state k).mu * (m 0 - m z) ≤ m 0 - m (h.state k).step := by
  induction k with
  | zero => exact (hphase h.initial.2.2.2).elim
  | succ k ih =>
    exact (h.transition k (by omega)).fraction_of_ne_minimize
      (fun hp => ih (by omega) hp) hphase

/-- A returned inner state with zero decrease certifies that the origin globally minimizes
its actual model. This follows from the trace, not merely an outer nonincrease condition. -/
theorem InnerExecution.isMin_zero_of_return_eq {P : Parameters} {m : F → ℝ} {z : F} {N : ℕ}
    (h : InnerExecution P m z N) (hreturn : (h.state N).phase = .returned)
    (heq : m (h.state N).step = m 0) : ∀ t, m 0 ≤ m t := by
  exact isMin_zero_of_fraction_eq h.is_minimizer (h.mu_bounds le_rfl).1
    (h.fraction_of_ne_minimize le_rfl (by rw [hreturn]; decide)) heq

end TraceFractions

section OuterTests
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A rejected trial reuses the actual failed test at the unchanged point and radii. -/
theorem OuterTransition.failedTest_of_next_test_false {P : Parameters} {f : F → ℝ}
    {a b : OuterState F} {fc dc : ℕ} (h : OuterTransition P f a (.next b) fc dc)
    (ha : a.test = false → Nonempty (FailedTest P f a.point a.radii)) (hb : b.test = false) :
    Nonempty (FailedTest P f b.point b.radii) := by
  cases h with
  | trial hfail hcache trial hstrict nextSigma hupdate =>
    split_ifs at hb ⊢ with hacc
    cases htest : a.test with
    | false => exact ha htest
    | true => exact hfail htest

/-- Whenever an outer state skips retesting after rejection, its actual failed witness
from the preceding test remains available. -/
theorem OuterExecution.failedTest_of_test_false {P : Parameters} {f : F → ℝ} {x : F}
    {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (h : OuterExecution P f x σ δ N)
    {k : ℕ} (hk : k ≤ N) (hfalse : (h.state k).test = false) :
    Nonempty (FailedTest P f (h.state k).point (h.state k).radii) := by
  induction k with
  | zero =>
    have he := congrArg OuterState.test h.initial.2.2
    rw [hfalse] at he
    cases he
  | succ k ih =>
    exact (h.transition k (by omega)).failedTest_of_next_test_false
      (fun hfalse => ih (by omega) hfalse) hfalse

/-- An equality-stopping outer pass has a failed test, either freshly computed or cached. -/
theorem OuterTransition.failedTest_of_stopEqual {P : Parameters} {f : F → ℝ}
    {a : OuterState F} {fc dc : ℕ} (h : OuterTransition P f a (.stopEqual a) fc dc)
    (ha : a.test = false → Nonempty (FailedTest P f a.point a.radii)) :
    Nonempty (FailedTest P f a.point a.radii) := by
  cases h with
  | equal hfail hcache trial heq =>
    cases htest : a.test with
    | false => exact ha htest
    | true => exact hfail htest

/-- Equality stopping retains a genuine failed outer test, including after cached rejections. -/
theorem OuterExecution.failedTest_of_stopEqual {P : Parameters} {f : F → ℝ} {x : F}
    {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ} (h : OuterExecution P f x σ δ N)
    (hstop : h.last = .stopEqual (h.state N)) :
    Nonempty (FailedTest P f (h.state N).point (h.state N).radii) := by
  have ht := h.final
  rw [hstop] at ht
  exact ht.failedTest_of_stopEqual (fun hfalse => h.failedTest_of_test_false le_rfl hfalse)

end OuterTests

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The regularizer has zero jets through the Taylor degree at zero, so all corresponding
Taylor decrements of the actual model agree with those of the original objective. -/
theorem model_taylorDecrement_zero {f : E → ℝ} {p j : ℕ} {x d : E} {σ : ℝ}
    (hf : ContDiffAt ℝ p f x) (hj : j ≤ p) :
    taylorDecrement (model f p x σ) j 0 d = taylorDecrement f j x d := by
  have hjet : ∀ i, i ≤ p → iteratedFDeriv ℝ i (model f p x σ) 0 =
      iteratedFDeriv ℝ i f x := by
    intro i hi
    rw [HigherOrderRegularization.iteratedFDeriv_model_of_le hi,
      RegularizedTaylorModel.iteratedFDeriv_taylorModel_zero hf hi]
    have hz : iteratedFDeriv ℝ i (fun z : E => ‖z‖ ^ (p + 1)) 0 = 0 := by
      simpa only [Real.rpow_natCast] using iteratedFDeriv_norm_rpow_zero_of_lt (E := E)
        (j := i) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega : i < p + 1))
    rw [hz, smul_zero, add_zero]
  unfold taylorDecrement RegularizedTaylorModel.taylorModel
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    rw [hjet i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj)]

/-- At a global model minimum in the unit ball, a sufficiently small radius forces every
Taylor gap below the positive target: a larger gap would give positive actual decrease. -/
theorem gapOn_model_lt_of_isMin {f : E → ℝ} {p j : ℕ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f p L) (hp : 1 ≤ p) {x s : E} {σ α δ : ℝ}
    (hσ : 0 ≤ σ) (hs : ‖s‖ ≤ 1) (hmin : ∀ t, model f p x σ s ≤ model f p x σ t)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 1 ≤ j) (hjp : j ≤ p)
    (hsmall : 4 * (3 * HigherOrderDerivativeFamily.maxConstant p L + σ) * δ ≤ α) :
    gapOn (taylorDecrement (model f p x σ) j s) (closedBall 0 δ) <
      α * δ ^ j / (j ! : ℝ) := by
  have hM : 0 ≤ 3 * HigherOrderDerivativeFamily.maxConstant p L + σ := by
    linarith [hf.maxConstant_nonneg]
  by_contra h
  have htarget : α * δ ^ j / (j ! : ℝ) ≤
      gapOn (taylorDecrement (model f p x σ) j s) (closedBall 0 δ) := le_of_not_gt h
  obtain ⟨d, hd, he⟩ := exists_eq_gapOn (isCompact_closedBall (0 : E) δ)
    ⟨0, by simpa using hδ.le⟩ (continuous_taylorDecrement (model f p x σ) j s).continuousOn
  have hm := HigherOrderRegularization.diagonalLipschitz_model (x := x) hf.smooth.contDiffAt hσ
  have hb : ∀ i ∈ Finset.Icc (j + 1) p,
      ‖iteratedFDeriv ℝ i (model f p x σ) s‖ ≤
        3 * HigherOrderDerivativeFamily.maxConstant p L + σ := by
    intro i hi
    exact hf.norm_iteratedFDeriv_model_le (by have := (Finset.mem_Icc.mp hi).1; omega)
      (Finset.mem_Icc.mp hi).2 x s hσ hs
  have hdec := hm.half_decrease_of_small_radius hp hjp hM
    (by linarith [hf.maxConstant_nonneg]) ⟨hδ.le, hδ1⟩ s d
    (by simpa using hd) hb hsmall (by rwa [he])
  have hpos : 0 < α * δ ^ j / (2 * (j ! : ℝ)) := by positivity
  have hh := hmin (s + d)
  linarith

/-- An actual regularized Taylor model has an admissible model step, with unit first/second
radii and quantitative higher-order radii when the selected global minimizer is in the unit ball. -/
theorem exists_modelStep (P : Parameters) {f : E → ℝ} {L : ℕ → ℝ}
    (hf : HigherOrderDerivativeFamily f P.p L)
    (hL : 1 ≤ HigherOrderDerivativeFamily.maxConstant P.p L) (x : E) {σ : ℝ}
    (hσ : 0 < σ) (inherited : ℕ → ℝ) :
    ∃ trial : ModelStep P f x σ inherited,
      (∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → trial.radii j = 1) ∧
      (‖trial.step‖ ≤ 1 → ∀ j, 3 ≤ j → j ≤ P.q →
        P.fraction * P.theta / (8 * (3 * HigherOrderDerivativeFamily.maxConstant P.p L + σ)) *
          P.epsilon j ≤ trial.radii j) := by
  classical
  let M := 3 * HigherOrderDerivativeFamily.maxConstant P.p L + σ
  have hM : 0 < M := by dsimp [M]; linarith
  have hp : 1 ≤ P.p := P.order_pos.trans P.order_le
  obtain ⟨s, hmin⟩ := exists_model_minimizer f P.p x hσ
  have hm : ContDiff ℝ P.p (model f P.p x σ) := contDiff_model f P.p x σ
  have hlocal : IsLocalMin (model f P.p x σ) s := Filter.Eventually.of_forall hmin
  have hε : ∀ j, 1 ≤ j → j ≤ P.q → 0 < P.fraction * P.theta * P.epsilon j := by
    intro j hj hjq
    exact mul_pos (mul_pos P.fraction_pos P.theta_pos) (P.epsilon_pos j hj hjq)
  have hft : P.fraction * P.theta ≤ 1 :=
    (mul_le_mul_of_nonneg_right P.fraction_le_one P.theta_pos.le).trans
      (by simpa using P.theta_lt_one.le)
  have hε1 : ∀ j, 1 ≤ j → j ≤ P.q → P.fraction * P.theta * P.epsilon j ≤ 1 := by
    intro j hj hjq
    exact (mul_le_mul_of_nonneg_right hft (P.epsilon_pos j hj hjq).le).trans
      (by simpa using (P.epsilon_lt_one j hj hjq).le)
  have hex : ∃ δ : ℕ → ℝ, ValidRadii P δ ∧
      (∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → δ j = 1) ∧
      (‖s‖ ≤ 1 → ∀ j, 3 ≤ j → j ≤ P.q →
        P.fraction * P.theta / (8 * M) * P.epsilon j ≤ δ j) ∧
      ∀ j, 1 ≤ j → j ≤ P.q →
        gapOn (taylorDecrement (model f P.p x σ) j s) (closedBall 0 (δ j)) ≤
          P.fraction * P.theta * P.epsilon j * δ j ^ j / (j ! : ℝ) := by
    by_cases hs : ‖s‖ ≤ 1
    · let δ : ℕ → ℝ := fun j => if j ≤ 2 then 1 else
        P.fraction * P.theta * P.epsilon j / (8 * M)
      have hd : ValidRadii P δ := by
        intro j hj hjq
        dsimp [δ]
        split_ifs with hlow
        · exact ⟨by norm_num, le_rfl⟩
        · refine ⟨div_pos (hε j hj hjq) (by positivity), ?_⟩
          apply (div_le_iff₀ (by positivity : 0 < 8 * M)).mpr
          exact (hε1 j hj hjq).trans (by dsimp [M]; linarith)
      refine ⟨δ, hd, fun j _ _ hj => by simp [δ, hj], ?_, ?_⟩
      · intro _ j hj _
        dsimp [δ]
        rw [ite_eq_right (by omega : ¬j ≤ 2)]
        exact le_of_eq (by ring)
      · intro j hj hjq
        by_cases hlow : j ≤ 2
        · rw [gapOn_taylorDecrement_eq_zero_of_isLocalMin
            (by omega : j = 1 ∨ j = 2)
            (hm.of_le (by exact_mod_cast hjq.trans P.order_le)) hlocal (hd j hj hjq).1]
          exact div_nonneg (mul_nonneg (hε j hj hjq).le (pow_nonneg (hd j hj hjq).1.le j))
            (by positivity)
        · apply (gapOn_model_lt_of_isMin hf hp hσ.le hs hmin (hε j hj hjq)
            (hd j hj hjq).1 (hd j hj hjq).2 hj (hjq.trans P.order_le) ?_).le
          change 4 * M * δ j ≤ P.fraction * P.theta * P.epsilon j
          dsimp [δ]
          rw [ite_eq_right hlow]
          calc
            _ = (P.fraction * P.theta * P.epsilon j) / 2 := by field_simp; ring
            _ ≤ _ := by linarith [hε j hj hjq]
    · obtain ⟨δ, hd, hl, hg⟩ := exists_radii_taylorDecrement_le_of_isLocalMin
        P.order_le hm hlocal (fun j => P.fraction * P.theta * P.epsilon j) hε
      exact ⟨δ, hd, hl, fun hn => (hs hn).elim, hg⟩
  obtain ⟨δ, hd, hlow, hlower, hg⟩ := hex
  have hexw : ∀ j : ℕ, ∃ d : E, 1 ≤ j → j ≤ P.q →
      GapWitness (model f P.p x σ) j s (δ j) P.fraction d ∧
      taylorDecrement (model f P.p x σ) j s d ≤
        P.fraction * P.theta * P.epsilon j * δ j ^ j / (j ! : ℝ) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ P.q
    · obtain ⟨d, hdm, he⟩ := exists_eq_gapOn (isCompact_closedBall (0 : E) (δ j))
        ⟨0, by simpa using (hd j hj.1 hj.2).1.le⟩
        (continuous_taylorDecrement (model f P.p x σ) j s).continuousOn
      have hnonneg : 0 ≤ gapOn (taylorDecrement (model f P.p x σ) j s) (closedBall 0 (δ j)) :=
        gapOn_nonneg (isCompact_closedBall 0 (δ j))
          (continuous_taylorDecrement (model f P.p x σ) j s).continuousOn
          (by simpa using (hd j hj.1 hj.2).1.le) (taylorDecrement_zero _ _ _)
      refine ⟨d, fun _ _ => ⟨⟨by simpa using hdm, ?_⟩, ?_⟩⟩
      · rw [he]
        exact mul_le_of_le_one_left hnonneg P.fraction_le_one
      · rw [he]
        exact hg j hj.1 hj.2
    · exact ⟨0, fun h1 hq => (hj ⟨h1, hq⟩).elim⟩
  choose d hdirection using hexw
  let trial : ModelStep P f x σ inherited := {
    step := s
    radii := δ
    radii_valid := hd
    nonincrease := hmin 0
    direction := d
    quality := Or.inr hdirection }
  exact ⟨trial, hlow, hlower⟩

/-- A globally minimizing model origin gives a true approximate objective minimizer for
some positive order-dependent radii. The objective constant is retained throughout. -/
theorem exists_approxMinimizer_of_model_isMin_zero (P : Parameters) {f : E → ℝ} {x : E}
    {σ : ℝ} (hf : ContDiffAt ℝ P.p f x)
    (hmin : ∀ t, model f P.p x σ 0 ≤ model f P.p x σ t) :
    ∃ δ : ℕ → ℝ, ValidRadii P δ ∧
      IsApproxMinimizer f x P.q P.epsilon δ (fun j => closedBall 0 (δ j)) ∧
      (∀ j, 1 ≤ j → j ≤ P.q → j ≤ 2 → δ j = 1) := by
  have hm : ContDiff ℝ P.p (model f P.p x σ) := contDiff_model f P.p x σ
  have hlocal : IsLocalMin (model f P.p x σ) 0 := Filter.Eventually.of_forall hmin
  obtain ⟨δ, hd, hl, hg⟩ := exists_radii_taylorDecrement_le_of_isLocalMin
    P.order_le hm hlocal P.epsilon P.epsilon_pos
  refine ⟨δ, hd, ?_, hl⟩
  exact {
    epsilon_pos := P.epsilon_pos
    radius_pos := fun j hj hjq => (hd j hj hjq).1
    compact := fun _ _ _ => isCompact_closedBall _ _
    zero_mem := fun j hj hjq => by simpa using (hd j hj hjq).1.le
    norm_le := fun _ _ _ _ hδ => by simpa using hδ
    gap_le := fun j hj hjq => by
      have he : taylorDecrement (model f P.p x σ) j 0 = taylorDecrement f j x :=
        funext fun d => model_taylorDecrement_zero hf (hjq.trans P.order_le)
      rw [← he]
      exact hg j hj hjq }

/-- If the model origin is globally minimizing and only the first two orders are requested,
no actual fractional witness can fail the positive outer tolerance test. -/
theorem not_failedTest_of_model_isMin_zero (P : Parameters) {f : E → ℝ} {x : E}
    {σ : ℝ} {δ : ℕ → ℝ} (hf : ContDiffAt ℝ P.p f x) (hq : P.q ≤ 2)
    (hd : ValidRadii P δ) (hmin : ∀ t, model f P.p x σ 0 ≤ model f P.p x σ t) :
    ¬Nonempty (FailedTest P f x δ) := by
  rintro ⟨test⟩
  have hjp : test.order ≤ P.p := test.order_le.trans P.order_le
  have hjlow : test.order = 1 ∨ test.order = 2 := by
    have h1 := test.order_pos
    have h2 := test.order_le.trans hq
    omega
  have hlocal : IsLocalMin (model f P.p x σ) 0 := Filter.Eventually.of_forall hmin
  have hgap := gapOn_taylorDecrement_eq_zero_of_isLocalMin hjlow
    ((contDiff_model f P.p x σ).of_le (by exact_mod_cast hjp)) hlocal
    (hd test.order test.order_pos test.order_le).1
  have he : taylorDecrement (model f P.p x σ) test.order 0 =
      taylorDecrement f test.order x := funext fun d => model_taylorDecrement_zero hf hjp
  rw [he] at hgap
  have hdirection := le_gapOn (isCompact_closedBall (0 : E) (δ test.order))
    (continuous_taylorDecrement f test.order x).continuousOn
    (show test.direction test.order ∈ closedBall 0 (δ test.order) by
      simpa using (test.witness test.order test.order_pos le_rfl).feasible)
  rw [hgap] at hdirection
  have hε := P.epsilon_pos test.order test.order_pos test.order_le
  have hδ := (hd test.order test.order_pos test.order_le).1
  have hpositive : 0 < P.fraction * P.epsilon test.order * δ test.order ^ test.order /
      (test.order ! : ℝ) :=
    div_pos (mul_pos (mul_pos P.fraction_pos hε) (pow_pos hδ _)) (by positivity)
  linarith [test.fails]

end HigherOrderApproximateRegularization
end Optimization
