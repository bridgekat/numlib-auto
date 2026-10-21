import Numlib.Optimization.HigherOrderRegularization
import Numlib.Optimization.InexactTaylorModels
import Numlib.Analysis.Normed.Multilinear.Diagonal
import Numlib.Optimization.TaylorCriticalityCriteria
import Numlib.Optimization.ParameterUpdatesFinite
import Numlib.Optimization.EvaluationComplexity
import Mathlib.Tactic

/-!
# Higher-order trust-region trials

Actual Taylor-gap witnesses determine the first failing order. Trial legality is required only
until the first termination test. The acceptance ratio uses that selected order, rather than a
fixed highest-order model. Derivatives are cached after rejections.
-/

noncomputable section
open scoped Nat
namespace Optimization.HigherOrderTrustRegion
open TaylorCriticality RegularizedTaylorModel HigherOrderRegularization ParameterUpdates
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Parameters for fraction-gap trust-region steps, allowing unit maximal expansion. -/
structure Parameters where
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  fraction : ℝ
  theta : ℝ
  radiusMax : ℝ
  eta1_pos : 0 < eta1
  eta_le : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma_le : gamma1 ≤ gamma2
  gamma2_lt_one : gamma2 < 1
  one_le_gamma3 : 1 ≤ gamma3
  fraction_pos : 0 < fraction
  fraction_le_one : fraction ≤ 1
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1

/-- Data recorded by a trust-region implementation, without any convergence assumptions. -/
structure Trace (E : Type*) where
  point : ℕ → E
  step : ℕ → E
  radius : ℕ → ℝ
  witness : ℕ → ℕ → E
  order : ℕ → ℕ

/-- The smaller radius used for criticality testing. -/
def testRadius (p : Parameters) (t : Trace E) (k : ℕ) : ℝ := min (t.radius k) p.theta

/-- The actual termination test on every requested Taylor witness. -/
def Stops (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ) (f : E → ℝ)
    (t : Trace E) (k : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ q → taylorDecrement f j (t.point k) (t.witness k j) ≤
    p.fraction * epsilon j * testRadius p t k ^ j / (j ! : ℝ)

/-- Actual reduction divided by the prediction at the selected failing order. -/
def ratio (f : E → ℝ) (t : Trace E) (k : ℕ) : ℝ :=
  (f (t.point k) - f (t.point k + t.step k)) /
    taylorDecrement f (t.order k) (t.point k) (t.step k)

/-- The scaled decrement from the selected failing witness. -/
def scaledGap (p : Parameters) (f : E → ℝ) (t : Trace E) (k : ℕ) : ℝ :=
  ((t.order k)! : ℝ) * taylorDecrement f (t.order k) (t.point k)
    (t.witness k (t.order k)) / testRadius p t k ^ t.order k

/-- A legal finite prefix. Every step precedes the actual all-orders stopping test; no
conditions are imposed on trial data beyond the endpoint. Endpoint witnesses allow testing
termination there. The first failing order implements the increasing-order scan. -/
structure LegalPrefix (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ) (f : E → ℝ)
    (t : Trace E) (N : ℕ) : Prop where
  initial_pos : 0 < t.radius 0
  initial_cap : t.radius 0 ≤ p.radiusMax
  witness_feasible : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q →
    ‖t.witness k j‖ ≤ testRadius p t k
  witness_fraction : ∀ k ≤ N, ∀ j, 1 ≤ j → j ≤ q →
    p.fraction * gapOn (taylorDecrement f j (t.point k))
      (closedBall 0 (testRadius p t k)) ≤ taylorDecrement f j (t.point k) (t.witness k j)
  nonterminal : ∀ k < N, ¬Stops p q epsilon f t k
  order_pos : ∀ k < N, 1 ≤ t.order k
  order_le : ∀ k < N, t.order k ≤ q
  first_failure : ∀ k < N, ∀ j, 1 ≤ j → j < t.order k →
    taylorDecrement f j (t.point k) (t.witness k j) ≤
      p.fraction * epsilon j * testRadius p t k ^ j / (j ! : ℝ)
  failure : ∀ k < N, p.fraction * epsilon (t.order k) *
    testRadius p t k ^ t.order k / ((t.order k)! : ℝ) <
      taylorDecrement f (t.order k) (t.point k) (t.witness k (t.order k))
  step_feasible : ∀ k < N, ‖t.step k‖ ≤ t.radius k
  prediction : ∀ k < N, taylorDecrement f (t.order k) (t.point k)
    (t.witness k (t.order k)) ≤ taylorDecrement f (t.order k) (t.point k) (t.step k)
  iterate : ∀ k < N, t.point (k + 1) =
    if p.eta1 ≤ ratio f t k then t.point k + t.step k else t.point k
  update : ∀ k < N, if p.eta2 ≤ ratio f t k
    then t.radius (k + 1) ∈ Icc (t.radius k) (min p.radiusMax (p.gamma3 * t.radius k))
    else if p.eta1 ≤ ratio f t k
    then t.radius (k + 1) ∈ Icc (p.gamma2 * t.radius k) (t.radius k)
    else t.radius (k + 1) ∈ Icc (p.gamma1 * t.radius k) (p.gamma2 * t.radius k)

variable {p : Parameters} {q N : ℕ} {epsilon : ℕ → ℝ} {f : E → ℝ} {t : Trace E}

/-- Every permitted update retains the smallest contraction fraction. -/
theorem LegalPrefix.radius_update_lower (h : LegalPrefix p q epsilon f t N)
    {k : ℕ} (hk : k < N) (hr : 0 ≤ t.radius k) :
    p.gamma1 * t.radius k ≤ t.radius (k + 1) := by
  have hu := h.update k hk
  split_ifs at hu
  · exact (mul_le_of_le_one_left hr (p.gamma_le.trans p.gamma2_lt_one.le)).trans hu.1
  · exact (mul_le_mul_of_nonneg_right p.gamma_le hr).trans hu.1
  · exact hu.1

/-- Initialization and interval updates preserve strict positivity through the endpoint. -/
theorem LegalPrefix.radius_pos (h : LegalPrefix p q epsilon f t N)
    {k : ℕ} (hk : k ≤ N) : 0 < t.radius k := by
  induction k with
  | zero => exact h.initial_pos
  | succ k ih =>
    have hp := ih (by omega)
    exact (mul_pos p.gamma1_pos hp).trans_le (h.radius_update_lower (by omega) hp.le)

/-- The actual criticality-testing radius is positive and at most one. -/
theorem LegalPrefix.testRadius_bounds (h : LegalPrefix p q epsilon f t N)
    {k : ℕ} (hk : k ≤ N) : 0 < testRadius p t k ∧ testRadius p t k ≤ 1 :=
  ⟨lt_min (h.radius_pos hk) p.theta_pos, (min_le_right _ _).trans p.theta_le_one⟩

/-- The selected prediction is strictly positive before termination. -/
theorem LegalPrefix.predicted_pos (h : LegalPrefix p q epsilon f t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j) {k : ℕ} (hk : k < N) :
    0 < taylorDecrement f (t.order k) (t.point k) (t.step k) := by
  have hp : 0 < p.fraction * epsilon (t.order k) *
      testRadius p t k ^ t.order k / ((t.order k)! : ℝ) :=
    div_pos (mul_pos (mul_pos p.fraction_pos (he _ (h.order_pos k hk) (h.order_le k hk)))
      (pow_pos (h.testRadius_bounds (k := k) (by omega)).1 _)) (by positivity)
  exact (hp.trans (h.failure k hk)).trans_le (h.prediction k hk)

/-- Failure of the selected threshold bounds its scaled criticality gap below. -/
theorem LegalPrefix.scaledGap_lower (h : LegalPrefix p q epsilon f t N)
    {emin : ℝ} (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j)
    {k : ℕ} (hk : k < N) : p.fraction * emin < scaledGap p f t k := by
  have hd := h.failure k hk
  have hr := pow_pos (h.testRadius_bounds (k := k) (by omega)).1 (t.order k)
  have hj : (0 : ℝ) < ((t.order k)! : ℝ) := by positivity
  have he' := mul_le_mul_of_nonneg_left (he _ (h.order_pos k hk) (h.order_le k hk))
    p.fraction_pos.le
  unfold scaledGap
  apply lt_of_le_of_lt he'
  apply (lt_div_iff₀ hr).mpr
  have hh := (div_lt_iff₀ hj).mp hd
  nlinarith

/-- The actual selected-order prediction dominates the scaled witness decrement. -/
theorem LegalPrefix.predicted_ge_scaledGap (h : LegalPrefix p q epsilon f t N)
    {k : ℕ} (hk : k < N) :
    scaledGap p f t k * testRadius p t k ^ t.order k / ((t.order k)! : ℝ) ≤
      taylorDecrement f (t.order k) (t.point k) (t.step k) := by
  have hr := (pow_pos (h.testRadius_bounds (k := k) (by omega)).1 (t.order k)).ne'
  have hj : ((t.order k)! : ℝ) ≠ 0 := by positivity
  simpa only [scaledGap, div_mul_cancel₀ _ hr, mul_div_cancel_left₀ _ hj] using h.prediction k hk

/-- Acceptance realizes its prescribed fraction of the actual selected Taylor decrement. -/
theorem LegalPrefix.accepted_decrease (h : LegalPrefix p q epsilon f t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j) {k : ℕ} (hk : k < N)
    (ha : p.eta1 ≤ ratio f t k) :
    p.eta1 * taylorDecrement f (t.order k) (t.point k) (t.step k) ≤
      f (t.point k) - f (t.point (k + 1)) := by
  rw [h.iterate k hk, ite_eq_left ha]
  exact (le_div_iff₀ (h.predicted_pos he hk)).mp ha

/-- Rejected points stay fixed and accepted points decrease the objective. -/
theorem LegalPrefix.objective_nonincrease (h : LegalPrefix p q epsilon f t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j) {k : ℕ} (hk : k < N) :
    f (t.point (k + 1)) ≤ f (t.point k) := by
  by_cases ha : p.eta1 ≤ ratio f t k
  · have hd := h.accepted_decrease he hk ha
    have hp := mul_pos p.eta1_pos (h.predicted_pos he hk)
    linarith
  · rw [h.iterate k hk, ite_eq_right ha]

/-- At the actual all-orders stopping test the fractional gap witnesses certify all true gaps. -/
theorem LegalPrefix.gaps_at_stop (h : LegalPrefix p q epsilon f t N)
    (hs : Stops p q epsilon f t N) :
    ∀ j, 1 ≤ j → j ≤ q → gapOn (taylorDecrement f j (t.point N))
      (closedBall 0 (testRadius p t N)) ≤ epsilon j * testRadius p t N ^ j / (j ! : ℝ) := by
  intro j hj hjq
  have hw := h.witness_fraction N le_rfl j hj hjq
  have hh := hs j hj hjq
  have heq : p.fraction * epsilon j * testRadius p t N ^ j / (j ! : ℝ) =
      p.fraction * (epsilon j * testRadius p t N ^ j / (j ! : ℝ)) := by ring
  rw [heq] at hh
  nlinarith [hw.trans hh, p.fraction_pos]

/-- A sufficiently small radius makes the selected-order trial very successful. The proof
uses the sharp factorial remainder of the actual derivative of the selected order. -/
theorem LegalPrefix.ratio_ge_of_radius (h : LegalPrefix p q epsilon f t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j) {L : ℝ}
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k < N) (hr : t.radius k ≤ p.theta)
    (hs : L * t.radius k ≤ (1 - p.eta2) * scaledGap p f t k) :
    p.eta2 ≤ ratio f t k := by
  have hd := h.predicted_pos he hk
  have hp := h.order_pos k hk
  have hj := hf _ hp (h.order_le k hk)
  have hrad := h.radius_pos (k := k) (by omega)
  have hfac : (0 : ℝ) < ((t.order k)! : ℝ) := by positivity
  have hfacmono : ((t.order k)! : ℝ) ≤ ((t.order k + 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hrem := (abs_le.mp (hj.value_remainder hp (t.point k) (t.step k))).2
  have hnorm : ‖t.step k‖ ^ (t.order k + 1) ≤ t.radius k ^ (t.order k + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (h.step_feasible k hk) _
  have hR : L / ((t.order k + 1)! : ℝ) * ‖t.step k‖ ^ (t.order k + 1) ≤
      L * t.radius k * (t.radius k ^ t.order k / ((t.order k)! : ℝ)) := by
    calc
      _ ≤ L / ((t.order k + 1)! : ℝ) * t.radius k ^ (t.order k + 1) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg hj.nonneg (by positivity))
      _ ≤ L / ((t.order k)! : ℝ) * t.radius k ^ (t.order k + 1) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hj.nonneg hfac hfacmono)
          (pow_nonneg hrad.le _)
      _ = _ := by rw [pow_succ]; ring
  have hpredict := h.predicted_ge_scaledGap hk
  simp only [testRadius, min_eq_left hr] at hpredict
  have hb := mul_le_mul_of_nonneg_right hs
    (div_nonneg (pow_nonneg hrad.le (t.order k)) hfac.le)
  have hlast := mul_le_mul_of_nonneg_left hpredict (sub_nonneg.mpr p.eta2_lt_one.le)
  have hh : L / ((t.order k + 1)! : ℝ) * ‖t.step k‖ ^ (t.order k + 1) ≤
      (1 - p.eta2) * taylorDecrement f (t.order k) (t.point k) (t.step k) := by
    calc
      _ ≤ L * t.radius k * (t.radius k ^ t.order k / ((t.order k)! : ℝ)) := hR
      _ ≤ (1 - p.eta2) * scaledGap p f t k *
          (t.radius k ^ t.order k / ((t.order k)! : ℝ)) := hb
      _ = (1 - p.eta2) * (scaledGap p f t k *
          t.radius k ^ t.order k / ((t.order k)! : ℝ)) := by ring
      _ ≤ _ := hlast
  unfold ratio
  rw [le_div_iff₀ hd]
  rw [taylorDecrement_eq]
  rw [taylorDecrement_eq] at hh
  linarith

/-- A very successful finite-prefix trial does not reduce the radius. -/
theorem LegalPrefix.radius_nondecrease (h : LegalPrefix p q epsilon f t N)
    {k : ℕ} (hk : k < N) (ha : p.eta2 ≤ ratio f t k) :
    t.radius k ≤ t.radius (k + 1) := by
  have hu := h.update k hk
  rw [ite_eq_left ha] at hu
  exact hu.1

/-- Lower radius bound from any common success threshold, using only executed updates. -/
theorem LegalPrefix.radius_lower_of_threshold (h : LegalPrefix p q epsilon f t N)
    {T : ℝ} (hsmall : ∀ k < N, t.radius k ≤ T → p.eta2 ≤ ratio f t k)
    {k : ℕ} (hk : k ≤ N) : min (t.radius 0) (p.gamma1 * T) ≤ t.radius k := by
  induction k with
  | zero => exact min_le_left _ _
  | succ k ih =>
    have hkN : k < N := by omega
    by_cases hr : t.radius k ≤ T
    · exact (ih (by omega)).trans (h.radius_nondecrease hkN (hsmall k hkN hr))
    · exact ((min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left (le_of_not_ge hr) p.gamma1_pos.le)).trans
          (h.radius_update_lower hkN (h.radius_pos (by omega)).le)

/-- A tolerance-independent coefficient for the radius lower bound. -/
def radiusCoefficient (p : Parameters) (initial L : ℝ) : ℝ :=
  min initial (min p.gamma1 (p.gamma1 * (1 - p.eta2) / L))

/-- The radius coefficient is positive when the Lipschitz bound and initial radius are. -/
theorem radiusCoefficient_pos {initial L : ℝ} (hi : 0 < initial) (hL : 0 < L) :
    0 < radiusCoefficient p initial L := by
  unfold radiusCoefficient
  exact lt_min hi (lt_min p.gamma1_pos
    (div_pos (mul_pos p.gamma1_pos (sub_pos.mpr p.eta2_lt_one)) hL))

/-- Before the first all-orders stop, every radius exceeds a constant times the smallest
tolerance. This coefficient is independent of the tolerance and the testing cap. -/
theorem LegalPrefix.radius_lower (h : LegalPrefix p q epsilon f t N)
    {emin L : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j) (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k ≤ N) :
    radiusCoefficient p (t.radius 0) L * p.fraction * emin ≤ t.radius k := by
  let T := min p.theta ((1 - p.eta2) * (p.fraction * emin) / L)
  have hs : ∀ i < N, t.radius i ≤ T → p.eta2 ≤ ratio f t i := by
    intro i hi hr
    apply h.ratio_ge_of_radius (fun j hj hjq => hemin.trans_le (he j hj hjq)) hf hi
      (hr.trans (min_le_left _ _))
    have hb := (le_div_iff₀ hL).mp (hr.trans (min_le_right _ _))
    have hg := h.scaledGap_lower he hi
    have hm := mul_le_mul_of_nonneg_left hg.le (sub_nonneg.mpr p.eta2_lt_one.le)
    nlinarith
  have hb := h.radius_lower_of_threshold hs hk
  apply le_trans _ hb
  apply le_min
  · have hc : radiusCoefficient p (t.radius 0) L ≤ t.radius 0 := min_le_left _ _
    have heps : p.fraction * emin ≤ 1 := by nlinarith [p.fraction_le_one, p.fraction_pos]
    have hm := mul_le_mul_of_nonneg_left heps (radiusCoefficient_pos (p := p) h.initial_pos hL).le
    nlinarith
  · dsimp [T]
    rw [mul_min_of_nonneg _ _ p.gamma1_pos.le]
    apply le_min
    · have hc : radiusCoefficient p (t.radius 0) L ≤ p.gamma1 :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hfe : p.fraction * emin ≤ p.theta := by nlinarith [p.fraction_le_one]
      have ha := mul_le_mul_of_nonneg_right hc (mul_nonneg p.fraction_pos.le hemin.le)
      have hb := mul_le_mul_of_nonneg_left hfe p.gamma1_pos.le
      nlinarith
    · have hc : radiusCoefficient p (t.radius 0) L ≤ p.gamma1 * (1 - p.eta2) / L :=
        (min_le_right _ _).trans (min_le_right _ _)
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg p.fraction_pos.le hemin.le)
      convert hh using 1 <;> ring

/-- The uniform scalar prediction obtained from a radius and scaled-gap lower bound. -/
theorem LegalPrefix.predicted_lower_of_radius (h : LegalPrefix p q epsilon f t N)
    {a : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1)
    {k : ℕ} (hk : k < N) (hr : a ≤ testRadius p t k)
    (hg : a ≤ scaledGap p f t k) :
    a ^ (q + 1) / (q ! : ℝ) ≤ taylorDecrement f (t.order k) (t.point k) (t.step k) := by
  have hp : a ^ q ≤ testRadius p t k ^ t.order k :=
    (pow_le_pow_of_le_one ha haone (h.order_le k hk)).trans
      (pow_le_pow_left₀ ha hr _)
  have hmul := mul_le_mul hg hp (pow_nonneg ha _) (ha.trans hg)
  have hfac : ((t.order k)! : ℝ) ≤ (q ! : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (h.order_le k hk))
  calc
    _ = a * a ^ q / (q ! : ℝ) := by rw [pow_succ]; ring
    _ ≤ scaledGap p f t k * testRadius p t k ^ t.order k / (q ! : ℝ) :=
      div_le_div_of_nonneg_right hmul (by positivity)
    _ ≤ scaledGap p f t k * testRadius p t k ^ t.order k / ((t.order k)! : ℝ) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (ha.trans hg) (pow_nonneg (h.testRadius_bounds (by omega)).1.le _))
        (by positivity) hfac
    _ ≤ _ := h.predicted_ge_scaledGap hk

/-- Uniform model decrease of order `emin^(q+1)`, valid for every positive requested order. -/
theorem LegalPrefix.predicted_lower (h : LegalPrefix p q epsilon f t N)
    {emin L : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j) (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    {k : ℕ} (hk : k < N) :
    (radiusCoefficient p (t.radius 0) L * p.fraction * emin) ^ (q + 1) / (q ! : ℝ) ≤
      taylorDecrement f (t.order k) (t.point k) (t.step k) := by
  let c := radiusCoefficient p (t.radius 0) L
  have hc : 0 < c := radiusCoefficient_pos h.initial_pos hL
  have hcone : c ≤ 1 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans (p.gamma_le.trans p.gamma2_lt_one.le)
  have hfe : p.fraction * emin ≤ emin := by nlinarith [p.fraction_le_one]
  have hce : c * p.fraction * emin ≤ emin := by nlinarith [p.fraction_pos]
  apply h.predicted_lower_of_radius
    (mul_nonneg (mul_nonneg hc.le p.fraction_pos.le) hemin.le) (hce.trans heone) hk
  · exact le_min (h.radius_lower hemin heone hetheta he hL hf (by omega)) (hce.trans hetheta)
  · have hg := (h.scaledGap_lower he hk).le
    have hh : c * p.fraction * emin ≤ p.fraction * emin := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hcone (mul_nonneg p.fraction_pos.le hemin.le)
    exact hh.trans hg

/-- Successful trials consume the fixed objective-decrease budget. -/
theorem LegalPrefix.success_count_le (h : LegalPrefix p q epsilon f t N)
    {emin L low : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j) (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L) (hlow : low ≤ f (t.point N)) :
    (successCount (fun k => p.eta1 ≤ ratio f t k) N : ℝ) ≤
      (f (t.point 0) - low) /
        (p.eta1 * ((radiusCoefficient p (t.radius 0) L * p.fraction * emin) ^ (q + 1) /
          (q ! : ℝ))) := by
  classical
  have hc := radiusCoefficient_pos (p := p) h.initial_pos hL
  have hfrac := p.fraction_pos
  have heta := p.eta1_pos
  have hdec : 0 < p.eta1 * ((radiusCoefficient p (t.radius 0) L * p.fraction * emin) ^
      (q + 1) / (q ! : ℝ)) := by positivity
  apply (le_div_iff₀ hdec).mpr
  unfold successCount
  apply EvaluationComplexity.card_mul_le_gap (u := fun k => f (t.point k))
    (Finset.filter_subset _ _) hlow
    (fun k hk => h.objective_nonincrease (fun j hj hjq => hemin.trans_le (he j hj hjq)) hk)
  intro k hk
  obtain ⟨hk, ha⟩ := Finset.mem_filter.mp hk
  have hkN := Finset.mem_range.mp hk
  exact (mul_le_mul_of_nonneg_left
    (h.predicted_lower hemin heone hetheta he hL hf hkN) p.eta1_pos.le).trans
      (h.accepted_decrease (fun j hj hjq => hemin.trans_le (he j hj hjq)) hkN ha)

/-- Finite trust-region updates yield the standard logarithmic total-trial budget. This
uses a constant continuation of scalar updates, without requiring any post-stop trials. -/
theorem LegalPrefix.total_count_le (h : LegalPrefix p q epsilon f t N)
    {m : ℝ} (hm : 0 < m) (hmin : m ≤ t.radius N) :
    (N : ℝ) ≤ (successCount (fun k => p.eta1 ≤ ratio f t k) N : ℝ) *
      (1 + Real.log p.gamma3 / |Real.log p.gamma2|) +
        Real.log (t.radius 0 / m) / |Real.log p.gamma2| := by
  let r := hold t.radius N
  let rho := continueRatio (ratio f t) N
  have hr : ∀ k, 0 < r k := fun k => h.radius_pos (Nat.min_le_right _ _)
  have hc : successCount (fun k => p.eta1 ≤ rho k) N =
      successCount (fun k => p.eta1 ≤ ratio f t k) N := by
    unfold successCount
    congr 1
    apply Finset.filter_congr
    intro k hk
    simp only [rho, continueRatio, ite_eq_left (Finset.mem_range.mp hk)]
  have hs : ∀ k, p.eta1 ≤ rho k → r (k + 1) ≤ p.gamma3 * r k := by
    intro k ha
    by_cases hk : k < N
    · have ha' : p.eta1 ≤ ratio f t k := by simpa [rho, continueRatio, hk] using ha
      have hu := h.update k hk
      have he : r (k + 1) = t.radius (k + 1) := hold_of_le _ (by omega)
      rw [he, show r k = t.radius k from hold_of_le _ (by omega)]
      split_ifs at hu
      · exact hu.2.trans (min_le_right _ _)
      · exact hu.2.trans (le_mul_of_one_le_left (h.radius_pos (by omega)).le p.one_le_gamma3)
    · have hn : N ≤ k := by omega
      simpa [r, hold_of_ge _ hn, hold_of_ge _ (show N ≤ k + 1 by omega)] using
        le_mul_of_one_le_left (h.radius_pos le_rfl).le p.one_le_gamma3
  have hu : ∀ k, ¬p.eta1 ≤ rho k → r (k + 1) ≤ p.gamma2 * r k := by
    intro k ha
    have hk : k < N := by
      by_contra hn
      have he : rho k = 1 := by simp [rho, continueRatio, hn]
      exact ha (he ▸ p.eta_le.trans p.eta2_lt_one.le)
    have ha' : ¬p.eta1 ≤ ratio f t k := by simpa [rho, continueRatio, hk] using ha
    have hn : ¬p.eta2 ≤ ratio f t k := fun hh => ha' (p.eta_le.trans hh)
    have hh := h.update k hk
    rw [ite_eq_right hn, ite_eq_right ha'] at hh
    simpa [r, hold_of_le _ (show k ≤ N by omega), hold_of_le _ (show k + 1 ≤ N by omega)] using hh.2
  have hh := ParameterUpdates.total_count_le_of_lower_bound hr
    (zero_lt_one.trans_le p.one_le_gamma3)
    ⟨p.gamma1_pos.trans_le p.gamma_le, p.gamma2_lt_one⟩ hs hu N hm
    (show m ≤ r N by simpa [r] using hmin)
  simpa [r, hc] using hh

/-- The successful-step coefficient does not involve the requested tolerances or test cap. -/
def successCoefficient (p : Parameters) (q : ℕ) (initial L : ℝ) : ℝ :=
  (q ! : ℝ) / (p.eta1 * (radiusCoefficient p initial L * p.fraction) ^ (q + 1))

/-- The logarithmic multiplicative overhead of unsuccessful trials. -/
def iterationFactor (p : Parameters) : ℝ := 1 + Real.log p.gamma3 / |Real.log p.gamma2|

/-- Every successful-step coefficient is positive for positive initial radius and smoothness. -/
theorem successCoefficient_pos {initial L : ℝ} (hi : 0 < initial) (hL : 0 < L) :
    0 < successCoefficient p q initial L := by
  have hc := radiusCoefficient_pos (p := p) hi hL
  have hf := p.fraction_pos
  have he := p.eta1_pos
  unfold successCoefficient
  positivity

/-- The count multiplier is positive even when the maximal expansion factor equals one. -/
theorem iterationFactor_pos : 0 < iterationFactor p := by
  have hg : 0 ≤ Real.log p.gamma3 := Real.log_nonneg p.one_le_gamma3
  unfold iterationFactor
  have hh : 0 ≤ Real.log p.gamma3 / |Real.log p.gamma2| := div_nonneg hg (abs_nonneg _)
  linarith

/-- The coefficient of the inverse tolerance power in the function-call bound. -/
def functionCoefficient (p : Parameters) (q : ℕ) (initial L : ℝ) : ℝ :=
  successCoefficient p q initial L * iterationFactor p

/-- The coefficient of the absolute logarithm of the tolerance. -/
def logCoefficient (p : Parameters) : ℝ := 1 / |Real.log p.gamma2|

/-- The additive function-call constant includes the initial objective evaluation. -/
def offsetCoefficient (p : Parameters) (initial L : ℝ) : ℝ :=
  |Real.log (initial / (radiusCoefficient p initial L * p.fraction))| /
    |Real.log p.gamma2| + 1

/-- All four evaluation-complexity constants are positive and contain no tolerance. -/
theorem complexity_constants_pos {initial L : ℝ} (hi : 0 < initial) (hL : 0 < L) :
    0 < functionCoefficient p q initial L ∧ 0 < logCoefficient p ∧
      0 < offsetCoefficient p initial L ∧ 0 < successCoefficient p q initial L := by
  have hs := successCoefficient_pos (p := p) (q := q) hi hL
  have hg := p.gamma1_pos.trans_le p.gamma_le
  have hz : 0 < |Real.log p.gamma2| := abs_pos.mpr (Real.log_neg hg p.gamma2_lt_one).ne
  refine ⟨mul_pos hs iterationFactor_pos, div_pos zero_lt_one hz, ?_, hs⟩
  unfold offsetCoefficient
  have hh : 0 ≤ |Real.log (initial / (radiusCoefficient p initial L * p.fraction))| /
      |Real.log p.gamma2| := div_nonneg (abs_nonneg _) hz.le
  linarith

/-- Uniform real-valued trial budget; integer stopping indices are bounded by its floor. -/
def trialBudget (p : Parameters) (q : ℕ) (initial L gap emin : ℝ) : ℝ :=
  successCoefficient p q initial L * gap / emin ^ (q + 1) * iterationFactor p +
    (|Real.log (initial / (radiusCoefficient p initial L * p.fraction))| + |Real.log emin|) /
      |Real.log p.gamma2|

/-- Expanding the trial budget gives the four source complexity constants. -/
theorem trialBudget_add_one_eq (initial L gap emin : ℝ) :
    trialBudget p q initial L gap emin + 1 =
      functionCoefficient p q initial L * gap / emin ^ (q + 1) +
        logCoefficient p * |Real.log emin| + offsetCoefficient p initial L := by
  unfold trialBudget functionCoefficient logCoefficient offsetCoefficient
  ring

/-- Rewriting the direct decrease denominator isolates the tolerance power. -/
theorem success_budget_eq {initial L gap emin : ℝ} (hi : 0 < initial)
    (hL : 0 < L) (he : 0 < emin) :
    gap / (p.eta1 * ((radiusCoefficient p initial L * p.fraction * emin) ^ (q + 1) /
      (q ! : ℝ))) = successCoefficient p q initial L * gap / emin ^ (q + 1) := by
  have hc := radiusCoefficient_pos (p := p) hi hL
  have hf := p.fraction_pos
  have hp := p.eta1_pos
  unfold successCoefficient
  rw [mul_pow]
  field_simp

/-- The total prefix count has the expected inverse-power plus logarithmic tolerance form. -/
theorem LegalPrefix.prefix_count_le (h : LegalPrefix p q epsilon f t N)
    {emin L low : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j) (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L) (hlow : low ≤ f (t.point N)) :
    (N : ℝ) ≤ trialBudget p q (t.radius 0) L (f (t.point 0) - low) emin := by
  have hc := radiusCoefficient_pos (p := p) h.initial_pos hL
  have hfrac := p.fraction_pos
  have hgamma : 0 < p.gamma2 := p.gamma1_pos.trans_le p.gamma_le
  have hlog : 0 < |Real.log p.gamma2| := abs_pos.mpr (Real.log_neg hgamma p.gamma2_lt_one).ne
  have hfactor : 0 ≤ iterationFactor p := by
    have hg : 0 ≤ Real.log p.gamma3 := Real.log_nonneg p.one_le_gamma3
    unfold iterationFactor
    positivity
  have hs := h.success_count_le hemin heone hetheta he hL hf hlow
  rw [success_budget_eq h.initial_pos hL hemin] at hs
  have hn := h.total_count_le
    (by positivity : 0 < radiusCoefficient p (t.radius 0) L * p.fraction * emin)
    (h.radius_lower hemin heone hetheta he hL hf le_rfl)
  have hlg : Real.log (t.radius 0 / (radiusCoefficient p (t.radius 0) L * p.fraction * emin)) ≤
      |Real.log (t.radius 0 / (radiusCoefficient p (t.radius 0) L * p.fraction))| +
        |Real.log emin| := by
    rw [show t.radius 0 / (radiusCoefficient p (t.radius 0) L * p.fraction * emin) =
      (t.radius 0 / (radiusCoefficient p (t.radius 0) L * p.fraction)) / emin by ring]
    rw [Real.log_div (div_pos h.initial_pos (mul_pos hc p.fraction_pos)).ne' hemin.ne']
    linarith [le_abs_self (Real.log (t.radius 0 /
      (radiusCoefficient p (t.radius 0) L * p.fraction))), neg_le_abs (Real.log emin)]
  unfold trialBudget
  exact hn.trans (add_le_add (mul_le_mul_of_nonneg_right hs hfactor)
    (div_le_div_of_nonneg_right hlg hlog.le))

/-- An execution supplies legal finite prefixes precisely as long as all previous actual
termination tests have failed. It requires no trial, decrement, or update after stopping. -/
def IsRun (p : Parameters) (q : ℕ) (epsilon : ℕ → ℝ) (f : E → ℝ) (t : Trace E) : Prop :=
  ∀ N, (∀ k < N, ¬Stops p q epsilon f t k) → LegalPrefix p q epsilon f t N

/-- Count actual objective evaluations: one initial value and one per executed trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Count derivative batches with rejection caching: one initial batch and one for every
accepted trial. Each batch evaluates all requested positive derivative orders. -/
def derivativeBatches (p : Parameters) (f : E → ℝ) (t : Trace E) (N : ℕ) : ℕ :=
  successCount (fun k => p.eta1 ≤ ratio f t k) N + 1

/-- The actual function-query locations: the initial point and each trial point. -/
def functionQueries (t : Trace E) (N : ℕ) : List E :=
  t.point 0 :: (List.range N).map (fun k => t.point k + t.step k)

open Classical in
/-- The cached derivative-query locations: the initial point and accepted endpoints only.
A query evaluates the requested actual derivative family at that point. -/
def derivativeQueries (p : Parameters) (f : E → ℝ) (t : Trace E) (N : ℕ) : List E :=
  t.point 0 :: (((Finset.range N).filter (fun k => p.eta1 ≤ ratio f t k)).toList.map
    (fun k => t.point (k + 1)))

omit [NormedSpace ℝ E] in
/-- Function evaluation counts are lengths of the actual function-query log. -/
theorem length_functionQueries (N : ℕ) : (functionQueries t N).length = functionEvaluations N := by
  simp [functionQueries, functionEvaluations]

/-- Derivative batch counts are lengths of the cached derivative-query log. -/
theorem length_derivativeQueries (N : ℕ) :
    (derivativeQueries p f t N).length = derivativeBatches p f t N := by
  simp [derivativeQueries, derivativeBatches, successCount]

/-- Rejection retains the point and hence every cached actual derivative tensor. -/
theorem LegalPrefix.rejected_derivative_cache (h : LegalPrefix p q epsilon f t N)
    {k : ℕ} (hk : k < N) (ha : ¬p.eta1 ≤ ratio f t k) (j : ℕ) :
    iteratedFDeriv ℝ j f (t.point (k + 1)) = iteratedFDeriv ℝ j f (t.point k) := by
  rw [h.iterate k hk, ite_eq_right ha]

/-- Finite termination, every requested true Taylor-gap criterion, and both actual oracle
counts. The first stopping index is bounded by a floor; constants in the budget do not involve
the tolerance or the testing cap. -/
theorem IsRun.complexity (h : IsRun p q epsilon f t)
    {emin L low : ℝ} (hemin : 0 < emin) (heone : emin ≤ 1) (hetheta : emin ≤ p.theta)
    (he : ∀ j, 1 ≤ j → j ≤ q → emin ≤ epsilon j) (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L)
    (hlow : ∀ x, low ≤ f x) :
    ∃ K ≤ ⌊trialBudget p q (t.radius 0) L (f (t.point 0) - low) emin⌋₊,
      Stops p q epsilon f t K ∧ (∀ i < K, ¬Stops p q epsilon f t i) ∧
      (0 < testRadius p t K ∧ testRadius p t K ≤ 1) ∧
      (∀ j, 1 ≤ j → j ≤ q → gapOn (taylorDecrement f j (t.point K))
        (closedBall 0 (testRadius p t K)) ≤ epsilon j * testRadius p t K ^ j / (j ! : ℝ)) ∧
      (functionEvaluations K : ℝ) ≤
        trialBudget p q (t.radius 0) L (f (t.point 0) - low) emin + 1 ∧
      (derivativeBatches p f t K : ℝ) ≤
        successCoefficient p q (t.radius 0) L * (f (t.point 0) - low) / emin ^ (q + 1) + 1 := by
  obtain ⟨K, hK, hs, hfirst⟩ := EvaluationComplexity.exists_first_of_prefix_bound
    (fun N hn => (h N hn).prefix_count_le hemin heone hetheta he hL hf (hlow _))
  have hp := h K hfirst
  have hfc := hp.prefix_count_le hemin heone hetheta he hL hf (hlow _)
  have hdc := hp.success_count_le hemin heone hetheta he hL hf (hlow _)
  rw [success_budget_eq hp.initial_pos hL hemin] at hdc
  refine ⟨K, hK, hs, hfirst, hp.testRadius_bounds le_rfl, hp.gaps_at_stop hs, ?_, ?_⟩
  · simpa only [functionEvaluations, Nat.cast_add, Nat.cast_one, add_comm] using
      add_le_add_right hfc 1
  · simpa only [derivativeBatches, Nat.cast_add, Nat.cast_one, add_comm] using
      add_le_add_right hdc 1

/-- A unit-ball Taylor decrement is bounded by twice a common positive-order diagonal
coefficient bound. No differentiability beyond the displayed actual coefficients is needed. -/
theorem taylorDecrement_le_two_mul {z d : E} {j : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hd : ‖d‖ ≤ 1)
    (hcoeff : ∀ i, 1 ≤ i → i ≤ j → (iteratedFDeriv ℝ i f z).diagonalNorm ≤ M) :
    taylorDecrement f j z d ≤ 2 * M := by
  rw [← InexactTaylorModels.decrement_iteratedFDeriv, InexactTaylorModels.decrement]
  apply (neg_le_abs _).trans
  rw [← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 j, M / (i ! : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi, hij⟩ := Finset.mem_Icc.mp hi
      have hdiag := (iteratedFDeriv ℝ i f z).norm_diagonal_le_diagonalNorm_mul
        (by omega) d
      have hp : ‖d‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hd
      have hcoef := hcoeff i hi hij
      have hn : ‖iteratedFDeriv ℝ i f z (fun _ => d)‖ ≤ M := by
        apply hdiag.trans
        exact (mul_le_mul_of_nonneg_right hcoef (pow_nonneg (norm_nonneg d) i)).trans
          (mul_le_of_le_one_right hM hp)
      simpa only [norm_div, Real.norm_natCast] using
        div_le_div_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (i ! : ℝ))
    _ = M * ∑ i ∈ Finset.Icc 1 j, (1 / (i ! : ℝ)) := by rw [Finset.mul_sum]; congr 1; funext i; ring
    _ ≤ 2 * M := by
      have hh := mul_le_mul_of_nonneg_left (InexactTaylorModels.sum_inv_factorial_le_two j) hM
      nlinarith

/-- Initial witness scaling is controlled by the initial derivative tensors, with the
source factor `2 * q!` and not the factorial of `2*q`. -/
theorem LegalPrefix.initial_scaledGap_upper (h : LegalPrefix p q epsilon f t N)
    (hN : 0 < N) {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ i, 1 ≤ i → i ≤ q →
      (iteratedFDeriv ℝ i f (t.point 0)).diagonalNorm ≤ M) :
    scaledGap p f t 0 ≤ 2 * (q ! : ℝ) * M / testRadius p t 0 ^ q := by
  have hd := h.witness_feasible 0 (by omega) _ (h.order_pos 0 hN) (h.order_le 0 hN)
  have hdb := h.testRadius_bounds (k := 0) (by omega)
  have hdec := taylorDecrement_le_two_mul hM (hd.trans hdb.2)
    (fun i hi hij => hcoeff i hi (hij.trans (h.order_le 0 hN)))
  have hfac : ((t.order 0)! : ℝ) ≤ (q ! : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (h.order_le 0 hN))
  have hpow : testRadius p t 0 ^ q ≤ testRadius p t 0 ^ t.order 0 :=
    pow_le_pow_of_le_one hdb.1.le hdb.2 (h.order_le 0 hN)
  unfold scaledGap
  calc
    _ ≤ ((t.order 0)! : ℝ) * (2 * M) / testRadius p t 0 ^ t.order 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdec (by positivity))
        (pow_nonneg hdb.1.le _)
    _ ≤ (q ! : ℝ) * (2 * M) / testRadius p t 0 ^ t.order 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (by positivity))
        (pow_nonneg hdb.1.le _)
    _ ≤ (q ! : ℝ) * (2 * M) / testRadius p t 0 ^ q :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hdb.1 _) hpow
    _ = _ := by ring

/-- The historical minimum of the selected scaled witness gaps. -/
def runningGap (p : Parameters) (f : E → ℝ) (t : Trace E) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' (by simp) (scaledGap p f t)

/-- The historical minimum is below every gap in that prefix. -/
theorem runningGap_le {i k : ℕ} (hi : i ≤ k) :
    runningGap p f t k ≤ scaledGap p f t i :=
  Finset.inf'_le _ (by simpa using hi)

/-- A bound shared by all earlier scaled gaps bounds their historical minimum. -/
theorem le_runningGap {k : ℕ} {a : ℝ}
    (ha : ∀ i ≤ k, a ≤ scaledGap p f t i) : a ≤ runningGap p f t k := by
  apply Finset.le_inf'
  intro i hi
  exact ha i (by simpa using hi)

/-- Restricting an executed prefix retains exactly the same trace data. -/
theorem LegalPrefix.restrict (h : LegalPrefix p q epsilon f t N) {M : ℕ} (hMN : M ≤ N) :
    LegalPrefix p q epsilon f t M where
  initial_pos := h.initial_pos
  initial_cap := h.initial_cap
  witness_feasible := fun k hk => h.witness_feasible k (hk.trans hMN)
  witness_fraction := fun k hk => h.witness_fraction k (hk.trans hMN)
  nonterminal := fun k hk => h.nonterminal k (hk.trans_le hMN)
  order_pos := fun k hk => h.order_pos k (hk.trans_le hMN)
  order_le := fun k hk => h.order_le k (hk.trans_le hMN)
  first_failure := fun k hk => h.first_failure k (hk.trans_le hMN)
  failure := fun k hk => h.failure k (hk.trans_le hMN)
  step_feasible := fun k hk => h.step_feasible k (hk.trans_le hMN)
  prediction := fun k hk => h.prediction k (hk.trans_le hMN)
  iterate := fun k hk => h.iterate k (hk.trans_le hMN)
  update := fun k hk => h.update k (hk.trans_le hMN)

/-- A scale satisfying the initial and success-threshold comparisons bounds every radius
by the historical minimum. This separates induction from the initial-jet estimate. -/
theorem LegalPrefix.radius_lower_runningGap (h : LegalPrefix p q epsilon f t N)
    (he : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j) {L c : ℝ} (hL : 0 < L)
    (hf : ∀ j, 1 ≤ j → j ≤ q → DiagonalLipschitz f j L) (hc : 0 ≤ c)
    (hca : c ≤ p.gamma1 * (1 - p.eta2) / L)
    (hinit : c * scaledGap p f t 0 ≤ t.radius 0)
    {k : ℕ} (hk : k < N) :
    min (p.gamma1 * p.theta) (c * runningGap p f t k) ≤ t.radius k := by
  let a := runningGap p f t k
  have ht : ∀ i < N, i ≤ k → t.radius i ≤ min p.theta ((1 - p.eta2) * a / L) →
      p.eta2 ≤ ratio f t i := by
    intro i hi hik hr
    apply h.ratio_ge_of_radius he hf hi (hr.trans (min_le_left _ _))
    have hh := (le_div_iff₀ hL).mp (hr.trans (min_le_right _ _))
    have hg := runningGap_le (p := p) (f := f) (t := t) hik
    have hm := mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr p.eta2_lt_one.le)
    nlinarith
  have ha : 0 ≤ a := by
    apply le_runningGap
    intro i hi
    have hg := h.scaledGap_lower (fun j hj hjq => (he j hj hjq).le) (by omega : i < N)
    simpa using hg.le
  have hi : c * a ≤ t.radius 0 :=
    (mul_le_mul_of_nonneg_left (runningGap_le (by omega : 0 ≤ k)) hc).trans hinit
  have hpre := h.restrict (show k + 1 ≤ N by omega)
  have hl := hpre.radius_lower_of_threshold
    (T := min p.theta ((1 - p.eta2) * a / L))
    (fun i hi hr => ht i (by omega) (by omega) hr) (k := k) (by omega)
  apply le_trans _ hl
  apply le_min
  · exact (min_le_right _ _).trans hi
  · rw [mul_min_of_nonneg _ _ p.gamma1_pos.le]
    apply min_le_min le_rfl
    have hh := mul_le_mul_of_nonneg_right hca ha
    (convert hh using 1; ring)

end Optimization.HigherOrderTrustRegion
