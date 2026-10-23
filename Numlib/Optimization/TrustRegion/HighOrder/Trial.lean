import Numlib.Optimization.HighOrder.Criticality
import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Analysis.Calculus.TaylorModel.Holder

/-!
# Actual finite-order trust-region trials

The parameters and trial predicate express the two radii, genuine approximate Taylor
criticality computations, first failing stopping test, model comparison, actual ratio,
and capped three-case radius update of the arbitrary-order trust-region method.
Small-radius acceptance follows from the actual Lipschitz Taylor remainder.
-/

namespace HighOrderTrustRegion
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed parameters of the arbitrary-order trust-region algorithm. The enlargement
factor may equal one, as in Algorithm 12.2.1. -/
structure Parameters (q : ℕ) where
  order_pos : 0 < q
  accuracy : Fin q → ℝ
  accuracy_pos : ∀ j, 0 < accuracy j
  accuracy_le_one : ∀ j, accuracy j ≤ 1
  zeta : ℝ
  zeta_pos : 0 < zeta
  zeta_le_one : zeta ≤ 1
  theta : ℝ
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  min_accuracy_le_theta : ∃ j, accuracy j ≤ theta
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  radiusMax : ℝ
  eta1_pos : 0 < eta1
  eta1_le_eta2 : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_le_gamma2 : gamma1 ≤ gamma2
  gamma2_lt_one : gamma2 < 1
  one_le_gamma3 : 1 ≤ gamma3

/-- The maximum of the actual per-order Lipschitz constants, equation (12.2.6). -/
noncomputable def maxLipschitzConstant {q : ℕ} (P : Parameters q) (L : Fin q → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0,P.order_pos⟩, Finset.mem_univ _⟩ L

/-- Every per-order constant is at most their finite maximum. -/
theorem le_maxLipschitzConstant {q : ℕ} (P : Parameters q) (L : Fin q → ℝ) (j : Fin q) :
    L j ≤ maxLipschitzConstant P L := Finset.le_sup' L (Finset.mem_univ j)

/-- A scalar bounds the maximum exactly when it bounds every per-order constant. -/
theorem maxLipschitzConstant_le_iff {q : ℕ} (P : Parameters q) (L : Fin q → ℝ) (a : ℝ) :
    maxLipschitzConstant P L ≤ a ↔ ∀ j, L j ≤ a := by
  constructor
  · intro h j
    exact (le_maxLipschitzConstant P L j).trans h
  · intro h
    exact Finset.sup'_le _ _ (fun j _ => h j)

/-- The common Lipschitz bound is positive when the per-order bounds are at least one. -/
theorem maxLipschitzConstant_pos {q : ℕ} (P : Parameters q) (L : Fin q → ℝ)
    (hL : ∀ j, 1 ≤ L j) : 0 < maxLipschitzConstant P L :=
  (by norm_num : (0 : ℝ) < 1).trans_le
    ((hL ⟨0,P.order_pos⟩).trans (le_maxLipschitzConstant P L _))

/-- The order of the selected nonterminal Taylor model. -/
def modelOrder {q : ℕ} (j : Fin q) : ℕ := j.val + 1

/-- Every selected Taylor model has positive order. -/
theorem modelOrder_pos {q : ℕ} (j : Fin q) : 0 < modelOrder j := Nat.succ_pos _

/-- Every selected Taylor model has order at most the algorithm's maximal order. -/
theorem modelOrder_le {q : ℕ} (j : Fin q) : modelOrder j ≤ q := Nat.succ_le_of_lt j.isLt

/-- The optimality radius is the smaller of the trust-region radius and its cap. -/
def optimalityRadius {q : ℕ} (P : Parameters q) (Δ : ℝ) : ℝ := min Δ P.theta

/-- The optimality radius is bounded by the trust-region radius. -/
theorem optimalityRadius_le_radius {q : ℕ} (P : Parameters q) (Δ : ℝ) :
    optimalityRadius P Δ ≤ Δ := min_le_left _ _

/-- The optimality radius is bounded by its cap. -/
theorem optimalityRadius_le_theta {q : ℕ} (P : Parameters q) (Δ : ℝ) :
    optimalityRadius P Δ ≤ P.theta := min_le_right _ _

/-- Below the optimality-radius cap, the two radii coincide. -/
theorem optimalityRadius_eq_radius {q : ℕ} (P : Parameters q) {Δ : ℝ}
    (hΔ : Δ ≤ P.theta) : optimalityRadius P Δ = Δ := min_eq_left hΔ

/-- One actual nonterminal trial, including the first failing selected-order test and
all derivative-model computations preceding it. No success or decrease estimate is assumed. -/
structure Trial {q : ℕ} (f : E → ℝ) (P : Parameters q) (x : E)
    (Δ : ℝ) (d : Fin q → E) (j : Fin q) (s xnext : E) (Δnext ρ : ℝ) : Prop where
  radius_pos : 0 < Δ
  direction_feasible : ∀ a, a ≤ j → ‖d a‖ ≤ optimalityRadius P Δ
  approximation : ∀ a, a ≤ j → P.zeta * TaylorModel.criticality f (modelOrder a) x
    (optimalityRadius P Δ) ≤ TaylorModel.decrement f (modelOrder a) x (d a)
  earlier_tests : ∀ a, a < j → TaylorModel.decrement f (modelOrder a) x (d a) ≤
    P.zeta * P.accuracy a * optimalityRadius P Δ ^ modelOrder a / (modelOrder a).factorial
  failed_test : P.zeta * P.accuracy j * optimalityRadius P Δ ^ modelOrder j /
    (modelOrder j).factorial < TaylorModel.decrement f (modelOrder j) x (d j)
  step_feasible : ‖s‖ ≤ Δ
  model_comparison : TaylorModel.decrement f (modelOrder j) x (d j) ≤
    TaylorModel.decrement f (modelOrder j) x s
  ratio : ρ = (f x - f (x + s)) / TaylorModel.decrement f (modelOrder j) x s
  point_update : xnext = if P.eta1 ≤ ρ then x + s else x
  radius_update :
    if P.eta2 ≤ ρ then Δnext ∈ Icc Δ (min P.radiusMax (P.gamma3 * Δ))
    else if P.eta1 ≤ ρ then Δnext ∈ Icc (P.gamma2 * Δ) Δ
    else Δnext ∈ Icc (P.gamma1 * Δ) (P.gamma2 * Δ)

/-- The actual scaled selected model decrement, equation (12.2.8). -/
noncomputable def scaledGap {q : ℕ} (f : E → ℝ) (P : Parameters q) (x : E)
    (Δ : ℝ) (d : Fin q → E) (j : Fin q) : ℝ :=
  ModelDecrease.scaled (TaylorModel.decrement f (modelOrder j) x (d j))
    (optimalityRadius P Δ) (modelOrder j)

namespace Trial
variable {q : ℕ} {f : E → ℝ} {P : Parameters q} {x xnext s : E}
  {Δ Δnext ρ : ℝ} {d : Fin q → E} {j : Fin q}

/-- Every actual trial has a strictly positive optimality radius. -/
theorem optimalityRadius_pos (h : Trial f P x Δ d j s xnext Δnext ρ) :
    0 < optimalityRadius P Δ := lt_min h.radius_pos P.theta_pos

/-- The failing source stopping test makes its genuine Taylor decrement positive. -/
theorem direction_decrement_pos (h : Trial f P x Δ d j s xnext Δnext ρ) :
    0 < TaylorModel.decrement f (modelOrder j) x (d j) := by
  apply lt_trans _ h.failed_test
  exact div_pos (mul_pos (mul_pos P.zeta_pos (P.accuracy_pos j))
    (pow_pos h.optimalityRadius_pos _)) (by positivity)

/-- The ratio denominator is positive, by the failed test and actual model comparison. -/
theorem denominator_pos (h : Trial f P x Δ d j s xnext Δnext ρ) :
    0 < TaylorModel.decrement f (modelOrder j) x s :=
  h.direction_decrement_pos.trans_le h.model_comparison

/-- The actual scaled model decrement is positive. -/
theorem scaledGap_pos (h : Trial f P x Δ d j s xnext Δnext ρ) :
    0 < scaledGap f P x Δ d j := by
  unfold scaledGap ModelDecrease.scaled
  exact div_pos (mul_pos (by positivity) h.direction_decrement_pos)
    (pow_pos h.optimalityRadius_pos _)

/-- The computed step attains at least the rescaled actual gap. -/
theorem scaledGap_le_decrement (h : Trial f P x Δ d j s xnext Δnext ρ) :
    scaledGap f P x Δ d j * optimalityRadius P Δ ^ modelOrder j /
      (modelOrder j).factorial ≤ TaylorModel.decrement f (modelOrder j) x s := by
  unfold scaledGap
  rw [ModelDecrease.scaled_mul_radius _ h.optimalityRadius_pos]
  exact h.model_comparison

/-- A very successful trial cannot decrease the trust-region radius. -/
theorem radius_le_next_of_very_successful (h : Trial f P x Δ d j s xnext Δnext ρ)
    (hs : P.eta2 ≤ ρ) : Δ ≤ Δnext := by
  have hu := h.radius_update
  rw [ite_eq_left hs] at hu
  exact hu.1

/-- The actual selected-order Taylor remainder gives the exact normalized ratio error
bound when both radii coincide. -/
theorem ratio_error_le (h : Trial f P x Δ d j s xnext Δnext ρ)
    (hf : ContDiff ℝ q f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ (modelOrder j) f y -
      iteratedFDeriv ℝ (modelOrder j) f z‖ ≤ L * ‖y - z‖)
    (hΔ : Δ ≤ P.theta) :
    |ρ - 1| ≤ L * Δ / ((modelOrder j + 1 : ℕ) * scaledGap f P x Δ d j) := by
  let k := modelOrder j
  have hk : 0 < k := modelOrder_pos j
  have hkq : k ≤ q := modelOrder_le j
  have hδ : optimalityRadius P Δ = Δ := optimalityRadius_eq_radius P hΔ
  have hgap := h.scaledGap_pos
  have hpred := h.scaledGap_le_decrement
  rw [hδ] at hpred
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hfacsucc : ((k + 1).factorial : ℝ) = (k + 1 : ℕ) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  have hsub : k - 1 + 1 = k := by omega
  have hsub2 : k - 1 + 2 = k + 1 := by omega
  have hlip' : ∀ y ∈ (univ : Set E), ∀ z ∈ (univ : Set E),
      ‖iteratedFDeriv ℝ (k - 1 + 1) f y - iteratedFDeriv ℝ (k - 1 + 1) f z‖ ≤ L * ‖y - z‖ := by
    intro y _ z _
    rw [hsub]
    exact hlip y z
  have herr := TaylorModel.abs_sub_eval_le_lipschitz (p := k - 1)
    (C := univ) (D := univ) isOpen_univ (Subset.refl _) convex_univ
    ((hf.of_le (by exact_mod_cast hkq)).contDiffOn) hL
    hlip'
    (mem_univ x) (mem_univ (x + s))
  simp only [hsub, hsub2] at herr
  have hpows := pow_le_pow_left₀ (norm_nonneg s) h.step_feasible (k + 1)
  have herr' : |f (x + s) - TaylorModel.eval f k x s| ≤
      L * Δ ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    herr.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpows hL) (by positivity))
  have hratio : |ρ - 1| = |f (x + s) - TaylorModel.eval f k x s| /
      TaylorModel.decrement f k x s := by
    have hden : 0 < f x - TaylorModel.eval f k x s := by
      simpa only [TaylorModel.decrement_eq] using h.denominator_pos
    rw [h.ratio, TaylorModel.decrement_eq]
    change |(f x - f (x + s)) / (f x - TaylorModel.eval f k x s) - 1| = _
    rw [div_sub_one hden.ne', abs_div, abs_of_pos hden]
    congr 1
    rw [show f x - f (x + s) - (f x - TaylorModel.eval f k x s) =
      -(f (x + s) - TaylorModel.eval f k x s) by ring, abs_neg]
  rw [hratio]
  apply (div_le_iff₀ h.denominator_pos).2
  apply herr'.trans
  have hnonneg : 0 ≤ L * Δ / ((k + 1 : ℕ) * scaledGap f P x Δ d j) :=
    div_nonneg (mul_nonneg hL h.radius_pos.le) (mul_nonneg (by positivity) hgap.le)
  have hm := mul_le_mul_of_nonneg_left hpred hnonneg
  apply le_trans _ hm
  rw [hfacsucc]
  have hΔne : Δ ≠ 0 := h.radius_pos.ne'
  have hgne : scaledGap f P x Δ d j ≠ 0 := hgap.ne'
  change L * Δ ^ (k + 1) / ((k + 1 : ℕ) * (k.factorial : ℝ)) ≤
    L * Δ / ((k + 1 : ℕ) * scaledGap f P x Δ d j) *
      (scaledGap f P x Δ d j * Δ ^ k / (k.factorial : ℝ))
  field_simp
  ring_nf
  exact le_rfl

/-- The source small-radius condition guarantees actual very successful acceptance
and nondecrease of the radius. -/
theorem very_successful (h : Trial f P x Δ d j s xnext Δnext ρ)
    (hf : ContDiff ℝ q f) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ (modelOrder j) f y -
      iteratedFDeriv ℝ (modelOrder j) f z‖ ≤ L * ‖y - z‖)
    (hsmall : Δ ≤ min P.theta ((1 - P.eta2) / L * scaledGap f P x Δ d j)) :
    P.eta2 ≤ ρ ∧ Δ ≤ Δnext := by
  have hbound := h.ratio_error_le hf hL.le hlip (le_min_iff.mp hsmall).1
  have hg := h.scaledGap_pos
  have hk : (1 : ℝ) ≤ (modelOrder j + 1 : ℕ) := by
    have : 1 ≤ modelOrder j + 1 := by omega
    exact_mod_cast this
  have hδ := (le_min_iff.mp hsmall).2
  have hmul : L * Δ ≤ (1 - P.eta2) * scaledGap f P x Δ d j := by
    have hh := mul_le_mul_of_nonneg_left hδ hL.le
    field_simp at hh
    nlinarith
  have hratio : L * Δ / ((modelOrder j + 1 : ℕ) * scaledGap f P x Δ d j) ≤ 1 - P.eta2 := by
    apply (div_le_iff₀ (mul_pos (by positivity) hg)).2
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hg.le hk) (sub_nonneg.mpr P.eta2_lt_one.le))
  have hs : P.eta2 ≤ ρ := by have hh := (abs_le.mp (hbound.trans hratio)).1; linarith
  exact ⟨hs, h.radius_le_next_of_very_successful hs⟩

end Trial
end HighOrderTrustRegion
