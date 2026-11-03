import NumlibSurface.ConnGouldToint.Chapter12.Section01
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Generalized Cauchy decrease -/

open Optimization Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter12

/-- The constants in the projected-path line search (12.2.3). -/
structure GeneralizedCauchyParams where
  upperSlope : ℝ
  lowerSlope : ℝ
  radiusFraction : ℝ
  endpointFactor : ℝ
  upper_pos : 0 < upperSlope
  slope_order : upperSlope < lowerSlope
  lower_lt_one : lowerSlope < 1
  fraction_pos : 0 < radiusFraction
  fraction_lt_one : radiusFraction < 1
  endpoint_pos : 0 < endpointFactor
  endpoint_lt_half : endpointFactor < 1 / 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Conditions (12.2.1)–(12.2.4) for an approximate generalized Cauchy point. -/
def IsApproxGeneralizedCauchyPoint (P : GeneralizedCauchyParams) (C : Set E)
    (f m : E → ℝ) (x : E) (Δ : ℝ) (z : E) : Prop :=
  ∃ t > 0, z = projectedGradientPath C f x t ∧ ‖z - x‖ ≤ Δ ∧
    m z ≤ m x + P.upperSlope * ⟪gradient f x, z - x⟫ ∧
    (P.radiusFraction * Δ ≤ ‖z - x‖ ∨
      m x + P.lowerSlope * ⟪gradient f x, z - x⟫ ≤ m z ∨
      ‖bestApprox (tangentDirections C z) (-gradient f x)‖ ≤
        P.endpointFactor * (|⟪gradient f x, z - x⟫| / Δ))

/-- Theorem 12.2.2. The curvature bound is only needed on the segment
to the trial point. The Taylor estimate is used in the lower-slope case. -/
theorem theorem_12_2_2_of_taylor_bound (P : GeneralizedCauchyParams) {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {f m : E → ℝ} {x z : E}
    (hx : x ∈ C) {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β)
    (hm : IsApproxGeneralizedCauchyPoint P C f m x Δ z)
    (hTaylor : m z - (m x + ⟪gradient f x, z - x⟫) ≤ β * ‖z - x‖ ^ 2 / 2) :
    let κ := min (P.upperSlope * P.radiusFraction / 2)
      (2 * P.upperSlope * (1 - P.lowerSlope))
    0 < κ ∧
    κ * criticality C f x 1 * min (criticality C f x 1 / β) (min Δ 1) ≤ m x - m z ∧
    P.upperSlope * |⟪gradient f x, z - x⟫| ≤ m x - m z := by
  obtain ⟨t, ht, rfl, _, hupper, hstop⟩ := hm
  let z := projectedGradientPath C f x t
  let d := z - x
  let r := ‖d‖
  let χ := criticality C f x 1
  let L := |⟪gradient f x, d⟫|
  let D := m x - m z
  let u := P.upperSlope
  let a := P.radiusFraction
  let κ := min (u * a / 2) (2 * u * (1 - P.lowerSlope))
  let q := min (χ / β) (min Δ 1)
  obtain ⟨hz, hmin, _⟩ := theorem_12_1_4 hclosed hconv (f := f) hx ht.le
  have hd : x + d = z := by dsimp [d]; abel
  have hz' : x + d ∈ C := hd ▸ hz
  have hs : ⟪gradient f x, d⟫ ≤ 0 := by
    have h := (isMinOn_iff.mp hmin) (0 : E) (by simp [hx])
    simpa only [inner_zero_right] using h
  have hL : L = -⟪gradient f x, d⟫ := abs_of_nonpos hs
  have hcr : criticality C f x r = L := by
    change linearDecrease C x (-gradient f x) r = L
    rw [hL, ← inner_neg_left]
    apply le_antisymm _ (inner_le_linearDecrease hz' le_rfl)
    apply linearDecrease_le hx (norm_nonneg _)
    intro v hv hn
    simpa only [inner_neg_left, neg_le_neg_iff] using (isMinOn_iff.mp hmin) v ⟨hv, hn⟩
  have hχ : 0 ≤ χ := linearDecrease_nonneg hx zero_le_one
  have hq : 0 ≤ q := le_min (div_nonneg hχ hβ.le) (le_min hΔ.le zero_le_one)
  have hD : u * L ≤ D := by
    change m z ≤ m x + u * ⟪gradient f x, d⟫ at hupper
    dsimp [D]
    rw [hL, mul_neg]
    linarith
  have hu : 0 < u := P.upper_pos
  have ha : 0 < a := P.fraction_pos
  have ha₁ : a ≤ 1 := P.fraction_lt_one.le
  have hκ : 0 < κ := lt_min (half_pos (mul_pos hu ha))
    (mul_pos (by positivity) (sub_pos.mpr P.lower_lt_one))
  have hκu : κ ≤ u := (min_le_left _ _).trans
    (by nlinarith [mul_le_mul_of_nonneg_left ha₁ hu.le])
  change 0 < κ ∧ κ * χ * q ≤ D ∧ u * L ≤ D
  refine ⟨hκ, ?_, hD⟩
  have hscale (b : ℝ) (hb : 0 < b) (hb₁ : b ≤ 1) :
      χ * b ≤ criticality C f x b := by
    have h := (theorem_12_1_5 (f := f) hconv hx).2.1
      (show b ∈ Set.Ioi 0 from hb) (show (1 : ℝ) ∈ Set.Ioi 0 from (zero_lt_one : (0 : ℝ) < 1)) hb₁
    change χ / 1 ≤ criticality C f x b / b at h
    rw [div_one] at h
    exact (le_div_iff₀ hb).mp h
  by_cases hbig : 1 ≤ r
  · have hc : χ ≤ L := hcr ▸ linearDecrease_mono_radius hx zero_le_one hbig
    have hq₁ : q ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    calc
      κ * χ * q ≤ κ * χ := mul_le_of_le_one_right (mul_nonneg hκ.le hχ) hq₁
      _ ≤ u * L := mul_le_mul hκu hc hχ hu.le
      _ ≤ D := hD
  have hr₁ : r < 1 := lt_of_not_ge hbig
  by_cases hzero : r = 0
  · have hdx : d = 0 := norm_eq_zero.mp hzero
    have hp : z = x := sub_eq_zero.mp hdx
    have hn := projectedRay_residual_mem_normal ⟨x, hx⟩ hclosed hconv x (-gradient f x) t
    change x + t • (-gradient f x) - z ∈ normalDirections C z at hn
    rw [hp, add_sub_cancel_left] at hn
    have hcrit : ∀ y ∈ C, 0 ≤ ⟪gradient f x, y - x⟫ := by
      intro y hy
      have h := mem_normalDirections.mp hn y hy
      rw [real_inner_smul_left, inner_neg_left] at h
      exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ t * ⟪gradient f x, y - x⟫) ht
    have hχ₀ := (linearDecrease_eq_zero_iff (v := -gradient f x) hconv hx).mpr
      (mem_normalDirections.mpr fun y hy ↦ by
        simpa only [inner_neg_left, neg_nonpos] using hcrit y hy)
    change χ = 0 at hχ₀
    rw [hχ₀, mul_zero, zero_mul]
    exact (mul_nonneg hu.le (abs_nonneg _)).trans hD
  have hr : 0 < r := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  have hχr : χ * r ≤ L := hcr ▸ hscale r hr hr₁.le
  have hqΔ : q ≤ Δ := (min_le_right _ _).trans (min_le_left _ _)
  have hqβ : q ≤ χ / β := min_le_left _ _
  have hfrom (c : ℝ) (hc : 0 ≤ c) (hcκ : κ ≤ u * c) (hL' : c * χ * q ≤ L) :
      κ * χ * q ≤ D := by
    calc
      κ * χ * q ≤ (u * c) * χ * q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcκ hχ) hq
      _ = u * (c * χ * q) := by ring
      _ ≤ u * L := mul_le_mul_of_nonneg_left hL' hu.le
      _ ≤ D := hD
  by_cases hfar : a * Δ ≤ r
  · apply hfrom a ha.le
    · exact (min_le_left _ _).trans (by linarith [mul_pos hu ha])
    · calc
        a * χ * q = χ * (a * q) := by ring
        _ ≤ χ * r := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_left hqΔ ha.le).trans hfar) hχ
        _ ≤ L := hχr
  rcases hstop with hf | hlower | hend
  · exact (hfar hf).elim
  · have hl : (1 - P.lowerSlope) * L ≤ β * r ^ 2 / 2 := by
      change m x + P.lowerSlope * ⟪gradient f x, d⟫ ≤ m z at hlower
      change m z - (m x + ⟪gradient f x, d⟫) ≤ β * r ^ 2 / 2 at hTaylor
      rw [hL]
      linarith
    have hl₀ : 0 ≤ 1 - P.lowerSlope := sub_nonneg.mpr P.lower_lt_one.le
    have hmul := (mul_le_mul_of_nonneg_left hχr hl₀).trans hl
    have hrr : 2 * (1 - P.lowerSlope) * (χ / β) ≤ r := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hβ).mpr
      apply (mul_le_mul_iff_of_pos_right hr).mp
      nlinarith only [hmul]
    apply hfrom (2 * (1 - P.lowerSlope)) (by positivity)
    · exact (min_le_right _ _).trans_eq (by ring)
    · calc
        _ = χ * (2 * (1 - P.lowerSlope) * q) := by ring
        _ ≤ χ * r := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_left hqβ (by positivity)).trans hrr) hχ
        _ ≤ L := hχr
  · let b := min (a * Δ) 1
    have hb : 0 < b := lt_min (mul_pos ha hΔ) zero_lt_one
    have hrb : r < b := lt_min (lt_of_not_ge hfar) hr₁
    have hbΔ : b ≤ Δ := (min_le_left _ _).trans (mul_le_of_le_one_left hΔ.le ha₁)
    let T := ‖bestApprox (tangentDirections C z) (-gradient f x)‖
    have hbound := (theorem_12_1_5 (f := f) hconv hx).2.2.1 d hz' b hrb
    have hT : T ≤ P.endpointFactor * (L / Δ) := hend
    have hLT : 0 ≤ L / Δ := div_nonneg (abs_nonneg _) hΔ.le
    have htwo : 2 * b * T ≤ L := by
      calc
        _ ≤ 2 * Δ * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbΔ (by norm_num)) (norm_nonneg _)
        _ ≤ 2 * Δ * (P.endpointFactor * (L / Δ)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
        _ = (2 * P.endpointFactor) * L := by field_simp
        _ ≤ L := mul_le_of_le_one_left (abs_nonneg _) (by linarith [P.endpoint_lt_half])
    rw [hd] at hbound
    have hχb := (hscale b hb (min_le_right _ _)).trans (hbound.trans (add_le_add le_rfl htwo))
    have hab : a * q ≤ b := le_min (mul_le_mul_of_nonneg_left hqΔ ha.le)
      ((mul_le_of_le_one_left hq ha₁).trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply hfrom (a / 2) (div_nonneg ha.le (by norm_num))
    · exact (min_le_left _ _).trans_eq (by ring)
    · have hh := (mul_le_mul_of_nonneg_left hab hχ).trans hχb
      linarith

/-- The generalized Cauchy decrease follows from gradient agreement and a
uniform model Hessian bound on the trial segment. -/
theorem theorem_12_2_2 (P : GeneralizedCauchyParams) {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {f m : E → ℝ} {x z : E}
    (hx : x ∈ C) {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β)
    (hpoint : IsApproxGeneralizedCauchyPoint P C f m x Δ z)
    (hm : Differentiable ℝ m) (hdm : Differentiable ℝ (fderiv ℝ m))
    (hgrad : fderiv ℝ m x = fderiv ℝ f x)
    (hH : ∀ y ∈ segment ℝ x z, ‖fderiv ℝ (fderiv ℝ m) y‖ ≤ β) :
    let κ := min (P.upperSlope * P.radiusFraction / 2)
      (2 * P.upperSlope * (1 - P.lowerSlope))
    0 < κ ∧
    κ * criticality C f x 1 * min (criticality C f x 1 / β) (min Δ 1) ≤ m x - m z ∧
    P.upperSlope * |⟪gradient f x, z - x⟫| ≤ m x - m z := by
  have he : x + (z - x) = z := by abel
  have ht := norm_sub_firstOrder_le_of_hessian_bound (s := z - x)
    (convex_segment x z) (left_mem_segment ℝ x z)
    (by rw [he]; exact right_mem_segment ℝ x z)
    (fun y _ ↦ hm y) (fun y _ ↦ hdm y) hH
  rw [he, hgrad, ← inner_gradient_left, Real.norm_eq_abs] at ht
  apply theorem_12_2_2_of_taylor_bound P hclosed hconv hx hΔ hβ hpoint
  exact (le_abs_self _).trans (ht.trans_eq (by ring))

/-- The capped first-order criticality measure (12.2.15). -/
noncomputable def cappedCriticality (C : Set E) (f : E → ℝ) (x : E) : ℝ :=
  min 1 (criticality C f x 1)

/-- The decrease bound gives the sufficient-decrease test with the capped
criticality measure and the conventional curvature denominator `β ≥ 1`. -/
theorem cappedCriticality_decrease {C : Set E} {f : E → ℝ} {x : E}
    (hx : x ∈ C) {κ β Δ D : ℝ} (hκ : 0 ≤ κ) (hβ : 1 ≤ β) (hΔ : 0 ≤ Δ)
    (h : κ * criticality C f x 1 * min (criticality C f x 1 / β) (min Δ 1) ≤ D) :
    κ * cappedCriticality C f x * min (cappedCriticality C f x / β) Δ ≤ D := by
  let π := cappedCriticality C f x
  let χ := criticality C f x 1
  have hχ : 0 ≤ χ := linearDecrease_nonneg hx zero_le_one
  have hπ : π ≤ χ := min_le_right _ _
  have hp : π / β ≤ 1 := (div_le_one (zero_lt_one.trans_le hβ)).mpr
    ((min_le_left _ _).trans hβ)
  have hmin : min (π / β) Δ ≤ min (χ / β) (min Δ 1) :=
    le_min ((min_le_left _ _).trans (div_le_div_of_nonneg_right hπ (by linarith)))
      (le_min (min_le_right _ _) ((min_le_left _ _).trans hp))
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hπ hκ) hmin
    (le_min (div_nonneg (le_min zero_le_one hχ) (by linarith)) hΔ)
    (mul_nonneg hκ hχ)).trans h

/-- The printed Theorem 12.2.1 needs a descent assumption on the model.
With opposite gradients, every positive projected trial fails (12.2.1).
The feasible set is the whole line, which can be described by the constant
strictly feasible constraint `1 ≥ 0`. -/
theorem theorem_12_2_1_without_model_gradient_agreement_counterexample
    (P : GeneralizedCauchyParams) :
    ContDiff ℝ 2 (id : ℝ → ℝ) ∧ ContDiff ℝ 2 (fun y : ℝ ↦ -y) ∧
    ∀ z, ¬ IsApproxGeneralizedCauchyPoint P Set.univ id (fun y : ℝ ↦ -y) 0 1 z := by
  refine ⟨contDiff_id, contDiff_id.neg, ?_⟩
  intro z hz
  obtain ⟨t, ht, rfl, _, hm, _⟩ := hz
  have hg : gradient (id : ℝ → ℝ) 0 = 1 := by rw [gradient_eq_deriv', deriv_id]
  have hp : projectedGradientPath Set.univ (id : ℝ → ℝ) 0 t = -t := by
    unfold projectedGradientPath projectedRay
    rw [hg]
    simp only [smul_eq_mul, mul_neg, mul_one, zero_add]
    apply (bestApprox_eq_iff ⟨0, Set.mem_univ _⟩ isClosed_univ
      (convex_univ : Convex ℝ (Set.univ : Set ℝ))).2
    exact ⟨Set.mem_univ _, by simp⟩
  rw [hp, hg] at hm
  simp only [neg_neg, neg_zero, sub_zero, zero_add, Real.inner_apply, one_mul] at hm
  nlinarith [mul_pos P.upper_pos ht]

/-- A bracket state for Algorithm 12.2.2. A missing upper endpoint
indicates that the algorithm is still doubling its trial parameter. -/
structure CauchySearchState where
  lo : ℝ
  hi : Option ℝ
  trial : ℝ

/-- The two test branches of Algorithm 12.2.2, with accepted states
retained so that the iteration is defined at every natural index. -/
noncomputable def cauchySearchStep (U L : ℝ → ℝ) (endpoint : ℝ → Prop)
    (s : CauchySearchState) : CauchySearchState :=
  open Classical in
  if U s.trial ≤ 0 then
    if 0 ≤ L s.trial ∨ endpoint s.trial then s else
      ⟨s.trial, s.hi, match s.hi with
        | none => 2 * s.trial
        | some b => (s.trial + b) / 2⟩
  else
    ⟨s.lo, some s.trial, (s.lo + s.trial) / 2⟩

/-- The bracket sequence of Algorithm 12.2.2. -/
noncomputable def cauchySearchIterate (U L : ℝ → ℝ) (endpoint : ℝ → Prop) (t₀ : ℝ) :
    ℕ → CauchySearchState
  | 0 => ⟨0, none, t₀⟩
  | k + 1 => cauchySearchStep U L endpoint (cauchySearchIterate U L endpoint t₀ k)

/-- An infinite nonterminating trace of Algorithm 12.2.2. The upper test
passes when `U ≤ 0`, the two scalar stopping tests pass when `0 ≤ L`,
and `endpoint` is the remaining stopping test. -/
structure InfiniteCauchySearch (U L : ℝ → ℝ) (endpoint : ℝ → Prop) where
  lo : ℕ → ℝ
  hi : ℕ → Option ℝ
  trial : ℕ → ℝ
  trial_initial_pos : 0 < trial 0
  lo_initial : lo 0 = 0
  hi_initial : hi 0 = none
  no_stop : ∀ k, U (trial k) ≤ 0 → L (trial k) < 0 ∧ ¬endpoint (trial k)
  pass : ∀ k, U (trial k) ≤ 0 → lo (k + 1) = trial k ∧ hi (k + 1) = hi k
  fail : ∀ k, 0 < U (trial k) → lo (k + 1) = lo k ∧ hi (k + 1) = some (trial k)
  next : ∀ k, trial (k + 1) =
    match hi (k + 1) with
    | none => 2 * trial k
    | some b => (lo (k + 1) + b) / 2

/-- If infinite nonterminating traces are impossible, the iterate sequence
reaches a positive parameter satisfying both stopping tests. -/
theorem exists_cauchySearch_accept {U L : ℝ → ℝ} {endpoint : ℝ → Prop}
    (hfinite : IsEmpty (InfiniteCauchySearch U L endpoint)) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ k, let t := (cauchySearchIterate U L endpoint t₀ k).trial
      0 < t ∧ U t ≤ 0 ∧ (0 ≤ L t ∨ endpoint t) := by
  classical
  let s := cauchySearchIterate U L endpoint t₀
  have hs (k : ℕ) : 0 ≤ (s k).lo ∧ 0 < (s k).trial ∧
      ∀ b, (s k).hi = some b → 0 < b := by
    induction k with
    | zero => exact ⟨le_rfl, ht₀, fun b h ↦ by simp [s, cauchySearchIterate] at h⟩
    | succ k ih =>
      change _ ∧ _ ∧ ∀ b, (cauchySearchStep U L endpoint (s k)).hi = some b → 0 < b
      change 0 ≤ (cauchySearchStep U L endpoint (s k)).lo ∧
        0 < (cauchySearchStep U L endpoint (s k)).trial ∧ _
      unfold cauchySearchStep
      split_ifs with hu ha
      · exact ih
      · refine ⟨ih.2.1.le, ?_, ih.2.2⟩
        cases hh : (s k).hi with
        | none => exact mul_pos (by norm_num) ih.2.1
        | some b => exact half_pos (add_pos ih.2.1 (ih.2.2 b hh))
      · refine ⟨ih.1, half_pos (add_pos_of_nonneg_of_pos ih.1 ih.2.1), ?_⟩
        intro b hb
        exact (Option.some.inj hb) ▸ ih.2.1
  by_contra h
  have hno (k : ℕ) (hu : U (s k).trial ≤ 0) : ¬(0 ≤ L (s k).trial ∨ endpoint (s k).trial) := by
    intro ha
    exact h ⟨k, (hs k).2.1, hu, ha⟩
  have hstop (k : ℕ) (hpass : U (s k).trial ≤ 0) :
      L (s k).trial < 0 ∧ ¬endpoint (s k).trial :=
    ⟨lt_of_not_ge fun hL ↦ hno k hpass (Or.inl hL), fun he ↦ hno k hpass (Or.inr he)⟩
  have hpass (k : ℕ) (hu : U (s k).trial ≤ 0) :
      s (k + 1) = ⟨(s k).trial, (s k).hi, match (s k).hi with
        | none => 2 * (s k).trial
        | some b => ((s k).trial + b) / 2⟩ := by
    change cauchySearchStep U L endpoint (s k) = _
    rw [cauchySearchStep, ite_eq_left hu, ite_eq_right (hno k hu)]
  have hfail (k : ℕ) (hu : 0 < U (s k).trial) :
      s (k + 1) = ⟨(s k).lo, some (s k).trial, ((s k).lo + (s k).trial) / 2⟩ := by
    change cauchySearchStep U L endpoint (s k) = _
    rw [cauchySearchStep, ite_eq_right (not_le_of_gt hu)]
  apply hfinite.false
  refine { lo := fun k ↦ (s k).lo, hi := fun k ↦ (s k).hi, trial := fun k ↦ (s k).trial
           trial_initial_pos := ht₀, lo_initial := rfl, hi_initial := rfl, no_stop := hstop
           pass := ?_, fail := ?_, next := ?_ }
  · intro k h
    rw [hpass k h]
    exact ⟨rfl, rfl⟩
  · intro k h
    rw [hfail k h]
    exact ⟨rfl, rfl⟩
  · intro k
    rcases le_or_gt (U (s k).trial) 0 with h | h
    · rw [hpass k h]
    · rw [hfail k h]

/-- The doubling and bisection argument of Theorem 12.2.1. A failed upper
endpoint and a passed lower endpoint cannot accumulate at the same
positive parameter when failure of the scalar stopping tests forces
strict satisfaction of the upper test. -/
theorem not_infiniteCauchySearch {U L : ℝ → ℝ} {endpoint : ℝ → Prop}
    (hU : Continuous U) (hL : Continuous L) (hL₀ : L 0 ≤ 0)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ∀ t, 0 < t → t < ε → U t ≤ 0)
    (hsep : ∀ t > 0, L t ≤ 0 → U t < 0)
    (hlarge : ∀ᶠ t in atTop, U t ≤ 0 → 0 ≤ L t ∨ endpoint t) :
    IsEmpty (InfiniteCauchySearch U L endpoint) := by
  constructor
  intro R
  have hinv (k : ℕ) :
      0 ≤ R.lo k ∧ R.lo k < R.trial k ∧ L (R.lo k) ≤ 0 ∧
      (∀ b, R.hi k = some b →
        R.trial k < b ∧ 0 < U b ∧ R.trial k = (R.lo k + b) / 2) := by
    induction k with
    | zero =>
      rw [R.lo_initial, R.hi_initial]
      exact ⟨le_rfl, R.trial_initial_pos, hL₀, fun b h ↦ by simp at h⟩
    | succ k ih =>
      obtain ⟨hlo, hlt, hLlo, hhi⟩ := ih
      have ht := hlo.trans_lt hlt
      by_cases hp : U (R.trial k) ≤ 0
      · obtain ⟨hla, hha⟩ := R.pass k hp
        have hLa := (R.no_stop k hp).1.le
        rw [hla]
        cases hk : R.hi k with
        | none =>
          have hh : R.hi (k + 1) = none := hha.trans hk
          have hn := R.next k
          rw [hh] at hn
          change R.trial (k + 1) = 2 * R.trial k at hn
          rw [hn]
          exact ⟨ht.le, by linarith, hLa, fun b h ↦ by rw [hh] at h; simp at h⟩
        | some b =>
          have hh : R.hi (k + 1) = some b := hha.trans hk
          obtain ⟨hbt, hbU, _⟩ := hhi b hk
          have hn := R.next k
          rw [hh, hla] at hn
          change R.trial (k + 1) = (R.trial k + b) / 2 at hn
          refine ⟨ht.le, by linarith, hLa, fun c hc ↦ ?_⟩
          have he : b = c := Option.some.inj (hh.symm.trans hc)
          subst c
          exact ⟨by linarith, hbU, hn⟩
      · obtain ⟨hla, hha⟩ := R.fail k (lt_of_not_ge hp)
        have hn := R.next k
        rw [hha, hla] at hn
        change R.trial (k + 1) = (R.lo k + R.trial k) / 2 at hn
        rw [hla]
        refine ⟨hlo, by linarith, hLlo, fun b hb ↦ ?_⟩
        have he := Option.some.inj (hha.symm.trans hb)
        subst b
        exact ⟨by linarith, lt_of_not_ge hp, hn⟩
  by_cases hall : ∀ k, R.hi k = none
  · have hpass (k : ℕ) : U (R.trial k) ≤ 0 := by
      by_contra! h
      have hh := (R.fail k h).2
      rw [hall] at hh
      simp at hh
    have hpow (k : ℕ) : R.trial k = (2 : ℝ) ^ k * R.trial 0 := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hn := R.next k
        rw [hall] at hn
        change R.trial (k + 1) = 2 * R.trial k at hn
        rw [hn, ih, pow_succ', mul_assoc]
    have ht : Tendsto R.trial atTop atTop := by
      exact ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
        R.trial_initial_pos).congr (fun k ↦ (hpow k).symm)
    obtain ⟨k, hk⟩ := (ht.eventually hlarge).exists
    exact (hk (hpass k)).elim (not_le_of_gt (R.no_stop k (hpass k)).1)
      (R.no_stop k (hpass k)).2
  push Not at hall
  obtain ⟨N, hN⟩ := hall
  let A (k : ℕ) := R.lo (N + k)
  let B (k : ℕ) := (R.hi (N + k)).getD 0
  have hsome (k : ℕ) : R.hi (N + k) = some (B k) := by
    induction k with
    | zero =>
      change R.hi N = some ((R.hi N).getD 0)
      cases h : R.hi N with
      | none => exact (hN h).elim
      | some b => rfl
    | succ k ih =>
      rw [Nat.add_succ]
      rcases le_or_gt (U (R.trial (N + k))) 0 with h | h
      · have he := (R.pass (N + k) h).2.trans ih
        change R.hi (N + k + 1) = some ((R.hi (N + k + 1)).getD 0)
        rw [he]
        rfl
      · have he := (R.fail (N + k) h).2
        change R.hi (N + k + 1) = some ((R.hi (N + k + 1)).getD 0)
        rw [he]
        rfl
  have hbounds (k : ℕ) :
      A k < B k ∧ L (A k) ≤ 0 ∧ 0 < U (B k) ∧ R.trial (N + k) = (A k + B k) / 2 := by
    obtain ⟨_, hlt, hLa, hhi⟩ := hinv (N + k)
    obtain ⟨hbt, hbU, hmid⟩ := hhi (B k) (hsome k)
    exact ⟨hlt.trans hbt, hLa, hbU, hmid⟩
  have hrec (k : ℕ) : B (k + 1) - A (k + 1) = (B k - A k) / 2 ∧
      A k ≤ A (k + 1) ∧ B (k + 1) ≤ B k := by
    have hmid := (hbounds k).2.2.2
    have hle := (hbounds k).1.le
    rcases le_or_gt (U (R.trial (N + k))) 0 with h | h
    · obtain ⟨ha, hb⟩ := R.pass (N + k) h
      have ha' : A (k + 1) = R.trial (N + k) := by simpa only [A, Nat.add_succ] using ha
      have hb' : B (k + 1) = B k := by
        change (R.hi (N + k + 1)).getD 0 = _
        rw [hb]
      rw [ha', hb', hmid]
      exact ⟨by ring, by linarith, le_rfl⟩
    · obtain ⟨ha, hb⟩ := R.fail (N + k) h
      have ha' : A (k + 1) = A k := by simpa only [A, Nat.add_succ] using ha
      have hb' : B (k + 1) = R.trial (N + k) := by
        change (R.hi (N + k + 1)).getD 0 = _
        rw [hb]
        rfl
      rw [ha', hb', hmid]
      exact ⟨by ring, le_rfl, by linarith⟩
  have hAm : Monotone A := monotone_nat_of_le_succ fun k ↦ (hrec k).2.1
  have hBm : Antitone B := antitone_nat_of_succ_le fun k ↦ (hrec k).2.2
  have hAb : BddAbove (Set.range A) := ⟨B 0, by
    rintro _ ⟨k, rfl⟩
    exact (hbounds k).1.le.trans (hBm (Nat.zero_le k))⟩
  have hBb : BddBelow (Set.range B) := ⟨A 0, by
    rintro _ ⟨k, rfl⟩
    exact (hAm (Nat.zero_le k)).trans (hbounds k).1.le⟩
  have hAl := tendsto_atTop_ciSup hAm hAb
  have hBl := tendsto_atTop_ciInf hBm hBb
  have hwidth (k : ℕ) : B k - A k = (B 0 - A 0) * (1 / 2 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [(hrec k).1, ih, pow_succ]; ring
  have hwidthlim : Tendsto (fun k ↦ B k - A k) atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num)).const_mul (B 0 - A 0)
    rw [mul_zero] at ht
    exact ht.congr (fun k ↦ (hwidth k).symm)
  have heq : (⨅ k, B k) = ⨆ k, A k :=
    sub_eq_zero.mp (tendsto_nhds_unique (hBl.sub hAl) hwidthlim)
  let τ := ⨅ k, B k
  have htB (k : ℕ) : ε ≤ B k := by
    by_contra! hlt
    have hh := (hinv (N + k)).1.trans_lt (hinv (N + k)).2.1
    have hpos := hh.trans ((hinv (N + k)).2.2.2 (B k) (hsome k)).1
    exact (not_le_of_gt (hbounds k).2.2.1) (hsmall (B k) hpos hlt)
  have hτ : 0 < τ := hε.trans_le (le_ciInf htB)
  have hAL : L τ ≤ 0 := by
    have hA' : Tendsto A atTop (𝓝 τ) := by dsimp [τ]; rwa [heq]
    exact le_of_tendsto ((hL.continuousAt.tendsto).comp hA')
      (Eventually.of_forall fun k ↦ (hbounds k).2.1)
  have hBU : 0 ≤ U τ :=
    ge_of_tendsto' ((hU.continuousAt.tendsto).comp hBl) (fun k ↦ (hbounds k).2.2.1.le)
  exact (not_lt_of_ge hBU) (hsep τ hτ hAL)

/-- Corrected Theorem 12.2.1. At a noncritical base point, agreement of
the model gradient with the objective gradient ensures that every sufficiently
small positive trial passes the upper tests. The projected-path line search
then has no infinite nonterminating trace. A critical base point can be
returned directly, avoiding initialization by division by a zero gradient. -/
theorem theorem_12_2_1 (P : GeneralizedCauchyParams) {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {f m : E → ℝ} {x : E} (hx : x ∈ C)
    (hncrit : -gradient f x ∉ normalDirections C x) {Δ : ℝ} (hΔ : 0 < Δ)
    (hm : Continuous m) (hmd : DifferentiableAt ℝ m x)
    (hgrad : fderiv ℝ m x = fderiv ℝ f x) :
    let z := projectedGradientPath C f x
    let r := fun t ↦ ‖z t - x‖
    let l := fun t ↦ ⟪gradient f x, z t - x⟫
    let U := fun t ↦ max (r t - Δ) (m (z t) - m x - P.upperSlope * l t)
    let L := fun t ↦ max (r t - P.radiusFraction * Δ) (m (z t) - m x - P.lowerSlope * l t)
    let endpoint := fun t ↦
      ‖bestApprox (tangentDirections C (z t)) (-gradient f x)‖ ≤ P.endpointFactor * (|l t| / Δ)
    IsEmpty (InfiniteCauchySearch U L endpoint) := by
  let g := gradient f x
  let z := projectedGradientPath C f x
  let d (t : ℝ) := z t - x
  let r (t : ℝ) := ‖d t‖
  let l (t : ℝ) := ⟪g, d t⟫
  let U (t : ℝ) := max (r t - Δ) (m (z t) - m x - P.upperSlope * l t)
  let L (t : ℝ) := max (r t - P.radiusFraction * Δ) (m (z t) - m x - P.lowerSlope * l t)
  let endpoint (t : ℝ) :=
    ‖bestApprox (tangentDirections C (z t)) (-g)‖ ≤ P.endpointFactor * (|l t| / Δ)
  change IsEmpty (InfiniteCauchySearch U L endpoint)
  have hz (t : ℝ) : z t ∈ C := projectedRay_mem ⟨x, hx⟩ hclosed hconv x (-g) t
  have hz₀ : z 0 = x := by
    change bestApprox C (x + (0 : ℝ) • (-g)) = x
    rw [zero_smul, add_zero]
    exact (bestApprox_eq_iff ⟨x, hx⟩ hclosed hconv).2 ⟨hx, by simp⟩
  have hcont : Continuous z :=
    (lipschitzWith_bestApprox ⟨x, hx⟩ hclosed hconv).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hrc : Continuous r := (hcont.sub continuous_const).norm
  have hlc : Continuous l := continuous_const.inner (hcont.sub continuous_const)
  have hUc : Continuous U := (hrc.sub continuous_const).max
    (((hm.comp hcont).sub continuous_const).sub (continuous_const.mul hlc))
  have hLc : Continuous L := (hrc.sub continuous_const).max
    (((hm.comp hcont).sub continuous_const).sub (continuous_const.mul hlc))
  have hL₀ : L 0 ≤ 0 := by
    simp [L, r, l, d, hz₀, P.fraction_pos.le, hΔ.le, mul_nonneg]
  have hproj (t : ℝ) : r t ^ 2 ≤ t * (-l t) := by
    have hn := mem_normalDirections.mp
      (projectedRay_residual_mem_normal ⟨x, hx⟩ hclosed hconv x (-g) t) x hx
    change ⟪x + t • (-g) - z t, x - z t⟫ ≤ 0 at hn
    rw [show x + t • (-g) - z t = t • (-g) - d t by dsimp [d]; abel,
      show x - z t = -(d t) by dsimp [d]; abel, inner_neg_right, inner_sub_left,
      real_inner_smul_left, inner_neg_left, real_inner_self_eq_norm_sq] at hn
    change r t ^ 2 ≤ t * (-l t)
    linarith only [hn]
  have hneg (t : ℝ) (ht : 0 < t) : l t < 0 := by
    have hd : d t ≠ 0 := by
      intro h
      have he : z t = x := sub_eq_zero.mp h
      have hn := projectedRay_residual_mem_normal ⟨x, hx⟩ hclosed hconv x (-g) t
      change x + t • (-g) - z t ∈ normalDirections C (z t) at hn
      rw [he, add_sub_cancel_left] at hn
      apply hncrit
      apply mem_normalDirections.mpr
      intro y hy
      have hh := mem_normalDirections.mp hn y hy
      rw [real_inner_smul_left] at hh
      exact nonpos_of_mul_nonpos_right hh ht
    have hpos : 0 < r t ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
    exact neg_pos.mp (pos_of_mul_pos_right (hpos.trans_le (hproj t)) ht.le)
  have hsep (t : ℝ) (ht : 0 < t) (h : L t ≤ 0) : U t < 0 := by
    obtain ⟨hr, hl⟩ := max_le_iff.mp h
    have hgap := mul_pos (sub_pos.mpr P.slope_order) (neg_pos.mpr (hneg t ht))
    apply max_lt_iff.mpr
    exact ⟨by nlinarith [mul_pos (sub_pos.mpr P.fraction_lt_one) hΔ], by linarith⟩
  have hlabs (t : ℝ) (ht : 0 ≤ t) : criticality C f x (r t) = -l t := by
    have hmin := (theorem_12_1_4 hclosed hconv (f := f) hx ht).2.1
    have he : x + d t = z t := by dsimp [d]; abel
    change linearDecrease C x (-g) (r t) = -l t
    rw [← show ⟪-g, d t⟫ = -l t from inner_neg_left _ _]
    apply le_antisymm _ (inner_le_linearDecrease (he ▸ hz t) le_rfl)
    apply linearDecrease_le hx (norm_nonneg _)
    intro v hv hvn
    simpa only [inner_neg_left, neg_le_neg_iff] using (isMinOn_iff.mp hmin) v ⟨hv, hvn⟩
  have hu : P.upperSlope < 1 := P.slope_order.trans P.lower_lt_one
  let χ := criticality C f x 1
  have hχ : 0 < χ := lt_of_le_of_ne (linearDecrease_nonneg hx zero_le_one)
    (fun he ↦ hncrit ((linearDecrease_eq_zero_iff hconv hx).mp he.symm))
  have hr₀ : r 0 = 0 := by simp [r, d, hz₀]
  have hrnear : ∀ᶠ t in 𝓝 (0 : ℝ), r t < min Δ 1 := by
    have ht := hrc.continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, hr₀] at ht
    exact ht.eventually (gt_mem_nhds (lt_min hΔ zero_lt_one))
  have hznear : Tendsto z (𝓝 0) (𝓝 x) := by
    have ht := hcont.continuousAt (x := (0 : ℝ))
    rwa [ContinuousAt, hz₀] at ht
  let γ := (1 - P.upperSlope) * χ
  have hγ : 0 < γ := mul_pos (sub_pos.mpr hu) hχ
  have hrem := hmd.hasFDerivAt.isLittleO.bound hγ
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), r t < min Δ 1 ∧
      ‖m (z t) - m x - fderiv ℝ m x (z t - x)‖ ≤ γ * r t :=
    hrnear.and (hznear.eventually hrem)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsmall (t : ℝ) (ht : 0 < t) (htε : t < ε) : U t ≤ 0 := by
    have htball : t ∈ Metric.ball (0 : ℝ) ε := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htε
    obtain ⟨hr, he⟩ := hball htball
    have hrpos : 0 < r t := by
      apply norm_pos_iff.mpr
      intro hd
      have hlt := hneg t ht
      change ⟪g, d t⟫ < 0 at hlt
      rw [hd, inner_zero_right] at hlt
      exact (lt_irrefl 0) hlt
    have hc := (theorem_12_1_5 (f := f) hconv hx).2.1
      (show r t ∈ Set.Ioi 0 from hrpos)
      (show (1 : ℝ) ∈ Set.Ioi 0 from (zero_lt_one : (0 : ℝ) < 1))
      (hr.le.trans (min_le_right _ _))
    change χ / 1 ≤ criticality C f x (r t) / r t at hc
    rw [div_one, hlabs t ht.le] at hc
    have hχr : χ * r t ≤ -l t := (le_div_iff₀ hrpos).mp hc
    have herror : m (z t) - m x - l t ≤ γ * r t := by
      rw [hgrad, ← inner_gradient_left, Real.norm_eq_abs] at he
      exact (le_abs_self _).trans he
    have hγr : γ * r t ≤ (1 - P.upperSlope) * (-l t) := by
      dsimp [γ]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hχr (sub_nonneg.mpr hu.le)
    exact max_le_iff.mpr ⟨sub_nonpos.mpr (hr.le.trans (min_le_left _ _)), by linarith⟩
  have hlarge : ∀ᶠ t in atTop, U t ≤ 0 → 0 ≤ L t ∨ endpoint t := by
    let e := P.endpointFactor * (-l 1)
    have he : 0 < e := mul_pos P.endpoint_pos (neg_pos.mpr (hneg 1 zero_lt_one))
    filter_upwards [eventually_ge_atTop (max 1 (Δ ^ 2 / e))] with t ht hu
    right
    have ht₁ := (le_max_left _ _).trans ht
    have ht₀ := zero_lt_one.trans_le ht₁
    have hrΔ : r t ≤ Δ := sub_nonpos.mp (max_le_iff.mp hu).1
    have hmon := (theorem_12_1_3 hclosed hconv (f := f) hx).1
      (show (1 : ℝ) ∈ Set.Ici 0 from (zero_le_one : (0 : ℝ) ≤ 1))
      (show t ∈ Set.Ici 0 from ht₀.le) ht₁
    have hlmono : -l 1 ≤ -l t := by
      rw [← hlabs 1 zero_le_one, ← hlabs t ht₀.le]
      exact linearDecrease_mono_radius hx (norm_nonneg _) hmon
    have hΔt : Δ / t ≤ e / Δ := by
      apply (div_le_div_iff₀ ht₀ hΔ).mpr
      have hh := (div_le_iff₀ he).mp ((le_max_right _ _).trans ht)
      nlinarith only [hh]
    have htan := norm_tangentProjection_projectedRay_le ⟨x, hx⟩ hclosed hconv x (-g) ht₀
    change ‖bestApprox (tangentDirections C (z t)) (-g)‖ ≤ r t / t at htan
    change ‖bestApprox (tangentDirections C (z t)) (-g)‖ ≤ P.endpointFactor * (|l t| / Δ)
    rw [abs_of_neg (hneg t ht₀), ← mul_div_assoc]
    exact htan.trans ((div_le_div_of_nonneg_right hrΔ ht₀.le).trans
      (hΔt.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlmono P.endpoint_pos.le) hΔ.le)))
  exact not_infiniteCauchySearch hUc hLc hL₀ hε hsmall hsep hlarge

/-- Algorithm 12.2.2 reaches an approximate generalized Cauchy point at
a finite index for every positive initial trial parameter. -/
theorem theorem_12_2_1_terminates (P : GeneralizedCauchyParams) {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {f m : E → ℝ} {x : E} (hx : x ∈ C)
    (hncrit : -gradient f x ∉ normalDirections C x) {Δ : ℝ} (hΔ : 0 < Δ)
    (hm : Continuous m) (hmd : DifferentiableAt ℝ m x)
    (hgrad : fderiv ℝ m x = fderiv ℝ f x)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    let z := projectedGradientPath C f x
    let r := fun t ↦ ‖z t - x‖
    let l := fun t ↦ ⟪gradient f x, z t - x⟫
    let U := fun t ↦ max (r t - Δ) (m (z t) - m x - P.upperSlope * l t)
    let L := fun t ↦ max (r t - P.radiusFraction * Δ) (m (z t) - m x - P.lowerSlope * l t)
    let endpoint := fun t ↦
      ‖bestApprox (tangentDirections C (z t)) (-gradient f x)‖ ≤ P.endpointFactor * (|l t| / Δ)
    ∃ k, IsApproxGeneralizedCauchyPoint P C f m x Δ
      (z (cauchySearchIterate U L endpoint t₀ k).trial) := by
  have hfinite := theorem_12_2_1 P hclosed hconv hx hncrit hΔ hm hmd hgrad
  obtain ⟨k, ht, hu, hl⟩ := exists_cauchySearch_accept hfinite ht₀
  dsimp only at ht hu hl ⊢
  obtain ⟨hR, hmU⟩ := max_le_iff.mp hu
  refine ⟨k, _, ht, rfl, sub_nonpos.mp hR, by linarith, ?_⟩
  rcases hl with hl | he
  · rcases le_max_iff.mp hl with hR' | hmL
    · exact Or.inl (sub_nonneg.mp hR')
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr he)

/-- A first-order critical base point already satisfies the generalized
Cauchy tests and can be returned before initializing the search. -/
theorem isApproxGeneralizedCauchyPoint_of_normal (P : GeneralizedCauchyParams)
    {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C) {f m : E → ℝ} {x : E}
    (hx : x ∈ C) (hn : -gradient f x ∈ normalDirections C x) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    IsApproxGeneralizedCauchyPoint P C f m x Δ x := by
  have hp : projectedGradientPath C f x 1 = x :=
    (projectedRay_eq_self_iff ⟨x, hx⟩ hclosed hconv hx).2 hn 1 zero_le_one
  refine ⟨1, zero_lt_one, hp.symm, ?_, ?_, Or.inr (Or.inl ?_)⟩ <;>
    simp [hΔ]

end ConnGouldToint.Chapter12
