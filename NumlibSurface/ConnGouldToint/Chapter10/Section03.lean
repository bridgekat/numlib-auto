/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis
import Numlib.Krylov.CG
import Numlib.Optimization.Subproblem.TrustRegion
import NumlibSurface.ConnGouldToint.Chapter06.Section06

/-! # Gradient-related backtracking directions -/

open Filter Topology Set
open ConnGouldToint.Chapter06
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem 10.3.2. Adding a nonascending correction to a Cauchy step
preserves a quantitative gradient angle. The two norm comparisons avoid
assuming the Cauchy radius in Euclidean norm bounds the final step norm. -/
theorem theorem_10_3_2 {g d w s : E} {t κ e β B ν Δ D K : ℝ}
    (hd : 0 < ‖d‖) (hκ : 0 < κ) (he : 0 < e) (hβ : 0 < β) (hβB : β ≤ B)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D) (hK : 0 < K) (hν : 1 / K ≤ ν)
    (hstep : ‖s‖ ≤ K * Δ) (hs : s = -t • d + w)
    (hw : ⟪g, w⟫ ≤ 0) (hangle : e * ‖g‖ * ‖d‖ ≤ ⟪g, d⟫)
    (ht : κ * min (e * ‖g‖ / (β * ‖d‖)) (ν * Δ / ‖d‖) ≤ t) :
    (κ * e * min (e * ‖g‖ / (B * K * D)) (1 / K ^ 2)) * ‖g‖ * ‖s‖ ≤ -⟪g, s⟫ := by
  have hB := hβ.trans_le hβB
  have hD := hΔ.trans_le hΔD
  have hν₀ := (one_div_pos.mpr hK).trans_le hν
  have ht₀ : 0 ≤ t := (mul_nonneg hκ.le (le_min (by positivity) (by positivity))).trans ht
  have htime : κ * min (e * ‖g‖ / β) (ν * Δ) ≤ t * ‖d‖ := by
    have h := mul_le_mul_of_nonneg_right ht hd.le
    rw [mul_assoc, min_mul_of_nonneg _ _ hd.le, div_mul_eq_mul_div,
      div_mul_cancel₀ _ hd.ne'] at h
    have heq : e * ‖g‖ * ‖d‖ / (β * ‖d‖) = e * ‖g‖ / β := by field_simp
    simpa only [heq] using h
  have hbound₁ : (e * ‖g‖ / (B * K * D)) * ‖s‖ ≤ e * ‖g‖ / β := by
    calc
      _ ≤ (e * ‖g‖ / (B * K * D)) * (K * D) :=
        mul_le_mul_of_nonneg_left (hstep.trans (mul_le_mul_of_nonneg_left hΔD hK.le))
          (by positivity)
      _ = e * ‖g‖ / B := by field_simp
      _ ≤ e * ‖g‖ / β := div_le_div_of_nonneg_left (by positivity) hβ hβB
  have hbound₂ : (1 / K ^ 2) * ‖s‖ ≤ ν * Δ := by
    calc
      _ ≤ (1 / K ^ 2) * (K * Δ) := mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (1 / K) * Δ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hν hΔ.le
  have hmin : min (e * ‖g‖ / (B * K * D)) (1 / K ^ 2) * ‖s‖ ≤
      min (e * ‖g‖ / β) (ν * Δ) := by
    rw [min_mul_of_nonneg _ _ (norm_nonneg _)]
    exact min_le_min hbound₁ hbound₂
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hκ.le)
    (show 0 ≤ e * ‖g‖ by positivity)
  have h' := mul_le_mul_of_nonneg_left htime (show 0 ≤ e * ‖g‖ by positivity)
  have h'' := mul_le_mul_of_nonneg_left hangle ht₀
  have hgstep : ⟪g, s⟫ = -t * ⟪g, d⟫ + ⟪g, w⟫ := by
    rw [hs, inner_add_right, real_inner_smul_right]
  rw [hgstep]
  nlinarith only [h, h', h'', hw]

/-- Theorem 10.3.3. Each direction computed after a positive-curvature
prefix of unpreconditioned CG has nonpositive inner product with the
initial model gradient. The final direction can trigger truncation. -/
theorem theorem_10_3_3 (H : E →ₗ[ℝ] E) (g : E) (hH : H.IsSymmetric) {j : ℕ}
    (hpos : ∀ i < j, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫) :
    ⟪g, (CG.iterate H (-g) 0 j).p⟫ = -‖(CG.iterate H (-g) 0 j).r‖ ^ 2 := by
  have h := CG.inner_residual_direction_eq_of_pos_prefix (-g) (0 : E) hH
    (fun i hi ↦ by simpa using hpos i hi) (Nat.zero_le j) (le_refl j)
  have hzero : (CG.iterate H (-g) 0 0).r = -g := by rw [CG.residual_eq]; simp
  rw [hzero, inner_neg_left] at h
  change -⟪g, (CG.iterate H (-g) 0 j).p⟫ = ‖(CG.iterate H (-g) 0 j).r‖ ^ 2 at h
  linarith

/-- Corrected Theorem 10.3.4 for a Euclidean ball. The positive
semidefinite shifted Hessian bounds the gradient angle even in the
hard case. The bound uses the radius cap only to make the angle uniform. -/
theorem theorem_10_3_4 {H : E →L[ℝ] E} {g s : E} {Δ D B : ℝ}
    (hH : H.toLinearMap.IsSymmetric) (hΔ : 0 < Δ) (hD : Δ ≤ D)
    (hB : 0 < B) (hHB : ‖H‖ ≤ B) (hs : ‖s‖ ≤ Δ)
    (hmin : IsMinOn (Subproblem.quadModel g H) (Metric.closedBall 0 Δ) s) :
    (1 / 3 : ℝ) * min (‖g‖ / (B * D)) 1 * ‖g‖ * ‖s‖ ≤ -⟪g, s⟫ := by
  obtain ⟨μ, hμ⟩ := (Subproblem.isMinOn_closedBall_iff hH hΔ hs).mp hmin
  let A := H + μ • (1 : E →L[ℝ] E)
  have hA : A.IsPositive := hμ.isPositive
  have hAs : A s = -g := hμ.shifted
  have hquad : 0 ≤ -⟪g, s⟫ := by
    simpa only [hAs, inner_neg_left] using hA.inner_nonneg_left s
  have hnorm : ‖g‖ ^ 2 ≤ ‖A‖ * (-⟪g, s⟫) := by
    simpa only [hAs, norm_neg, inner_neg_left, RCLike.re_to_real] using
      hA.norm_apply_sq_le_norm_mul_re_inner s
  have hAn : ‖A‖ ≤ B + μ := by
    calc
      _ ≤ ‖H‖ + ‖μ • (1 : E →L[ℝ] E)‖ := norm_add_le _ _
      _ ≤ B + μ := by
        rw [norm_smul, Real.norm_of_nonneg hμ.nonneg]
        have hnormOne : ‖(1 : E →L[ℝ] E)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z ↦ by simp)
        exact add_le_add hHB (mul_le_of_le_one_right hμ.nonneg hnormOne)
  have hmult : μ * ‖s‖ ≤ ‖g‖ + B * ‖s‖ := by
    have he : μ • s = -g - H s := by
      have h := hAs
      simp only [A, add_apply, smul_apply, one_apply_eq_self] at h
      rw [← h, add_sub_cancel_left]
    have h := (norm_sub_le (-g) (H s)).trans
      (add_le_add (norm_neg g).le ((H.le_opNorm s).trans
        (mul_le_mul_of_nonneg_right hHB (norm_nonneg _))))
    simpa only [← he, norm_smul, Real.norm_of_nonneg hμ.nonneg] using h
  let p := min (‖g‖ / (B * D)) 1
  have hp : 0 ≤ p := le_min (by positivity [hΔ.trans_le hD]) zero_le_one
  have hp₁ : p ≤ 1 := min_le_right _ _
  have hps : p * (B * ‖s‖) ≤ ‖g‖ := by
    have hBD : 0 < B * D := mul_pos hB (hΔ.trans_le hD)
    have h := (le_div_iff₀ hBD).mp (min_le_left (‖g‖ / (B * D)) 1)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hs.trans hD) hB.le) hp).trans h
  have hscale : p * ‖s‖ * ‖A‖ ≤ 3 * ‖g‖ := by
    have h₁ := mul_le_mul_of_nonneg_left hAn (mul_nonneg hp (norm_nonneg s))
    have h₂ := mul_le_mul_of_nonneg_left hmult hp
    have h₃ := mul_le_of_le_one_left (norm_nonneg g) hp₁
    nlinarith only [h₁, h₂, h₃, hps]
  by_cases hg : g = 0
  · simp [hg]
  have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have h₁ := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hp (norm_nonneg s))
  have h₂ := mul_le_mul_of_nonneg_right hscale hquad
  have h₃ : ‖g‖ * (p * ‖g‖ * ‖s‖) ≤ ‖g‖ * (3 * (-⟪g, s⟫)) := by
    nlinarith only [h₁, h₂]
  have h₄ := le_of_mul_le_mul_left h₃ hgn
  change (1 / 3 : ℝ) * p * ‖g‖ * ‖s‖ ≤ _
  linarith only [h₄]

/-- Uniform equivalence with Euclidean norm does not suffice in
Theorem 10.3.4. On the unit diamond, the smooth quadratic
(u/2-v^2) is minimized at ((0,1)), orthogonal to its nonzero
gradient at the origin. -/
theorem theorem_10_3_4_general_norm_counterexample :
    IsMinOn (fun p : ℝ × ℝ ↦ p.1 / 2 - p.2 ^ 2) {p | |p.1| + |p.2| ≤ 1} (0, 1) ∧
      (0 : ℝ) / 2 = 0 ∧ (1 / 2 : ℝ) ≠ 0 := by
  refine ⟨isMinOn_iff.mpr ?_, by norm_num, by norm_num⟩
  rintro ⟨u, v⟩ (hv : |u| + |v| ≤ 1)
  have hv₁ : |v| ≤ 1 := by linarith [abs_nonneg u]
  have hv₂ : v ^ 2 ≤ |v| := by
    rw [← sq_abs]
    nlinarith only [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hv₁)]
  change (0 : ℝ) / 2 - 1 ^ 2 ≤ u / 2 - v ^ 2
  nlinarith only [hv, hv₂, neg_abs_le u, abs_nonneg u]

/-- With a bounded set of accepted step lengths and acceptance for
sufficiently short steps, a geometric line search over all integer
indices has a first accepted trial. Its predecessor is rejected. -/
theorem exists_first_integer_lineSearch_trial {q r R : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hr : 0 < r) {accept : ℝ → Prop}
    (hsmall : ∀ t, 0 < t → t ≤ r → accept t)
    (hbounded : ∀ t, 0 < t → accept t → t ≤ R) :
    ∃ j : ℤ, accept (q ^ j) ∧ (∀ i : ℤ, i < j → ¬ accept (q ^ i)) ∧
      ¬ accept (q ^ j / q) := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hq'
  have hex : ∃ j : ℤ, accept (q ^ j) :=
    ⟨n, by rw [zpow_natCast]; exact hsmall _ (pow_pos hq _) hn.le⟩
  have hqinv : 1 < q⁻¹ := (one_lt_inv₀ hq).mpr hq'
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt R hqinv
  have hbd : ∃ i : ℤ, ∀ j : ℤ, accept (q ^ j) → i ≤ j := by
    refine ⟨-(N : ℤ), fun j hj ↦ ?_⟩
    by_contra! hj'
    have hle := zpow_le_zpow_right_of_le_one₀ hq hq'.le hj'.le
    rw [zpow_neg, zpow_natCast, ← inv_pow] at hle
    exact hN.not_ge (hle.trans (hbounded _ (zpow_pos hq _) hj))
  obtain ⟨j, hj, hleast⟩ := Int.exists_least_of_bdd hbd hex
  have hrej (i : ℤ) (hi : i < j) : ¬ accept (q ^ i) := fun h ↦ hi.not_ge (hleast i h)
  refine ⟨j, hj, hrej, ?_⟩
  have he : q ^ (j - 1) = q ^ j / q := by rw [zpow_sub₀ hq.ne', zpow_one]
  rw [← he]
  exact hrej _ (by omega)

/-- The Armijo test and its failed predecessor give a uniform first-order
decrease for a direction satisfying (10.3.1). The step length is not capped
at the starting time of the search. -/
theorem doubleLineSearch_first_order_decrease {f : E → ℝ} {x d : E}
    {a D L q b t : ℝ} (ha : 0 < a) (hD : 0 < D) (hL : 0 < L)
    (hq : 0 < q) (hb : 0 < b) (hb' : b < 1) (ht : 0 < t)
    (hf : Differentiable ℝ f)
    (hlip : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖)
    (hslope : fderiv ℝ f x d ≤ -a * ‖fderiv ℝ f x‖ ^ 2)
    (hdir : ‖d‖ ≤ D * ‖fderiv ℝ f x‖)
    (haccept : f (x + t • d) ≤ f x + b * t * fderiv ℝ f x d)
    (hfail : f x + b * (t / q) * fderiv ℝ f x d < f (x + (t / q) • d)) :
    (b * (q * (2 * (1 - b) * a / (L * D ^ 2))) * a) * ‖fderiv ℝ f x‖ ^ 2 ≤
      f x - f (x + t • d) := by
  let u := t / q
  let G := ‖fderiv ℝ f x‖
  have hu : 0 < u := div_pos ht hq
  have hg : 0 < G := by
    by_contra! h
    have he : G = 0 := le_antisymm h (norm_nonneg _)
    have hd : d = 0 := norm_le_zero_iff.mp (hdir.trans (by rw [show ‖fderiv ℝ f x‖ = 0 from he,
      mul_zero]))
    simp [hd] at hfail
  have hTaylor := norm_sub_firstOrder_le_of_lipschitz_on_segment
    (x := x) (s := u • d) (γ := L) (fun _ _ ↦ hf _) (by
      intro v hv
      have h := hlip (x + v • (u • d)) x
      rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hv.1] at h)
  have hT := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hTaylor)
  have hT' : f (x + u • d) - (f x + u * fderiv ℝ f x d) ≤
      L * (u * ‖d‖) ^ 2 / 2 := by
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hu.le] at hT
    nlinarith only [hT]
  have hsq := pow_le_pow_left₀ (norm_nonneg d) hdir 2
  have hT'' := hT'.trans (show L * (u * ‖d‖) ^ 2 / 2 ≤ L * u ^ 2 * D ^ 2 * G ^ 2 / 2 by
    have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ L * u ^ 2 / 2 by positivity)
    nlinarith only [h])
  have hs := mul_le_mul_of_nonneg_left hslope (show 0 ≤ (1 - b) * u by positivity)
  have hfu : f x + b * u * fderiv ℝ f x d < f (x + u • d) := hfail
  have hpos : 0 < u * G ^ 2 := mul_pos hu (sq_pos_of_pos hg)
  have hdu : 2 * (1 - b) * a / (L * D ^ 2) ≤ u := by
    apply (div_le_iff₀ (mul_pos hL (sq_pos_of_pos hD))).mpr
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hT'', hfu, hs]
  have htime : q * (2 * (1 - b) * a / (L * D ^ 2)) ≤ t :=
    (mul_le_mul_of_nonneg_left hdu hq.le).trans_eq (by dsimp [u]; field_simp)
  have h₁ := mul_le_mul_of_nonneg_left htime (show 0 ≤ b * a * G ^ 2 by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hslope (mul_nonneg hb.le ht.le)
  change (b * (q * (2 * (1 - b) * a / (L * D ^ 2))) * a) * G ^ 2 ≤ _
  nlinarith only [h₁, h₂, haccept]

/-- Negative-curvature line search on an unrestricted ray. The first
accepted time, if its predecessor fails, gives the same clipped decrease
as a bounded-radius eigenpoint search with unit length cap. -/
theorem doubleLineSearch_negative_curvature_decrease {ray : ℝ → ℝ}
    {q b κ τ R t g : ℝ} (hq : 0 < q) (hb : 0 < b) (hbκ : b < κ / 2)
    (hτ : τ < 0) (hR : 0 < R) (ht : 0 < t) (hg : g ≤ 0)
    (hTaylor : ∀ u ∈ Ioc (0 : ℝ) 1,
      ray u ≤ ray 0 + u * g + κ / 2 * τ * u ^ 2 + R * u ^ 3)
    (haccept : ray t ≤ ray 0 + b * τ * t ^ 2)
    (hfail : ray 0 + b * τ * (t / q) ^ 2 < ray (t / q)) :
    b * (q * min 1 ((κ / 2 - b) / R)) ^ 2 * (-τ) * min 1 (τ ^ 2) ≤ ray 0 - ray t := by
  let u := t / q
  let A := (κ / 2 - b) / R
  have hA : 0 < A := div_pos (sub_pos.mpr hbκ) hR
  have hu : 0 < u := div_pos ht hq
  have hτ' : 0 < -τ := neg_pos.mpr hτ
  have hs : min 1 (A * (-τ)) ≤ u := by
    by_cases h₁ : 1 ≤ u
    · exact (min_le_left _ _).trans h₁
    have hT := hTaylor u ⟨hu, (lt_of_not_ge h₁).le⟩
    have hlin := mul_nonpos_of_nonneg_of_nonpos hu.le hg
    have hf : ray 0 + b * τ * u ^ 2 < ray u := hfail
    apply (min_le_right _ _).trans
    rw [show A * (-τ) = ((κ / 2 - b) * (-τ)) / R by dsimp [A]; ring]
    apply (div_le_iff₀ hR).mpr
    apply le_of_mul_le_mul_right _ (sq_pos_of_pos hu)
    nlinarith only [hT, hlin, hf]
  have hscale : min 1 A * min 1 (-τ) ≤ min 1 (A * (-τ)) := by
    have hpos := le_min zero_le_one hτ'.le
    exact le_min ((mul_le_of_le_one_left hpos (min_le_left _ _)).trans (min_le_left _ _))
      (mul_le_mul (min_le_right _ _) (min_le_right _ _) hpos hA.le)
  have ht' : q * (min 1 A * min 1 (-τ)) ≤ t :=
    (mul_le_mul_of_nonneg_left (hscale.trans hs) hq.le).trans_eq (by dsimp [u]; field_simp)
  have hsq := pow_le_pow_left₀
    (mul_nonneg hq.le (mul_nonneg (le_min zero_le_one hA.le) (le_min zero_le_one hτ'.le))) ht' 2
  have heq : (min 1 (-τ)) ^ 2 = min 1 (τ ^ 2) := by
    rcases le_total 1 (-τ) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]
      norm_num
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
      ring
  rw [← mul_assoc, mul_pow, heq] at hsq
  have h := mul_le_mul_of_nonneg_left hsq (mul_nonneg hb.le hτ'.le)
  change b * (q * min 1 A) ^ 2 * (-τ) * min 1 (τ ^ 2) ≤ _
  linarith only [h, haccept]

/-- The uncapped Armijo search has a first accepted index at a
nonstationary point in a bounded objective sublevel. A uniform Taylor
bound is needed only to ensure that sufficiently short trials pass. -/
theorem exists_doubleLineSearch_armijo_trial {f : E → ℝ} {x d : E}
    {q b g L : ℝ} (hq : 0 < q) (hq' : q < 1) (hb : 0 < b) (hb' : b < 1)
    (hg : g < 0) (hd : d ≠ 0) (hL : 0 < L)
    (hbound : Bornology.IsBounded {y | f y ≤ f x})
    (hTaylor : ∀ t > (0 : ℝ), f (x + t • d) ≤ f x + t * g + L * t ^ 2) :
    ∃ j : ℤ, f (x + q ^ j • d) ≤ f x + b * q ^ j * g ∧
      (∀ i : ℤ, i < j → f x + b * q ^ i * g < f (x + q ^ i • d)) ∧
      f x + b * (q ^ j / q) * g < f (x + (q ^ j / q) • d) := by
  let accept (t : ℝ) := f (x + t • d) ≤ f x + b * t * g
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hbound
  have hcap (t : ℝ) (ht : 0 < t) (hh : accept t) : t ≤ R / ‖d‖ := by
    have hy : x + t • d ∈ {y | f y ≤ f x} :=
      hh.trans (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hb.le ht.le) hg.le))
    have hdist := hR hy (show x ∈ {y | f y ≤ f x} from by change f x ≤ f x; exact le_rfl)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le] at hdist
    exact (le_div_iff₀ (norm_pos_iff.mpr hd)).mpr hdist
  let r := (1 - b) * (-g) / L
  have hr : 0 < r := div_pos (mul_pos (sub_pos.mpr hb') (neg_pos.mpr hg)) hL
  have hsmall (t : ℝ) (ht : 0 < t) (htr : t ≤ r) : accept t := by
    have hh := mul_le_mul_of_nonneg_right ((le_div_iff₀ hL).mp htr) ht.le
    exact (hTaylor t ht).trans (by nlinarith only [hh])
  obtain ⟨j, hj, hfirst, hpred⟩ := exists_first_integer_lineSearch_trial hq hq' hr hsmall hcap
  exact ⟨j, hj, fun i hi ↦ lt_of_not_ge (hfirst i hi), lt_of_not_ge hpred⟩

/-- The uncapped eigenpoint search has a first accepted index on a
bounded sublevel when the small-time Taylor estimate exhibits negative
curvature. -/
theorem exists_doubleLineSearch_eigen_trial {f : E → ℝ} {x d : E}
    {q b κ τ g R : ℝ} (hq : 0 < q) (hq' : q < 1) (hb : 0 < b) (hbκ : b < κ / 2)
    (hτ : τ < 0) (hg : g ≤ 0) (hd : ‖d‖ = 1) (hR : 0 < R)
    (hbound : Bornology.IsBounded {y | f y ≤ f x})
    (hTaylor : ∀ t ∈ Ioc (0 : ℝ) 1,
      f (x + t • d) ≤ f x + t * g + κ / 2 * τ * t ^ 2 + R * t ^ 3) :
    ∃ j : ℤ, f (x + q ^ j • d) ≤ f x + b * τ * (q ^ j) ^ 2 ∧
      (∀ i : ℤ, i < j → f x + b * τ * (q ^ i) ^ 2 < f (x + q ^ i • d)) ∧
      f x + b * τ * (q ^ j / q) ^ 2 < f (x + (q ^ j / q) • d) := by
  let accept (t : ℝ) := f (x + t • d) ≤ f x + b * τ * t ^ 2
  obtain ⟨U, hU⟩ := Metric.isBounded_iff.mp hbound
  have hcap (t : ℝ) (ht : 0 < t) (hh : accept t) : t ≤ U := by
    have hy : x + t • d ∈ {y | f y ≤ f x} :=
      hh.trans (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hb.le hτ.le) (sq_nonneg _)))
    have hdist := hU hy (show x ∈ {y | f y ≤ f x} from by change f x ≤ f x; exact le_rfl)
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le,
      hd, mul_one] using hdist
  let r := min 1 ((κ / 2 - b) * (-τ) / R)
  have hr : 0 < r := lt_min zero_lt_one (div_pos (mul_pos (sub_pos.mpr hbκ) (neg_pos.mpr hτ)) hR)
  have hsmall (t : ℝ) (ht : 0 < t) (htr : t ≤ r) : accept t := by
    have hh := (le_div_iff₀ hR).mp (htr.trans (min_le_right _ _))
    exact (hTaylor t ⟨ht, htr.trans (min_le_left _ _)⟩).trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg t),
        mul_nonpos_of_nonneg_of_nonpos ht.le hg])
  obtain ⟨j, hj, hfirst, hpred⟩ := exists_first_integer_lineSearch_trial hq hq' hr hsmall hcap
  exact ⟨j, hj, fun i hi ↦ lt_of_not_ge (hfirst i hi), lt_of_not_ge hpred⟩

/-- Any strictly decreasing sequence in a bounded level set has an
exact-model BTR representation with constant radius. Every step is
very successful, so the given iterate sequence is reproduced exactly. -/
noncomputable def exactModelBTRRun {P : BTRParams} {f : E → ℝ} (x : ℕ → E)
    (R : ℝ) (hR : 0 < R) (hstep : ∀ k, ‖x (k + 1) - x k‖ ≤ R)
    (hdrop : ∀ k, 0 < f (x k) - f (x (k + 1))) :
    BTRRun f P (fun _ _ _ _ ↦ True) where
  x := x
  s k := x (k + 1) - x k
  Δ _ := R
  p _ := normSeminorm ℝ E
  norm_separates _ _ h := norm_eq_zero.mp h
  model _ := f
  delta_initial_pos := hR
  feasible k := by
    have he : x k + (x (k + 1) - x k) = x (k + 1) := by abel
    rw [he, mem_trustRegion]
    exact hstep k
  sufficient_decrease _ := trivial
  predicted_pos k := by
    simpa only [show x k + (x (k + 1) - x k) = x (k + 1) by abel] using hdrop k
  iterate_update k := by
    have he : x k + (x (k + 1) - x k) = x (k + 1) := by abel
    have hr : Optimization.reductionRatio f (x k) (x (k + 1) - x k)
        (f (x k) - f (x k + (x (k + 1) - x k))) = 1 := by
      unfold Optimization.reductionRatio
      rw [he, div_self (hdrop k).ne']
    rw [Optimization.acceptStep_of_le (hr ▸ P.eta₁_le_eta₂.trans P.eta₂_lt_one.le), he]
  radius_update k := by
    have he : x k + (x (k + 1) - x k) = x (k + 1) := by abel
    have hr : btrRatio f f (x k) (x (k + 1) - x k) = 1 := by
      unfold btrRatio Optimization.reductionRatio
      rw [he, div_self (hdrop k).ne']
    rw [hr]
    exact ⟨fun _ ↦ le_rfl, fun _ h ↦ (not_lt_of_ge P.eta₂_lt_one.le h).elim,
      fun h ↦ (not_lt_of_ge (P.eta₁_le_eta₂.trans P.eta₂_lt_one.le) h).elim⟩

/-- Theorem 10.3.1. The decrease certificates of the two line searches
give first-order convergence and second-order criticality of every
subsequential limit. The compact level set ensures one exists and bounds
every displacement, so the exact objective serves as the model with a
constant trust-region radius. -/
theorem theorem_10_3_1 [CompleteSpace E] [Nontrivial E]
    {f : E → ℝ} (x : ℕ → E) (hf : ContDiff ℝ 2 f)
    (hcompact : IsCompact {y | f y ≤ f (x 0)}) (hlower : BddBelow (range f))
    {B κ κ₂ : ℝ} (hB : 0 < B) (hκ : 0 < κ) (hκ' : κ < 1) (hκ₂ : 0 < κ₂)
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ B)
    (hdrop : ∀ k, 0 < f (x k) - f (x (k + 1)))
    (hfirst : ∀ k, κ * ‖gradient f (x k)‖ ^ 2 / B ≤ f (x k) - f (x (k + 1)))
    (hsecond : ∀ k, let τ := leastUnitCurvature (fderiv ℝ (fderiv ℝ f) (x k))
      τ < 0 → κ₂ * |τ| * τ ^ 2 ≤ f (x k) - f (x (k + 1))) :
    Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0) ∧
      (∃ z ∈ {y | f y ≤ f (x 0)}, ∃ j : ℕ → ℕ, StrictMono j ∧
        Tendsto (x ∘ j) atTop (𝓝 z) ∧ fderiv ℝ f z = 0 ∧
        ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) z v v) ∧
      ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) →
        fderiv ℝ f z = 0 ∧ ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) z v v := by
  have hmono : Antitone (f ∘ x) := antitone_nat_of_succ_le fun k ↦ sub_nonneg.mp (hdrop k).le
  have hx (k : ℕ) : x k ∈ {y | f y ≤ f (x 0)} := hmono (Nat.zero_le k)
  obtain ⟨R₀, hR₀⟩ := Metric.isBounded_iff.mp hcompact.isBounded
  let R := max 1 R₀
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hstep (k : ℕ) : ‖x (k + 1) - x k‖ ≤ R := by
    rw [← dist_eq_norm]
    exact (hR₀ (hx (k + 1)) (hx k)).trans (le_max_right _ _)
  let run := exactModelBTRRun (P := defaultBTRParams) x R hR hstep hdrop
  have hdrop' (k : ℕ) :
      run.model k (run.x k) - run.model k (run.x k + run.s k) = f (x k) - f (x (k + 1)) := by
    change f (x k) - f (x k + (x (k + 1) - x k)) = _
    rw [show x k + (x (k + 1) - x k) = x (k + 1) by abel]
  have hdec (k : ℕ) : HasSufficientModelDecrease (run.model k) (run.x k) (run.s k)
      (gradient f (run.x k)) B (run.Δ k) κ := by
    refine ⟨⟨hκ, hκ'⟩, ?_⟩
    rw [hdrop']
    change κ * ‖gradient f (x k)‖ * min (‖gradient f (x k)‖ / B) R ≤ _
    have h := mul_le_mul_of_nonneg_left (min_le_left (‖gradient f (x k)‖ / B) R)
      (mul_nonneg hκ.le (norm_nonneg (gradient f (x k))))
    exact h.trans (by convert hfirst k using 1; ring)
  have hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0) := by
    have h := theorem_6_4_6 run (fun _ ↦ B) (fun _ ↦ hB) (fun _ ↦ le_rfl)
      (fun _ ↦ rfl) hdec (fun k ↦ by change |f _ - f _| ≤ _; rw [sub_self, abs_zero]; positivity)
      hlower hf hH (K := 1) zero_le_one (fun _ _ ↦ by simp [run, exactModelBTRRun])
    change Tendsto (fun k ↦ ‖fderiv ℝ f (run.x k)‖) atTop (𝓝 0)
    simpa only [gradient, LinearIsometryEquiv.norm_map] using h
  refine ⟨hcrit, theorem_6_6_5_of_hessians run hcompact hx hf hcrit (fun _ ↦ rfl) hlower
    (fun ε hε ↦ ⟨1, zero_lt_one, Eventually.of_forall (fun _ _ ↦ by
      change |f _ - f _| ≤ _; rw [sub_self, abs_zero]; positivity)⟩)
    (fun _ ↦ by
      change Tendsto (fun k ↦ ‖fderiv ℝ (fderiv ℝ f) (x k) -
        fderiv ℝ (fderiv ℝ f) (x k)‖) atTop (𝓝 0)
      have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0 := ContinuousLinearMap.opNorm_zero
      simpa only [sub_self, hz] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))) hκ₂ ?_, ?_⟩
  · intro k
    refine ⟨hκ₂, fun hτ ↦ ?_⟩
    rw [hdrop']
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _)
      (mul_nonneg hκ₂.le (abs_nonneg _))).trans (hsecond k hτ)
  · intro z j hj hz
    have hgc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have ht : Tendsto (fun k ↦ ‖fderiv ℝ f (x (j k))‖) atTop (𝓝 ‖fderiv ℝ f z‖) :=
      hgc.norm.continuousAt.tendsto.comp hz
    refine ⟨norm_eq_zero.mp (tendsto_nhds_unique ht (hcrit.comp hj.tendsto_atTop)), ?_⟩
    apply (leastUnitCurvature_nonneg_iff _).mp
    by_contra! hn
    let curv (y : E) := leastUnitCurvature (fderiv ℝ (fderiv ℝ f) y)
    let a := -curv z / 2
    have ha : 0 < a := half_pos (neg_pos.mpr hn)
    have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    have hc : Continuous curv :=
      continuous_leastUnitCurvature.comp (hDf.continuous_fderiv (by norm_num))
    have hτ : ∀ᶠ n in atTop, curv (x (j n)) < -a :=
      (hc.continuousAt.tendsto.comp hz).eventually_lt_const (by dsimp [a, curv]; linarith)
    have hval := tendsto_atTop_ciInf hmono
      (hlower.mono (show range (f ∘ x) ⊆ range f from fun _ ⟨k, hk⟩ ↦ ⟨x k, hk⟩))
    have hdiff : Tendsto (fun k ↦ f (x k) - f (x (k + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self] using
        hval.sub (hval.comp (tendsto_add_atTop_nat 1))
    have hpos : 0 < κ₂ * a * a ^ 2 := mul_pos (mul_pos hκ₂ ha) (sq_pos_of_pos ha)
    obtain ⟨n, hnτ, hnd⟩ := (hτ.and ((hdiff.comp hj.tendsto_atTop).eventually_lt_const hpos)).exists
    have hnτ' : curv (x (j n)) < 0 := hnτ.trans (neg_lt_zero.mpr ha)
    have habs : a ≤ |curv (x (j n))| := by rw [abs_of_neg hnτ']; linarith
    have hsq : a ^ 2 ≤ (curv (x (j n))) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ ha.le habs 2
    exact hnd.not_ge ((mul_le_mul (mul_le_mul_of_nonneg_left habs hκ₂.le) hsq
      (sq_nonneg _) (mul_nonneg hκ₂.le (abs_nonneg _))).trans (hsecond (j n) hnτ'))

/-- Under the local convexity and nonsingularity assumptions of
Theorem 6.5.2, the exact-model double line-search sequence converges to
the given subsequential limit. Its BTR representation has constant
positive radius and exact agreement, so all iterations are very successful. -/
theorem theorem_10_3_1_local_convergence {f : E → ℝ} (x : ℕ → E)
    (hf : ContDiff ℝ 2 f) {D : ℝ} (hD : 0 < D)
    (hstep : ∀ k, ‖x (k + 1) - x k‖ ≤ D)
    (hdrop : ∀ k, 0 < f (x k) - f (x (k + 1)))
    {z : E} {j : ℕ → ℕ} (hj : Tendsto j atTop atTop) (hz : Tendsto (x ∘ j) atTop (𝓝 z))
    (hzcrit : fderiv ℝ f z = 0)
    (hcrit : Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0))
    {σ R μ : ℝ} (hσ : 0 < σ) (hR : 0 < R) (hμ : 0 < μ)
    (hH : ∀ v, σ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ f) z v‖)
    (hcurv : ∀ᶠ k in atTop, ‖x k - z‖ < R → ∀ y ∈ segment ℝ (x k) (x (k + 1)),
      μ * ‖x (k + 1) - x k‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ f) y (x (k + 1) - x k) (x (k + 1) - x k)) :
    Tendsto x atTop (𝓝 z) := by
  let run := exactModelBTRRun (P := defaultBTRParams) x D hD hstep hdrop
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  apply theorem_6_5_2 run hj hz hf hzcrit hcrit hσ hR hμ hH
    (fun _ y _ ↦ hf.differentiable (by norm_num) y)
    (fun _ y _ ↦ hDf.differentiable (by norm_num) y) (fun _ ↦ rfl)
  filter_upwards [hcurv] with k hk hnear y hy
  have he : run.x k + run.s k = x (k + 1) := by
    change x k + (x (k + 1) - x k) = _
    abel
  rw [he] at hy
  exact hk hnear y hy

end ConnGouldToint.Chapter10
