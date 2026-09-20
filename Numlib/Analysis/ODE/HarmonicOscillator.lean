/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` (the derivatives of
`c₀ cos(ωt) + c₁/ω sin(ωt)`) and `Mathlib.Analysis.ODE.Gronwall` (the uniqueness).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The harmonic oscillator `a'' = −λ a` on `[0, ∞)`

The scalar equation `a'' + λ a = 0`, `λ > 0`, in first-order form `a' = b`, `b' = −λ a` within
`[0, ∞)`: the energy `b² + λ a²` is constant, so a solution with `a(0) = b(0) = 0` vanishes
(`eq_zero_of_hasDerivWithinAt_oscillator`), and every solution is
`a(t) = a(0) cos(√λ t) + (b(0)/√λ) sin(√λ t)` (`eq_cos_add_sin_of_hasDerivWithinAt_oscillator`).
This is the mode equation behind the eigenfunction expansion of the wave equation
([brezis2011functional] chapter 10, Remark 9): the coefficients `⟪u(t), eₙ⟫` of a solution solve
it with `λ = λₙ`.
-/

open Set


/-- **Uniqueness for the harmonic oscillator `a'' = −λ a` on `[0, ∞)`**, first-order form: if
`a' = b` and `b' = −λ a` within `[0, ∞)`, `λ > 0`, and `a(0) = b(0) = 0`, then `a = 0` on
`[0, ∞)` — the energy `b² + λ a²` is constant and vanishes at `0`. -/
theorem eq_zero_of_hasDerivWithinAt_oscillator {a b : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ t, 0 ≤ t → HasDerivWithinAt a (b t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → HasDerivWithinAt b (-lam * a t) (Ici 0) t) (ha0 : a 0 = 0)
    (hb0 : b 0 = 0) {t : ℝ} (ht : 0 ≤ t) : a t = 0 := by
  have hE : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s ↦ b s ^ 2 + lam * a s ^ 2) 0 (Ici 0) s :=
    fun s hs ↦ by
      have h1 := ((hb s hs).pow 2).add (((ha s hs).pow 2).const_mul lam)
      refine h1.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
  have hconst : b t ^ 2 + lam * a t ^ 2 = b 0 ^ 2 + lam * a 0 ^ 2 := by
    rcases eq_or_lt_of_le ht with rfl | hpos
    · rfl
    exact constant_of_derivWithin_zero (f := fun s ↦ b s ^ 2 + lam * a s ^ 2) (a := 0) (b := t)
      (fun x hx ↦ ((hE x hx.1).mono Icc_subset_Ici_self).differentiableWithinAt)
      (fun x hx ↦ ((hE x hx.1).mono Icc_subset_Ici_self).derivWithin
        (uniqueDiffOn_Icc hpos x ⟨hx.1, hx.2.le⟩)) t (right_mem_Icc.2 ht)
  rw [ha0, hb0] at hconst
  have h2 : lam * a t ^ 2 ≤ 0 := by nlinarith [sq_nonneg (b t)]
  have h3 : a t ^ 2 ≤ 0 := by nlinarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h3 (sq_nonneg _))

/-- The derivative of `c₀ cos(w t) + (c₁ / w) sin(w t)`. -/
theorem hasDerivAt_cos_add_sin (c₀ c₁ w t : ℝ) :
    HasDerivAt (fun t ↦ c₀ * Real.cos (w * t) + c₁ / w * Real.sin (w * t))
      (-(c₀ * w) * Real.sin (w * t) + c₁ / w * w * Real.cos (w * t)) t := by
  have h1 : HasDerivAt (fun t ↦ w * t) w t := by simpa using (hasDerivAt_id t).const_mul w
  have h2 := (Real.hasDerivAt_cos (w * t)).comp t h1
  have h3 := (Real.hasDerivAt_sin (w * t)).comp t h1
  refine ((h2.const_mul c₀).add (h3.const_mul (c₁ / w))).congr_deriv ?_
  ring

/-- The derivative of `−c₀ w sin(w t) + (c₁ / w) w cos(w t)`. -/
theorem hasDerivAt_neg_sin_add_cos (c₀ c₁ w t : ℝ) :
    HasDerivAt (fun t ↦ -(c₀ * w) * Real.sin (w * t) + c₁ / w * w * Real.cos (w * t))
      (-(w ^ 2) * (c₀ * Real.cos (w * t) + c₁ / w * Real.sin (w * t))) t := by
  have h1 : HasDerivAt (fun t ↦ w * t) w t := by simpa using (hasDerivAt_id t).const_mul w
  have h2 := (Real.hasDerivAt_cos (w * t)).comp t h1
  have h3 := (Real.hasDerivAt_sin (w * t)).comp t h1
  refine ((h3.const_mul (-(c₀ * w))).add (h2.const_mul (c₁ / w * w))).congr_deriv ?_
  ring

/-- **The harmonic oscillator on `[0, ∞)`**: if `a' = b` and `b' = −λ a` within `[0, ∞)` with
`λ > 0`, then `a(t) = a(0) cos(√λ t) + (b(0) / √λ) sin(√λ t)` for `t ≥ 0`. -/
theorem eq_cos_add_sin_of_hasDerivWithinAt_oscillator {a b : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ t, 0 ≤ t → HasDerivWithinAt a (b t) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → HasDerivWithinAt b (-lam * a t) (Ici 0) t) {t : ℝ} (ht : 0 ≤ t) :
    a t = a 0 * Real.cos (√lam * t) + b 0 / √lam * Real.sin (√lam * t) := by
  have hw : √lam ^ 2 = lam := Real.sq_sqrt hlam.le
  have hw0 : √lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
  have key := eq_zero_of_hasDerivWithinAt_oscillator (lam := lam)
    (a := fun t ↦ a t - (a 0 * Real.cos (√lam * t) + b 0 / √lam * Real.sin (√lam * t)))
    (b := fun t ↦ b t - (-(a 0 * √lam) * Real.sin (√lam * t)
      + b 0 / √lam * √lam * Real.cos (√lam * t))) hlam
    (fun s hs ↦ (ha s hs).sub (hasDerivAt_cos_add_sin (a 0) (b 0) √lam s).hasDerivWithinAt)
    (fun s hs ↦ by
      refine ((hb s hs).sub
        (hasDerivAt_neg_sin_add_cos (a 0) (b 0) √lam s).hasDerivWithinAt).congr_deriv ?_
      rw [hw]
      ring)
    (by simp) (by simp [div_mul_cancel₀ _ hw0]) ht
  exact sub_eq_zero.1 key
