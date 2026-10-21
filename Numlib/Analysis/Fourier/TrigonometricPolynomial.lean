/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a file beside `Mathlib.Analysis.Fourier.AddCircle`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Orthogonality and Parseval for trigonometric polynomials

Finite computations with interval integrals over one period, for trigonometric polynomials with
integer frequencies:

* `integral_cos_int_mul_neg_pi_pi`: `∫_{-π}^{π} cos (m r) dr = 2π δ_{m0}`;
* `integral_exp_I_int_mul`: `∫_0^{2π} e^{ikφ} dφ = 2π δ_{k0}`;
* `integral_norm_sq_trigPoly`: **Parseval's identity** for a trigonometric polynomial,
  `∫_0^{2π} |∑_s v_s e^{-isφ}|² dφ = 2π ∑_s |v_s|²`.

They need no `L²` theory of the circle: the cross terms integrate to zero one by one.
-/

open scoped Real

/-- **Orthogonality of the cosines over a symmetric period**: `∫_{-π}^{π} cos (m r) dr` is `2π` at
`m = 0` and `0` at every other integer frequency. The half-period form
`∫_0^π cos (m x) dx = π δ_{m0}` is `integral_cos_int_mul` in `Numlib.Analysis.Fourier.CosineBasis`.
-/
theorem integral_cos_int_mul_neg_pi_pi (m : ℤ) :
    (∫ r in -π..π, Real.cos ((m : ℝ) * r)) = if m = 0 then 2 * π else 0 := by
  by_cases hm : m = 0
  · rw [ite_eq_left hm, hm]
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, intervalIntegral.integral_const,
      smul_eq_mul, mul_one]
    ring
  · have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.2 hm
    rw [ite_eq_right hm, intervalIntegral.integral_comp_mul_left Real.cos hm',
      integral_cos, smul_eq_mul]
    have h1 : Real.sin ((m : ℝ) * π) = 0 := Real.sin_int_mul_pi m
    have h2 : Real.sin ((m : ℝ) * -π) = 0 := by
      rw [show (m : ℝ) * -π = -((m : ℝ) * π) by ring, Real.sin_neg, h1, neg_zero]
    rw [h1, h2]
    ring

section Exp

open Complex

/-- `conj (e^{-isφ}) = e^{isφ}` for an integer `s` and a real `φ`. -/
private theorem conj_exp_neg_int_mul (s : ℤ) (φ : ℝ) :
    (starRingEnd ℂ) (exp (-(I * s * φ))) = exp (I * s * φ) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- **Orthogonality of the exponentials over one period**: `∫_0^{2π} e^{ikφ} dφ` is `2π` when
`k = 0` and `0` otherwise. -/
theorem integral_exp_I_int_mul (k : ℤ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), exp (I * k * φ))
      = if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [ite_eq_right hk]
    have hc : (I * (k : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.2 hk)
    have h := integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * Real.pi) hc
    have htop : Complex.exp (I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h, htop]
    simp

/-- **Parseval's identity for a trigonometric polynomial**: for finitely many complex
coefficients, `∫_0^{2π} |∑_s v_s e^{-isφ}|² dφ = 2π ∑_s |v_s|²`. -/
theorem integral_norm_sq_trigPoly (A : Finset ℤ) (v : ℤ → ℂ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), ‖∑ s ∈ A, v s * exp (-(I * s * φ))‖ ^ 2)
      = 2 * Real.pi * ∑ s ∈ A, ‖v s‖ ^ 2 := by
  have hexpand : ∀ φ : ℝ,
      (∑ s ∈ A, v s * exp (-(I * s * φ))) * (starRingEnd ℂ) (∑ s ∈ A, v s * exp (-(I * s * φ)))
        = ∑ s ∈ A, ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ) := by
    intro φ
    simp only [map_sum, map_mul, conj_exp_neg_int_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [show v s * exp (-(I * s * φ)) * ((starRingEnd ℂ) (v t) * exp (I * t * φ))
        = v s * (starRingEnd ℂ) (v t) * (exp (-(I * s * φ)) * exp (I * t * φ)) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  have hcint : ∀ s t : ℤ, IntervalIntegrable
      (fun φ : ℝ => v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    intro s t
    exact (by fun_prop : Continuous fun φ : ℝ =>
      v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ)).intervalIntegrable _ _
  have hsumint : ∀ s : ℤ, IntervalIntegrable
      (fun φ : ℝ => ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
      MeasureTheory.volume 0 (2 * Real.pi) := fun s =>
    (by fun_prop : Continuous fun φ : ℝ =>
      ∑ t ∈ A, v s * (starRingEnd ℂ) (v t)
        * exp (I * ((t : ℂ) - (s : ℂ)) * φ)).intervalIntegrable _ _
  have hdiag : ∀ s t : ℤ,
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
        = if t = s then ((2 * Real.pi : ℝ) : ℂ) * (v s * (starRingEnd ℂ) (v t)) else 0 := by
    intro s t
    rw [intervalIntegral.integral_const_mul]
    have hk : (fun φ : ℝ => exp (I * ((t : ℂ) - (s : ℂ)) * φ))
        = fun φ : ℝ => exp (I * ((t - s : ℤ) : ℂ) * φ) := by
      funext φ; push_cast; ring_nf
    rw [hk, integral_exp_I_int_mul (t - s)]
    rcases eq_or_ne t s with rfl | hts
    · simp [mul_comm]
    · rw [ite_eq_right (sub_ne_zero.2 hts), ite_eq_right hts, mul_zero]
  have hcomplex : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((‖∑ s ∈ A, v s * exp (-(I * s * φ))‖ ^ 2 : ℝ) : ℂ))
      = ((2 * Real.pi * ∑ s ∈ A, ‖v s‖ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ φ : ℝ, ((‖∑ s ∈ A, v s * exp (-(I * s * φ))‖ ^ 2 : ℝ) : ℂ)
        = (∑ s ∈ A, v s * exp (-(I * s * φ))) *
          (starRingEnd ℂ) (∑ s ∈ A, v s * exp (-(I * s * φ))) := by
      intro φ
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [intervalIntegral.integral_congr fun φ _ => (hpt φ).trans (hexpand φ),
      intervalIntegral.integral_finsetSum (f := fun s (φ : ℝ) =>
          ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
        fun s _ => hsumint s]
    have hstep : ∀ s ∈ A, (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
          = ((2 * Real.pi : ℝ) : ℂ) * ((‖v s‖ : ℝ) : ℂ) ^ 2 := by
      intro s hs
      rw [intervalIntegral.integral_finsetSum (f := fun t (φ : ℝ) =>
            v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
          fun t _ => hcint s t,
        Finset.sum_congr rfl fun t _ => hdiag s t, Finset.sum_ite_eq' A s]
      rw [ite_eq_left hs, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    push_cast
    ring
  rw [intervalIntegral.integral_ofReal] at hcomplex
  exact_mod_cast hcomplex

end Exp
