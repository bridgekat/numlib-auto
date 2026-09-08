/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality`, whose
`TODO` asks for exactly the orthogonality proved here.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Numlib.Analysis.Fourier.CosineBasis

/-!
# Integrals of the Chebyshev polynomials of the second kind

`Polynomial.Chebyshev.U n` is the Chebyshev polynomial of the second kind, characterized by
`U_n(cos α) sin α = sin ((n + 1) α)`. This file collects what an integration against `U_n` needs:

* `T_{n + 1} / (n + 1)` is an antiderivative of `U_n`, which is the formal identity
  `derivative (T (n + 1)) = (n + 1) U_n` read through the fundamental theorem of calculus;
* the substitution `t = cos α` turns an integral over `[-1, 1]` into one over `[0, π]` against
  `sin α`, and turns `U_n` into the sine of frequency `n + 1`;
* consequently `U_n` and `U_m` are orthogonal on `[-1, 1]` for the weight `√(1 - t²)`, the
  counterpart for the second kind of the orthogonality of `T_n` for the weight `√(1 - t²)⁻¹`;
* the *ridge* chord integral
  `∫ U_n(t cos γ + s sin γ) ds = 2 U_n(t) U_n(cos γ) √(1 - t²) / (n + 1)`
  over the chord `|s| ≤ √(1 - t²)` of the unit disk, which is the one-dimensional heart of the
  Radon (chord) decomposition of an integral of a ridge polynomial over the disk.

The chord formula is uniform in `γ`: the substitution `u = t cos γ + s sin γ` is available only for
`sin γ ≠ 0`, but the value it produces extends continuously — and is the correct one — across
`sin γ = 0`, where the integrand is constant along the chord.

## Main statements

* `integral_neg_one_one_eq_integral_cos` — the substitution `t = cos α`.
* `Polynomial.Chebyshev.hasDerivAt_eval_T_add_one` and `Polynomial.Chebyshev.integral_eval_U` —
  the antiderivative `T_{n + 1} / (n + 1)` of `U_n`.
* `Polynomial.Chebyshev.integral_eval_U_mul_eval_U_sqrt` — orthogonality on `[-1, 1]` for the
  weight `√(1 - t²)`.
* `Polynomial.Chebyshev.integral_eval_U_ridge_chord` — the chord integral of a ridge polynomial.
-/

open MeasureTheory Set

open scoped Real

/-- **The substitution `t = cos α`**: an integral over `[-1, 1]` is the integral over `[0, π]` of
the composite against `sin α`. -/
theorem integral_neg_one_one_eq_integral_cos {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t in (-1 : ℝ)..1, g t = ∫ α in (0 : ℝ)..π, Real.sin α * g (Real.cos α) := by
  have h := intervalIntegral.integral_deriv_smul_comp (a := (0 : ℝ)) (b := π)
    (f := Real.cos) (f' := fun x => -Real.sin x) (g := g)
    (fun x _ => Real.hasDerivAt_cos x) (by fun_prop) hg
  simp only [Function.comp_apply, smul_eq_mul, Real.cos_zero, Real.cos_pi] at h
  have hleft : ∫ x in (0 : ℝ)..π, -Real.sin x * g (Real.cos x)
      = -∫ x in (0 : ℝ)..π, Real.sin x * g (Real.cos x) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hright : ∫ x in (1 : ℝ)..(-1), g x = -∫ x in (-1 : ℝ)..1, g x :=
    intervalIntegral.integral_symm (-1) 1
  rw [hleft, hright] at h
  linarith [h]

namespace Polynomial.Chebyshev

/-- **The derivative of `T_{n + 1}` is `(n + 1) U_n`**, in the form the fundamental theorem of
calculus consumes. It is `Polynomial.Chebyshev.T_derivative_eq_U` at the index `n + 1`. -/
theorem hasDerivAt_eval_T_add_one (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (T ℝ ((n : ℤ) + 1)).eval y) (((n : ℝ) + 1) * (U ℝ (n : ℤ)).eval x) x := by
  have h := (T ℝ ((n : ℤ) + 1)).hasDerivAt (𝕜 := ℝ) x
  rw [T_derivative_eq_U, show (n : ℤ) + 1 - 1 = (n : ℤ) by ring] at h
  simpa using h

/-- **`T_{n + 1} / (n + 1)` is an antiderivative of `U_n`.** -/
theorem integral_eval_U (n : ℕ) (a b : ℝ) :
    ∫ t in a..b, (U ℝ (n : ℤ)).eval t
      = ((T ℝ ((n : ℤ) + 1)).eval b - (T ℝ ((n : ℤ) + 1)).eval a) / (n + 1) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have key : ∫ t in a..b, ((n : ℝ) + 1) * (U ℝ (n : ℤ)).eval t
      = (T ℝ ((n : ℤ) + 1)).eval b - (T ℝ ((n : ℤ) + 1)).eval a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_eval_T_add_one n x)
      (((U ℝ (n : ℤ)).continuous.const_mul ((n : ℝ) + 1)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at key
  field_simp
  linarith [key]

/-- **The Chebyshev polynomials of the second kind are orthogonal on `[-1, 1]` for the weight
`√(1 - t²)`**, with `π/2` for every squared norm. Under `t = cos α` the weight is `sin α` and
`U_n(cos α) sin α = sin ((n + 1) α)`, so this is the orthogonality of the sines of positive
frequency on `[0, π]`. -/
theorem integral_eval_U_mul_eval_U_sqrt (n m : ℕ) :
    ∫ t in (-1 : ℝ)..1, (U ℝ (n : ℤ)).eval t * (U ℝ (m : ℤ)).eval t * √(1 - t ^ 2)
      = if n = m then π / 2 else 0 := by
  rw [integral_neg_one_one_eq_integral_cos (by fun_prop)]
  have hcongr : ∀ α ∈ uIcc (0 : ℝ) π,
      Real.sin α * ((U ℝ (n : ℤ)).eval (Real.cos α) * (U ℝ (m : ℤ)).eval (Real.cos α)
          * √(1 - Real.cos α ^ 2))
        = Real.sin ((n + 1 : ℕ) * α) * Real.sin ((m + 1 : ℕ) * α) := by
    intro α hα
    rw [uIcc_of_le Real.pi_pos.le, mem_Icc] at hα
    have hs : √(1 - Real.cos α ^ 2) = Real.sin α := by
      rw [show 1 - Real.cos α ^ 2 = Real.sin α ^ 2 by nlinarith [Real.sin_sq_add_cos_sq α],
        Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi hα.1 hα.2)]
    have hn := U_real_cos α (n : ℤ)
    have hm := U_real_cos α (m : ℤ)
    rw [hs, show ((n + 1 : ℕ) : ℝ) = ((n : ℤ) : ℝ) + 1 by push_cast; ring,
      show ((m + 1 : ℕ) : ℝ) = ((m : ℤ) : ℝ) + 1 by push_cast; ring, ← hn, ← hm]
    ring
  rw [intervalIntegral.integral_congr hcongr, integral_sin_nat_mul_sin_nat_mul]
  simp

/-- **The chord integral of a ridge Chebyshev polynomial**: along the chord `|s| ≤ √(1 - t²)` of the
unit disk at abscissa `t`,
`∫ U_n(t cos γ + s sin γ) ds = 2 U_n(t) U_n(cos γ) √(1 - t²) / (n + 1)`.

For `sin γ ≠ 0` this is the substitution `u = t cos γ + s sin γ` together with the antiderivative
`T_{n + 1} / (n + 1)`, read at `t = cos α`: the two endpoints are `cos (α ∓ γ)`, so the difference
of the antiderivative is `2 sin ((n + 1) α) sin ((n + 1) γ)`. For `sin γ = 0` the integrand is
constant along the chord, and the same value comes out. -/
theorem integral_eval_U_ridge_chord (n : ℕ) (γ : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    ∫ s in (-√(1 - t ^ 2))..√(1 - t ^ 2), (U ℝ (n : ℤ)).eval (t * Real.cos γ + s * Real.sin γ)
      = 2 / (n + 1) * (U ℝ (n : ℤ)).eval t * (U ℝ (n : ℤ)).eval (Real.cos γ) * √(1 - t ^ 2) := by
  obtain ⟨ht1, ht2⟩ := abs_le.1 ht
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rcases eq_or_ne (Real.sin γ) 0 with hγ | hγ
  · -- The integrand is constant along the chord, and `cos γ = ± 1`.
    have hcos : (Real.cos γ - 1) * (Real.cos γ + 1) = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq γ]
    have hconst : ∀ s : ℝ, (U ℝ (n : ℤ)).eval (t * Real.cos γ + s * Real.sin γ)
        = (U ℝ (n : ℤ)).eval (t * Real.cos γ) := by
      intro s; rw [hγ, mul_zero, add_zero]
    rw [intervalIntegral.integral_congr (fun s _ => hconst s), intervalIntegral.integral_const,
      smul_eq_mul]
    rcases mul_eq_zero.1 hcos with h | h
    · have h1 : Real.cos γ = 1 := by linarith
      rw [h1, mul_one, U_eval_one]
      push_cast
      field_simp
      ring
    · have h1 : Real.cos γ = -1 := by linarith
      have hneg := U_eval_neg (R := ℝ) n t
      rw [h1, mul_neg_one, hneg, U_eval_neg_one]
      push_cast
      field_simp
      ring
  · -- The substitution `u = t cos γ + s sin γ`.
    set w := √(1 - t ^ 2) with hw
    set α := Real.arccos t with hα
    have hcosα : Real.cos α = t := Real.cos_arccos ht1 ht2
    have hsinα : Real.sin α = w := Real.sin_arccos t
    rw [intervalIntegral.integral_congr
        (fun s _ => by rw [show t * Real.cos γ + s * Real.sin γ
          = Real.sin γ * s + t * Real.cos γ from by ring]),
      intervalIntegral.integral_comp_mul_add (fun u => (U ℝ (n : ℤ)).eval u) hγ (t * Real.cos γ),
      integral_eval_U, smul_eq_mul]
    have hupper : Real.sin γ * w + t * Real.cos γ = Real.cos (α - γ) := by
      rw [Real.cos_sub, hcosα, hsinα]; ring
    have hlower : Real.sin γ * -w + t * Real.cos γ = Real.cos (α + γ) := by
      rw [Real.cos_add, hcosα, hsinα]; ring
    rw [hupper, hlower, T_real_cos, T_real_cos]
    have hdiff : Real.cos (((n : ℤ) + 1 : ℝ) * (α - γ)) - Real.cos (((n : ℤ) + 1 : ℝ) * (α + γ))
        = 2 * Real.sin (((n : ℤ) + 1 : ℝ) * α) * Real.sin (((n : ℤ) + 1 : ℝ) * γ) := by
      have h1 := Real.cos_sub (((n : ℤ) + 1 : ℝ) * α) (((n : ℤ) + 1 : ℝ) * γ)
      have h2 := Real.cos_add (((n : ℤ) + 1 : ℝ) * α) (((n : ℤ) + 1 : ℝ) * γ)
      rw [show ((n : ℤ) + 1 : ℝ) * (α - γ) = ((n : ℤ) + 1 : ℝ) * α - ((n : ℤ) + 1 : ℝ) * γ by ring,
        show ((n : ℤ) + 1 : ℝ) * (α + γ) = ((n : ℤ) + 1 : ℝ) * α + ((n : ℤ) + 1 : ℝ) * γ by ring,
        h1, h2]
      ring
    have hsα := U_real_cos α (n : ℤ)
    have hsγ := U_real_cos γ (n : ℤ)
    rw [hcosα, hsinα] at hsα
    push_cast at hdiff hsα hsγ ⊢
    rw [hdiff, ← hsα, ← hsγ]
    field_simp

end Polynomial.Chebyshev
