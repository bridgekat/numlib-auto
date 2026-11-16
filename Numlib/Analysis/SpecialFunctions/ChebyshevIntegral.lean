/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

The Chebyshev polynomial of the second kind $U_n$ (`Polynomial.Chebyshev.U`) is characterized by
$U_n(\cos \alpha) \sin \alpha = \sin((n + 1)\alpha)$. This file collects the facts that an
integration against $U_n$ needs. First, $T_{n+1}/(n + 1)$ is an antiderivative of $U_n$; this is the
identity $T_{n+1}' = (n + 1) U_n$ together with the fundamental theorem of calculus. Second, the
substitution $t = \cos \alpha$ turns an integral over $[-1, 1]$ into an integral over $[0, \pi]$
against $\sin \alpha$, and turns $U_n$ into a sine of frequency $n + 1$. Consequently, $U_n$ and
$U_m$ are orthogonal on $[-1, 1]$ for the weight $\sqrt{1 - t^2}$. This is the counterpart for the
second kind of the orthogonality of $T_n$ for the weight $1/\sqrt{1 - t^2}$.

The last result is the chord integral of a ridge polynomial: for $|t| \le 1$,
$$\int_{-\sqrt{1 - t^2}}^{\sqrt{1 - t^2}} U_n(t \cos \gamma + s \sin \gamma)\,ds = \frac{2}{n + 1}\,
  U_n(t)\, U_n(\cos \gamma) \sqrt{1 - t^2}.$$
The integral runs over the chord of the unit disk at abscissa $t$. It is the one-dimensional core of
the Radon (chord) decomposition of an integral of a ridge polynomial over the disk. The formula
holds for every $\gamma$. The substitution $u = t \cos \gamma + s \sin \gamma$ is available only for
$\sin \gamma \neq 0$, but at $\sin \gamma = 0$ the integrand is constant along the chord and gives
the same value.

## Main results

* `integral_neg_one_one_eq_integral_cos`: the substitution $t = \cos \alpha$, $\int_{-1}^1
  g(t)\,dt = \int_0^\pi g(\cos \alpha) \sin \alpha\,d\alpha$.
* `Polynomial.Chebyshev.hasDerivAt_eval_T_add_one`: the derivative of $T_{n+1}$ is $(n + 1) U_n$.
* `Polynomial.Chebyshev.integral_eval_U`: $\int_a^b U_n(t)\,dt = (T_{n+1}(b) - T_{n+1}(a))/(n + 1)$.
* `Polynomial.Chebyshev.integral_eval_U_mul_eval_U_sqrt`: $\int_{-1}^1 U_n U_m \sqrt{1 - t^2}\,dt$
  is $\pi/2$ if $n = m$ and $0$ otherwise.
* `Polynomial.Chebyshev.integral_eval_U_ridge_chord`: the chord integral of
  $U_n(t \cos \gamma + s \sin \gamma)$ displayed above.
-/

open MeasureTheory Set

open scoped Real

/-- The **substitution $t = \cos \alpha$**: for every continuous function
$g : \mathbb{R} \to \mathbb{R}$,
$$\int_{-1}^1 g(t)\,dt = \int_0^\pi \sin \alpha \; g(\cos \alpha)\,d\alpha.$$
-/
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

/-- For every natural number $n$ and every $x \in \mathbb{R}$, the function $y \mapsto T_{n+1}(y)$
has derivative $(n + 1)\, U_n(x)$ at $x$.

This is `Polynomial.Chebyshev.T_derivative_eq_U` at the index $n + 1$, in the form that the
fundamental theorem of calculus uses. -/
theorem hasDerivAt_eval_T_add_one (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (T ℝ ((n : ℤ) + 1)).eval y) (((n : ℝ) + 1) * (U ℝ (n : ℤ)).eval x) x := by
  have h := (T ℝ ((n : ℤ) + 1)).hasDerivAt (𝕜 := ℝ) x
  rw [T_derivative_eq_U, show (n : ℤ) + 1 - 1 = (n : ℤ) by ring] at h
  simpa using h

/-- The polynomial $T_{n+1}/(n + 1)$ is an antiderivative of $U_n$: for every natural number $n$ and
all $a, b \in \mathbb{R}$,
$$\int_a^b U_n(t)\,dt = \frac{T_{n+1}(b) - T_{n+1}(a)}{n + 1}.$$
-/
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

/-- The **Chebyshev polynomials of the second kind are orthogonal** on $[-1, 1]$ for the weight
$\sqrt{1 - t^2}$: for all natural numbers $n$ and $m$,
$$\int_{-1}^1 U_n(t)\, U_m(t) \sqrt{1 - t^2}\,dt = \begin{cases} \pi/2 & \text{if } n = m, \\ 0
  & \text{if } n \neq m. \end{cases}$$

Under $t = \cos \alpha$ the weight becomes $\sin \alpha$, and $U_n(\cos \alpha) \sin \alpha =
\sin((n + 1)\alpha)$. So the statement is the orthogonality of the sines of positive frequency
on $[0, \pi]$. -/
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

/-- The **chord integral of a ridge Chebyshev polynomial**: let $n$ be a natural number, let
$\gamma \in \mathbb{R}$, and let $t \in \mathbb{R}$ with $|t| \le 1$. Then, along the chord
$|s| \le \sqrt{1 - t^2}$ of the unit disk at abscissa $t$,
$$\int_{-\sqrt{1 - t^2}}^{\sqrt{1 - t^2}} U_n(t \cos \gamma + s \sin \gamma)\,ds = \frac{2}{n +
  1}\, U_n(t)\, U_n(\cos \gamma) \sqrt{1 - t^2}.$$

For $\sin \gamma \neq 0$ the proof substitutes $u = t \cos \gamma + s \sin \gamma$ and uses the
antiderivative $T_{n+1}/(n + 1)$ at $t = \cos \alpha$: the two endpoints are
$\cos(\alpha \mp \gamma)$, so the difference of the antiderivative is
$2 \sin((n + 1)\alpha) \sin((n + 1)\gamma)$. For $\sin \gamma = 0$ the integrand is constant
along the chord, and the same value results. -/
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
