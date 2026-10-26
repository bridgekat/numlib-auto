import Numlib.Optimization.Optimality.Approximate
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Stability of approximate high-order minimizers

A small Taylor-decrement measure `φ^δ_{f,S,j}(x) = taylorMeasure (ftaylorSeries ℝ f x) j δ S`
bounds the possible decrease of `f` on the feasible part `x + S` of a neighbourhood of `x`, when
`∇^j f` is Lipschitz continuous near `x` ([cartis2022evaluation], Theorem 12.1.8 for `S = univ`
and no slack, Theorem 14.2.1 with a feasible set and an additive slack `η`). Applied to the
Lagrangian `f - ⟪y, c⟫` it gives Theorem 14.3.2.

## Main results

* `le_of_taylorMeasure_le`: (12.1.39) with slack `η`;
* `le_of_taylorMeasure_le_of_mul_le`: (14.2.6) (and (12.1.35)), radius condition written
  multiplicatively, `L ‖d‖ ≤ (j+1) ε`, so that `L = 0` needs no division;
* `le_of_taylorMeasure_le_of_lipschitz_zero`: (14.2.7) (and (12.1.36));
* `le_of_lagrangian_taylorMeasure_le`: (14.3.10), with the variants
  `le_of_lagrangian_taylorMeasure_le_of_eq` and `le_of_lagrangian_taylorMeasure_le_of_eq_zero`
  for (14.3.12).

## Implementation notes

Smoothness and Lipschitz hypotheses are local, on `closedBall x δ`, in the hypothesis shape of
`Numlib/Analysis/Calculus/MultivariateTaylor/Remainder` (implied by the book's "open
neighbourhood of radius larger than `δ_j`"). Theorem 14.3.2's "neighbourhood of diameter `δ_j`"
is read as radius `δ_j`: otherwise displacements of norm `δ_j` leave it. Its componentwise
Lipschitz constant `L_{c,j}` is read as the constant of the vector-valued derivative `∇^j c`
(operator norm into `F`); with componentwise constants an extra factor `√m` would appear.
-/

open Metric
open scoped Nat InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Optimization

variable {f : E → ℝ} {x : E} {j : ℕ} {δ ε η L : ℝ} {S : Set E}

/-- **Stability of approximate minimizers** ([cartis2022evaluation], (12.1.39), with the slack
`η` of Theorem 14.2.1). If `f` is `C^j` near `x` with `L`-Lipschitz `∇^j f` on `closedBall x δ`
and `φ^δ_{f,S,j}(x) ≤ ε δ^j/j! + η`, then for every `d ∈ S` with `‖d‖ ≤ δ`,
`f(x + d) ≥ f(x) - L/(j+1)! ‖d‖ δ^j - ε δ^j/j! - η`. -/
theorem le_of_taylorMeasure_le (hf : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j L (closedBall x δ)) (hL0 : 0 ≤ L)
    (h : taylorMeasure (ftaylorSeries ℝ f x) j δ S ≤ ε * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) :
    f x - L / (j + 1)! * ‖d‖ * δ ^ j - ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have hδ : 0 ≤ δ := (norm_nonneg d).trans hd
  have hx : x ∈ closedBall x δ := mem_closedBall_self hδ
  have hxd : x + d ∈ closedBall x δ := by simpa [dist_eq_norm] using hd
  have hrem := abs_sub_taylorPolynomial_le_of_lipschitz (convex_closedBall x δ) hf hL hx hxd
  have hdec := (taylorDecrement_le_taylorMeasure (ftaylorSeries ℝ f x) j
    ⟨by simpa using hd, hdS⟩).trans h
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right] at hdec
  have hpow : ‖d‖ ^ (j + 1) ≤ ‖d‖ * δ ^ j := by
    rw [pow_succ, mul_comm]
    gcongr
  have : L / (j + 1)! * ‖d‖ ^ (j + 1) ≤ L / (j + 1)! * ‖d‖ * δ ^ j := by
    rw [mul_assoc]
    gcongr
  linarith [(abs_le.1 hrem).1]

/-- **Stability with a radius condition** ([cartis2022evaluation], (14.2.6), and (12.1.35) for
`S = univ`, `η = 0`): under the hypotheses of `le_of_taylorMeasure_le`, if moreover
`L ‖d‖ ≤ (j+1) ε`, then `f(x + d) ≥ f(x) - 2 ε δ^j/j! - η`. -/
theorem le_of_taylorMeasure_le_of_mul_le (hf : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j L (closedBall x δ)) (hL0 : 0 ≤ L)
    (h : taylorMeasure (ftaylorSeries ℝ f x) j δ S ≤ ε * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hLd : L * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := le_of_taylorMeasure_le hf hL hL0 h hdS hd
  have hδ : 0 ≤ δ := (norm_nonneg d).trans hd
  have hfs : ((j + 1)! : ℝ) = (j + 1) * j ! := by push_cast [Nat.factorial_succ]; ring
  have hf0 : (0 : ℝ) < j ! := by positivity
  have hq : L * ‖d‖ / (j + 1)! ≤ ε / j ! := by
    rw [hfs, div_le_div_iff₀ (by positivity) hf0]
    nlinarith
  have : L / (j + 1)! * ‖d‖ * δ ^ j ≤ ε * δ ^ j / j ! :=
    calc L / (j + 1)! * ‖d‖ * δ ^ j = L * ‖d‖ / (j + 1)! * δ ^ j := by ring
      _ ≤ ε / j ! * δ ^ j := by gcongr
      _ = ε * δ ^ j / j ! := by ring
  have e : 2 * ε * δ ^ j / j ! = ε * δ ^ j / j ! + ε * δ ^ j / j ! := by ring
  linarith

/-- **Stability with a constant `j`-th derivative** ([cartis2022evaluation], (14.2.7), and
(12.1.36) for `S = univ`, `η = 0`): if `∇^j f` is constant on `closedBall x δ` (Lipschitz with
constant `0`), then `f(x + d) ≥ f(x) - ε δ^j/j! - η` for every `d ∈ S` with `‖d‖ ≤ δ`. -/
theorem le_of_taylorMeasure_le_of_lipschitz_zero
    (hf : ∀ y ∈ closedBall x δ, ContDiffAt ℝ j f y)
    (hL : IteratedFDerivLipschitzOn f j 0 (closedBall x δ))
    (h : taylorMeasure (ftaylorSeries ℝ f x) j δ S ≤ ε * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) :
    f x - ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  simpa using le_of_taylorMeasure_le hf hL le_rfl h hdS hd

section Lagrangian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {c : E → F} {y : F}
  {ε₀ Lf Lc : ℝ}

/-- `1 + a ≤ √2 √(1 + a²)`, i.e. `‖(1, y)‖ ≥ (1 + ‖y‖)/√2`. -/
private theorem one_add_le_sqrt_two_mul_sqrt (a : ℝ) : 1 + a ≤ √2 * √(1 + a ^ 2) := by
  rw [← Real.sqrt_mul zero_le_two]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (1 - a)]

/-- Core of Theorem 14.3.2 of [cartis2022evaluation]: the stability estimate (14.3.13) for the
Lagrangian `ℒ = f - ⟪y, c⟫`, whose `j`-th derivative is `(Lf + ‖y‖ Lc)`-Lipschitz. -/
theorem lagrangian_le_of_taylorMeasure_le (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - ⟪y, c x⟫_ℝ - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤
      f (x + d) - ⟪y, c (x + d)⟫_ℝ := by
  set K := √(1 + ‖y‖ ^ 2)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hyc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j (innerSL ℝ y ∘ c) z := fun z hz =>
    (innerSL ℝ y).contDiff.contDiffAt.comp z (hc z hz)
  have hℒ : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j (fun z => f z - ⟪y, c z⟫_ℝ) z := fun z hz =>
    (hf z hz).sub (hyc z hz)
  have hLℒ : IteratedFDerivLipschitzOn (fun z => f z - ⟪y, c z⟫_ℝ) j (Lf + ‖y‖ * Lc)
      (closedBall x δ) := by
    have := hLf.sub ((hLc.continuousLinearMap_comp (innerSL ℝ y) hc)) hf hyc
    rwa [innerSL_apply_norm] at this
  have hMax : Lf + ‖y‖ * Lc ≤ (1 + ‖y‖) * max Lf Lc := by
    nlinarith [le_max_left Lf Lc, le_max_right Lf Lc, norm_nonneg y]
  have hrad : (Lf + ‖y‖ * Lc) * ‖d‖ ≤ (j + 1) * (ε * K) := by
    have h1 := one_add_le_sqrt_two_mul_sqrt ‖y‖
    have hm0 : 0 ≤ max Lf Lc := hLf0.trans (le_max_left _ _)
    calc (Lf + ‖y‖ * Lc) * ‖d‖ ≤ (1 + ‖y‖) * max Lf Lc * ‖d‖ := by gcongr
      _ ≤ √2 * K * max Lf Lc * ‖d‖ := by gcongr
      _ = K * (√2 * max Lf Lc * ‖d‖) := by ring
      _ ≤ K * ((j + 1) * ε) := by gcongr
      _ = (j + 1) * (ε * K) := by ring
  have := le_of_taylorMeasure_le_of_mul_le hℒ hLℒ (by positivity) (ε := ε * K)
    (by simpa [mul_assoc] using h) hdS hd hrad
  convert this using 2
  ring

/-- **Local sufficiency of the Lagrangian for approximate minimizers** ([cartis2022evaluation],
Theorem 14.3.2, (14.3.10)). Let `f : E → ℝ` and `c : E → F` be `C^j` near `x` with `Lf`- and
`Lc`-Lipschitz `j`-th derivatives on `closedBall x δ`, `‖c(x)‖ ≤ ε₀`, and let the Lagrangian
`ℒ = f - ⟪y, c⟫` satisfy `φ^δ_{ℒ,V,j}(x) ≤ ε ‖(1, y)‖ δ^j/j! + η`, where
`‖(1, y)‖ = √(1 + ‖y‖²)`. Then for every `d ∈ V` with `‖d‖ ≤ δ`, `‖c(x + d)‖ ≤ ε₀` and
`√2 max(Lf, Lc) ‖d‖ ≤ (j+1) ε` (14.3.11),
`f(x + d) ≥ f(x) - 2 ε₀ ‖y‖ - 2 ε ‖(1, y)‖ δ^j/j! - η`. -/
theorem le_of_lagrangian_taylorMeasure_le (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (hcx : ‖c x‖ ≤ ε₀)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hcd : ‖c (x + d)‖ ≤ ε₀)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε₀ * ‖y‖ - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := lagrangian_le_of_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 h hdS hd hLd
  have h2 : ⟪y, c x⟫_ℝ - ⟪y, c (x + d)⟫_ℝ ≤ 2 * ε₀ * ‖y‖ := by
    rw [← inner_sub_right]
    calc ⟪y, c x - c (x + d)⟫_ℝ ≤ ‖y‖ * ‖c x - c (x + d)‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (ε₀ + ε₀) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hcx hcd)
      _ = 2 * ε₀ * ‖y‖ := by ring
  linarith

/-- (14.3.12) of [cartis2022evaluation], first case: if `c(x + d) = c(x)`, the `ε₀` term of
Theorem 14.3.2 can be dropped. -/
theorem le_of_lagrangian_taylorMeasure_le_of_eq (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hcd : c (x + d) = c x)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := lagrangian_le_of_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 h hdS hd hLd
  rw [hcd] at h1
  linarith

/-- (14.3.12) of [cartis2022evaluation], second case: if `c(x + d) = 0` and `⟪y, c(x)⟫ ≤ 0`, the
`ε₀` term of Theorem 14.3.2 can be dropped. -/
theorem le_of_lagrangian_taylorMeasure_le_of_eq_zero
    (hf : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall x δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall x δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall x δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (h : taylorMeasure (ftaylorSeries ℝ (fun z => f z - ⟪y, c z⟫_ℝ) x) j δ S ≤
      ε * √(1 + ‖y‖ ^ 2) * δ ^ j / j ! + η)
    {d : E} (hdS : d ∈ S) (hd : ‖d‖ ≤ δ) (hcd : c (x + d) = 0) (hyc : ⟪y, c x⟫_ℝ ≤ 0)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    f x - 2 * ε * √(1 + ‖y‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
  have h1 := lagrangian_le_of_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 h hdS hd hLd
  rw [hcd, inner_zero_right] at h1
  linarith

end Lagrangian

end Optimization
