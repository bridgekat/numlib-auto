/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Complex.Norm
import Numlib.Analysis.Calculus.RootMultiplicity
import NumlibSurface.QuarteroniSaccoSaleri.Chapter02.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 6.1: Conditioning of a nonlinear equation

This module formalizes Section 6.1 of [quarteroni2000numerical], the conditioning of a root $\alpha$
of the equation $f(x) = \varphi(x) - d = 0$ with datum $d$. The root is $\alpha = G(d)$ for the
resolvent $G = \varphi^{-1}$, so its conditioning is the conditioning of $G$ in the sense of Chapter
2, as the book itself says ("using the notation of Chapter 2"). At a simple root the absolute
condition number is $1/|f'(\alpha)|$ (6.3). At a root of multiplicity $m \ge 2$ the condition number
is infinite, and a perturbation $\delta d$ of the datum moves the root by about
$(m!/|f^{(m)}(\alpha)|)^{1/m} |\delta d|^{1/m}$ (6.4). The estimates (6.5)–(6.7) bound the error
$|\hat\alpha - \alpha|$ by the residual $|f(\hat\alpha)|$, and for a polynomial by the size of a
perturbation of its coefficients; Example 6.1 shows that this bound is sharp. The results (6.3) and
(6.4) restate `QuarteroniSaccoSaleri.Chapter02.example_2_4`,
`QuarteroniSaccoSaleri.Chapter02.example_2_4_rel` and
`QuarteroniSaccoSaleri.Chapter02.example_2_4_multiple_root`; the multiple-root estimates specialize
`Numlib.Analysis.Calculus.RootMultiplicity`.

## Main results

* Equation (6.3), `QuarteroniSaccoSaleri.Chapter06.equation_6_3_abs` and
  `QuarteroniSaccoSaleri.Chapter06.equation_6_3_rel`: at a simple root,
  $K_{abs}(d) = 1/|f'(\alpha)|$ and $K(d) = |d| / (|\alpha| |f'(\alpha)|)$.
* Equation (6.4), `QuarteroniSaccoSaleri.Chapter06.equation_6_4_absCondNumber_eq_top`: at a root of
  multiplicity $m \ge 2$, $K_{abs}(d) = +\infty$.
* Equation (6.4), `QuarteroniSaccoSaleri.Chapter06.equation_6_4`: $|x - \alpha| / |f(x)|^{1/m} \to
  (m!/|f^{(m)}(\alpha)|)^{1/m}$ as $x \to \alpha$.
* Equation (6.5), `QuarteroniSaccoSaleri.Chapter06.equation_6_5`: at a simple root, the relative
  error is bounded by $c\,|f(\hat\alpha)|/|\alpha|$ for every $c > 1/|f'(\alpha)|$.
* Equation (6.6), `QuarteroniSaccoSaleri.Chapter06.equation_6_6`: at a root of multiplicity $m$, the
  relative error is bounded by $c\,|f(\hat\alpha)|^{1/m}$.
* Equation (6.7), `QuarteroniSaccoSaleri.Chapter06.equation_6_7`: the relative error of a real root
  of a perturbed polynomial $p + q$ is bounded by $c\,|q(\hat\alpha)|^{1/m}$.
* Example 6.1, `QuarteroniSaccoSaleri.Chapter06.example_6_1` and
  `QuarteroniSaccoSaleri.Chapter06.example_6_1_norm`: the roots of $(x - 1)^4 - \varepsilon$ are
  $1 + \varepsilon^{1/4} i^k$, with relative error exactly $\varepsilon^{1/4}$.

## Conventions

* A root of multiplicity $m$ of a function $f$ is `IsRootOfMultiplicity f α m`: $f(\alpha) =
  f'(\alpha) = \dots = f^{(m-1)}(\alpha) = 0$ and $f^{(m)}(\alpha) \neq 0$. The smoothness that
  makes the derivatives meaningful is a separate hypothesis.
* The absolute and relative condition numbers are `Conditioning.absCondNumber` and
  `Conditioning.relCondNumber` of Chapter 2, with values in $[0, \infty]$.

## Deviations from the source

* **Reading.** The approximate sensitivities are exact local condition numbers under the stated
  inverse-branch hypotheses. See `QuarteroniSaccoSaleri.Chapter06.equation_6_3_abs`,
  `QuarteroniSaccoSaleri.Chapter06.equation_6_3_rel`.
* **Reading.** At a multiple root the local absolute condition number is infinite on a continuous
  inverse branch. See `QuarteroniSaccoSaleri.Chapter06.equation_6_4_absCondNumber_eq_top`.
* **Reading.** The leading perturbation estimate is a punctured limit under local smoothness. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_4`.
* **Reading.** Relative bounds use any constant above the asymptotic coefficient. Equation (6.7)
  restricts roots to real values and allows arbitrary perturbation degree. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_5`, `QuarteroniSaccoSaleri.Chapter06.equation_6_6`,
  `QuarteroniSaccoSaleri.Chapter06.equation_6_7`.
* **Correction.** The four complex roots have distinct phases and the claimed displacement size
  holds for every positive perturbation. See `QuarteroniSaccoSaleri.Chapter06.example_6_1`,
  `QuarteroniSaccoSaleri.Chapter06.example_6_1_norm`.
* **Equation (6.4)** (reading). The source writes $K_{abs}(d) \simeq |m!\,\delta d /
  f^{(m)}(\alpha)|^{1/m} / |\delta d|$, a quantity that depends on $\delta d$; the condition number
  of Definition 2.1 is $+\infty$, and the content of (6.4) is stated as a limit. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_4`.
* **Equations (6.5)–(6.7)** (reading). The source's $\lesssim$ is read as: for every constant above
  the asymptotic one, the inequality holds for all approximate roots close enough to $\alpha$. See
  `QuarteroniSaccoSaleri.Chapter06.equation_6_6`.
* **Equation (6.7)** (reading). The source allows complex roots; the theorem is stated for real
  roots of real polynomials. See `QuarteroniSaccoSaleri.Chapter06.equation_6_7`.

## Not formalized

* **Equation (6.7) for complex roots.** It would need `IsRootOfMultiplicity` over $\mathbb{C}$,
  which is not in the backbone.
-/

open Conditioning Filter Polynomial Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

section Equation63

variable {φ G : ℝ → ℝ} {d : ℝ}

/-- **Equation (6.3)** of [quarteroni2000numerical], absolute condition number. Let
$\varphi : \mathbb{R} \to \mathbb{R}$ be continuously differentiable and $d \in \mathbb{R}$. Let
$G$ be a local inverse of $\varphi$ near $d$ that is continuous at $d$, that is,
$\varphi(G(y)) = y$ for all $y$ near $d$. Let $\alpha = G(d)$ be a simple root of
$f(x) = \varphi(x) - d$, that is, $f'(\alpha) \neq 0$. Then the first-order absolute condition
number of the root is $$K_{abs}(d) = \frac{1}{|f'(\alpha)|}.$$

The source writes $K_{abs}(d) \simeq 1/|f'(\alpha)|$; here it is an equality for the first-order
condition number. This is `QuarteroniSaccoSaleri.Chapter02.example_2_4` with $f' = \varphi'$.

**Reading.** The displayed approximate sensitivities become exact local condition numbers for a
continuous local inverse branch with nonzero derivative. The relative formula requires nonzero datum
and root.
-/
theorem equation_6_3_abs (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hf' : deriv (fun x => φ x - d) (G d) ≠ 0) :
    absCondNumber G univ d = ENNReal.ofReal |deriv (fun x => φ x - d) (G d)|⁻¹ := by
  rw [deriv_sub_const] at hf' ⊢
  exact Chapter02.example_2_4 hφ hG hinv hf'

/-- **Equation (6.3)** of [quarteroni2000numerical], relative condition number. Under the hypotheses
of `QuarteroniSaccoSaleri.Chapter06.equation_6_3_abs`, and with $d \neq 0$ and
$\alpha = G(d) \neq 0$, the first-order relative condition number of the root is $$K(d) =
\frac{|d|}{|\alpha|\, |f'(\alpha)|}.$$

This is `QuarteroniSaccoSaleri.Chapter02.example_2_4_rel`.

**Reading.** The displayed approximate sensitivities become exact local condition numbers for a
continuous local inverse branch with nonzero derivative. The relative formula requires nonzero datum
and root.
-/
theorem equation_6_3_rel (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hf' : deriv (fun x => φ x - d) (G d) ≠ 0) (hd : d ≠ 0)
    (hα : G d ≠ 0) :
    relCondNumber G univ d = ENNReal.ofReal (|d| / (|G d| * |deriv (fun x => φ x - d) (G d)|)) := by
  rw [deriv_sub_const] at hf' ⊢
  rw [Chapter02.example_2_4_rel hφ hG hinv hf' hd hα]
  congr 1
  have := abs_pos.2 hα
  have := abs_pos.2 hf'
  field_simp

/-- **Equation (6.4)** of [quarteroni2000numerical], the multiple-root case as a condition number.
Let $\varphi$, $d$ and $G$ be as in `QuarteroniSaccoSaleri.Chapter06.equation_6_3_abs`, and let
$\alpha = G(d)$ be a root of $f = \varphi - d$ of multiplicity $m \ge 2$, so that
$f'(\alpha) = 0$. Then the first-order absolute condition number of the root is infinite:
$K_{abs}(d) = +\infty$.

This is the precise form of the remark of the source that "$K_{abs}(d)$ could nevertheless be a
large number". It is `QuarteroniSaccoSaleri.Chapter02.example_2_4_multiple_root`.

**Reading.** For multiplicity at least two, the unbounded first-order condition number is stated for
a continuous local inverse branch.
-/
theorem equation_6_4_absCondNumber_eq_top (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) {m : ℕ} (hm : 2 ≤ m)
    (hα : IsRootOfMultiplicity (fun x => φ x - d) (G d) m) : absCondNumber G univ d = ⊤ := by
  refine Chapter02.example_2_4_multiple_root hφ hG hinv ?_
  have := hα.1 1 (by omega)
  rwa [iteratedDeriv_one, deriv_sub_const] at this

end Equation63

section MultipleRoot

variable {f : ℝ → ℝ} {α : ℝ} {m : ℕ}

/-- **Equation (6.4)** of [quarteroni2000numerical], the multiple-root asymptotics. Let $m \ge 1$,
let $f : \mathbb{R} \to \mathbb{R}$ be $m$ times continuously differentiable at $\alpha$, and
let $\alpha$ be a root of $f$ of multiplicity $m$. Then $$\frac{|x - \alpha|}{|f(x)|^{1/m}} \to
\Big(\frac{m!}{|f^{(m)}(\alpha)|}\Big)^{1/m} \quad \text{as } x \to \alpha,\ x \neq \alpha.$$ So
a perturbation $\delta d = f(\alpha + \delta\alpha)$ of the datum moves the root by
$|\delta\alpha| \simeq (m!/|f^{(m)}(\alpha)|)^{1/m} |\delta d|^{1/m}$.

**Reading.** The source writes $K_{abs}(d) \simeq |m!\,\delta d / f^{(m)}(\alpha)|^{1/m} /
|\delta d|$. This quantity depends on $\delta d$, so it is not a condition number in the sense
of Definition 2.1, whose value at a multiple root is $+\infty$
(`QuarteroniSaccoSaleri.Chapter06.equation_6_4_absCondNumber_eq_top`). Its content is the
asymptotic relation above, stated as a limit.

The proof specializes `IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow`.

**Reading.** The displayed nonlinear dependence is a punctured asymptotic ratio under local
smoothness of order equal to the root multiplicity.
-/
theorem equation_6_4 (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α) (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => |x - α| / |f x| ^ (1 / (m : ℝ))) (𝓝[≠] α)
      (𝓝 ((m.factorial / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)))) :=
  hα.tendsto_abs_sub_div_abs_rpow hm hf

/-- **Equation (6.5)** of [quarteroni2000numerical], error and residual at a simple root. Let
$f : \mathbb{R} \to \mathbb{R}$ be continuously differentiable at $\alpha$, with
$f(\alpha) = 0$, $f'(\alpha) \neq 0$ and $\alpha \neq 0$. Then for every $c > 1/|f'(\alpha)|$
and every $\hat\alpha$ close enough to $\alpha$, $$\frac{|\hat\alpha - \alpha|}{|\alpha|} \le
c\, \frac{|\hat r|}{|\alpha|}, \qquad \hat r = f(\hat\alpha).$$

**Reading.** The source writes $|\hat\alpha - \alpha|/|\alpha| \lesssim |\hat r| /
(|f'(\alpha)|\, |\alpha|)$. The theorem reads $\lesssim$ as: for every constant above
$1/|f'(\alpha)|$, the inequality holds near $\alpha$.

This is the case $m = 1$ of `IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow`.

**Reading.** The asymptotic bound becomes an eventual inequality with any constant strictly greater
than the leading coefficient. Relative errors require a nonzero root. Equation (6.7) is stated for
real roots and the perturbing polynomial can have arbitrary degree.
-/
theorem equation_6_5 (hf : ContDiffAt ℝ 1 f α) (hα : f α = 0) (hf' : deriv f α ≠ 0)
    (hα0 : α ≠ 0) {c : ℝ} (hc : 1 / |deriv f α| < c) :
    ∀ᶠ x in 𝓝 α, |x - α| / |α| ≤ c * |f x| / |α| := by
  have hroot : IsRootOfMultiplicity f α 1 := isRootOfMultiplicity_one_iff.2 ⟨hα, hf'⟩
  have hc' : ((1 : ℕ).factorial / |iteratedDeriv 1 f α|) ^ (1 / ((1 : ℕ) : ℝ)) < c := by
    simpa using hc
  filter_upwards [hroot.eventually_abs_sub_le_mul_abs_rpow le_rfl (by simpa using hf) hc'] with x hx
  have hα' : 0 < |α| := abs_pos.2 hα0
  rw [div_le_div_iff_of_pos_right hα']
  simpa using hx

/-- For $a \ge 0$, $b \in \mathbb{R}$ and $m \ge 1$, $$\frac{a^{1/m}}{|b|} =
\Big(\frac{a}{|b|^m}\Big)^{1/m}.$$ This relates the constants of (6.4) and (6.6) of
[quarteroni2000numerical]. -/
theorem rpow_div_abs_eq {a b : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) :
    a ^ (1 / (m : ℝ)) / |b| = (a / |b| ^ m) ^ (1 / (m : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  rw [Real.div_rpow ha (pow_nonneg (abs_nonneg b) m), one_div,
    Real.pow_rpow_inv_natCast (abs_nonneg b) hm0]

/-- **Equation (6.6)** of [quarteroni2000numerical], error and residual at a root of multiplicity
$m$. Let $m \ge 1$, let $f : \mathbb{R} \to \mathbb{R}$ be $m$ times continuously differentiable
at $\alpha$, and let $\alpha \neq 0$ be a root of $f$ of multiplicity $m$. Then for every $$c >
\Big(\frac{m!}{|f^{(m)}(\alpha)|\, |\alpha|^m}\Big)^{1/m}$$ and every $\hat\alpha$ close enough
to $\alpha$, $$\frac{|\hat\alpha - \alpha|}{|\alpha|} \le c\, |\hat r|^{1/m}, \qquad \hat r =
f(\hat\alpha).$$

**Reading.** The source writes this bound with $\lesssim$ and the constant above. The theorem
reads $\lesssim$ as: for every constant above the asymptotic one, the inequality holds near
$\alpha$.

The proof specializes `IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow` with the
constant $c |\alpha|$.

**Reading.** The asymptotic bound becomes an eventual inequality with any constant strictly greater
than the leading coefficient. Relative errors require a nonzero root. Equation (6.7) is stated for
real roots and the perturbing polynomial can have arbitrary degree.
-/
theorem equation_6_6 (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α) (hα : IsRootOfMultiplicity f α m)
    (hα0 : α ≠ 0) {c : ℝ}
    (hc : (m.factorial / (|iteratedDeriv m f α| * |α| ^ m)) ^ (1 / (m : ℝ)) < c) :
    ∀ᶠ x in 𝓝 α, |x - α| / |α| ≤ c * |f x| ^ (1 / (m : ℝ)) := by
  have hα' : 0 < |α| := abs_pos.2 hα0
  have hc' : (m.factorial / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)) < c * |α| := by
    rw [← div_lt_iff₀ hα', rpow_div_abs_eq (by positivity) hm, div_div]
    exact hc
  filter_upwards [hα.eventually_abs_sub_le_mul_abs_rpow hm hf hc'] with x hx
  rw [div_le_iff₀ hα']
  linarith

/-- **Equation (6.7)** of [quarteroni2000numerical], the sensitivity of a polynomial root to a
perturbation of the coefficients. Let $p, q$ be real polynomials, and let $\alpha \neq 0$ be a
real root of $p$ of multiplicity $m \ge 1$. Then for every $$c >
\Big(\frac{m!}{|p^{(m)}(\alpha)|\, |\alpha|^m}\Big)^{1/m}$$ there is $\delta > 0$ such that
every real root $\hat\alpha$ of $p + q$ with $|\hat\alpha - \alpha| < \delta$ satisfies
$$\frac{|\hat\alpha - \alpha|}{|\alpha|} \le c\, |q(\hat\alpha)|^{1/m}.$$

**Reading.** The source states (6.7) with $\lesssim$ and for complex roots. The theorem reads
$\lesssim$ as in (6.6), and it is stated for real roots only; the complex form would need
`IsRootOfMultiplicity` over $\mathbb{C}$, which is not in the backbone.

The multiplicity is `Polynomial.rootMultiplicity`. The theorem is (6.6) for $f = p$, whose
residual at $\hat\alpha$ is $p(\hat\alpha) = -q(\hat\alpha)$.

**Reading.** The asymptotic bound becomes an eventual inequality with any constant strictly greater
than the leading coefficient. Relative errors require a nonzero root. Equation (6.7) is stated for
real roots and the perturbing polynomial can have arbitrary degree.
-/
theorem equation_6_7 {p q : ℝ[X]} {α : ℝ} (hα0 : α ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hmult : p.rootMultiplicity α = m) {c : ℝ}
    (hc : (m.factorial / (|(derivative^[m] p).eval α| * |α| ^ m)) ^ (1 / (m : ℝ)) < c) :
    ∃ δ > 0, ∀ x, |x - α| < δ → (p + q).IsRoot x →
      |x - α| / |α| ≤ c * |q.eval x| ^ (1 / (m : ℝ)) := by
  have hp : p ≠ 0 := by
    rintro rfl
    rw [rootMultiplicity_zero] at hmult
    omega
  have hroot : IsRootOfMultiplicity (fun x => p.eval x) α m :=
    (isRootOfMultiplicity_eval_iff hp).2 hmult
  have hf : ContDiffAt ℝ m (fun x => p.eval x) α := by
    have := Polynomial.contDiff_aeval (𝕜 := ℝ) p m
    simpa [Polynomial.coe_aeval_eq_eval] using this.contDiffAt
  have hc' : (m.factorial / (|iteratedDeriv m (fun x => p.eval x) α| * |α| ^ m)) ^ (1 / (m : ℝ))
      < c := by
    rwa [iteratedDeriv_eval]
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (equation_6_6 hm hf hroot hα0 hc')
  refine ⟨δ, hδ, fun x hx hroot' => ?_⟩
  have := h (by rwa [Real.dist_eq])
  have hq : |p.eval x| = |q.eval x| := by
    rw [IsRoot.def, eval_add, add_eq_zero_iff_eq_neg] at hroot'
    rw [hroot', abs_neg]
  simpa [hq] using this

end MultipleRoot

section Example61

open Complex

/-- **Example 6.1** of [quarteroni2000numerical], the roots. Let $\varepsilon > 0$. A complex number
$z$ is a root of the perturbed polynomial $\hat p_4(x) = (x - 1)^4 - \varepsilon$ if and only if
$$z = 1 + \varepsilon^{1/4} i^k \quad \text{for some } k = 0, 1, 2, 3.$$ So the four roots lie
at angular spacing $\pi/2$ on the circle of radius $\varepsilon^{1/4}$ about $1$, the fourfold
root of $p_4(x) = (x - 1)^4$.

**Correction.** The four displacements have the four phases $i^k$. Their common absolute size is the
fourth root of the perturbation. The identities hold for all positive perturbations.
-/
theorem example_6_1 {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ((X - 1) ^ 4 - C (ε : ℂ)).IsRoot z ↔
      ∃ k : Fin 4, z = 1 + ((ε ^ (1 / 4 : ℝ) : ℝ) : ℂ) * I ^ (k : ℕ) := by
  set r : ℝ := ε ^ (1 / 4 : ℝ) with hr
  have hr4 : r ^ 4 = ε := by
    rw [hr, one_div, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_inv_natCast_pow hε.le (by norm_num)]
  have hr0 : 0 < r := Real.rpow_pos_of_pos hε _
  have key : ∀ w : ℂ, w ^ 4 - (r : ℂ) ^ 4 =
      (w - r) * (w + r) * (w - r * I) * (w + r * I) := by
    intro w
    ring_nf
    simp only [I_sq]
    ring
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]
  have hε' : (ε : ℂ) = (r : ℂ) ^ 4 := by rw [← hr4]; push_cast; rfl
  rw [IsRoot.def, eval_sub, eval_pow, eval_sub, eval_X, eval_one, eval_C, hε', key,
    mul_eq_zero, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg,
    add_eq_zero_iff_eq_neg]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨0, by simp only [Fin.val_zero, pow_zero]; linear_combination h⟩
    · exact ⟨2, by simp only [Fin.val_two, I_sq]; linear_combination h⟩
    · exact ⟨1, by simp only [Fin.val_one, pow_one]; linear_combination h⟩
    · exact ⟨3, by rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, hI3]; linear_combination h⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl (Or.inl (Or.inl (by simp)))
    · exact Or.inl (Or.inr (by simp))
    · exact Or.inl (Or.inl (Or.inr (by simp [I_sq])))
    · exact Or.inr (by simp [hI3])

/-- **Example 6.1** of [quarteroni2000numerical], the relative error. Let $\varepsilon > 0$. Every
root $\hat\alpha$ of $(x - 1)^4 - \varepsilon$ has the relative error $$\frac{|\hat\alpha -
\alpha|}{|\alpha|} = \varepsilon^{1/4}$$ from the fourfold root $\alpha = 1$. So the problem is
stable ($\hat\alpha \to 1$ as $\varepsilon \to 0$) but ill-conditioned.

Here $m = 4$, $p_4^{(4)} = 4!$ and $|q(\hat\alpha)| = \varepsilon$, so the asymptotic constant
of (6.7) is $1$, and (6.7) with this constant holds with equality.

**Correction.** The four displacements have the four phases $i^k$. Their common absolute size is the
fourth root of the perturbation. The identities hold for all positive perturbations.
-/
theorem example_6_1_norm {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : ((X - 1) ^ 4 - C (ε : ℂ)).IsRoot z) :
    ‖z - 1‖ / ‖(1 : ℂ)‖ = ε ^ (1 / 4 : ℝ) := by
  obtain ⟨k, rfl⟩ := (example_6_1 hε z).1 hz
  have hr0 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.le _
  rw [norm_one, div_one, add_sub_cancel_left, norm_mul, norm_pow, norm_I, one_pow, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hr0]

end Example61

end QuarteroniSaccoSaleri.Chapter06
