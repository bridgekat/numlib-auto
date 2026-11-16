/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Deriv` and
`Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, beside the one-variable `ContDiffOn` lemmas.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Calculus of $C^n$ functions on a compact interval

This module treats real functions of class $C^2$ or $C^3$ on a compact interval $[a, b]$. It passes
between three ways to name their derivatives. The derivatives within the interval (`derivWithin`,
`iteratedDerivWithin`) exist at the endpoints as well. The ordinary derivatives (`deriv`,
`iteratedDeriv`) agree with them at interior points. Explicit derivative data, such as a function
$u_1$ with the derivative $u_1(x)$ of $u$ within $[a, b]$ at each $x$, are what the error analyses
of one-step methods and the weak formulations of boundary value problems have at hand.

## Main results

* `contDiffOn_two_of_hasDerivWithinAt`: explicit derivative data $u' = u_1$ and $u_1' = u_2$ within
  a set of unique differentiability, with $u_2$ continuous, make $u$ a $C^2$ function on the set.
* `iteratedDeriv_two_eq_of_hasDerivWithinAt`: at interior points, the ordinary second derivative is
  the second derivative datum $u_2$.
* `hasDerivAt_of_contDiffOn_two`: at an interior point, a $C^2$ function on $[a, b]$ has the
  ordinary derivative given by its derivative within $[a, b]$, and that function has the ordinary
  derivative $u''$.
* `hasDerivWithinAt_derivWithin_of_contDiffOn_two`,
  `hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three`,
  `hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn`: a $C^2$, $C^3$ or $C^k$ function on $[a, b]$
  has, within $[a, b]$ and at every point of it, the derivatives given by `derivWithin` and
  `iteratedDerivWithin`.
* `eqOn_zero_of_hasDerivAt_zero`: a continuous function on $[a, b]$ whose derivative has derivative
  $0$ in the interior, and which vanishes at both ends, vanishes on $[a, b]$.
-/

open Set Filter Topology intervalIntegral

/-- Let $s \subseteq \mathbb{R}$ be a set of unique differentiability, and let
$u, u_1, u_2 : \mathbb{R} \to \mathbb{R}$. If at every point $x \in s$ the function $u$ has the
derivative $u_1(x)$ within $s$ and $u_1$ has the derivative $u_2(x)$ within $s$, and $u_2$ is
continuous on $s$, then $u$ is $C^2$ on $s$. -/
theorem contDiffOn_two_of_hasDerivWithinAt {u u₁ u₂ : ℝ → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (h₁ : ∀ x ∈ s, HasDerivWithinAt u (u₁ x) s x) (h₂ : ∀ x ∈ s, HasDerivWithinAt u₁ (u₂ x) s x)
    (h₃ : ContinuousOn u₂ s) : ContDiffOn ℝ 2 u s := by
  have hd₁ : ∀ x ∈ s, derivWithin u s x = u₁ x := fun x hx => (h₁ x hx).derivWithin (hs x hx)
  have hd₂ : ∀ x ∈ s, derivWithin u₁ s x = u₂ x := fun x hx => (h₂ x hx).derivWithin (hs x hx)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun x hx => (h₁ x hx).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
  refine ContDiffOn.congr ?_ hd₁
  rw [contDiffOn_one_iff_derivWithin hs]
  exact ⟨fun x hx => (h₂ x hx).differentiableWithinAt, h₃.congr hd₂⟩

/-- Let $u, u_1, u_2 : \mathbb{R} \to \mathbb{R}$. If at every point of $[a, b]$ the function $u$
has the derivative $u_1$ within $[a, b]$ and $u_1$ has the derivative $u_2$ within $[a, b]$,
then $u''(x) = u_2(x)$ for every interior point $x \in (a, b)$.

The second derivative $u''$ is the ordinary derivative `iteratedDeriv 2 u`. -/
theorem iteratedDeriv_two_eq_of_hasDerivWithinAt {u u₁ u₂ : ℝ → ℝ} {a b x : ℝ}
    (h₁ : ∀ x ∈ Icc a b, HasDerivWithinAt u (u₁ x) (Icc a b) x)
    (h₂ : ∀ x ∈ Icc a b, HasDerivWithinAt u₁ (u₂ x) (Icc a b) x) (hx : x ∈ Ioo a b) :
    iteratedDeriv 2 u x = u₂ x := by
  have hderiv : ∀ y ∈ Ioo a b, deriv u y = u₁ y := fun y hy =>
    ((h₁ y (Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2)).deriv
  have heq : deriv u =ᶠ[𝓝 x] u₁ := eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) hderiv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  exact ((h₂ x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv

/-- Let $u$ be $C^2$ on $[a, b]$, and let $x \in (a, b)$. Then $u$ has the ordinary derivative
$u'(x)$ at $x$, where $u'$ is the derivative of $u$ within $[a, b]$, and $u'$ has the ordinary
derivative $u''(x)$ at $x$.

Here $u'$ is `derivWithin u (Icc a b)` and $u''$ is `iteratedDeriv 2 u`. -/
theorem hasDerivAt_of_contDiffOn_two {u : ℝ → ℝ} {a b x : ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) (hx : x ∈ Ioo a b) :
    HasDerivAt u (derivWithin u (Icc a b) x) x ∧
      HasDerivAt (derivWithin u (Icc a b)) (iteratedDeriv 2 u x) x := by
  have hmem : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  refine ⟨((hu.differentiableOn (by norm_num)) x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
    |>.hasDerivAt hmem, ?_⟩
  have hopen : ContDiffOn ℝ (1 + 1) u (Ioo a b) := hu.mono Ioo_subset_Icc_self
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] at hopen
  have hd : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    ((hopen.2.2.differentiableOn one_ne_zero) x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
      |>.hasDerivAt
  have heq : derivWithin u (Icc a b) =ᶠ[𝓝 x] deriv u :=
    eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy =>
      derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact hd.congr_of_eventuallyEq heq

/-- Let $a \le b$, let $w$ and $w_1$ be continuous on $[a, b]$, and suppose that at every
$x \in (a, b)$ the function $w$ has the derivative $w_1(x)$ and $w_1$ has the derivative $0$. If
$w(a) = w(b) = 0$, then $w = 0$ on $[a, b]$.

The hypotheses make $w$ affine on $[a, b]$. -/
theorem eqOn_zero_of_hasDerivAt_zero {w w₁ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (hw₁ : ContinuousOn w₁ (Icc a b))
    (h₁ : ∀ x ∈ Ioo a b, HasDerivAt w (w₁ x) x) (h₂ : ∀ x ∈ Ioo a b, HasDerivAt w₁ 0 x)
    (ha : w a = 0) (hb : w b = 0) : EqOn w 0 (Icc a b) := by
  -- `w₁` is constant on `[a, b]`
  have hconst : ∀ x ∈ Icc a b, w₁ x = w₁ a := by
    intro x hx
    have h := integral_eq_sub_of_hasDerivAt_of_le hx.1 (hw₁.mono (Icc_subset_Icc le_rfl hx.2))
      (f' := fun _ => (0 : ℝ)) (fun t ht => h₂ t ⟨ht.1, ht.2.trans_le hx.2⟩)
      intervalIntegrable_const
    rw [integral_zero] at h
    exact (sub_eq_zero.1 h.symm)
  -- hence `w x = (x - a) w₁ a`
  have hw' : ∀ x ∈ Icc a b, w x = (x - a) * w₁ a := by
    intro x hx
    have h := integral_eq_sub_of_hasDerivAt_of_le hx.1 (hw.mono (Icc_subset_Icc le_rfl hx.2))
      (fun t ht => h₁ t ⟨ht.1, ht.2.trans_le hx.2⟩)
      ((hw₁.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
    rw [ha, sub_zero] at h
    rw [← h, integral_congr (g := fun _ => w₁ a) fun t ht => ?_, integral_const, smul_eq_mul]
    rw [uIcc_of_le hx.1] at ht
    exact hconst t ⟨ht.1, ht.2.trans hx.2⟩
  rcases hab.eq_or_lt with rfl | hlt
  · intro x hx
    rw [Icc_self, mem_singleton_iff] at hx
    rw [hx]
    exact ha
  · have hzero : w₁ a = 0 := by
      have h := hw' b ⟨hab, le_rfl⟩
      rw [hb] at h
      rcases mul_eq_zero.1 h.symm with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hlt.ne'
      · exact h0
    intro x hx
    rw [Pi.zero_apply, hw' x hx, hzero, mul_zero]

/-- Let $a < b$, and let $y$ be $C^2$ on $[a, b]$. Then at every point $s \in [a, b]$, the function
$y$ has the derivative $y'(s)$ within $[a, b]$, and $y'$ has the derivative $y''(s)$ within
$[a, b]$.

Here $y'$ is `derivWithin y (Icc a b)` and $y''$ is `iteratedDerivWithin 2 y (Icc a b)`. This
turns a `ContDiffOn` hypothesis into the explicit derivative hypotheses of `Numlib.ODE.OneStep`. -/
theorem hasDerivWithinAt_derivWithin_of_contDiffOn_two {a b : ℝ} (hlt : a < b) {y : ℝ → ℝ}
    (hy : ContDiffOn ℝ 2 y (Icc a b)) :
    (∀ s ∈ Icc a b, HasDerivWithinAt y (derivWithin y (Icc a b) s) (Icc a b) s) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt (derivWithin y (Icc a b))
        (iteratedDerivWithin 2 y (Icc a b) s) (Icc a b) s := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  rw [h2, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)] at hy
  refine ⟨fun s hs => (hy.1 s hs).hasDerivWithinAt, fun s hs => ?_⟩
  have := ((hy.2.2.differentiableOn one_ne_zero) s hs).hasDerivWithinAt
  rwa [iteratedDerivWithin_succ, iteratedDerivWithin_one]

/-- Let $a < b$, and let $y$ be $C^3$ on $[a, b]$. Then at every point $s \in [a, b]$, within
$[a, b]$, the function $y$ has the derivative $y'(s)$, $y'$ has the derivative $y''(s)$, and
$y''$ has the derivative $y'''(s)$.

Here $y'$ is `derivWithin y (Icc a b)`, and $y''$ and $y'''$ are
`iteratedDerivWithin 2 y (Icc a b)` and `iteratedDerivWithin 3 y (Icc a b)`. This is the
three-level form of `hasDerivWithinAt_derivWithin_of_contDiffOn_two`. -/
theorem hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three {a b : ℝ} (hlt : a < b)
    {y : ℝ → ℝ} (hy : ContDiffOn ℝ 3 y (Icc a b)) :
    (∀ s ∈ Icc a b, HasDerivWithinAt y (derivWithin y (Icc a b) s) (Icc a b) s) ∧
    (∀ s ∈ Icc a b, HasDerivWithinAt (derivWithin y (Icc a b))
      (iteratedDerivWithin 2 y (Icc a b) s) (Icc a b) s) ∧
    ∀ s ∈ Icc a b, HasDerivWithinAt (iteratedDerivWithin 2 y (Icc a b))
      (iteratedDerivWithin 3 y (Icc a b) s) (Icc a b) s := by
  have h3 : (3 : WithTop ℕ∞) = 2 + 1 := rfl
  rw [h3, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)] at hy
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_derivWithin_of_contDiffOn_two hlt hy.2.2
  refine ⟨fun s hs => (hy.1 s hs).hasDerivWithinAt, fun s hs => ?_, fun s hs => ?_⟩
  · have := h1 s hs
    rwa [show iteratedDerivWithin 2 y (Icc a b) = derivWithin (derivWithin y (Icc a b)) (Icc a b)
      by rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]]
  · have := h2 s hs
    rwa [show iteratedDerivWithin 2 y (Icc a b) = derivWithin (derivWithin y (Icc a b)) (Icc a b)
      by rw [iteratedDerivWithin_succ, iteratedDerivWithin_one],
      show iteratedDerivWithin 3 y (Icc a b) =
        iteratedDerivWithin 2 (derivWithin y (Icc a b)) (Icc a b) from
        iteratedDerivWithin_succ']

/-- Let $a < b$, let $k \in \mathbb{N} \cup \{\infty, \omega\}$, let $y$ be $C^k$ on $[a, b]$, and
let $j < k$ be a natural number. Then at every point $s \in [a, b]$, the $j$-th derivative
$y^{(j)}$ of $y$ within $[a, b]$ has the derivative $y^{(j+1)}(s)$ within $[a, b]$.

The derivatives are `iteratedDerivWithin j y (Icc a b)`. This is the general form of
`hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three`. -/
theorem hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn {a b : ℝ} (hlt : a < b) {y : ℝ → ℝ}
    {k : WithTop ℕ∞} (hy : ContDiffOn ℝ k y (Icc a b)) {j : ℕ} (hj : (j : WithTop ℕ∞) < k)
    {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivWithinAt (iteratedDerivWithin j y (Icc a b))
      (iteratedDerivWithin (j + 1) y (Icc a b) s) (Icc a b) s := by
  rw [iteratedDerivWithin_succ]
  exact ((hy.differentiableOn_iteratedDerivWithin hj (uniqueDiffOn_Icc hlt)) s hs).hasDerivWithinAt
