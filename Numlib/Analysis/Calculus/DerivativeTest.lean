/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.DerivativeTest`, beside the sufficient second-derivative
test `isLocalMin_of_deriv_deriv_pos`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The necessary second-derivative test

Mathlib's `isLocalMin_of_deriv_deriv_pos` is the sufficient second-derivative test: a critical point
with positive second derivative is a local minimum. This module proves the necessary test, in the
forms that the classical maximum principles of [brezis2011functional] use (Chapter 8, Remarks 26 and
27, and Theorem 10.6). At an interior local maximum of a function $f : \mathbb{R} \to \mathbb{R}$
that is continuous there, $f'' \le 0$. At an endpoint $x_0$, a function that is $C^2$ on
$[x_0, x_0 + \delta)$, has one-sided derivative $u'(x_0^+) = 0$ and has a local maximum at $x_0$
among the points to the right satisfies $u''(x_0^+) \le 0$. On a real normed space, the Hessian of a
$C^2$ function is negative semidefinite at a local maximum and positive semidefinite at a local
minimum.

The several-variable form follows from the one-variable test applied to the restriction
$s \mapsto f(x_0 + s v)$ to a line, whose second derivative at $0$ is $D^2 f(x_0)[v, v]$. The
Laplacian form `IsLocalMax.laplacian_nonpos` is in
`Numlib.Analysis.Calculus.DerivativeTest.Laplacian`.

## Main results

* `IsLocalMax.deriv_deriv_nonpos`, `IsLocalMin.deriv_deriv_nonneg`: at an interior local maximum
  (minimum) of a function continuous there, $f'' \le 0$ ($f'' \ge 0$).
* `IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici`: the one-sided test at an endpoint, with explicit
  derivative data.
* `IsLocalMaxOn.deriv_deriv_nonpos_of_deriv_eq_zero`: the one-sided test at an endpoint for a
  function that is $C^2$ to the right of it.
* `ContDiffAt.deriv_deriv_comp_add_smul`: the second derivative of $s \mapsto f(x_0 + s v)$ at $0$
  is $D^2 f(x_0)[v, v]$.
* `IsLocalMax.fderiv_fderiv_apply_self_nonpos`, `IsLocalMin.fderiv_fderiv_apply_self_nonneg`: the
  Hessian of a $C^2$ function is negative (positive) semidefinite at a local maximum (minimum).

## Implementation notes

* The interior test uses Mathlib's convention that `deriv` is $0$ where the derivative does not
  exist, so no differentiability is assumed. The continuity cannot be dropped: the function with
  $f(x) = x^2/2$ for $x \neq 0$ and $f(0) = 1$ has a local maximum at $0$, with `deriv f = id` and
  `deriv (deriv f) 0 = 1`.
* The one-sided derivatives at an endpoint $x_0$ are `derivWithin … (Set.Ici x₀)`.
* The Hessian $D^2 f(x_0)[v, v]$ appears in two forms, `fderiv ℝ (fderiv ℝ f) x₀ v v` and
  `iteratedFDeriv ℝ 2 f x₀ ![v, v]`.
-/

open Filter Set Topology

/-- The **second-derivative test at an interior maximum**. Let $f : \mathbb{R} \to \mathbb{R}$ have
a local maximum at $x_0$ and be continuous at $x_0$. Then $f''(x_0) \le 0$.

The second derivative is `deriv (deriv f) x₀`, which is $0$ where a derivative does not exist,
so no differentiability is assumed. The continuity is needed. The proof is the contrapositive of
`isLocalMin_of_deriv_deriv_pos`: a point that is both a local maximum and a local minimum has a
neighbourhood on which $f$ is constant, and there both derivatives vanish. -/
theorem IsLocalMax.deriv_deriv_nonpos {f : ℝ → ℝ} {x₀ : ℝ} (hf : IsLocalMax f x₀)
    (hc : ContinuousAt f x₀) : deriv (deriv f) x₀ ≤ 0 := by
  by_contra hpos
  replace hpos : 0 < deriv (deriv f) x₀ := not_le.1 hpos
  have hmin : IsLocalMin f x₀ := isLocalMin_of_deriv_deriv_pos hpos hf.deriv_eq_zero hc
  -- `f` is constant near `x₀`
  have hconst : ∀ᶠ y in 𝓝 x₀, f y = f x₀ := by
    filter_upwards [hf, hmin] with y hy hy'
    exact le_antisymm hy hy'
  -- hence `deriv f` vanishes near `x₀`, and so does `deriv (deriv f)` at `x₀`
  have hderiv : ∀ᶠ y in 𝓝 x₀, deriv f y = 0 := by
    filter_upwards [eventually_eventually_nhds.2 hconst] with y hy
    rw [Filter.EventuallyEq.deriv_eq (hy : f =ᶠ[𝓝 y] fun _ ↦ f x₀), deriv_const]
  have : deriv (deriv f) x₀ = 0 := by
    rw [Filter.EventuallyEq.deriv_eq (hderiv : deriv f =ᶠ[𝓝 x₀] fun _ ↦ 0), deriv_const]
  exact absurd this hpos.ne'

/-- The **second-derivative test at an interior minimum**. Let $f : \mathbb{R} \to \mathbb{R}$ have
a local minimum at $x_0$ and be continuous at $x_0$. Then $f''(x_0) \ge 0$.

The second derivative is `deriv (deriv f) x₀`. The proof applies `IsLocalMax.deriv_deriv_nonpos`
to $-f$. -/
theorem IsLocalMin.deriv_deriv_nonneg {f : ℝ → ℝ} {x₀ : ℝ} (hf : IsLocalMin f x₀)
    (hc : ContinuousAt f x₀) : 0 ≤ deriv (deriv f) x₀ := by
  have h := hf.neg.deriv_deriv_nonpos hc.neg
  have hd : deriv (fun x => -f x) = fun x => -deriv f x := funext fun x => deriv.fun_neg
  rw [hd, deriv.fun_neg] at h
  linarith

/-- The **one-sided second-derivative test at an endpoint**, with explicit derivative data. Let
$u, u' : \mathbb{R} \to \mathbb{R}$ and $x_0, c \in \mathbb{R}$. Suppose that $u$ has a local
maximum at $x_0$ among the points of $[x_0, \infty)$, that $u$ has the derivative $u'(y)$ within
$[x_0, \infty)$ at every $y \ge x_0$ near $x_0$, that $u'$ has the derivative $c$ within
$[x_0, \infty)$ at $x_0$, and that $u'(x_0) = 0$. Then $c \le 0$.

If $c > 0$, then $u'$ is positive just to the right of $x_0$, and by the mean value theorem $u$
increases there. -/
theorem IsLocalMaxOn.nonpos_of_hasDerivWithinAt_Ici {u u' : ℝ → ℝ} {x₀ c : ℝ}
    (hmax : IsLocalMaxOn u (Ici x₀) x₀)
    (hu : ∀ᶠ y in 𝓝[≥] x₀, HasDerivWithinAt u (u' y) (Ici x₀) y)
    (hu' : HasDerivWithinAt u' c (Ici x₀) x₀) (h0 : u' x₀ = 0) : c ≤ 0 := by
  by_contra hc
  replace hc : 0 < c := not_le.1 hc
  -- `u' > 0` just to the right of `x₀`
  have hpos : ∀ᶠ y in 𝓝[>] x₀, 0 < u' y := by
    have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x₀)).1
      (hu'.mono Ioi_subset_Ici_self)
    filter_upwards [hslope.eventually (eventually_gt_nhds hc), self_mem_nhdsWithin] with y hy hy'
    rw [slope_def_field, h0, sub_zero] at hy
    exact (div_pos_iff_of_pos_right (sub_pos.2 hy')).1 hy
  -- a right neighbourhood on which `u ≤ u x₀`, `u` is differentiable and `u' > 0`
  have hall : ∀ᶠ y in 𝓝[>] x₀,
      u y ≤ u x₀ ∧ HasDerivWithinAt u (u' y) (Ici x₀) y ∧ 0 < u' y := by
    have h1 : ∀ᶠ y in 𝓝[>] x₀, u y ≤ u x₀ :=
      (hmax : ∀ᶠ y in 𝓝[Ici x₀] x₀, u y ≤ u x₀).filter_mono
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact h1.and ((hu.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)).and hpos)
  obtain ⟨b, hb, hP⟩ := (nhdsGT_basis x₀).eventually_iff.1 hall
  set t := (x₀ + b) / 2 with ht
  have htx : x₀ < t := by rw [ht]; linarith
  have htb : t < b := by rw [ht]; linarith
  -- the mean value theorem on `[x₀, t]`
  have hx₀ : HasDerivWithinAt u (u' x₀) (Ici x₀) x₀ := hu.self_of_nhdsWithin (mem_Ici.2 le_rfl)
  have hcont : ContinuousOn u (Icc x₀ t) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with rfl | hlt
    · exact hx₀.continuousWithinAt.mono Icc_subset_Ici_self
    · exact ((hP ⟨hlt, hy.2.trans_lt htb⟩).2.1.hasDerivAt (Ici_mem_nhds hlt)).continuousAt
        |>.continuousWithinAt
  have hdiff : ∀ y ∈ Ioo x₀ t, HasDerivAt u (u' y) y := fun y hy ↦
    (hP ⟨hy.1, hy.2.trans htb⟩).2.1.hasDerivAt (Ici_mem_nhds hy.1)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope u u' htx hcont hdiff
  have hξpos : 0 < u' ξ := (hP ⟨hξ.1, hξ.2.trans htb⟩).2.2
  have hut : u t ≤ u x₀ := (hP ⟨htx, htb⟩).1
  have : u' ξ * (t - x₀) = u t - u x₀ := by
    rw [hξeq, div_mul_cancel₀ _ (sub_pos.2 htx).ne']
  nlinarith [mul_pos hξpos (sub_pos.2 htx)]

/-- The **one-sided second-derivative test at an endpoint** ([brezis2011functional], Chapter 8,
Remark 27). Let $\delta > 0$, let $u : \mathbb{R} \to \mathbb{R}$ be $C^2$ on
$[x_0, x_0 + \delta)$, let its one-sided derivative satisfy $u'(x_0^+) = 0$, and let $x_0$ be a
local maximum of $u$ among the points of $[x_0, \infty)$. Then the one-sided second derivative
satisfies $u''(x_0^+) \le 0$.

The one-sided derivatives are derivatives within `Set.Ici x₀`: $u'$ is
`derivWithin u (Set.Ici x₀)` and $u''(x_0^+)$ is `derivWithin (derivWithin u (Set.Ici x₀))
(Set.Ici x₀) x₀`. When $u$ is $C^2$ on a neighbourhood of $x_0$, they are the ordinary
derivatives (`derivWithin_of_mem_nhds`). -/
theorem IsLocalMaxOn.deriv_deriv_nonpos_of_deriv_eq_zero {u : ℝ → ℝ} {x₀ δ : ℝ} (hδ : 0 < δ)
    (hu : ContDiffOn ℝ 2 u (Ico x₀ (x₀ + δ))) (h0 : derivWithin u (Ici x₀) x₀ = 0)
    (hmax : IsLocalMaxOn u (Ici x₀) x₀) :
    derivWithin (derivWithin u (Ici x₀)) (Ici x₀) x₀ ≤ 0 := by
  set S := Ico x₀ (x₀ + δ) with hS
  have hSu : UniqueDiffOn ℝ S := uniqueDiffOn_Ico x₀ (x₀ + δ)
  have hSmem : ∀ y ∈ S, S ∈ 𝓝[Ici x₀] y := fun y hy ↦ by
    rw [hS, ← Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds hy.2)
  have hx₀S : x₀ ∈ S := ⟨le_rfl, by linarith⟩
  -- on `S`, the derivative within `S` is the one-sided derivative
  have hderiv : ∀ y ∈ S, derivWithin u S y = derivWithin u (Ici x₀) y := fun y hy ↦ by
    rw [hS, ← Ici_inter_Iio, derivWithin_inter (Iio_mem_nhds hy.2)]
  -- `u` is differentiable within `S`, with the one-sided derivative
  have hu1 : ∀ y ∈ S, HasDerivWithinAt u (derivWithin u (Ici x₀) y) (Ici x₀) y := fun y hy ↦ by
    rw [← hderiv y hy]
    exact ((hu.differentiableOn (by norm_num)) y hy).hasDerivWithinAt.mono_of_mem_nhdsWithin
      (hSmem y hy)
  -- the derivative within `S` is `C¹` on `S`, hence differentiable within `S` at `x₀`
  have hu2 : ContDiffOn ℝ 1 (derivWithin u S) S := by
    have h2 : ContDiffOn ℝ ((1 : ℕ) + 1) u S := hu
    exact ((contDiffOn_succ_iff_derivWithin hSu).1 h2).2.2
  have hc : HasDerivWithinAt (derivWithin u (Ici x₀)) (derivWithin (derivWithin u S) S x₀)
      (Ici x₀) x₀ := by
    refine (((hu2.differentiableOn one_ne_zero) x₀ hx₀S).hasDerivWithinAt.congr
      (fun y hy ↦ (hderiv y hy).symm) (hderiv x₀ hx₀S).symm).mono_of_mem_nhdsWithin
      (hSmem x₀ hx₀S)
  rw [hc.derivWithin (uniqueDiffWithinAt_Ici x₀)]
  exact hmax.nonpos_of_hasDerivWithinAt_Ici
    (eventually_of_mem (hSmem x₀ hx₀S) hu1) hc h0

/-! ### The second derivative along a line, and the Hessian at an extremum -/

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **second derivative along a line**. Let $E$ be a real normed space, let
$f : E \to \mathbb{R}$ be $C^2$ at $x_0$, and let $v \in E$. Then the second derivative at
$s = 0$ of $s \mapsto f(x_0 + s v)$ is $D^2 f(x_0)[v, v]$.

Here $D^2 f(x_0)[v, v]$ is `iteratedFDeriv ℝ 2 f x₀ ![v, v]`. Near $0$, the first derivative of
the restriction is $s \mapsto Df(x_0 + s v)\, v$ by the chain rule, since $f$ is differentiable
near $x_0$. Its derivative at $0$ is $D^2 f(x_0)\, v\, v$, by the chain rule again, since $Df$
is differentiable at $x_0$. -/
theorem ContDiffAt.deriv_deriv_comp_add_smul {f : E → ℝ} {x₀ : E} (hf : ContDiffAt ℝ 2 f x₀)
    (v : E) : deriv (deriv fun s : ℝ ↦ f (x₀ + s • v)) 0 = iteratedFDeriv ℝ 2 f x₀ ![v, v] := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ x₀ + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x₀
  have hcont : Continuous fun s : ℝ ↦ x₀ + s • v := by fun_prop
  have h0 : x₀ + (0 : ℝ) • v = x₀ := by simp
  -- `f` is differentiable along the line near `s = 0`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x₀ + s • v) := by
    have h1 : ∀ᶠ y in 𝓝 (x₀ + (0 : ℝ) • v), DifferentiableAt ℝ f y := by
      rw [h0]
      exact (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
    exact (hcont.tendsto 0).eventually h1
  have h1 : (deriv fun s : ℝ ↦ f (x₀ + s • v)) =ᶠ[𝓝 0] fun s ↦ fderiv ℝ f (x₀ + s • v) v := by
    filter_upwards [hev] with s hs
    exact (hs.hasFDerivAt.comp_hasDerivAt s (hline s)).deriv
  rw [h1.deriv_eq]
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) x₀ :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h3 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x₀ + s • v)) (fderiv ℝ (fderiv ℝ f) x₀ v) 0 := by
    have h2' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x₀) (x₀ + (0 : ℝ) • v) := by
      rw [h0]; exact h2.hasFDerivAt
    exact h2'.comp_hasDerivAt (0 : ℝ) (hline 0)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [h4.deriv, iteratedFDeriv_two_apply]
  simp

/-- The **Hessian of a $C^2$ function is negative semidefinite at a local maximum**. Let $E$ be a
real normed space, and let $f : E \to \mathbb{R}$ have a local maximum at $x_0$ and be $C^2$ at
$x_0$. Then $D^2 f(x_0)[v, v] \le 0$ for every $v \in E$.

The Hessian is `fderiv ℝ (fderiv ℝ f) x₀ v v`. It is the second derivative at $0$ of the
restriction $s \mapsto f(x_0 + s v)$ (`ContDiffAt.deriv_deriv_comp_add_smul`), which has a local
maximum at $0$ (`IsLocalMax.deriv_deriv_nonpos`). -/
theorem IsLocalMax.fderiv_fderiv_apply_self_nonpos {f : E → ℝ} {x₀ : E} (hmax : IsLocalMax f x₀)
    (hf : ContDiffAt ℝ 2 f x₀) (v : E) : fderiv ℝ (fderiv ℝ f) x₀ v v ≤ 0 := by
  have h := hf.deriv_deriv_comp_add_smul v
  rw [iteratedFDeriv_two_apply] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h]
  have hline : Continuous fun s : ℝ ↦ x₀ + s • v := by fun_prop
  have h0 : x₀ + (0 : ℝ) • v = x₀ := by simp
  refine IsLocalMax.deriv_deriv_nonpos ?_ ?_
  · have : IsLocalMax f ((fun s : ℝ ↦ x₀ + s • v) 0) := by simpa only [h0] using hmax
    exact IsLocalMax.comp_continuous (g := fun s : ℝ ↦ x₀ + s • v) (b := 0) this
      hline.continuousAt
  · exact hf.continuousAt.comp_of_eq hline.continuousAt h0

/-- The **Hessian of a $C^2$ function is positive semidefinite at a local minimum**. Let $E$ be a
real normed space, and let $f : E \to \mathbb{R}$ have a local minimum at $x_0$ and be $C^2$ at
$x_0$. Then $D^2 f(x_0)[v, v] \ge 0$ for every $v \in E$.

The Hessian is `fderiv ℝ (fderiv ℝ f) x₀ v v`. The proof applies
`IsLocalMax.fderiv_fderiv_apply_self_nonpos` to $-f$. -/
theorem IsLocalMin.fderiv_fderiv_apply_self_nonneg {f : E → ℝ} {x₀ : E} (hmin : IsLocalMin f x₀)
    (hf : ContDiffAt ℝ 2 f x₀) (v : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x₀ v v := by
  have h := hmin.neg.fderiv_fderiv_apply_self_nonpos hf.neg v
  have hd : fderiv ℝ (fun x => -f x) = fun x => -fderiv ℝ f x := funext fun x => fderiv_fun_neg
  rw [hd, fderiv_fun_neg] at h
  simpa using h

/-- Let $E$ be a real normed space, and let $f : E \to \mathbb{R}$ have a local minimum at $x_0$ and
be $C^2$ at $x_0$. Then $D^2 f(x_0)[v, v] \ge 0$ for every $v \in E$, with the second derivative
in the form `iteratedFDeriv ℝ 2 f x₀`.

The argument of the bilinear form is the constant family `fun _ => v`. -/
theorem IsLocalMin.iteratedFDeriv_two_apply_self_nonneg {f : E → ℝ} {x₀ : E}
    (hmin : IsLocalMin f x₀) (hf : ContDiffAt ℝ 2 f x₀) (v : E) :
    0 ≤ iteratedFDeriv ℝ 2 f x₀ (fun _ => v) := by
  simpa [iteratedFDeriv_two_apply] using hmin.fderiv_fderiv_apply_self_nonneg hf v

/-- Let $E$ be a real normed space, and let $f : E \to \mathbb{R}$ have a local maximum at $x_0$ and
be $C^2$ at $x_0$. Then $D^2 f(x_0)[v, v] \le 0$ for every $v \in E$, with the second derivative
in the form `iteratedFDeriv ℝ 2 f x₀`.

The argument of the bilinear form is the constant family `fun _ => v`. -/
theorem IsLocalMax.iteratedFDeriv_two_apply_self_nonpos {f : E → ℝ} {x₀ : E}
    (hmax : IsLocalMax f x₀) (hf : ContDiffAt ℝ 2 f x₀) (v : E) :
    iteratedFDeriv ℝ 2 f x₀ (fun _ => v) ≤ 0 := by
  simpa [iteratedFDeriv_two_apply] using hmax.fderiv_fderiv_apply_self_nonpos hf v

end Hessian
