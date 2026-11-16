/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of a functional through its directional derivatives

Let $V$ be a real normed space, let $K \subseteq V$ be convex, and let $f \colon V \to \mathbb{R}$.
Suppose that at every $u \in K$ the directional derivatives of $f$ are given by a continuous linear
functional $f'(u) \colon V \to \mathbb{R}$: for every direction $h$, the derivative of
$s \mapsto f(u + sh)$ at $s = 0$ is $f'(u)h$. Then three conditions are equivalent: $f$ is convex on
$K$; the tangent functional at each point is a minorant, $f(u) + f'(u)(v - u) \le f(v)$ for all
$u, v \in K$; and the derivative is a monotone operator, $0 \le (f'(v) - f'(u))(v - u)$ for all
$u, v \in K$. The strict forms hold as well. A minimizer of $f$ over $K$ is then characterized by a
variational inequality. Over a subspace this inequality becomes a variational equation, and the
inequality still holds after a second convex term, which need not be differentiable, is added to
$f$. The last form turns a constrained convex minimization problem into an elliptic variational
inequality.

This material is classical. It appears as Theorems 5.3.17–5.3.19 and Theorem 11.2.1 of
[han2009theoretical].

## Main results

* `convexOn_iff_forall_add_lineDeriv_le`: $f$ is convex on $K$ if and only if
  $f(u) + f'(u)(v - u) \le f(v)$ for all $u, v \in K$.
* `convexOn_iff_monotone_lineDeriv`: $f$ is convex on $K$ if and only if
  $0 \le (f'(v) - f'(u))(v - u)$ for all $u, v \in K$.
* `strictConvexOn_iff_forall_add_lineDeriv_lt`, `strictConvexOn_iff_forall_lineDeriv_sub_pos`: the
  strict forms of these two equivalences.
* `isMinOn_add_iff_forall_le`: for $f$ and $j$ convex on $K$, a point $u \in K$ minimizes $f + j$
  over $K$ if and only if $0 \le f'(u)(v - u) + j(v) - j(u)$ for all $v \in K$.
* `isMinOn_iff_forall_lineDeriv_nonneg`: the case $j = 0$.
* `isMinOn_iff_forall_lineDeriv_eq_zero`: over a subspace $K$, $u$ minimizes $f$ if and only if
  $f'(u)v = 0$ for all $v \in K$.

## Implementation notes

* The continuous linear functionals $f'(u)$ are given as data, `f' : V → V →L[ℝ] ℝ`, and are not
  derived. `HasLineDerivAt` gives one number for each direction and does not combine these numbers
  into a functional, and the classical Gâteaux derivative is required to be bounded and linear. The
  hypothesis is therefore always written as `∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h`.
* There is no separate version for `fderiv`. `HasFDerivAt.hasLineDerivAt` specializes every
  statement, and a Fréchet derivative is a stronger hypothesis than the applications have.
* `HasLineDerivAt.hasDerivAt_line` translates the parameter of a line derivative. All the results
  rest on it. It is stated for a general normed target because it belongs with the restriction to
  one dimension.
-/

open Filter Set Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Let $V$ and $W$ be real normed spaces, let $g \colon V \to W$, and let $u, h \in V$ and
$t \in \mathbb{R}$. If $g$ has the line derivative $a$ at the point $u + th$ in the direction
$h$, then the function $s \mapsto g(u + sh)$ has the derivative $a$ at $s = t$.

`HasLineDerivAt` gives this only at $t = 0$. The translation of the parameter makes a mean value
theorem along a segment available. -/
theorem HasLineDerivAt.hasDerivAt_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {a : W} {u h : V} {t : ℝ} (hg : HasLineDerivAt ℝ g a (u + t • h) h) :
    HasDerivAt (fun s : ℝ => g (u + s • h)) a t := by
  have hg0 : HasDerivAt (fun s : ℝ => g (u + t • h + s • h)) a 0 := hg
  have h0 : HasDerivAt (fun s : ℝ => g (u + t • h + s • h)) a ((fun s : ℝ => s - t) t) := by
    simpa using hg0
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 : HasDerivAt ((fun s : ℝ => g (u + t • h + s • h)) ∘ fun s : ℝ => s - t)
      ((1 : ℝ) • a) t := HasDerivAt.scomp t h0 h1
  have heq : ((fun s : ℝ => g (u + t • h + s • h)) ∘ fun s : ℝ => s - t)
      = fun s : ℝ => g (u + s • h) := by
    funext s
    simp only [Function.comp_apply]
    congr 1
    module
  rw [heq, one_smul] at h2
  exact h2

section Convexity

variable {K : Set V} {f j : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- Mean value theorem along a segment $[u, v]$ in a convex set $K$, for a function whose
directional derivatives on $K$ are the functionals $f'$: there is $c \in (0, 1)$ with
$u + c(v - u) \in K$ and $f'(u + c(v - u))(v - u) = f(v) - f(u)$. -/
private theorem exists_lineDeriv_eq_sub (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) {v : V}
    (hv : v ∈ K) :
    ∃ c ∈ Ioo (0 : ℝ) 1, u + c • (v - u) ∈ K ∧ f' (u + c • (v - u)) (v - u) = f v - f u := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (u + s • (v - u))) (f' (u + t • (v - u)) (v - u)) t :=
    fun t ht => (hG _ (hK.add_smul_sub_mem hu hv ht) (v - u)).hasDerivAt_line
  have hcont : ContinuousOn (fun s : ℝ => f (u + s • (v - u))) (Icc 0 1) :=
    fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f (u + s • (v - u)))
    (fun t : ℝ => f' (u + t • (v - u)) (v - u)) zero_lt_one hcont
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
  have h1v : u + (1 : ℝ) • (v - u) = v := by module
  have h0v : u + (0 : ℝ) • (v - u) = u := by module
  simp only [h1v, h0v, sub_zero, div_one] at hcslope
  exact ⟨c, hc, hK.add_smul_sub_mem hu hv ⟨hc.1.le, hc.2.le⟩, hcslope⟩

/-- **A convex function lies above its tangent functionals.** Let $f \colon V \to \mathbb{R}$ be
convex on $K \subseteq V$, let $u, v \in K$, and let $A \colon V \to \mathbb{R}$ be a continuous
linear functional such that for every direction $h \in V$, the line derivative of $f$ at $u$ in
the direction $h$ is $Ah$. Then
$$f(u) + A(v - u) \le f(v).$$
-/
theorem ConvexOn.add_lineDeriv_le (hf : ConvexOn ℝ K f) {A : V →L[ℝ] ℝ} {u v : V} (hu : u ∈ K)
    (hv : v ∈ K) (hA : ∀ h, HasLineDerivAt ℝ f (A h) u h) : f u + A (v - u) ≤ f v := by
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (f (u + t • (v - u)) - f u)) (𝓝[>] (0 : ℝ))
      (𝓝 (A (v - u))) := (hA (v - u)).tendsto_slope_zero_right
  have hle : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t⁻¹ • (f (u + t • (v - u)) - f u) ≤ f v - f u := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have hpt : (1 - t) • u + t • v = u + t • (v - u) := by module
    have hconv := hf.2 hu hv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    rw [hpt] at hconv
    simp only [smul_eq_mul] at hconv ⊢
    rw [inv_mul_le_iff₀ ht.1]
    linarith
  have hmain := le_of_tendsto hslope hle
  linarith

/-- A linear functional $A$ balances the displacements from a convex combination: if $a + b = 1$ and
$w = ax + by$, then $a A(x - w) + b A(y - w) = 0$. -/
private theorem weighted_apply_sub_combo_eq_zero (A : V →L[ℝ] ℝ) (x y : V) {a b : ℝ}
    (hab : a + b = 1) :
    a * A (x - (a • x + b • y)) + b * A (y - (a • x + b • y)) = 0 := by
  have hz : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have hexp : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))
        = (a • x + b • y) - (a + b) • (a • x + b • y) := by module
    rw [hexp, hab, one_smul, sub_self]
  have hc := congrArg A hz
  rw [map_add, map_smul, map_smul, map_zero] at hc
  simpa [smul_eq_mul] using hc

/-- Let $K \subseteq V$ be convex, and let $f'(u)$, $u \in V$, be any continuous linear functionals.
If $f(u) + f'(u)(v - u) \le f(v)$ for all $u, v \in K$, then $f$ is convex on $K$. No
differentiability is used. -/
theorem convexOn_of_add_lineDeriv_le (hK : Convex ℝ K)
    (h : ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) : ConvexOn ℝ K f := by
  refine ⟨hK, ?_⟩
  intro x hx y hy a b ha hb hab
  have hwK : a • x + b • y ∈ K := hK hx hy ha hb hab
  have h1 := h _ hwK x hx
  have h2 := h _ hwK y hy
  have hlin := weighted_apply_sub_combo_eq_zero (f' (a • x + b • y)) x y hab
  have ha1 := mul_le_mul_of_nonneg_left h1 ha
  have hb1 := mul_le_mul_of_nonneg_left h2 hb
  have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith

/-- **Convexity through the tangent inequality.** Let $K \subseteq V$ be convex and let
$f \colon V \to \mathbb{R}$. Suppose that for every $u \in K$ and every direction $h \in V$, the
line derivative of $f$ at $u$ in the direction $h$ is $f'(u)h$, where $f'(u)$ is a continuous
linear functional. Then $f$ is convex on $K$ if and only if
$$f(u) + f'(u)(v - u) \le f(v) \quad \text{for all } u, v \in K.$$
-/
theorem convexOn_iff_forall_add_lineDeriv_le (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v :=
  ⟨fun hf u hu _v hv => ConvexOn.add_lineDeriv_le hf hu hv (hG u hu),
    convexOn_of_add_lineDeriv_le hK⟩

/-- If $f(u) + f'(u)(v - u) \le f(v)$ for all $u, v \in K$, then the derivative is a monotone
operator on $K$: $0 \le (f'(v) - f'(u))(v - u)$ for all $u, v \in K$. Adding the inequality at
$u$ to the inequality at $v$ cancels the values of $f$. -/
theorem monotone_lineDeriv_of_add_lineDeriv_le
    (h : ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) {u : V} (hu : u ∈ K) {v : V} (hv : v ∈ K) :
    0 ≤ (f' v - f' u) (v - u) := by
  have h1 := h u hu v hv
  have h2 := h v hv u hu
  have h3 : f' v (u - v) = -f' v (v - u) := by rw [← map_neg, neg_sub]
  rw [h3] at h2
  rw [sub_apply]
  linarith

/-- Let $K$ be convex, and let the line derivatives of $f$ at the points of $K$ be given by the
continuous linear functionals $f'(u)$. If $0 \le (f'(v) - f'(u))(v - u)$ for all $u, v \in K$,
then $f(u) + f'(u)(v - u) \le f(v)$ for all $u, v \in K$.

This is the only direction that needs the mean value theorem on the segment $[u, v]$: the
derivative at an intermediate point is compared with the derivative at $u$. -/
theorem add_lineDeriv_le_of_monotone_lineDeriv (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h)
    (h : ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u)) {u : V} (hu : u ∈ K) {v : V} (hv : v ∈ K) :
    f u + f' u (v - u) ≤ f v := by
  obtain ⟨c, hc, hcmem, hcslope⟩ := exists_lineDeriv_eq_sub hK hG hu hv
  have hmono := h u hu _ hcmem
  rw [show u + c • (v - u) - u = c • (v - u) by abel, sub_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul] at hmono
  have hkey : f' u (v - u) ≤ f' (u + c • (v - u)) (v - u) := by nlinarith [hc.1]
  linarith

/-- **Convexity through a monotone derivative.** Let $K \subseteq V$ be convex and let
$f \colon V \to \mathbb{R}$. Suppose that for every $u \in K$ and every direction $h \in V$, the
line derivative of $f$ at $u$ in the direction $h$ is $f'(u)h$, where $f'(u)$ is a continuous
linear functional. Then $f$ is convex on $K$ if and only if
$$0 \le (f'(v) - f'(u))(v - u) \quad \text{for all } u, v \in K.$$
-/
theorem convexOn_iff_monotone_lineDeriv (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u) :=
  (convexOn_iff_forall_add_lineDeriv_le hK hG).trans
    ⟨fun h _ hu _ hv => monotone_lineDeriv_of_add_lineDeriv_le h hu hv,
      fun h _ hu _ hv => add_lineDeriv_le_of_monotone_lineDeriv hK hG h hu hv⟩

/-- Let $f$ be strictly convex on $K$, let $u, v \in K$ with $u \neq v$, and let $A$ be a continuous
linear functional such that the line derivative of $f$ at $u$ in every direction $h$ is $Ah$.
Then $f(u) + A(v - u) < f(v)$.

The proof applies the nonstrict inequality at the midpoint of $[u, v]$, and this makes the
inequality strict. -/
theorem StrictConvexOn.add_lineDeriv_lt (hf : StrictConvexOn ℝ K f) {A : V →L[ℝ] ℝ} {u v : V}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) (hA : ∀ h, HasLineDerivAt ℝ f (A h) u h) :
    f u + A (v - u) < f v := by
  have hw : (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v ∈ K :=
    hf.1 hu hv (by norm_num) (by norm_num) (by norm_num)
  have hlt := hf.2 hu hv huv (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num)
  have hb := ConvexOn.add_lineDeriv_le hf.convexOn hu hw hA
  have hwu : (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v - u = (2 : ℝ)⁻¹ • (v - u) := by module
  rw [hwu, map_smul, smul_eq_mul] at hb
  simp only [smul_eq_mul] at hlt
  linarith

/-- Let $K$ be convex, and let $f'(u)$ be any continuous linear functionals. If
$f(u) + f'(u)(v - u) < f(v)$ for all $u, v \in K$ with $u \neq v$, then $f$ is strictly convex
on $K$. -/
theorem strictConvexOn_of_add_lineDeriv_lt (hK : Convex ℝ K)
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v) : StrictConvexOn ℝ K f := by
  refine ⟨hK, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hwK : a • x + b • y ∈ K := hK hx hy ha.le hb.le hab
  have hwx : a • x + b • y ≠ x := by
    intro hcon
    have hb0 : b • (y - x) = 0 := by
      have hexp : b • (y - x) = a • x + b • y - (a + b) • x := by module
      rw [hexp, hab, one_smul, hcon, sub_self]
    rcases smul_eq_zero.mp hb0 with h' | h'
    · exact hb.ne' h'
    · exact hxy (sub_eq_zero.mp h').symm
  have hwy : a • x + b • y ≠ y := by
    intro hcon
    have ha0 : a • (x - y) = 0 := by
      have hexp : a • (x - y) = a • x + b • y - (a + b) • y := by module
      rw [hexp, hab, one_smul, hcon, sub_self]
    rcases smul_eq_zero.mp ha0 with h' | h'
    · exact ha.ne' h'
    · exact hxy (sub_eq_zero.mp h')
  have h1 := h _ hwK x hx hwx
  have h2 := h _ hwK y hy hwy
  have hlin := weighted_apply_sub_combo_eq_zero (f' (a • x + b • y)) x y hab
  have ha1 := mul_lt_mul_of_pos_left h1 ha
  have hb1 := mul_lt_mul_of_pos_left h2 hb
  have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith

/-- **Strict convexity through the tangent inequality.** Let $K \subseteq V$ be convex and let
$f \colon V \to \mathbb{R}$. Suppose that for every $u \in K$ and every direction $h \in V$, the
line derivative of $f$ at $u$ in the direction $h$ is $f'(u)h$, where $f'(u)$ is a continuous
linear functional. Then $f$ is strictly convex on $K$ if and only if
$$f(u) + f'(u)(v - u) < f(v) \quad \text{for all } u, v \in K \text{ with } u \neq v.$$
-/
theorem strictConvexOn_iff_forall_add_lineDeriv_lt (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v :=
  ⟨fun hf u hu _v hv huv => StrictConvexOn.add_lineDeriv_lt hf hu hv huv (hG u hu),
    strictConvexOn_of_add_lineDeriv_lt hK⟩

/-- If $f(u) + f'(u)(v - u) < f(v)$ for all $u, v \in K$ with $u \neq v$, then the derivative is
strictly monotone on $K$: $0 < (f'(v) - f'(u))(v - u)$ for all $u, v \in K$ with $u \neq v$. -/
theorem lineDeriv_sub_pos_of_add_lineDeriv_lt
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v) {u : V} (hu : u ∈ K) {v : V}
    (hv : v ∈ K) (huv : u ≠ v) : 0 < (f' v - f' u) (v - u) := by
  have h1 := h u hu v hv huv
  have h2 := h v hv u hu huv.symm
  have h3 : f' v (u - v) = -f' v (v - u) := by rw [← map_neg, neg_sub]
  rw [h3] at h2
  rw [sub_apply]
  linarith

/-- Let $K$ be convex, and let the line derivatives of $f$ at the points of $K$ be given by the
continuous linear functionals $f'(u)$. If $0 < (f'(v) - f'(u))(v - u)$ for all $u, v \in K$ with
$u \neq v$, then $f(u) + f'(u)(v - u) < f(v)$ for all such $u, v$. The proof uses the mean value
theorem on the segment $[u, v]$. -/
theorem add_lineDeriv_lt_of_lineDeriv_sub_pos (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h)
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (f' v - f' u) (v - u)) {u : V} (hu : u ∈ K) {v : V}
    (hv : v ∈ K) (huv : u ≠ v) : f u + f' u (v - u) < f v := by
  obtain ⟨c, hc, hcmem, hcslope⟩ := exists_lineDeriv_eq_sub hK hG hu hv
  have hne : u ≠ u + c • (v - u) := by
    intro hcon
    have hz : c • (v - u) = 0 := by
      have hd : u + c • (v - u) - u = c • (v - u) := by abel
      rw [← hd, ← hcon, sub_self]
    rcases smul_eq_zero.mp hz with h' | h'
    · exact absurd h' (ne_of_gt hc.1)
    · exact huv (sub_eq_zero.mp h').symm
  have hmono := h u hu _ hcmem hne
  rw [show u + c • (v - u) - u = c • (v - u) by abel, sub_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul] at hmono
  have hkey : f' u (v - u) < f' (u + c • (v - u)) (v - u) := by nlinarith [hc.1]
  linarith

/-- **Strict convexity through a strictly monotone derivative.** Let $K \subseteq V$ be convex and
let $f \colon V \to \mathbb{R}$. Suppose that for every $u \in K$ and every direction $h \in V$,
the line derivative of $f$ at $u$ in the direction $h$ is $f'(u)h$, where $f'(u)$ is a
continuous linear functional. Then $f$ is strictly convex on $K$ if and only if
$$0 < (f'(v) - f'(u))(v - u) \quad \text{for all } u, v \in K \text{ with } u \neq v.$$
-/
theorem strictConvexOn_iff_forall_lineDeriv_sub_pos (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (f' v - f' u) (v - u) :=
  (strictConvexOn_iff_forall_add_lineDeriv_lt hK hG).trans
    ⟨fun h _ hu _ hv huv => lineDeriv_sub_pos_of_add_lineDeriv_lt h hu hv huv,
      fun h _ hu _ hv huv => add_lineDeriv_lt_of_lineDeriv_sub_pos hK hG h hu hv huv⟩

/-- **The variational inequality of a constrained minimizer**, with a second convex term that need
not be differentiable. Let $f, j \colon V \to \mathbb{R}$ be convex on $K \subseteq V$. Suppose
that for every $u \in K$ and every direction $h \in V$, the line derivative of $f$ at $u$ in the
direction $h$ is $f'(u)h$, where $f'(u)$ is a continuous linear functional. Then a point
$u \in K$ minimizes $f + j$ over $K$ if and only if
$$0 \le f'(u)(v - u) + j(v) - j(u) \quad \text{for every } v \in K.$$

This statement turns a constrained convex minimization problem into an elliptic variational
inequality. The convexity of $K$ follows from the convexity of $f$ on $K$. -/
theorem isMinOn_add_iff_forall_le (hf : ConvexOn ℝ K f) (hj : ConvexOn ℝ K j)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) :
    IsMinOn (f + j) K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) + j v - j u := by
  rw [isMinOn_iff]
  simp only [Pi.add_apply]
  constructor
  · intro hmin v hv
    have hslope : Tendsto (fun t : ℝ => t⁻¹ • (f (u + t • (v - u)) - f u)) (𝓝[>] (0 : ℝ))
        (𝓝 (f' u (v - u))) := (hG u hu (v - u)).tendsto_slope_zero_right
    have hge : j u - j v ≤ f' u (v - u) := by
      refine ge_of_tendsto hslope ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have hpt : (1 - t) • u + t • v = u + t • (v - u) := by module
      have hjc := hj.2 hu hv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
      rw [hpt] at hjc
      have hmem : u + t • (v - u) ∈ K :=
        hf.1.add_smul_sub_mem hu hv ⟨ht.1.le, (by linarith [ht.2] : t ≤ 1)⟩
      have hmin' := hmin _ hmem
      simp only [smul_eq_mul] at hjc ⊢
      rw [le_inv_mul_iff₀ ht.1]
      nlinarith
    linarith
  · intro h v hv
    have hb := ConvexOn.add_lineDeriv_le hf hu hv (hG u hu)
    have hv0 := h v hv
    linarith

/-- **The variational inequality of a constrained minimizer.** Let $f \colon V \to \mathbb{R}$ be
convex on $K \subseteq V$. Suppose that for every $u \in K$ and every direction $h \in V$, the
line derivative of $f$ at $u$ in the direction $h$ is $f'(u)h$, where $f'(u)$ is a continuous
linear functional. Then a point $u \in K$ minimizes $f$ over $K$ if and only if
$$0 \le f'(u)(v - u) \quad \text{for every } v \in K.$$

This is the case $j = 0$ of `isMinOn_add_iff_forall_le`. -/
theorem isMinOn_iff_forall_lineDeriv_nonneg (hf : ConvexOn ℝ K f)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) :
    IsMinOn f K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) := by
  have hzero : ConvexOn ℝ K (0 : V → ℝ) := convexOn_const 0 hf.1
  simpa using isMinOn_add_iff_forall_le hf hzero hG hu

/-- **The variational equation over a subspace.** Let $K$ be a linear subspace of $V$ and let
$f \colon V \to \mathbb{R}$ be convex on $K$. Suppose that for every $u \in K$ and every
direction $h \in V$, the line derivative of $f$ at $u$ in the direction $h$ is $f'(u)h$, where
$f'(u)$ is a continuous linear functional. Then a point $u \in K$ minimizes $f$ over $K$ if and
only if
$$f'(u)v = 0 \quad \text{for every } v \in K.$$

Both $v$ and $-v$ are admissible directions, and this removes the inequality of
`isMinOn_iff_forall_lineDeriv_nonneg`. -/
theorem isMinOn_iff_forall_lineDeriv_eq_zero {K : Submodule ℝ V}
    (hf : ConvexOn ℝ (K : Set V) f)
    (hG : ∀ u ∈ (K : Set V), ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) :
    IsMinOn f (K : Set V) u ↔ ∀ v ∈ K, f' u v = 0 := by
  rw [isMinOn_iff_forall_lineDeriv_nonneg hf hG hu]
  constructor
  · intro h v hv
    have h1 := h (u + v) (K.add_mem hu hv)
    have h2 := h (u - v) (K.sub_mem hu hv)
    rw [show u + v - u = v by abel] at h1
    rw [show u - v - u = -v by abel, map_neg] at h2
    linarith
  · intro h v hv
    exact le_of_eq (h (v - u) (K.sub_mem hv hu)).symm

end Convexity
