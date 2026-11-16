/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Calculus.Taylor
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Quadrature
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Polynomial splines and interpolatory cubic splines

Let $a = x_0 < x_1 < \dots < x_n = b$ be a partition of $[a, b]$ with the panel lengths
$h_i = x_i - x_{i-1}$. The spline space $S_k^r$ consists of the continuous functions on $[a, b]$
that are of class $C^r$ and agree with a polynomial of degree at most $k$ on every panel
$[x_{i-1}, x_i]$. This file shows that the monomials $1, t, \dots, t^k$ and the truncated powers
$(t - x_j)_+^s$, $0 < j < n$, $r < s \le k$, form a basis of $S_k^r$, so that
$\dim S_k^r = n(k - r) + r + 1$. The presentation follows [quarteroni2000numerical], §8.6–8.6.1
(Definition 8.1, (8.44)–(8.49), Property 8.2, Exercises 8.10–8.11). The source quotes these results
from de Boor, *A Practical Guide to Splines*.

The second part treats the interpolatory cubic spline ($k = 3$, $r = 2$) of data $f_0, \dots, f_n$.
On the panel $[x_{i-1}, x_i]$ the spline is the cubic with the end values $f_{i-1}, f_i$ and the end
second derivatives $M_{i-1}, M_i$, the *moments*. The glued function is of class $C^2$ exactly when
the moments satisfy the M-continuity equations
$$\mu_i M_{i-1} + 2 M_i + \lambda_i M_{i+1} = d_i, \qquad 1 \le i \le n - 1,$$
with $\mu_i = h_i / (h_i + h_{i+1})$, $\lambda_i = h_{i+1} / (h_i + h_{i+1})$ and $d_i =
\frac{6}{h_i + h_{i+1}} \left( \frac{f_{i+1} - f_i}{h_{i+1}} - \frac{f_i - f_{i-1}}{h_i} \right)$.
The closure rows $2 M_0 + \lambda_0 M_1 = d_0$ and $\mu_n M_{n-1} + 2 M_n = d_n$ complete a
tridiagonal system. For $0 \le \lambda_0, \mu_n \le 1$ its matrix $A$ is strictly diagonally
dominant and $\|A^{-1}\|_\infty \le 1$. The file treats the natural, the clamped, the not-a-knot and
the periodic splines, proves Holladay's minimum-norm property and the best-approximation property of
the clamped spline, and bounds the error of the clamped spline by $O(h^4)$.

## Main definitions

* `Spline.splineSpace`: the spline space $S_k^r$, a subspace of $C([a, b])$.
* `Spline.truncPowCM`: the truncated power $t \mapsto (t - c)_+^s$ on $[a, b]$.
* `Spline.truncPowFamily`: the monomials of degree at most $k$ together with the truncated powers at
  the interior breakpoints.
* `Spline.panelCubic`: the cubic on $[x_{i-1}, x_i]$ with the end values $f_{i-1}, f_i$ and the end
  second derivatives $M_{i-1}, M_i$, from (8.46) integrated twice.
* `Spline.panelGlue`: the function equal to a given panel function $Q_i$ on each panel
  $[x_{i-1}, x_i]$.
* `Spline.cubicSplineFun`: the panel cubics glued into one function on $\mathbb{R}$.
* `Spline.momentMatrix`: the matrix of the M-continuity system (8.47)–(8.48).
* `Spline.momentRhs`: the right-hand side of this system.
* `Spline.IsCubicSpline`: a function of class $C^2$ on $[a, b]$ that is a cubic on every panel.
* `Spline.IsCubicInterp`: a cubic spline with $s(x_i) = f_i$ for $0 \le i \le n$.
* `Spline.moment`: the moments $M_i = s''(x_i)$.
* `Spline.HasClosure`: the closure rows of type (8.48).
* `Spline.cubicInterp`: the interpolatory cubic spline with a closure of type (8.48).
* `Spline.naturalInterp`: the natural cubic spline, $s''(a) = s''(b) = 0$.
* `Spline.clampedInterp`: the clamped cubic spline with prescribed slopes at $a$ and $b$.
* `Spline.cardinalBasis`: the cardinal basis of the clamped splines.
* `Spline.IsNotAKnot`: the not-a-knot condition.
* `Spline.IsPeriodicEnd`: the periodic end conditions $s'(a) = s'(b)$, $s''(a) = s''(b)$.
* `Spline.cubicInterpVec`: the interpolatory cubic spline of data in a real vector space.

## Main results

* `Spline.linearIndependent_truncPow`: the truncated-power family is linearly independent.
* `Spline.span_truncPow_eq_splineSpace`: the truncated-power family spans $S_k^r$.
* `Spline.finrank_splineSpace`: $\dim S_k^r = n(k - r) + r + 1$ for $n \ge 1$ and $r \le k$.
* `Spline.exists_basis_truncPow`: $S_k$ has a basis of the monomials $t^i$, $i \le k$, and the
  truncated powers $(t - x_j)_+^k$.
* `Spline.contDiff_cubicSplineFun`: if the moments satisfy the M-continuity equations, the glued
  panel cubics form a function of class $C^2$.
* `Spline.moment_eq_of_contDiffOn`: conversely, a function of class $C^2$ made of panel cubics has
  moments that satisfy the M-continuity equations.
* `Spline.isStrictDiagDominant_momentMatrix`: the moment matrix is strictly diagonally dominant for
  $0 \le \lambda_0, \mu_n \le 1$.
* `Spline.linfty_opNorm_inv_momentMatrix_le`: the inverse of the moment matrix has sup-norm operator
  norm at most $1$.
* `Spline.existsUnique_isCubicInterp_of_closure`: there is exactly one interpolatory cubic spline
  with a given closure of type (8.48), up to its values outside $[a, b]$.
* `Spline.existsUnique_isCubicInterp_notAKnot`: the same for the not-a-knot condition, for
  $n \ge 3$.
* `Spline.existsUnique_isCubicInterp_periodic`: the same for the periodic end conditions, for
  $n \ge 2$.
* `Spline.clampedInterp_eq_sum_cardinalBasis`: the clamped spline is $\sum_i f_i \varphi_i + f'_0
  \varphi_{n+1} + f'_n \varphi_{n+2}$ in the cardinal basis.
* `Spline.integral_sub_deriv2_mul_deriv2_eq_zero`: Holladay's orthogonality identity
  $\int_a^b (f'' - s'') s'' = 0$ for a natural or clamped interpolatory spline $s$ of $f$.
* `Spline.holladay`: the natural spline $s_3$ of $f \in C^2[a, b]$ satisfies
  $\int_a^b (s_3'')^2 \le \int_a^b (f'')^2$.
* `Spline.holladay_eq_iff`: equality holds in `Spline.holladay` exactly when $f = s_3$ on $[a, b]$.
* `Spline.holladay_clamped`: the minimum-norm property of the clamped spline.
* `Spline.integral_sq_sub_deriv2_clampedInterp_le`: the second derivative of the clamped spline is
  the best $L^2$ approximation of $f''$ by second derivatives of cubic splines.
* `Spline.cubicInterpVec_affine`: cubic spline interpolation commutes with affine maps of the data.
* `Spline.norm_deriv2_sub_clampedInterp_le`: for $f$ of class $C^4$ with $|f^{(4)}| \le K$ and panel
  lengths at most $h$, the moments of the clamped spline are within $\frac34 h^2 K$ of $f''$ at the
  nodes.
* `Spline.norm_deriv2_sub_clampedInterp_le_of_mem`: under the same hypotheses
  $|f'' - s''| \le \frac74 h^2 K$ on $[a, b]$.
* `Spline.norm_deriv_sub_clampedInterp_le`: under the same hypotheses $|f' - s'| \le \frac74 h^3 K$
  on $[a, b]$.
* `Spline.norm_sub_clampedInterp_le`: under the same hypotheses $|f - s| \le \frac78 h^4 K$ on
  $[a, b]$. The constants are not the sharp ones of Hall and Meyer.

## Implementation notes

* The nodes are a sequence `x : ℕ → ℝ` with `IsIntervalPartition a b n x` from
  `Numlib.Approximation.Partition`, that is, $a = x_0 < x_1 < \dots < x_n = b$. The $i$-th panel is
  $[x_{i-1}, x_i]$ for $1 \le i \le n$, and $h_i$ is `Spline.panelLength x i`.
* Membership of `Spline.splineSpace` asks for a function of class $C^r$ on `Set.Icc a b` that agrees
  with the given continuous map there and with a polynomial of degree at most $k$ on every panel. So
  no derivative of a function on the subtype is needed. The space $S_k$ of the source is the case
  $r = k - 1$. The space $X_h^k$ of the source, the range of the piecewise polynomial interpolation
  operator of `Numlib.Approximation.Interpolation`, is the case $r = 0$. The case $r = k$ gives back
  the polynomials `polyLE (Set.Icc a b) k`.
* Everything about cubic splines is stated for functions $\mathbb{R} \to \mathbb{R}$. The glued
  function `Spline.cubicSplineFun` continues the first and the last panel cubics outside $[a, b]$.
  So it is of class $C^2$ on all of $\mathbb{R}$ once the moment equations hold, and its derivatives
  at the nodes are ordinary derivatives. An arbitrary interpolating spline $s$ is only assumed of
  class $C^2$ on `Set.Icc a b`, and its moments are the derivatives within $[a, b]$,
  `iteratedDerivWithin 2 s (Set.Icc a b) (x i)`.
* Moment vectors are indexed by `Fin (n + 1)` and extended by zero to $\mathbb{N}$ with
  `Spline.extendFin`. The spline `Spline.cubicInterp` uses the matrix inverse of Mathlib, so it is
  defined for every closure. Its properties need $0 \le \lambda_0, \mu_n \le 1$.
-/

open Filter Polynomial Set
open scoped Topology

namespace Spline

variable {a b : ℝ} {n k r : ℕ} {x : ℕ → ℝ}

/-! ### The spline space -/

/-- The **spline space** $S_k^r$ of degree $k$ and smoothness $C^r$ for the nodes $x_0, \dots, x_n$:
the subspace of $C([a, b])$ of the functions $f$ for which there is a function
$g : \mathbb{R} \to \mathbb{R}$ of class $C^r$ on $[a, b]$ with $f = g$ on $[a, b]$ such that,
for each $0 \le j < n$, $g$ agrees on $[x_j, x_{j+1}]$ with a polynomial of degree at most $k$.
This is Definition 8.1 of [quarteroni2000numerical] for $r = k - 1$.

The space $X_h^k$ of §8.3 of the source is the case $r = 0$, and the case $r = k$ gives the
polynomials of degree at most $k$. The definition does not require the nodes to increase; the
results below assume `IsIntervalPartition a b n x`. -/
noncomputable def splineSpace (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k r : ℕ) :
    Submodule ℝ C(Icc a b, ℝ) where
  carrier := {f | ∃ g : ℝ → ℝ, ContDiffOn ℝ r g (Icc a b) ∧ (∀ t : Icc a b, f t = g t) ∧
    ∀ j < n, ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1)))}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, hf₁, hp₁⟩ ⟨g₂, hg₂, hf₂, hp₂⟩
    refine ⟨g₁ + g₂, hg₁.add hg₂, fun t => by simp [hf₁ t, hf₂ t], fun j hj => ?_⟩
    obtain ⟨p₁, hp₁d, hp₁e⟩ := hp₁ j hj
    obtain ⟨p₂, hp₂d, hp₂e⟩ := hp₂ j hj
    exact ⟨p₁ + p₂, (degree_add_le _ _).trans (max_le hp₁d hp₂d),
      fun t ht => by simp [hp₁e ht, hp₂e ht]⟩
  zero_mem' := ⟨0, contDiffOn_const, fun _ => rfl, fun _ _ => ⟨0, by simp, fun _ _ => by simp⟩⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hf, hp⟩
    refine ⟨c • g, hg.const_smul c, fun t => by simp [hf t], fun j hj => ?_⟩
    obtain ⟨p, hpd, hpe⟩ := hp j hj
    exact ⟨c • p, (degree_smul_le _ _).trans hpd, fun t ht => by simp [hpe ht]⟩

/-- A function $f \in C([a, b])$ lies in $S_k^r$ if and only if there is
$g : \mathbb{R} \to \mathbb{R}$ of class $C^r$ on $[a, b]$ with $f(t) = g(t)$ for all
$t \in [a, b]$ such that, for each $0 \le j < n$, $g$ agrees on $[x_j, x_{j+1}]$ with a
polynomial of degree at most $k$. -/
theorem mem_splineSpace_iff {f : C(Icc a b, ℝ)} :
    f ∈ splineSpace a b n x k r ↔ ∃ g : ℝ → ℝ, ContDiffOn ℝ r g (Icc a b) ∧
      (∀ t : Icc a b, f t = g t) ∧
      ∀ j < n, ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1))) :=
  Iff.rfl

/-- Every polynomial of degree at most $k$ on $[a, b]$ lies in $S_k^r$, for all nodes
$x_0, \dots, x_n$ and every $r$. The source remarks that "obviously, any polynomial of degree
$k$ on $[a, b]$ is a spline".

The polynomials are `polyLE (Set.Icc a b) k`. -/
theorem polyLE_le_splineSpace (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k r : ℕ) :
    polyLE (Icc a b) k ≤ splineSpace a b n x k r := by
  intro f hf
  obtain ⟨P, hPd, hPv⟩ := mem_polyLE_iff.mp hf
  exact ⟨P.eval, (P.contDiff_eval r).contDiffOn, hPv, fun _ _ => ⟨P, hPd, fun _ _ => rfl⟩⟩

/-- If $r \le r'$, then $S_k^{r'} \subseteq S_k^r$: smoother splines form a smaller space. -/
theorem splineSpace_anti_smoothness {r' : ℕ} (hrr : r ≤ r') :
    splineSpace a b n x k r' ≤ splineSpace a b n x k r := by
  rintro f ⟨g, hg, hf, hp⟩
  exact ⟨g, hg.of_le (by exact_mod_cast hrr), hf, hp⟩

/-- If $k \le k'$, then $S_k^r \subseteq S_{k'}^r$: splines of lower degree form a smaller space. -/
theorem splineSpace_mono_degree {k' : ℕ} (hkk : k ≤ k') :
    splineSpace a b n x k r ≤ splineSpace a b n x k' r := by
  rintro f ⟨g, hg, hf, hp⟩
  refine ⟨g, hg, hf, fun j hj => ?_⟩
  obtain ⟨p, hpd, hpe⟩ := hp j hj
  exact ⟨p, hpd.trans (by exact_mod_cast hkk), hpe⟩

/-! ### Truncated powers -/

/-- For $c \in \mathbb{R}$ and $s \in \mathbb{N}$, the function $t \mapsto \max(t - c, 0)^{s+2}$ has
the derivative $(s + 2) \max(t - c, 0)^{s+1}$ at every $t \in \mathbb{R}$, the point $t = c$
included. -/
theorem hasDerivAt_max_sub_pow (c : ℝ) (s : ℕ) (t : ℝ) :
    HasDerivAt (fun t => max (t - c) 0 ^ (s + 2)) ((s + 2) * max (t - c) 0 ^ (s + 1)) t := by
  rcases lt_trichotomy t c with htc | rfl | htc
  · have h : (fun t => max (t - c) 0 ^ (s + 2)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds htc] with u (hu : u < c)
      simp [max_eq_right (sub_nonpos.mpr hu.le)]
    rw [max_eq_right (sub_nonpos.mpr htc.le), zero_pow (Nat.succ_ne_zero s), mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h
  · rw [sub_self, max_self, zero_pow (Nat.succ_ne_zero s), mul_zero,
      hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [add_sub_cancel_left, sub_self, max_self, zero_pow (Nat.succ_ne_zero _), sub_zero,
      smul_zero]
    have h1 : (fun h : ℝ => max h 0) =O[𝓝 0] fun h => h :=
      Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => by
        simp only [Real.norm_eq_abs, one_mul]
        rcases le_or_gt h 0 with hh | hh
        · simp [max_eq_right hh]
        · simp [max_eq_left hh.le])
    have h2 : (fun h : ℝ => max h 0 ^ (s + 1)) =o[𝓝 0] fun _ => (1 : ℝ) := by
      rw [Asymptotics.isLittleO_one_iff]
      have : Tendsto (fun h : ℝ => max h 0 ^ (s + 1)) (𝓝 0) (𝓝 (max 0 0 ^ (s + 1))) :=
        ((continuous_id.max continuous_const).pow _).tendsto 0
      simpa using this
    have := h1.mul_isLittleO h2
    simpa [pow_succ, mul_comm] using this
  · have h : (fun t => max (t - c) 0 ^ (s + 2)) =ᶠ[𝓝 t] fun t => (t - c) ^ (s + 2) := by
      filter_upwards [Ioi_mem_nhds htc] with u (hu : c < u)
      simp [max_eq_left (sub_nonneg.mpr hu.le)]
    rw [max_eq_left (sub_nonneg.mpr htc.le)]
    have := (hasDerivAt_pow (s + 2) (t - c)).comp t ((hasDerivAt_id t).sub_const c)
    simp only [Nat.cast_add, Nat.cast_ofNat, mul_one] at this
    exact this.congr_of_eventuallyEq h

/-- For $c \in \mathbb{R}$ and $s \in \mathbb{N}$, the truncated power $t \mapsto (t - c)_+^{s+1} =
\max(t - c, 0)^{s+1}$ is of class $C^s$ on $\mathbb{R}$. Its derivatives of order at most $s$
vanish at $c$ from both sides. -/
theorem contDiff_max_sub_pow (c : ℝ) (s : ℕ) :
    ContDiff ℝ s (fun t => max (t - c) 0 ^ (s + 1)) := by
  induction s with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact ((continuous_id.sub continuous_const).max continuous_const).pow 1
  | succ s ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_max_sub_pow c s t).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have : deriv (fun t => max (t - c) 0 ^ (s + 1 + 1)) =
        fun t => ((s : ℝ) + 2) * max (t - c) 0 ^ (s + 1) :=
      funext fun t => (hasDerivAt_max_sub_pow c s t).deriv
    rw [this]
    exact contDiff_const.mul ih

/-- The **truncated power** $t \mapsto (t - c)_+^s = \max(t - c, 0)^s$, as an element of
$C([a, b])$. For $s = 0$ it is the constant function $1$. For $s \ge 1$ it agrees with
`Quadrature.truncPow s t c` (`Spline.truncPowCM_apply_eq`). -/
noncomputable def truncPowCM (a b c : ℝ) (s : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => max ((t : ℝ) - c) 0 ^ s,
    ((continuous_subtype_val.sub continuous_const).max continuous_const).pow s⟩

/-- The truncated power takes the value $\max(t - c, 0)^s$ at $t \in [a, b]$. -/
@[simp]
theorem truncPowCM_apply (a b c : ℝ) (s : ℕ) (t : Icc a b) :
    truncPowCM a b c s t = max ((t : ℝ) - c) 0 ^ s := rfl

/-- For $s \ge 1$ and $t \in [a, b]$, the truncated power $(t - c)_+^s$ is
`Quadrature.truncPow s t c`, which is $(t - c)^s$ for $t \ge c$ and $0$ otherwise. -/
theorem truncPowCM_apply_eq (a b c : ℝ) {s : ℕ} (hs : 1 ≤ s) (t : Icc a b) :
    truncPowCM a b c s t = Quadrature.truncPow s t c := by
  rw [truncPowCM_apply, Quadrature.truncPow]
  split_ifs with h
  · rw [max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), zero_pow (by omega)]

/-- The monomial $t \mapsto t^i$, as an element of $C([a, b])$. -/
noncomputable def monomialCM (a b : ℝ) (i : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => (t : ℝ) ^ i, continuous_subtype_val.pow i⟩

/-- The monomial takes the value $t^i$ at $t \in [a, b]$. -/
@[simp]
theorem monomialCM_apply (a b : ℝ) (i : ℕ) (t : Icc a b) : monomialCM a b i t = (t : ℝ) ^ i := rfl

/-- For $i \le k$, the monomial $t^i$ lies in the space `polyLE (Set.Icc a b) k` of the polynomials
of degree at most $k$ on $[a, b]$. -/
theorem monomialCM_mem_polyLE (a b : ℝ) {i : ℕ} (hi : i ≤ k) :
    monomialCM a b i ∈ polyLE (Icc a b) k :=
  mem_polyLE_iff.mpr ⟨X ^ i, (degree_X_pow_le i).trans (by exact_mod_cast hi), fun t => by simp⟩

/-- Let $a = x_0 < \dots < x_n = b$ be a partition, let $0 \le j < n$, and let $r < s \le k$. Then
the truncated power $(t - x_j)_+^s$ lies in $S_k^r$.

The truncated power is of class $C^{s-1}$ by `Spline.contDiff_max_sub_pow`, and it is a
polynomial on each side of $x_j$. For $j = 0$ it is the polynomial $(t - a)^s$ on $[a, b]$. -/
theorem truncPowCM_mem_splineSpace (hx : IsIntervalPartition a b n x) {j s : ℕ} (hjn : j < n)
    (hrs : r < s) (hsk : s ≤ k) : truncPowCM a b (x j) s ∈ splineSpace a b n x k r := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  refine ⟨fun t => max (t - x j) 0 ^ (s + 1),
    ((contDiff_max_sub_pow (x j) s).of_le (by exact_mod_cast (by omega : r ≤ s))).contDiffOn,
    fun t => rfl, fun i hi => ?_⟩
  rcases le_or_gt j i with hji | hij
  · refine ⟨(X - C (x j)) ^ (s + 1), (degree_pow_le _ _).trans ?_, fun t ht => ?_⟩
    · calc ((s + 1) • (X - C (x j)).degree : WithBot ℕ) ≤ (s + 1) • (1 : WithBot ℕ) :=
          nsmul_le_nsmul_right (degree_X_sub_C_le _) _
        _ = ((s + 1 : ℕ) : WithBot ℕ) := by simp
        _ ≤ k := by exact_mod_cast hsk
    · have : x j ≤ t := (hx.mono hji (by omega)).trans ht.1
      simp [max_eq_left (sub_nonneg.mpr this)]
  · refine ⟨0, by simp, fun t ht => ?_⟩
    have : t ≤ x j := ht.2.trans (hx.mono (by omega) hjn.le)
    simp [max_eq_right (sub_nonpos.mpr this)]

/-!
### The truncated-power basis

The family of Exercise 8.10 of [quarteroni2000numerical]: the monomials $1, t, \dots, t^k$ together
with the truncated powers $(t - x_j)_+^s$ at the interior breakpoints $x_1, \dots, x_{n-1}$, for the
exponents $r < s \le k$. Its index type has $(k + 1) + (n - 1)(k - r)$ elements.
-/

/-- The index type of the truncated-power family. An index `Sum.inl i`, $0 \le i \le k$, stands for
the monomial exponent $i$. An index `Sum.inr (j, s)`, $0 \le j < n - 1$, $0 \le s < k - r$,
stands for the interior breakpoint $x_{j+1}$ and the exponent $r + 1 + s$. -/
abbrev TruncPowIndex (n k r : ℕ) : Type := Fin (k + 1) ⊕ (Fin (n - 1) × Fin (k - r))

/-- The **truncated-power family** of $S_k^r$: the monomial $t^i$ at the index `Sum.inl i`,
$0 \le i \le k$, and the truncated power $(t - x_{j+1})_+^{r+1+s}$ at the index
`Sum.inr (j, s)`, $0 \le j < n - 1$, $0 \le s < k - r$. -/
noncomputable def truncPowFamily (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k r : ℕ) :
    TruncPowIndex n k r → C(Icc a b, ℝ)
  | Sum.inl i => monomialCM a b i
  | Sum.inr (j, s) => truncPowCM a b (x (j + 1)) (r + 1 + s)

/-- For a partition $a = x_0 < \dots < x_n = b$, every member of the truncated-power family lies in
$S_k^r$. -/
theorem truncPowFamily_mem_splineSpace (hx : IsIntervalPartition a b n x)
    (i : TruncPowIndex n k r) :
    truncPowFamily a b n x k r i ∈ splineSpace a b n x k r := by
  rcases i with i | ⟨j, s⟩
  · exact polyLE_le_splineSpace a b n x k r (monomialCM_mem_polyLE a b (Nat.lt_succ_iff.mp i.2))
  · exact truncPowCM_mem_splineSpace hx (by have := j.2; omega) (by omega) (by have := s.2; omega)

/-- **Order-$r$ contact of the pieces of a $C^r$ function.** Let $u < v < w$, let $e$ be of class
$C^r$ on $(u, w)$ with $e = 0$ on $(u, v)$, and let $d$ be a polynomial with $e = d$ on
$(v, w)$. Then $d^{(m)}(v) = 0$ for every $m \le r$, because $e^{(m)}$ is continuous on
$(u, w)$, equal to $0$ to the left of $v$ and equal to $d^{(m)}$ to the right of $v$. -/
theorem iterate_derivative_eval_eq_zero_of_eqOn {u v w : ℝ} (huv : u < v) (hvw : v < w)
    {e : ℝ → ℝ} (he : ContDiffOn ℝ r e (Ioo u w)) (h0 : EqOn e 0 (Ioo u v)) {d : ℝ[X]}
    (hd : EqOn e d.eval (Ioo v w)) {m : ℕ} (hm : m ≤ r) : (derivative^[m] d).eval v = 0 := by
  have hcont : ContinuousOn (iteratedDeriv m e) (Ioo u w) :=
    (he.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) isOpen_Ioo.uniqueDiffOn).congr
      (iteratedDerivWithin_of_isOpen isOpen_Ioo).symm
  have hv : v ∈ Ioo u w := ⟨huv, hvw⟩
  have hleft : Tendsto (iteratedDeriv m e) (𝓝[Ioo u v] v) (𝓝 (iteratedDeriv m e v)) :=
    (hcont v hv).tendsto.mono_left (nhdsWithin_mono _ (Ioo_subset_Ioo_right hvw.le))
  have hright : Tendsto (iteratedDeriv m e) (𝓝[Ioo v w] v) (𝓝 (iteratedDeriv m e v)) :=
    (hcont v hv).tendsto.mono_left (nhdsWithin_mono _ (Ioo_subset_Ioo_left huv.le))
  have hl0 : Tendsto (iteratedDeriv m e) (𝓝[Ioo u v] v) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [h0.iteratedDeriv_of_isOpen isOpen_Ioo m ht]
    cases m <;> simp
  have hr0 : Tendsto (iteratedDeriv m e) (𝓝[Ioo v w] v) (𝓝 ((derivative^[m] d).eval v)) := by
    have : Tendsto (fun t => (derivative^[m] d).eval t) (𝓝[Ioo v w] v)
        (𝓝 ((derivative^[m] d).eval v)) :=
      ((derivative^[m] d).continuous.tendsto v).mono_left nhdsWithin_le_nhds
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hd.iteratedDeriv_of_isOpen isOpen_Ioo m ht, Polynomial.iteratedDeriv_eval]
  have : (𝓝[Ioo u v] v).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsLT huv]; infer_instance
  have : (𝓝[Ioo v w] v).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsGT hvw]; infer_instance
  rw [← tendsto_nhds_unique hright hr0, tendsto_nhds_unique hleft hl0]

/-- Let $d$ be a polynomial of degree at most $k$ with $d^{(m)}(v) = 0$ for all $m \le r$. Then for
all $t$,
$$d(t) = \sum_{r < s \le k} c_s (t - v)^s,$$
where $c_s$ is the coefficient of $(t - v)^s$ in the Taylor expansion of $d$ at $v$. -/
theorem eval_eq_sum_Ioc_of_iterate_derivative_eq_zero {d : ℝ[X]} (hd : d.natDegree ≤ k) {v : ℝ}
    (h0 : ∀ m ≤ r, (derivative^[m] d).eval v = 0) (t : ℝ) :
    d.eval t = ∑ s ∈ Finset.Ioc r k, (taylor v d).coeff s * (t - v) ^ s := by
  have hcoeff : ∀ m ≤ r, (taylor v d).coeff m = 0 := by
    intro m hm
    have h := congrArg (Polynomial.eval v) (congrFun (factorial_smul_hasseDeriv (R := ℝ) m) d)
    rw [LinearMap.smul_apply, eval_smul, nsmul_eq_mul, h0 m hm] at h
    rw [taylor_coeff]
    have hfac : ((m.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    exact (mul_eq_zero.mp h).resolve_left hfac
  rw [← taylor_eval_sub v, eval_eq_sum_range' (n := k + 1) (by rw [natDegree_taylor]; omega)]
  rw [← Finset.sum_filter_of_ne (p := fun s => r < s)]
  · congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  · intro s _ hs
    by_contra hrs
    exact hs (by rw [hcoeff s (not_lt.mp hrs), zero_mul])

/-- If the polynomial $\sum_{s < N} c_s (X - v)^{r+1+s}$ is zero, then $c_s = 0$ for every $s < N$.
-/
theorem eq_zero_of_sum_C_mul_X_sub_C_pow_eq_zero {N : ℕ} {c : Fin N → ℝ} {v : ℝ}
    (h : ∑ s : Fin N, C (c s) * (X - C v) ^ (r + 1 + s) = 0) (s : Fin N) : c s = 0 := by
  have h' := congrArg (taylor v) h
  simp only [map_sum, taylor_mul, taylor_C, taylor_pow, map_sub, taylor_X, add_sub_cancel_right,
    map_zero] at h'
  have := congrArg (fun p => p.coeff (r + 1 + s)) h'
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single s (fun s' _ hs' => by
      rw [ite_eq_right]; intro h; exact hs' (Fin.ext (by omega)))
    (fun h => absurd (Finset.mem_univ s) h), ite_eq_left rfl] at this
  exact this

/-- A real polynomial that vanishes on an interval $[u, v]$ with $u < v$ is the zero polynomial. -/
theorem eq_zero_of_eval_eq_zero_on_Icc {p : ℝ[X]} {u v : ℝ} (huv : u < v)
    (h : ∀ t ∈ Icc u v, p.eval t = 0) : p = 0 :=
  p.eq_zero_of_infinite_isRoot ((Icc_infinite huv).mono fun t ht => h t ht)

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. Then the truncated-power family,
the monomials $t^i$, $0 \le i \le k$, together with the truncated powers $(t - x_j)_+^s$,
$0 < j < n$, $r < s \le k$, is linearly independent in $C([a, b])$. This is the independence
half of Exercise 8.10 of [quarteroni2000numerical].

On the first panel only the monomials are nonzero, so their coefficients vanish. Then, panel by
panel, only the truncated powers at the breakpoints to the left are nonzero. The coefficients of
the powers at the newest breakpoint vanish, because the polynomials $(t - x_j)^s$,
$r < s \le k$, are linearly independent. -/
theorem linearIndependent_truncPow (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (truncPowFamily a b n x k r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- the vanishing combination as a real function
  have hval : ∀ t : Icc a b, ∑ i : Fin (k + 1), g (Sum.inl i) * (t : ℝ) ^ (i : ℕ) +
      ∑ j : Fin (n - 1), ∑ s : Fin (k - r),
        g (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) = 0 := by
    intro t
    have := congrArg (fun f : C(Icc a b, ℝ) => f t) hg
    simp only [ContinuousMap.coe_zero, Pi.zero_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type] at this
    simpa [truncPowFamily] using this
  -- truncated powers at breakpoints to the right of a point vanish there
  have hvan : ∀ (i : ℕ) (j : Fin (n - 1)) (s : Fin (k - r)) (t : ℝ), i ≤ n → t ≤ x i →
      i ≤ (j : ℕ) + 1 → max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 := by
    intro i j s t hi ht hij
    rw [max_eq_right (sub_nonpos.mpr (ht.trans (hx.mono hij (by omega)))),
      zero_pow (by omega)]
  -- the monomial coefficients vanish
  have hmono : ∀ i, g (Sum.inl i) = 0 := by
    have hpoly : (∑ i : Fin (k + 1), C (g (Sum.inl i)) * X ^ (i : ℕ)) = 0 := by
      refine eq_zero_of_eval_eq_zero_on_Icc (hx.step 0 hn) fun t ht => ?_
      have ht' : t ∈ Icc a b := hx.Icc_subset hn ht
      have h0 : ∑ i : Fin (k + 1), g (Sum.inl i) * t ^ (i : ℕ) + ∑ j : Fin (n - 1),
          ∑ s : Fin (k - r), g (Sum.inr (j, s)) * max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 :=
        hval ⟨t, ht'⟩
      have hz : ∑ j : Fin (n - 1), ∑ s : Fin (k - r),
          g (Sum.inr (j, s)) * max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 :=
        Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun s _ => by
          rw [hvan 1 j s t hn (by simpa using ht.2) (by omega), mul_zero]
      rw [hz, add_zero] at h0
      simpa only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] using h0
    intro i
    have := congrArg (fun p => p.coeff (i : ℕ)) hpoly
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single i (fun i' _ hi' => by
        rw [ite_eq_right]; intro h; exact hi' (Fin.ext h.symm))
      (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl] at this
    exact this
  -- the truncated-power coefficients vanish, breakpoint by breakpoint
  have htrunc : ∀ m : ℕ, ∀ j : Fin (n - 1), (j : ℕ) ≤ m → ∀ s, g (Sum.inr (j, s)) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro j hjm s
    have hj : (j : ℕ) + 1 < n := by omega
    have hpoly : (∑ s : Fin (k - r), C (g (Sum.inr (j, s))) * (X - C (x (j + 1))) ^ (r + 1 + s))
        = 0 := by
      refine eq_zero_of_eval_eq_zero_on_Icc (hx.step (j + 1) hj) fun t ht => ?_
      have ht' : t ∈ Icc a b := hx.Icc_subset hj ht
      have h0 : ∑ i : Fin (k + 1), g (Sum.inl i) * t ^ (i : ℕ) + ∑ j : Fin (n - 1),
          ∑ s : Fin (k - r), g (Sum.inr (j, s)) * max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 :=
        hval ⟨t, ht'⟩
      simp only [hmono, zero_mul, Finset.sum_const_zero, zero_add] at h0
      rw [Finset.sum_eq_single j] at h0
      · simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
        rw [← h0]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [max_eq_left (sub_nonneg.mpr ht.1)]
      · intro j' _ hj'
        rcases lt_or_gt_of_ne (fun h => hj' (Fin.ext h)) with h | h
        · refine Finset.sum_eq_zero fun s _ => ?_
          rw [ih j' (by omega) j' le_rfl s, zero_mul]
        · refine Finset.sum_eq_zero fun s _ => ?_
          rw [hvan (j + 2) j' s t (by omega) (by simpa [add_assoc] using ht.2) (by omega),
            mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    exact eq_zero_of_sum_C_mul_X_sub_C_pow_eq_zero hpoly s
  rintro (i | ⟨j, s⟩)
  · exact hmono i
  · exact htrunc j j le_rfl s

/-- For $F : \mathbb{N} \to \mathbb{R}$, $\sum_{r < s \le k} F(s) = \sum_{s=0}^{k-r-1} F(r + 1 +
s)$. -/
theorem sum_Ioc_eq_sum_fin (F : ℕ → ℝ) :
    ∑ s ∈ Finset.Ioc r k, F s = ∑ s : Fin (k - r), F (r + 1 + s) := by
  have : Finset.Ioc r k = Finset.Ico (r + 1) (k + 1) := by
    ext s; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun s => F (r + 1 + s)),
    Nat.succ_sub_succ_eq_sub]

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. Then the truncated-power family
spans $S_k^r$. This is the spanning half of Exercise 8.10 of [quarteroni2000numerical].

A spline is its polynomial $p_0$ on the first panel plus, at each interior breakpoint $x_j$, the
difference $p_j - p_{j-1}$ of the polynomials on the two adjacent panels. This difference has
derivatives of order at most $r$ that vanish at $x_j$
(`Spline.iterate_derivative_eval_eq_zero_of_eqOn`). So it is a combination of $(t - x_j)^s$,
$r < s \le k$, and its continuation by zero to the left of $x_j$ is a combination of truncated
powers. -/
theorem span_truncPow_eq_splineSpace (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    Submodule.span ℝ (Set.range (truncPowFamily a b n x k r)) = splineSpace a b n x k r := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun f hf => ?_
  · rintro _ ⟨i, rfl⟩
    exact truncPowFamily_mem_splineSpace hx i
  obtain ⟨g, hg, hf, hp⟩ := hf
  have hp' : ∀ j, ∃ p : ℝ[X], j < n → p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1))) :=
    fun j => if h : j < n then (hp j h).imp fun _ hp' _ => hp' else ⟨0, fun h' => absurd h' h⟩
  choose p hp using hp'
  -- the coefficients
  set c : TruncPowIndex n k r → ℝ := fun i => match i with
    | Sum.inl i => (p 0).coeff i
    | Sum.inr (j, s) => (taylor (x (j + 1)) (p (j + 1) - p j)).coeff (r + 1 + s) with hc
  have hdeg : ∀ j < n, (p j).natDegree ≤ k := fun j hj =>
    natDegree_le_of_degree_le (hp j hj).1
  -- the differences of adjacent panel polynomials as sums of shifted powers
  have hdiff : ∀ j : Fin (n - 1), ∀ t, (p (j + 1) - p j).eval t =
      ∑ s : Fin (k - r), c (Sum.inr (j, s)) * (t - x (j + 1)) ^ (r + 1 + s) := by
    intro j t
    have hj : (j : ℕ) + 1 < n := by omega
    rw [eval_eq_sum_Ioc_of_iterate_derivative_eq_zero (k := k) (r := r)
      ((natDegree_sub_le _ _).trans (max_le (hdeg _ hj) (hdeg _ (by omega)))), sum_Ioc_eq_sum_fin]
    intro m hm
    refine iterate_derivative_eval_eq_zero_of_eqOn (e := fun t => g t - (p j).eval t)
      (hx.step j (by omega)) (hx.step (j + 1) hj) ?_ ?_ ?_ hm
    · exact (hg.mono (Ioo_subset_Icc_self.trans
        (Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right (by omega))))).sub
        ((p j).contDiff_eval _).contDiffOn
    · intro t ht
      simp [(hp j (by omega)).2 (Ioo_subset_Icc_self ht)]
    · intro t ht
      simp [(hp (j + 1) hj).2 (Ioo_subset_Icc_self ht)]
  -- the claimed representation
  have hrep : f = ∑ i, c i • truncPowFamily a b n x k r i := by
    ext t
    obtain ⟨i, hi1, hin, hti, -⟩ := hx.exists_mem_panel hn t.2
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp only [add_tsub_cancel_right] at hti
    have hmn : m < n := by omega
    rw [hf t, (hp m hmn).2 hti]
    have hrhs : (∑ i, c i • truncPowFamily a b n x k r i) t =
        ∑ i : Fin (k + 1), c (Sum.inl i) * (t : ℝ) ^ (i : ℕ) + ∑ j : Fin (n - 1),
          ∑ s : Fin (k - r), c (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) := by
      simp [Fintype.sum_sum_type, Fintype.sum_prod_type, truncPowFamily]
    rw [hrhs]
    -- the monomial part is `p 0`
    have h0 : ∑ i : Fin (k + 1), c (Sum.inl i) * (t : ℝ) ^ (i : ℕ) = (p 0).eval (t : ℝ) := by
      rw [eval_eq_sum_range' (n := k + 1) (by have := hdeg 0 hn; omega),
        Fin.sum_univ_eq_sum_range (fun i => (p 0).coeff i * (t : ℝ) ^ i)]
    -- the truncated part telescopes
    have h1 : ∑ j : Fin (n - 1), ∑ s : Fin (k - r),
        c (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) =
        ∑ j ∈ Finset.range m, ((p (j + 1)).eval (t : ℝ) - (p j).eval (t : ℝ)) := by
      have : ∀ j : Fin (n - 1), ∑ s : Fin (k - r),
          c (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) =
          if (j : ℕ) < m then (p (j + 1)).eval (t : ℝ) - (p j).eval (t : ℝ) else 0 := by
        intro j
        split_ifs with hjm
        · rw [← eval_sub, hdiff j]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [max_eq_left (sub_nonneg.mpr ((hx.mono (by omega) hmn.le).trans hti.1))]
        · refine Finset.sum_eq_zero fun s _ => ?_
          rw [max_eq_right (sub_nonpos.mpr (hti.2.trans (hx.mono (by omega)
            (by omega)))), zero_pow (by omega), mul_zero]
      simp_rw [this]
      rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then (p (j + 1)).eval (t : ℝ) -
        (p j).eval (t : ℝ) else 0) (n - 1), ← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [h0, h1, Finset.sum_range_sub (fun j => (p j).eval (t : ℝ)) m]
    ring
  rw [hrep]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- For $n \ge 1$ and $r \le k$, the truncated-power family has $n(k - r) + r + 1$ members. -/
theorem card_truncPowIndex (hn : 1 ≤ n) (hrk : r ≤ k) :
    Fintype.card (TruncPowIndex n k r) = n * (k - r) + r + 1 := by
  simp only [TruncPowIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = r + d := ⟨k - r, by omega⟩
  simp only [add_tsub_cancel_right, add_tsub_cancel_left]
  ring

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $r \le k$. Then
$$\dim S_k^r = n(k - r) + r + 1.$$
For $r = k - 1$ this is $\dim S_k = n + k$ of Definition 8.1 of [quarteroni2000numerical], and
for $r = 0$ it is $nk + 1$; compare (8.43) of the source.

The truncated-power family is a basis by `Spline.linearIndependent_truncPow` and
`Spline.span_truncPow_eq_splineSpace`, and `Spline.card_truncPowIndex` counts it. -/
theorem finrank_splineSpace (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (hrk : r ≤ k) :
    Module.finrank ℝ (splineSpace a b n x k r) = n * (k - r) + r + 1 := by
  rw [← span_truncPow_eq_splineSpace hx hn, finrank_span_eq_card (linearIndependent_truncPow hx hn),
    card_truncPowIndex hn hrk]

/-- For a partition $a = x_0 < \dots < x_n = b$ with $n \ge 1$, the spline space $S_k^r$ is
finite-dimensional. -/
theorem finiteDimensional_splineSpace (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) :
    FiniteDimensional ℝ (splineSpace a b n x k r) := by
  rw [← span_truncPow_eq_splineSpace hx hn]
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $k \ge 1$. Then
$S_k = S_k^{k-1}$ has a basis $(B_i)_{0 \le i < n + k}$ with $B_i(t) = t^i$ for $i \le k$ and
$B_i(t) = (t - x_{i-k})_+^k$ for $k < i < n + k$. So the basis consists of the monomials
$1, t, \dots, t^k$ and the truncated powers $(t - x_j)_+^k$, $j = 1, \dots, n - 1$. This is
Exercise 8.10 of [quarteroni2000numerical].

The truncated power is written `Quadrature.truncPow k t (x (i - k))`. -/
theorem exists_basis_truncPow (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ (splineSpace a b n x k (k - 1)),
      (∀ i : Fin (n + k), (i : ℕ) ≤ k → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = (t : ℝ) ^ (i : ℕ)) ∧
      ∀ i : Fin (n + k), k < i → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = Quadrature.truncPow k (t : ℝ) (x (i - k)) := by
  classical
  set φ : TruncPowIndex n k (k - 1) → Fin (n + k) := fun i => match i with
    | Sum.inl i => ⟨i, by omega⟩
    | Sum.inr (j, _) => ⟨k + 1 + j, by omega⟩ with hφ
  have hφb : Function.Bijective φ := by
    constructor
    · rintro (i | ⟨j, s⟩) (i' | ⟨j', s'⟩) h <;> simp only [hφ, Fin.mk.injEq] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · omega
      · omega
      · have hs : s = s' := Fin.ext (by omega)
        rw [hs, show j = j' from Fin.ext (by omega)]
    · intro i
      by_cases hi : (i : ℕ) ≤ k
      · exact ⟨Sum.inl ⟨i, by omega⟩, Fin.ext rfl⟩
      · exact ⟨Sum.inr (⟨i - k - 1, by omega⟩, ⟨0, by omega⟩), Fin.ext (by
          simp only [hφ]; omega)⟩
  set e : TruncPowIndex n k (k - 1) ≃ Fin (n + k) := Equiv.ofBijective φ hφb with he
  set B₀ := Module.Basis.span (linearIndependent_truncPow (k := k) (r := k - 1) hx hn) with hB₀
  set B := (B₀.map (LinearEquiv.ofEq _ _ (span_truncPow_eq_splineSpace hx hn))).reindex e with hB
  have hBval : ∀ i, (B i : C(Icc a b, ℝ)) = truncPowFamily a b n x k (k - 1) (e.symm i) := by
    intro i
    rw [hB, Module.Basis.reindex_apply, Module.Basis.map_apply, hB₀, Module.Basis.span_apply]
    rfl
  refine ⟨B, fun i hi t => ?_, fun i hi t => ?_⟩
  · have : e.symm i = Sum.inl ⟨i, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext rfl
    rw [hBval, this]
    rfl
  · have : e.symm i = Sum.inr (⟨i - k - 1, by omega⟩, ⟨0, by omega⟩) := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (by simp only [he, Equiv.ofBijective_apply, hφ]; omega)
    rw [hBval, this]
    change truncPowCM a b (x (i - k - 1 + 1)) (k - 1 + 1 + 0) t = _
    rw [show i - k - 1 + 1 = i - k by omega, show k - 1 + 1 + 0 = k by omega]
    exact truncPowCM_apply_eq a b _ hk t

/-!
### Gluing functions along a partition

A function given panel by panel, $Q_i$ on the panel $[x_{i-1}, x_i]$ for $1 \le i \le n$, is glued
by `Spline.panelGlue`, which selects the panel through `Spline.panelIndex`. The first panel is
extended to $-\infty$ and the last panel to $+\infty$ (`Spline.extPanel`). So the glued function is
defined on all of $\mathbb{R}$, not only on $[a, b]$, and near each point it is given by panel
functions. Derivatives at the nodes are then ordinary derivatives, and the smoothness of the glued
function follows from the agreement of the panel functions at the interior nodes
(`Spline.hasDerivAt_panelGlue`, `Spline.continuous_panelGlue`).
-/

/-- The index of the panel that contains $t$: $1 + \#\{j : 1 \le j < n,\ x_j \le t\}$. For
increasing nodes it is $1$ for $t < x_1$, it is $i$ for $x_{i-1} \le t < x_i$ with
$2 \le i < n$, and it is $n$ for $t \ge x_{n-1}$. For $n \le 1$ it is $1$ everywhere. -/
noncomputable def panelIndex (n : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℕ :=
  1 + ((Finset.Ico 1 n).filter fun j => x j ≤ t).card

/-- The function **glued** from the panel functions $Q_i$: its value at $t$ is $Q_i(t)$, where $i$
is the panel index of $t$ (`Spline.panelIndex`). On the $i$-th panel $[x_{i-1}, x_i]$ it is
$Q_i$, provided the panel functions agree at the interior nodes (`Spline.panelGlue_eq_of_mem`). -/
noncomputable def panelGlue {E : Type*} (n : ℕ) (x : ℕ → ℝ) (Q : ℕ → ℝ → E) (t : ℝ) : E :=
  Q (panelIndex n x t) t

/-- The $i$-th **extended panel**: the set of $t$ with $x_{i-1} \le t$ if $i > 1$ and with
$t \le x_i$ if $i < n$. It is the panel $[x_{i-1}, x_i]$, extended to $-\infty$ for $i = 1$ and
to $+\infty$ for $i = n$. -/
def extPanel (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Set ℝ :=
  {t | (1 < i → x (i - 1) ≤ t) ∧ (i < n → t ≤ x i)}

/-- A point $t$ lies in the $i$-th extended panel if and only if $x_{i-1} \le t$ in the case $i > 1$
and $t \le x_i$ in the case $i < n$. -/
theorem mem_extPanel_iff {i : ℕ} {t : ℝ} :
    t ∈ extPanel n x i ↔ (1 < i → x (i - 1) ≤ t) ∧ (i < n → t ≤ x i) := Iff.rfl

/-- The closed panel $[x_{i-1}, x_i]$ lies in the $i$-th extended panel. -/
theorem Icc_subset_extPanel (i : ℕ) : Icc (x (i - 1)) (x i) ⊆ extPanel n x i :=
  fun _ ht => ⟨fun _ => ht.1, fun _ => ht.2⟩

/-- Let $a = x_0 < \dots < x_n = b$ be a partition, and let $1 \le i \le n$. If $x_{i-1} \le t$ in
the case $i > 1$ and $t < x_i$ in the case $i < n$, then the panel index of $t$ is $i$. -/
theorem panelIndex_eq (hx : IsIntervalPartition a b n x) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht1 : 1 < i → x (i - 1) ≤ t) (ht2 : i < n → t < x i) : panelIndex n x t = i := by
  classical
  have : ((Finset.Ico 1 n).filter fun j => x j ≤ t) = Finset.Ico 1 i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hj1, hjn⟩, hjt⟩
      refine ⟨hj1, ?_⟩
      by_contra h
      have hin' : i < n := lt_of_le_of_lt (not_lt.mp h) hjn
      exact absurd ((hx.mono (not_lt.mp h) hjn.le).trans hjt) (not_le.mpr (ht2 hin'))
    · rintro ⟨hj1, hji⟩
      exact ⟨⟨hj1, by omega⟩, (hx.mono (by omega) (by omega)).trans (ht1 (by omega))⟩
  rw [panelIndex, this, Nat.card_Ico]
  omega

/-- Let $a = x_0 < \dots < x_n = b$ be a partition, and let the real panel functions satisfy
$Q_i(x_i) = Q_{i+1}(x_i)$ for $1 \le i < n$. Then for $1 \le i \le n$ the glued function equals
$Q_i$ on the $i$-th extended panel. -/
theorem panelGlue_eq_of_mem (hx : IsIntervalPartition a b n x) {Q : ℕ → ℝ → ℝ}
    (hQ : ∀ i, 1 ≤ i → i < n → Q i (x i) = Q (i + 1) (x i)) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {t : ℝ} (ht : t ∈ extPanel n x i) : panelGlue n x Q t = Q i t := by
  by_cases h : i < n ∧ t = x i
  · obtain ⟨hin', rfl⟩ := h
    rw [panelGlue, panelIndex_eq hx (i := i + 1) (by omega) hin' (fun _ => by simp)
      (fun h => by simpa using hx.step i hin'), hQ i hi1 hin']
  · rw [panelGlue, panelIndex_eq hx hi1 hin ht.1 fun hin' =>
      lt_of_le_of_ne (ht.2 hin') fun h' => h ⟨hin', h'⟩]

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $t \in \mathbb{R}$. Then
there is an index $1 \le i \le n$ such that $t$ lies in the $i$-th extended panel and either
this extended panel is a neighbourhood of $t$, or $t = x_i$ with $i < n$ and the union of the
$i$-th and the $(i + 1)$-th extended panels is a neighbourhood of $t$. -/
theorem _root_.IsIntervalPartition.exists_extPanel_mem_nhds (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) (t : ℝ) : ∃ i, 1 ≤ i ∧ i ≤ n ∧ t ∈ extPanel n x i ∧ (extPanel n x i ∈ 𝓝 t ∨
      (t = x i ∧ i < n ∧ extPanel n x i ∪ extPanel n x (i + 1) ∈ 𝓝 t)) := by
  rcases le_or_gt t a with hta | hat
  · refine ⟨1, le_rfl, hn, ⟨fun h => absurd h (lt_irrefl _), fun _ => hta.trans ?_⟩, Or.inl ?_⟩
    · exact hx.first ▸ (hx.step 0 hn).le
    · refine mem_of_superset (Iio_mem_nhds (hta.trans_lt (hx.first ▸ hx.step 0 hn))) ?_
      exact fun s hs => ⟨fun h => absurd h (lt_irrefl _), fun _ => le_of_lt hs⟩
  rcases le_or_gt b t with hbt | htb
  · refine ⟨n, hn, le_rfl, ⟨fun _ => ?_, fun h => absurd h (lt_irrefl _)⟩, Or.inl ?_⟩
    · exact (hx.le_right (Nat.sub_le n 1)).trans hbt
    · have hlt : x (n - 1) < t := by
        refine lt_of_lt_of_le ?_ hbt
        rw [← hx.last]
        exact hx.lt (by omega) le_rfl
      refine mem_of_superset (Ioi_mem_nhds hlt) ?_
      exact fun s hs => ⟨fun _ => le_of_lt hs, fun h => absurd h (lt_irrefl _)⟩
  obtain ⟨i, hi1, hin, hti, hlt⟩ := hx.exists_mem_panel hn ⟨hat.le, htb.le⟩
  have hlt' : x (i - 1) < t := by
    rcases hlt with h | rfl
    · exact h
    · simpa [hx.first] using hat
  rcases lt_or_eq_of_le hti.2 with htx | htx
  · refine ⟨i, hi1, hin, Icc_subset_extPanel i hti, Or.inl ?_⟩
    exact mem_of_superset (Ioo_mem_nhds hlt' htx)
      fun s hs => ⟨fun _ => hs.1.le, fun _ => hs.2.le⟩
  · have hin' : i < n := by
      by_contra h
      have : i = n := by omega
      subst this
      exact absurd (htx ▸ htb) (hx.last ▸ lt_irrefl _)
    refine ⟨i, hi1, hin, Icc_subset_extPanel i hti, Or.inr ⟨htx, hin', ?_⟩⟩
    refine mem_of_superset (Ioo_mem_nhds hlt' (htx ▸ hx.step i hin')) fun s hs => ?_
    rcases le_or_gt s (x i) with hsx | hsx
    · exact Or.inl ⟨fun _ => hs.1.le, fun _ => hsx⟩
    · exact Or.inr ⟨fun _ => by simpa using hsx.le, fun _ => hs.2.le⟩

/-- **Differentiability of a glued function.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$, and let $Q_i, Q'_i : \mathbb{R} \to \mathbb{R}$ be functions such that, for
$1 \le i \le n$, $Q_i$ has the derivative $Q'_i(t)$ at every point $t$ of the $i$-th extended
panel. If $Q_i(x_i) = Q_{i+1}(x_i)$ and $Q'_i(x_i) = Q'_{i+1}(x_i)$ for $1 \le i < n$, then the
glued function of the $Q_i$ has, at every $t \in \mathbb{R}$, the derivative given by the glued
function of the $Q'_i$. -/
theorem hasDerivAt_panelGlue (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {Q Q' : ℕ → ℝ → ℝ}
    (hQ : ∀ i, 1 ≤ i → i < n → Q i (x i) = Q (i + 1) (x i))
    (hQ' : ∀ i, 1 ≤ i → i < n → Q' i (x i) = Q' (i + 1) (x i))
    (hd : ∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ extPanel n x i, HasDerivAt (Q i) (Q' i t) t) (t : ℝ) :
    HasDerivAt (panelGlue n x Q) (panelGlue n x Q' t) t := by
  obtain ⟨i, hi1, hin, hti, hcase⟩ := hx.exists_extPanel_mem_nhds hn t
  have hloc : ∀ j, 1 ≤ j → j ≤ n → t ∈ extPanel n x j →
      HasDerivWithinAt (panelGlue n x Q) (Q' j t) (extPanel n x j) t := fun j hj1 hjn htj =>
    ((hd j hj1 hjn t htj).hasDerivWithinAt).congr
      (fun s hs => panelGlue_eq_of_mem hx hQ hj1 hjn hs) (panelGlue_eq_of_mem hx hQ hj1 hjn htj)
  rw [panelGlue_eq_of_mem hx hQ' hi1 hin hti]
  rcases hcase with hmem | ⟨rfl, hin', hmem⟩
  · exact (hloc i hi1 hin hti).hasDerivAt hmem
  · have h2 := hloc (i + 1) (by omega) hin' ⟨fun _ => by simp, fun _ => (hx.step i hin').le⟩
    rw [← hQ' i hi1 hin'] at h2
    exact ((hloc i hi1 hin hti).union h2).hasDerivAt hmem

/-- **Continuity of a glued function.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$. If each $Q_i$ is continuous on the $i$-th extended panel and
$Q_i(x_i) = Q_{i+1}(x_i)$ for $1 \le i < n$, then the glued function of the $Q_i$ is continuous
on $\mathbb{R}$. -/
theorem continuous_panelGlue (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {Q : ℕ → ℝ → ℝ}
    (hQ : ∀ i, 1 ≤ i → i < n → Q i (x i) = Q (i + 1) (x i))
    (hc : ∀ i, 1 ≤ i → i ≤ n → ContinuousOn (Q i) (extPanel n x i)) :
    Continuous (panelGlue n x Q) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  obtain ⟨i, hi1, hin, hti, hcase⟩ := hx.exists_extPanel_mem_nhds hn t
  have hloc : ∀ j, 1 ≤ j → j ≤ n → t ∈ extPanel n x j →
      ContinuousWithinAt (panelGlue n x Q) (extPanel n x j) t := fun j hj1 hjn htj =>
    (hc j hj1 hjn t htj).congr (fun s hs => panelGlue_eq_of_mem hx hQ hj1 hjn hs)
      (panelGlue_eq_of_mem hx hQ hj1 hjn htj)
  rcases hcase with hmem | ⟨rfl, hin', hmem⟩
  · exact (hloc i hi1 hin hti).continuousAt hmem
  · have h2 := hloc (i + 1) (by omega) hin' ⟨fun _ => by simp, fun _ => (hx.step i hin').le⟩
    exact ((hloc i hi1 hin hti).union h2).continuousAt hmem

/-- Let $u, u_1, u_2 : \mathbb{R} \to \mathbb{R}$. If $u$ has the derivative $u_1(t)$ and $u_1$ has
the derivative $u_2(t)$ at every $t \in \mathbb{R}$, and $u_2$ is continuous, then $u$ is of
class $C^2$. -/
theorem contDiff_two_of_hasDerivAt {u u₁ u₂ : ℝ → ℝ} (h₁ : ∀ t, HasDerivAt u (u₁ t) t)
    (h₂ : ∀ t, HasDerivAt u₁ (u₂ t) t) (h₃ : Continuous u₂) : ContDiff ℝ 2 u := by
  have hd₁ : deriv u = u₁ := funext fun t => (h₁ t).deriv
  have hd₂ : deriv u₁ = u₂ := funext fun t => (h₂ t).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (h₁ t).differentiableAt, fun h => absurd h (by simp), ?_⟩
  rw [hd₁, contDiff_one_iff_deriv, hd₂]
  exact ⟨fun t => (h₂ t).differentiableAt, h₃⟩

/-! ### The panel cubics -/

/-- The **panel cubic** on $[x_{i-1}, x_i]$ with the end values $f_{i-1}, f_i$ and the end second
derivatives $M_{i-1}, M_i$, as a polynomial. With $h_i = x_i - x_{i-1}$ it is
$$M_{i-1} \frac{(x_i - t)^3}{6 h_i} + M_i \frac{(t - x_{i-1})^3}{6 h_i} + C_{i-1} (t -
  x_{i-1}) + \tilde C_{i-1},$$
where $\tilde C_{i-1} = f_{i-1} - M_{i-1} h_i^2 / 6$ and $C_{i-1} = (f_i - f_{i-1}) / h_i - (h_i
/ 6)(M_i - M_{i-1})$. This is (8.46) of [quarteroni2000numerical] integrated twice. -/
noncomputable def panelCubicPoly (x : ℕ → ℝ) (f M : ℕ → ℝ) (i : ℕ) : ℝ[X] :=
  C (M (i - 1) / (6 * (x i - x (i - 1)))) * (C (x i) - X) ^ 3
    + C (M i / (6 * (x i - x (i - 1)))) * (X - C (x (i - 1))) ^ 3
    + C ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6 * (M i - M (i - 1)))
      * (X - C (x (i - 1)))
    + C (f (i - 1) - M (i - 1) * (x i - x (i - 1)) ^ 2 / 6)

/-- The panel cubic `Spline.panelCubicPoly x f M i`, as a function $\mathbb{R} \to \mathbb{R}$. -/
noncomputable def panelCubic (x : ℕ → ℝ) (f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (panelCubicPoly x f M i).eval t

/-- The panel cubic has degree at most $3$. -/
theorem degree_panelCubicPoly_le (x f M : ℕ → ℝ) (i : ℕ) : (panelCubicPoly x f M i).degree ≤ 3 := by
  unfold panelCubicPoly
  refine (degree_add_le _ _).trans (max_le ((degree_add_le _ _).trans (max_le
    ((degree_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
  · refine (degree_mul_le _ _).trans ?_
    calc (C _).degree + ((C (x i) - X) ^ 3).degree ≤ 0 + 3 • (C (x i) - X).degree :=
          add_le_add degree_C_le (degree_pow_le _ _)
      _ ≤ 0 + 3 • 1 := by
          gcongr
          exact (degree_sub_le _ _).trans (max_le (degree_C_le.trans zero_le_one) degree_X_le)
      _ = 3 := by simp
  · refine (degree_mul_le _ _).trans ?_
    calc (C _).degree + ((X - C (x (i - 1))) ^ 3).degree ≤ 0 + 3 • (X - C (x (i - 1))).degree :=
          add_le_add degree_C_le (degree_pow_le _ _)
      _ ≤ 0 + 3 • 1 := by gcongr; exact degree_X_sub_C_le _
      _ = 3 := by simp
  · refine (degree_mul_le _ _).trans ?_
    calc (C _).degree + (X - C (x (i - 1))).degree ≤ 0 + 1 :=
          add_le_add degree_C_le (degree_X_sub_C_le _)
      _ ≤ 3 := by norm_num
  · exact degree_C_le.trans (by norm_num)

/-- The explicit form of the panel cubic: with $h_i = x_i - x_{i-1}$,
$$M_{i-1} \frac{(x_i - t)^3}{6 h_i} + M_i \frac{(t - x_{i-1})^3}{6 h_i} + \left( \frac{f_i -
  f_{i-1}}{h_i} - \frac{h_i}{6} (M_i - M_{i-1}) \right) (t - x_{i-1}) + f_{i-1} - \frac{M_{i-1}
  h_i^2}{6}.$$
-/
theorem panelCubic_apply (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    panelCubic x f M i t = M (i - 1) * (x i - t) ^ 3 / (6 * (x i - x (i - 1)))
      + M i * (t - x (i - 1)) ^ 3 / (6 * (x i - x (i - 1)))
      + ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6 * (M i - M (i - 1)))
        * (t - x (i - 1))
      + (f (i - 1) - M (i - 1) * (x i - x (i - 1)) ^ 2 / 6) := by
  simp only [panelCubic, panelCubicPoly, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  ring

/-- The first derivative of the panel cubic, as a function $\mathbb{R} \to \mathbb{R}$. -/
noncomputable def panelCubicD1 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (derivative (panelCubicPoly x f M i)).eval t

/-- The second derivative of the panel cubic, as a function $\mathbb{R} \to \mathbb{R}$. -/
noncomputable def panelCubicD2 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (derivative (derivative (panelCubicPoly x f M i))).eval t

/-- The third derivative of the panel cubic, as a function $\mathbb{R} \to \mathbb{R}$. It is
constant (`Spline.panelCubicD3_apply`). -/
noncomputable def panelCubicD3 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (derivative (derivative (derivative (panelCubicPoly x f M i)))).eval t

/-- At every $t \in \mathbb{R}$, the panel cubic has the derivative `Spline.panelCubicD1 x f M i t`.
-/
theorem hasDerivAt_panelCubic (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (panelCubic x f M i) (panelCubicD1 x f M i t) t :=
  (panelCubicPoly x f M i).hasDerivAt t

/-- At every $t \in \mathbb{R}$, the first derivative of the panel cubic has the derivative
`Spline.panelCubicD2 x f M i t`. -/
theorem hasDerivAt_panelCubicD1 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (panelCubicD1 x f M i) (panelCubicD2 x f M i t) t :=
  (derivative (panelCubicPoly x f M i)).hasDerivAt t

/-- At every $t \in \mathbb{R}$, the second derivative of the panel cubic has the derivative
`Spline.panelCubicD3 x f M i t`. -/
theorem hasDerivAt_panelCubicD2 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (panelCubicD2 x f M i) (panelCubicD3 x f M i t) t :=
  (derivative (derivative (panelCubicPoly x f M i))).hasDerivAt t

/-- If $x_{i-1} < x_i$, the first derivative of the panel cubic is
$$-M_{i-1} \frac{(x_i - t)^2}{2 h_i} + M_i \frac{(t - x_{i-1})^2}{2 h_i} + \frac{f_i -
  f_{i-1}}{h_i} - \frac{h_i}{6} (M_i - M_{i-1}),$$
where $h_i = x_i - x_{i-1}$. -/
theorem panelCubicD1_apply (x f M : ℕ → ℝ) {i : ℕ} (hh : x (i - 1) < x i) (t : ℝ) :
    panelCubicD1 x f M i t = -(M (i - 1) * (x i - t) ^ 2) / (2 * (x i - x (i - 1)))
      + M i * (t - x (i - 1)) ^ 2 / (2 * (x i - x (i - 1)))
      + ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6 * (M i - M (i - 1))) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  simp only [panelCubicD1, panelCubicPoly, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, eval_add, eval_mul, eval_C, eval_pow, eval_sub,
    eval_X, eval_zero, eval_one]
  field_simp
  ring

/-- **The second derivative of the panel cubic is linear.** If $x_{i-1} < x_i$, the second
derivative of the panel cubic is
$$M_{i-1} \frac{x_i - t}{h_i} + M_i \frac{t - x_{i-1}}{h_i},$$
where $h_i = x_i - x_{i-1}$; it interpolates the moments. This is (8.46) of
[quarteroni2000numerical]. -/
theorem panelCubicD2_apply (x f M : ℕ → ℝ) {i : ℕ} (hh : x (i - 1) < x i) (t : ℝ) :
    panelCubicD2 x f M i t = M (i - 1) * (x i - t) / (x i - x (i - 1))
      + M i * (t - x (i - 1)) / (x i - x (i - 1)) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  simp only [panelCubicD2, panelCubicPoly, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, derivative_one, derivative_zero, eval_add,
    eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_zero, eval_one]
  field_simp
  ring

/-- If $x_{i-1} < x_i$, the third derivative of the panel cubic is the constant
$(M_i - M_{i-1}) / h_i$, where $h_i = x_i - x_{i-1}$. -/
theorem panelCubicD3_apply (x f M : ℕ → ℝ) {i : ℕ} (hh : x (i - 1) < x i) (t : ℝ) :
    panelCubicD3 x f M i t = (M i - M (i - 1)) / (x i - x (i - 1)) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  simp only [panelCubicD3, panelCubicPoly, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, derivative_one, derivative_zero, eval_add,
    eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_zero, eval_one]
  field_simp
  ring

section PanelCubicValues

variable {f M : ℕ → ℝ} {i : ℕ}

/-- If $x_{i-1} < x_i$, the panel cubic takes the value $f_{i-1}$ at the left end $x_{i-1}$ of its
panel. -/
theorem panelCubic_left (hh : x (i - 1) < x i) : panelCubic x f M i (x (i - 1)) = f (i - 1) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubic_apply]
  field_simp
  ring

/-- If $x_{i-1} < x_i$, the panel cubic takes the value $f_i$ at the right end $x_i$ of its panel.
-/
theorem panelCubic_right (hh : x (i - 1) < x i) : panelCubic x f M i (x i) = f i := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubic_apply]
  field_simp
  ring

/-- If $x_i < x_{i+1}$, the panel cubic of the panel $[x_i, x_{i+1}]$ takes the value $f_i$ at
$x_i$. -/
theorem panelCubic_left_succ (hh : x i < x (i + 1)) : panelCubic x f M (i + 1) (x i) = f i := by
  have := panelCubic_left (x := x) (f := f) (M := M) (i := i + 1) (by simpa using hh)
  simpa using this

/-- If $x_{i-1} < x_i$, the second derivative of the panel cubic is $M_{i-1}$ at the left end
$x_{i-1}$. -/
theorem panelCubicD2_left (hh : x (i - 1) < x i) :
    panelCubicD2 x f M i (x (i - 1)) = M (i - 1) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD2_apply x f M hh]
  field_simp
  ring

/-- If $x_i < x_{i+1}$, the second derivative of the panel cubic of the panel $[x_i, x_{i+1}]$ is
$M_i$ at $x_i$. -/
theorem panelCubicD2_left_succ (hh : x i < x (i + 1)) : panelCubicD2 x f M (i + 1) (x i) = M i := by
  have := panelCubicD2_left (x := x) (f := f) (M := M) (i := i + 1) (by simpa using hh)
  simpa using this

/-- If $x_{i-1} < x_i$, the second derivative of the panel cubic is $M_i$ at the right end $x_i$. -/
theorem panelCubicD2_right (hh : x (i - 1) < x i) : panelCubicD2 x f M i (x i) = M i := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD2_apply x f M hh]
  field_simp
  ring

/-- **The slope from the left at the node $x_i$.** If $x_{i-1} < x_i$, the first derivative of the
panel cubic of $[x_{i-1}, x_i]$ at $x_i$ is
$$s'(x_i^-) = \frac{h_i M_{i-1}}{6} + \frac{h_i M_i}{3} + \frac{f_i - f_{i-1}}{h_i},$$
where $h_i = x_i - x_{i-1}$. This is the first displayed line before (8.47) in
[quarteroni2000numerical]. -/
theorem panelCubicD1_right (hh : x (i - 1) < x i) :
    panelCubicD1 x f M i (x i) = (x i - x (i - 1)) * M (i - 1) / 6 + (x i - x (i - 1)) * M i / 3
      + (f i - f (i - 1)) / (x i - x (i - 1)) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD1_apply x f M hh]
  field_simp
  ring

/-- **The slope from the right at the node $x_i$.** If $x_i < x_{i+1}$, the first derivative of the
panel cubic of $[x_i, x_{i+1}]$ at $x_i$ is
$$s'(x_i^+) = -\frac{h_{i+1} M_i}{3} - \frac{h_{i+1} M_{i+1}}{6} + \frac{f_{i+1} -
  f_i}{h_{i+1}},$$
where $h_{i+1} = x_{i+1} - x_i$. This is the second displayed line before (8.47) in
[quarteroni2000numerical]. -/
theorem panelCubicD1_left (hh : x i < x (i + 1)) :
    panelCubicD1 x f M (i + 1) (x i) = -((x (i + 1) - x i) * M i) / 3
      - (x (i + 1) - x i) * M (i + 1) / 6 + (f (i + 1) - f i) / (x (i + 1) - x i) := by
  have h0 : x (i + 1) - x i ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD1_apply x f M (by simpa using hh)]
  simp only [add_tsub_cancel_right]
  field_simp
  ring

/-- If $x_{i-1} < x_i$, the derivative of the panel cubic of $[x_{i-1}, x_i]$ at $x_i$ is
$$\frac{h_i M_{i-1}}{6} + \frac{h_i M_i}{3} + \frac{f_i - f_{i-1}}{h_i},$$
where $h_i = x_i - x_{i-1}$. This is the slope $s'(x_i^-)$ from the left at the node $x_i$, the
first displayed line before (8.47) in [quarteroni2000numerical].

The derivative is `deriv` of `Spline.panelCubic`. -/
theorem deriv_panelCubic_right (hh : x (i - 1) < x i) :
    deriv (panelCubic x f M i) (x i) = (x i - x (i - 1)) * M (i - 1) / 6
      + (x i - x (i - 1)) * M i / 3 + (f i - f (i - 1)) / (x i - x (i - 1)) := by
  rw [(hasDerivAt_panelCubic x f M i (x i)).deriv, panelCubicD1_right hh]

/-- If $x_i < x_{i+1}$, the derivative of the panel cubic of $[x_i, x_{i+1}]$ at $x_i$ is
$$-\frac{h_{i+1} M_i}{3} - \frac{h_{i+1} M_{i+1}}{6} + \frac{f_{i+1} - f_i}{h_{i+1}},$$
where $h_{i+1} = x_{i+1} - x_i$. This is the slope $s'(x_i^+)$ from the right at the node $x_i$,
the second displayed line before (8.47) in [quarteroni2000numerical].

The derivative is `deriv` of `Spline.panelCubic`. -/
theorem deriv_panelCubic_left (hh : x i < x (i + 1)) :
    deriv (panelCubic x f M (i + 1)) (x i) = -((x (i + 1) - x i) * M i) / 3
      - (x (i + 1) - x i) * M (i + 1) / 6 + (f (i + 1) - f i) / (x (i + 1) - x i) := by
  rw [(hasDerivAt_panelCubic x f M (i + 1) (x i)).deriv, panelCubicD1_left hh]

end PanelCubicValues

/-!
### The moment system

The moments $M_i = s''(x_i)$ of a piecewise cubic of class $C^2$ satisfy, at every interior node,
the row $\mu_i M_{i-1} + 2 M_i + \lambda_i M_{i+1} = d_i$ of (8.47) in [quarteroni2000numerical].
Here $\mu_i = h_i / (h_i + h_{i+1})$, $\lambda_i = h_{i+1} / (h_i + h_{i+1})$, and $d_i$ is $6$
times the second divided difference of the data. The two closure rows $2 M_0 + \lambda_0 M_1 = d_0$
and $\mu_n M_{n-1} + 2 M_n = d_n$ complete the tridiagonal system (8.48). The panel lengths are a
function $h : \mathbb{N} \to \mathbb{R}$, where $h_i$ is the length of the $i$-th panel
$[x_{i-1}, x_i]$.
-/

/-- The superdiagonal coefficient of the moment system: $\lambda_i = h_{i+1} / (h_i + h_{i+1})$ for
$i \ne 0$, and the closure parameter $\lambda_0$ for $i = 0$. -/
noncomputable def momentLam (h : ℕ → ℝ) (lam0 : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then lam0 else h (i + 1) / (h i + h (i + 1))

/-- The subdiagonal coefficient of the moment system: $\mu_i = h_i / (h_i + h_{i+1})$ for $i \ne n$,
and the closure parameter $\mu_n$ for $i = n$. -/
noncomputable def momentMu (n : ℕ) (h : ℕ → ℝ) (mun : ℝ) (i : ℕ) : ℝ :=
  if i = n then mun else h i / (h i + h (i + 1))

/-- The **M-continuity matrix** $A$ of order $n + 1$, with the rows and the columns indexed by
$0, \dots, n$: the tridiagonal matrix with $A_{ii} = 2$, $A_{i,i+1} = \lambda_i$ for $i < n$,
$A_{i,i-1} = \mu_i$ for $i > 0$, and all other entries $0$. The coefficients $\lambda_i$ and
$\mu_i$ are `Spline.momentLam` and `Spline.momentMu`, with the closure parameters $\lambda_0$
and $\mu_n$. This is the matrix of (8.48) in [quarteroni2000numerical]. -/
noncomputable def momentMatrix (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then 2
    else if (j : ℕ) = i + 1 then momentLam h lam0 i
    else if (i : ℕ) = j + 1 then momentMu n h mun i
    else 0

/-- The **right-hand side of the moment system**:
$$d_i = \frac{6}{h_i + h_{i+1}} \left( \frac{f_{i+1} - f_i}{h_{i+1}} - \frac{f_i - f_{i-1}}{h_i}
  \right)$$
for $0 < i < n$, and the closure values $d_0$ at $i = 0$ and $d_n$ at $i = n$. This is the
right-hand side of (8.47)–(8.48) in [quarteroni2000numerical]. For $n = 0$ the single entry is
$d_0$. -/
noncomputable def momentRhs (n : ℕ) (h : ℕ → ℝ) (f : ℕ → ℝ) (d0 dn : ℝ) : Fin (n + 1) → ℝ :=
  fun i =>
    if (i : ℕ) = 0 then d0 else if (i : ℕ) = n then dn
    else 6 / (h i + h (i + 1)) * ((f (i + 1) - f i) / h (i + 1) - (f i - f (i - 1)) / h i)

/-- A vector $v$ indexed by $\{0, \dots, n\}$, extended by $0$ to a sequence on $\mathbb{N}$: the
extension takes the value $v_i$ at $i \le n$ and $0$ at $i > n$. -/
noncomputable def extendFin {E : Type*} [Zero E] (v : Fin (n + 1) → E) : ℕ → E :=
  Function.extend Fin.val v 0

/-- The extension by zero of $v$ takes the value $v_i$ at each $i \le n$. -/
@[simp]
theorem extendFin_val {E : Type*} [Zero E] (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    extendFin v i = v i :=
  Fin.val_injective.extend_apply _ _ _

/-- For $i < n + 1$, the extension by zero of $v$ takes the value $v_i$. -/
theorem extendFin_of_lt {E : Type*} [Zero E] (v : Fin (n + 1) → E) {i : ℕ} (hi : i < n + 1) :
    extendFin v i = v ⟨i, hi⟩ :=
  extendFin_val v ⟨i, hi⟩

/-- For $i \ge n + 1$, the extension by zero of $v$ takes the value $0$. -/
theorem extendFin_of_le {E : Type*} [Zero E] (v : Fin (n + 1) → E) {i : ℕ} (hi : n + 1 ≤ i) :
    extendFin v i = 0 := by
  rw [extendFin, Function.extend_apply']
  · rfl
  · rintro ⟨j, rfl⟩
    exact absurd j.2 (not_lt.mpr hi)

/-- The entry $(i, j)$ of the moment matrix is the sum of three terms: $2$ if $j = i$, $\lambda_i$
if $j = i + 1$, and $\mu_i$ if $i = j + 1$, where each term is $0$ when its condition fails. -/
theorem momentMatrix_apply (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) (i j : Fin (n + 1)) :
    momentMatrix n h lam0 mun i j = (if j = i then 2 else 0)
      + (if (j : ℕ) = i + 1 then momentLam h lam0 i else 0)
      + (if (i : ℕ) = j + 1 then momentMu n h mun i else 0) := by
  simp only [momentMatrix, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | ring

/-- For $c \in \mathbb{R}$, a vector $v$ indexed by $\{0, \dots, n\}$ and $m \in \mathbb{N}$,
$\sum_{j=0}^{n} \delta_{jm}\, c\, v_j = c\, \tilde v_m$, where $\tilde v$ is the extension of
$v$ by zero (`Spline.extendFin`). -/
theorem sum_ite_val_eq_mul (c : ℝ) (v : Fin (n + 1) → ℝ) (m : ℕ) :
    ∑ j : Fin (n + 1), (if (j : ℕ) = m then c else 0) * v j = c * extendFin v m := by
  by_cases hm : m < n + 1
  · rw [Finset.sum_eq_single ⟨m, hm⟩ (fun j _ hj => by
      rw [ite_eq_right, zero_mul]; intro h; exact hj (Fin.ext h))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, extendFin_of_lt v hm]
  · rw [extendFin_of_le v (by omega), mul_zero]
    exact Finset.sum_eq_zero fun j _ => by
      rw [ite_eq_right, zero_mul]; intro h; exact hm (h ▸ j.2)

/-- **The moment matrix applied to a vector**: for $v$ indexed by $\{0, \dots, n\}$,
$$(A v)_i = 2 v_i + \lambda_i v_{i+1} + \mu_i v_{i-1},$$
where $v_{n+1}$ is read as $0$, and the last term is read as $0$ for $i = 0$. -/
theorem momentMatrix_mulVec_apply (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (momentMatrix n h lam0 mun).mulVec v i = 2 * v i + momentLam h lam0 i * extendFin v (i + 1)
      + momentMu n h mun i * (if (i : ℕ) = 0 then 0 else extendFin v (i - 1)) := by
  simp only [Matrix.mulVec, dotProduct, momentMatrix_apply, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_val_eq_mul, Finset.sum_eq_single i (fun j _ hj => by
      rw [ite_eq_right, zero_mul]; exact fun h => hj h)
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
  congr 1
  split_ifs with h0
  · rw [mul_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right, zero_mul]; omega
  · rw [← sum_ite_val_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ((i : ℕ) = j + 1) ↔ ((j : ℕ) = i - 1) := by omega
    simp only [this]

/-- The moment matrix is tridiagonal (`Matrix.IsTridiagonal`). -/
theorem isTridiagonal_momentMatrix (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) :
    (momentMatrix n h lam0 mun).IsTridiagonal := by
  intro i j hij
  simp only [momentMatrix, Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

section Dominance

open scoped Matrix.Norms.Operator

variable {h : ℕ → ℝ} {lam0 mun : ℝ}

/-- In row $i$ of the moment matrix, the sum of the absolute values of the off-diagonal entries is
at most $|\lambda_i| + |\mu_i|$, where the term $|\lambda_i|$ is present only for $i < n$ and
the term $|\mu_i|$ only for $i > 0$. -/
theorem sum_norm_momentMatrix_le (i : Fin (n + 1)) :
    ∑ j ∈ Finset.univ.erase i, ‖momentMatrix n h lam0 mun i j‖ ≤
      (if (i : ℕ) < n then |momentLam h lam0 i| else 0)
        + (if 0 < (i : ℕ) then |momentMu n h mun i| else 0) := by
  have hrow : ∀ j ∈ Finset.univ.erase i, ‖momentMatrix n h lam0 mun i j‖ =
      (if (j : ℕ) = i + 1 then |momentLam h lam0 i| else 0)
        + (if (i : ℕ) = j + 1 then |momentMu n h mun i| else 0) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [momentMatrix_apply, ite_eq_right hji, zero_add, Real.norm_eq_abs]
    split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  gcongr
  · split_ifs with hi
    · rw [Finset.sum_eq_single_of_mem (⟨i + 1, by omega⟩ : Fin (n + 1))
        (Finset.mem_erase.mpr ⟨fun h => by simp [Fin.ext_iff] at h, Finset.mem_univ _⟩)
        (fun j _ hj => by rw [ite_eq_right]; intro h; exact hj (Fin.ext h))]
      simp
    · exact le_of_eq (Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; intro h; omega)
  · split_ifs with hi
    · rw [Finset.sum_eq_single_of_mem (⟨i - 1, by omega⟩ : Fin (n + 1))
        (Finset.mem_erase.mpr ⟨fun h => by simp [Fin.ext_iff] at h; omega, Finset.mem_univ _⟩)
        (fun j _ hj => by rw [ite_eq_right]; intro h; exact hj (Fin.ext (by simp; omega)))]
      rw [ite_eq_left (by simp; omega)]
    · exact le_of_eq (Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; intro h; omega)

/-- Let $h_i > 0$ for $1 \le i \le n$, and let $0 < i < n$. Then $\lambda_i \ge 0$, $\mu_i \ge 0$
and $\lambda_i + \mu_i = 1$. -/
theorem momentLam_add_momentMu (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i) {i : ℕ} (hi0 : i ≠ 0)
    (hin : i ≠ n) (hi : i ≤ n) :
    0 ≤ momentLam h lam0 i ∧ 0 ≤ momentMu n h mun i ∧
      momentLam h lam0 i + momentMu n h mun i = 1 := by
  have h1 : 0 < h i := hh i (by omega) hi
  have h2 : 0 < h (i + 1) := hh (i + 1) (by omega) (by omega)
  simp only [momentLam, momentMu, hi0, hin, ↓reduceIte]
  refine ⟨div_nonneg h2.le (by positivity), div_nonneg h1.le (by positivity), ?_⟩
  field_simp
  ring

/-- Let $h_i > 0$ for $1 \le i \le n$, and let the closure parameters satisfy $|\lambda_0| < 2$ and
$|\mu_n| < 2$. Then the moment matrix is strictly diagonally dominant by rows.

Each interior row has the off-diagonal sum $\mu_i + \lambda_i = 1 < 2$, and the two end rows
have the off-diagonal sums $|\lambda_0|$ and $|\mu_n|$. -/
theorem isStrictDiagDominant_momentMatrix_of_abs_lt (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl : |lam0| < 2) (hm : |mun| < 2) : (momentMatrix n h lam0 mun).IsStrictDiagDominant := by
  intro i
  refine (sum_norm_momentMatrix_le i).trans_lt ?_
  have hii : ‖momentMatrix n h lam0 mun i i‖ = 2 := by simp [momentMatrix]
  rw [hii]
  by_cases hi0 : (i : ℕ) = 0
  · have hl0 : momentLam h lam0 i = lam0 := by simp [momentLam, hi0]
    rw [hl0, ite_eq_right (show ¬ 0 < (i : ℕ) by omega), add_zero]
    split_ifs
    · exact hl
    · norm_num
  · by_cases hin : (i : ℕ) = n
    · have : momentMu n h mun i = mun := by simp [momentMu, hin]
      rw [this, ite_eq_right (show ¬ (i : ℕ) < n by omega),
        ite_eq_left (show 0 < (i : ℕ) by omega), zero_add]
      exact hm
    · obtain ⟨h1, h2, h3⟩ := momentLam_add_momentMu (lam0 := lam0) (mun := mun) hh hi0 hin
        (Nat.lt_succ_iff.mp i.2)
      rw [ite_eq_left (show (i : ℕ) < n by omega), ite_eq_left (show 0 < (i : ℕ) by omega),
        abs_of_nonneg h1, abs_of_nonneg h2, h3]
      norm_num

/-- Let $h_i > 0$ for $1 \le i \le n$, and let $0 \le \lambda_0 \le 1$ and $0 \le \mu_n \le 1$. Then
the moment matrix is strictly diagonally dominant by rows. This is the remark after (8.48) in
§8.6.1 of [quarteroni2000numerical]. -/
theorem isStrictDiagDominant_momentMatrix (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) :
    (momentMatrix n h lam0 mun).IsStrictDiagDominant :=
  isStrictDiagDominant_momentMatrix_of_abs_lt hh (by rw [abs_of_nonneg hl0]; linarith)
    (by rw [abs_of_nonneg hm0]; linarith)

/-- Let $h_i > 0$ for $1 \le i \le n$, and let $0 \le \lambda_0 \le 1$ and $0 \le \mu_n \le 1$. Then
the moment matrix is invertible. This is stated in §8.6.1 of [quarteroni2000numerical].

The proof is strict diagonal dominance and `Matrix.IsStrictDiagDominant.isUnit`. -/
theorem isUnit_momentMatrix (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) :
    IsUnit (momentMatrix n h lam0 mun) :=
  (isStrictDiagDominant_momentMatrix hh hl0 hl1 hm0 hm1).isUnit

/-- **The moment matrix does not shrink the sup norm.** Let $h_i > 0$ for $1 \le i \le n$, and let
$0 \le \lambda_0 \le 1$ and $0 \le \mu_n \le 1$. Then for every vector $v$ indexed by
$\{0, \dots, n\}$,
$$\|v\|_\infty \le \|A v\|_\infty,$$
where $A$ is the moment matrix. Equivalently, $\|A^{-1}\|_\infty \le 1$.

At an index $i$ where $|v_i|$ is maximal, $|(A v)_i| \ge 2 |v_i| - (\lambda_i + \mu_i) |v_i| \ge
|v_i|$. The norm on `Fin (n + 1) → ℝ` is the sup norm.
-/
theorem norm_le_norm_momentMatrix_mulVec (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) (v : Fin (n + 1) → ℝ) :
    ‖v‖ ≤ ‖(momentMatrix n h lam0 mun).mulVec v‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) Finset.univ_nonempty
  have hnorm : ‖v‖ = |v i| := by
    refine le_antisymm (pi_norm_le_iff_of_nonneg (abs_nonneg _) |>.mpr fun j => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hi j (Finset.mem_univ _)
    · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
  have hext : ∀ m, |extendFin v m| ≤ |v i| := by
    intro m
    rcases lt_or_ge m (n + 1) with hm | hm
    · rw [extendFin_of_lt v hm]; exact hi _ (Finset.mem_univ _)
    · rw [extendFin_of_le v hm, abs_zero]; exact abs_nonneg _
  rw [hnorm]
  refine le_trans ?_ (norm_le_pi_norm _ i)
  rw [Real.norm_eq_abs, momentMatrix_mulVec_apply]
  set R := momentLam h lam0 i * extendFin v (i + 1)
    + momentMu n h mun i * (if (i : ℕ) = 0 then 0 else extendFin v (i - 1)) with hR
  -- the off-diagonal contribution is at most `|v i|`
  have hRle : |R| ≤ |v i| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    by_cases hi0 : (i : ℕ) = 0
    · have hl : momentLam h lam0 i = lam0 := by simp [momentLam, hi0]
      rw [hl, ite_eq_left hi0, abs_zero, mul_zero, add_zero, abs_of_nonneg hl0]
      calc lam0 * |extendFin v (i + 1)| ≤ 1 * |v i| :=
            mul_le_mul hl1 (hext _) (abs_nonneg _) zero_le_one
        _ = |v i| := one_mul _
    · by_cases hin : (i : ℕ) = n
      · have : momentMu n h mun i = mun := by simp [momentMu, hin]
        rw [this, extendFin_of_le v (by omega), abs_zero, mul_zero, zero_add, ite_eq_right hi0,
          abs_of_nonneg hm0]
        calc mun * |extendFin v (i - 1)| ≤ 1 * |v i| :=
              mul_le_mul hm1 (hext _) (abs_nonneg _) zero_le_one
          _ = |v i| := one_mul _
      · obtain ⟨h1, h2, h3⟩ := momentLam_add_momentMu (lam0 := lam0) (mun := mun) hh hi0 hin
          (Nat.lt_succ_iff.mp i.2)
        rw [ite_eq_right hi0, abs_of_nonneg h1, abs_of_nonneg h2]
        calc _ ≤ momentLam h lam0 i * |v i| + momentMu n h mun i * |v i| :=
              add_le_add (mul_le_mul_of_nonneg_left (hext _) h1)
                (mul_le_mul_of_nonneg_left (hext _) h2)
          _ = |v i| := by rw [← add_mul, h3, one_mul]
  have h2 : |2 * v i| = 2 * |v i| := by rw [abs_mul, abs_two]
  have := abs_sub_abs_le_abs_sub (2 * v i) (-R)
  rw [abs_neg, sub_neg_eq_add, h2, hR, ← add_assoc] at this
  linarith

/-- Let $h_i > 0$ for $1 \le i \le n$, and let $0 \le \lambda_0 \le 1$ and $0 \le \mu_n \le 1$. Then
the inverse of the moment matrix $A$ has operator norm at most $1$ for the sup norm:
$$\|A^{-1}\|_\infty \le 1.$$
The error bounds for the clamped spline rest on this bound.

The norm is the $L^\infty$ operator norm `Matrix.linftyOpNormedAddCommGroup`, a scoped instance
in `Matrix.Norms.Operator`. The proof uses `Spline.norm_le_norm_momentMatrix_mulVec`. -/
theorem linfty_opNorm_inv_momentMatrix_le (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) :
    ‖(momentMatrix n h lam0 mun)⁻¹‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul]
  have hA := isUnit_momentMatrix hh hl0 hl1 hm0 hm1
  have hw : (momentMatrix n h lam0 mun).mulVec ((momentMatrix n h lam0 mun)⁻¹.mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      Matrix.one_mulVec]
  change ‖(momentMatrix n h lam0 mun)⁻¹.mulVec w‖ ≤ ‖w‖
  calc ‖(momentMatrix n h lam0 mun)⁻¹.mulVec w‖
      ≤ ‖(momentMatrix n h lam0 mun).mulVec ((momentMatrix n h lam0 mun)⁻¹.mulVec w)‖ :=
        norm_le_norm_momentMatrix_mulVec hh hl0 hl1 hm0 hm1 _
    _ = ‖w‖ := by rw [hw]

end Dominance

/-! ### The glued cubic spline -/

/-- The length $h_i = x_i - x_{i-1}$ of the $i$-th panel. -/
def panelLength (x : ℕ → ℝ) (i : ℕ) : ℝ := x i - x (i - 1)

/-- For a partition $a = x_0 < \dots < x_n = b$ and $1 \le i \le n$, the panel length $h_i$ is
positive. -/
theorem _root_.IsIntervalPartition.panelLength_pos (hx : IsIntervalPartition a b n x) {i : ℕ}
    (hi1 : 1 ≤ i) (hin : i ≤ n) : 0 < panelLength x i :=
  sub_pos.mpr (hx.lt (by omega) hin)

/-- The **interior moment equation** at the node $x_i$:
$$\mu_i M_{i-1} + 2 M_i + \lambda_i M_{i+1} = d_i,$$
with $\mu_i = h_i / (h_i + h_{i+1})$, $\lambda_i = h_{i+1} / (h_i + h_{i+1})$ and
$$d_i = \frac{6}{h_i + h_{i+1}} \left( \frac{f_{i+1} - f_i}{h_{i+1}} - \frac{f_i - f_{i-1}}{h_i}
  \right),$$
where $h_i$ is the panel length `Spline.panelLength x i`. This is (8.47) of
[quarteroni2000numerical]. -/
def IsMomentEq (x f M : ℕ → ℝ) (i : ℕ) : Prop :=
  panelLength x i / (panelLength x i + panelLength x (i + 1)) * M (i - 1) + 2 * M i
    + panelLength x (i + 1) / (panelLength x i + panelLength x (i + 1)) * M (i + 1)
    = 6 / (panelLength x i + panelLength x (i + 1))
      * ((f (i + 1) - f i) / panelLength x (i + 1) - (f i - f (i - 1)) / panelLength x i)

/-- Let $x_{i-1} < x_i < x_{i+1}$. The interior moment equation at $x_i$ holds if and only if the
panel cubics of $[x_{i-1}, x_i]$ and of $[x_i, x_{i+1}]$ have the same slope at $x_i$. -/
theorem isMomentEq_iff {f M : ℕ → ℝ} {i : ℕ} (h1 : x (i - 1) < x i) (h2 : x i < x (i + 1)) :
    IsMomentEq x f M i ↔ panelCubicD1 x f M i (x i) = panelCubicD1 x f M (i + 1) (x i) := by
  rw [panelCubicD1_right h1, panelCubicD1_left h2, IsMomentEq, panelLength, panelLength,
    add_tsub_cancel_right]
  have ha : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr h1.ne'
  have hb : x (i + 1) - x i ≠ 0 := sub_ne_zero.mpr h2.ne'
  have hab : x i - x (i - 1) + (x (i + 1) - x i) ≠ 0 := by
    linarith
  have hc : 6 / (x i - x (i - 1) + (x (i + 1) - x i)) ≠ 0 := div_ne_zero (by norm_num) hab
  have key : (x i - x (i - 1)) / (x i - x (i - 1) + (x (i + 1) - x i)) * M (i - 1) + 2 * M i
      + (x (i + 1) - x i) / (x i - x (i - 1) + (x (i + 1) - x i)) * M (i + 1)
      - 6 / (x i - x (i - 1) + (x (i + 1) - x i))
        * ((f (i + 1) - f i) / (x (i + 1) - x i) - (f i - f (i - 1)) / (x i - x (i - 1)))
      = 6 / (x i - x (i - 1) + (x (i + 1) - x i)) * (((x i - x (i - 1)) * M (i - 1) / 6
        + (x i - x (i - 1)) * M i / 3 + (f i - f (i - 1)) / (x i - x (i - 1)))
        - (-((x (i + 1) - x i) * M i) / 3 - (x (i + 1) - x i) * M (i + 1) / 6
          + (f (i + 1) - f i) / (x (i + 1) - x i))) := by
    field_simp
    ring
  rw [← sub_eq_zero, key, mul_eq_zero, or_iff_right hc, sub_eq_zero]

/-- The **glued cubic spline** of the data $f$ and the moments $M$: the function equal to the panel
cubic `Spline.panelCubic x f M i` on the panel $[x_{i-1}, x_i]$, continued by the first panel
cubic to the left of $x_0$ and by the last panel cubic to the right of $x_n$. -/
noncomputable def cubicSplineFun (n : ℕ) (x f M : ℕ → ℝ) : ℝ → ℝ :=
  panelGlue n x (panelCubic x f M)

section CubicSplineFun

variable (hx : IsIntervalPartition a b n x) {f M : ℕ → ℝ}
include hx

/-- For a partition and $1 \le i < n$, the panel cubics of $[x_{i-1}, x_i]$ and of $[x_i, x_{i+1}]$
take the same value at $x_i$. -/
theorem panelCubic_apply_node_succ {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    panelCubic x f M i (x i) = panelCubic x f M (i + 1) (x i) := by
  rw [panelCubic_right (hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le),
    panelCubic_left_succ (hx.step i hin)]

/-- For a partition and $1 \le i < n$, the second derivatives of the panel cubics of
$[x_{i-1}, x_i]$ and of $[x_i, x_{i+1}]$ take the same value at $x_i$. -/
theorem panelCubicD2_apply_node_succ {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    panelCubicD2 x f M i (x i) = panelCubicD2 x f M (i + 1) (x i) := by
  rw [panelCubicD2_right (hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le),
    panelCubicD2_left_succ (hx.step i hin)]

/-- For a partition and $1 \le i \le n$, the glued cubic spline equals the $i$-th panel cubic on the
$i$-th extended panel. -/
theorem cubicSplineFun_eq_of_mem {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : t ∈ extPanel n x i) : cubicSplineFun n x f M t = panelCubic x f M i t :=
  panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubic_apply_node_succ hx hi1 hin) hi1 hin ht

/-- For a partition and $1 \le i \le n$, the glued cubic spline equals the $i$-th panel cubic on the
panel $[x_{i-1}, x_i]$. -/
theorem cubicSplineFun_eqOn {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    EqOn (cubicSplineFun n x f M) (panelCubic x f M i) (Icc (x (i - 1)) (x i)) :=
  fun _ ht => cubicSplineFun_eq_of_mem hx hi1 hin (Icc_subset_extPanel i ht)

/-- **The glued cubic spline interpolates the data.** For a partition with $n \ge 1$, the glued
cubic spline $s$ satisfies $s(x_i) = f_i$ for $0 \le i \le n$. -/
theorem cubicSplineFun_apply_node (hn : 1 ≤ n) {i : ℕ} (hi : i ≤ n) :
    cubicSplineFun n x f M (x i) = f i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [cubicSplineFun_eq_of_mem hx le_rfl hn ⟨fun h => absurd h (lt_irrefl _),
      fun _ => (hx.step 0 hn).le⟩]
    exact panelCubic_left_succ (hx.step 0 hn)
  · rw [cubicSplineFun_eq_of_mem hx hi0 hi
      (Icc_subset_extPanel i ⟨(hx.mono (by omega) hi), le_rfl⟩)]
    exact panelCubic_right (hx.lt (by omega) hi)

variable (hn : 1 ≤ n) (hM : ∀ i, 1 ≤ i → i < n → IsMomentEq x f M i)
include hM

/-- For a partition, if the interior moment equations hold at $x_1, \dots, x_{n-1}$, then for
$1 \le i < n$ the panel cubics of $[x_{i-1}, x_i]$ and of $[x_i, x_{i+1}]$ have the same slope
at $x_i$. -/
theorem panelCubicD1_apply_node_succ {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    panelCubicD1 x f M i (x i) = panelCubicD1 x f M (i + 1) (x i) :=
  (isMomentEq_iff (hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le) (hx.step i hin)).mp
    (hM i hi1 hin)

include hn

/-- **The glued cubic spline is differentiable.** For a partition with $n \ge 1$, if the interior
moment equations hold at $x_1, \dots, x_{n-1}$, then at every $t \in \mathbb{R}$ the glued cubic
spline has the derivative given by the glued function of the first derivatives of the panel
cubics. -/
theorem hasDerivAt_cubicSplineFun (t : ℝ) :
    HasDerivAt (cubicSplineFun n x f M) (panelGlue n x (panelCubicD1 x f M) t) t :=
  hasDerivAt_panelGlue hx hn (fun _ hi1 hin => panelCubic_apply_node_succ hx hi1 hin)
    (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin)
    (fun i _ _ t _ => hasDerivAt_panelCubic x f M i t) t

/-- For a partition with $n \ge 1$, if the interior moment equations hold at $x_1, \dots, x_{n-1}$,
then at every $t \in \mathbb{R}$ the glued function of the first derivatives of the panel cubics
has the derivative given by the glued function of the second derivatives. -/
theorem hasDerivAt_cubicSplineFun_deriv (t : ℝ) :
    HasDerivAt (panelGlue n x (panelCubicD1 x f M)) (panelGlue n x (panelCubicD2 x f M) t) t :=
  hasDerivAt_panelGlue hx hn (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin)
    (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin)
    (fun i _ _ t _ => hasDerivAt_panelCubicD1 x f M i t) t

omit hM in
/-- For a partition with $n \ge 1$, the glued function of the second derivatives of the panel cubics
is continuous on $\mathbb{R}$. No moment equation is needed. -/
theorem continuous_cubicSplineFun_deriv2 :
    Continuous (panelGlue n x (panelCubicD2 x f M)) :=
  continuous_panelGlue hx hn (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin)
    fun i _ _ => continuousOn_of_forall_continuousAt fun t _ =>
      (hasDerivAt_panelCubicD2 x f M i t).continuousAt

/-- **The M-continuity system is sufficient.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$, and let the data $f$ and the moments $M$ satisfy the interior moment equations at
$x_1, \dots, x_{n-1}$. Then the glued cubic spline is of class $C^2$ on all of $\mathbb{R}$.
This is stated in §8.6.1 of [quarteroni2000numerical]. -/
theorem contDiff_cubicSplineFun : ContDiff ℝ 2 (cubicSplineFun n x f M) :=
  contDiff_two_of_hasDerivAt (hasDerivAt_cubicSplineFun hx hn hM)
    (hasDerivAt_cubicSplineFun_deriv hx hn hM) (continuous_cubicSplineFun_deriv2 hx hn)

/-- **The M-continuity system is sufficient.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$, and let the data $f$ and the moments $M$ satisfy the interior moment equations at
$x_1, \dots, x_{n-1}$. Then the glued cubic spline is of class $C^2$ on $[a, b]$. -/
theorem contDiffOn_cubicSplineFun : ContDiffOn ℝ 2 (cubicSplineFun n x f M) (Icc a b) :=
  (contDiff_cubicSplineFun hx hn hM).contDiffOn

/-- For a partition with $n \ge 1$ and moments that satisfy the interior moment equations, the
derivative of the glued cubic spline is the glued function of the first derivatives of the panel
cubics. -/
theorem deriv_cubicSplineFun :
    deriv (cubicSplineFun n x f M) = panelGlue n x (panelCubicD1 x f M) :=
  funext fun t => (hasDerivAt_cubicSplineFun hx hn hM t).deriv

/-- For a partition with $n \ge 1$ and moments that satisfy the interior moment equations, the
second derivative of the glued cubic spline is the glued function of the second derivatives of
the panel cubics. -/
theorem iteratedDeriv_two_cubicSplineFun :
    iteratedDeriv 2 (cubicSplineFun n x f M) = panelGlue n x (panelCubicD2 x f M) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cubicSplineFun hx hn hM]
  exact funext fun t => (hasDerivAt_cubicSplineFun_deriv hx hn hM t).deriv

/-- **The moments of the glued cubic spline are the $M_i$.** For a partition with $n \ge 1$ and
moments that satisfy the interior moment equations, the glued cubic spline $s$ has
$s''(x_i) = M_i$ for $0 \le i \le n$. -/
theorem iteratedDeriv_two_cubicSplineFun_node {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv 2 (cubicSplineFun n x f M) (x i) = M i := by
  rw [iteratedDeriv_two_cubicSplineFun hx hn hM]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin) le_rfl hn
      ⟨fun h => absurd h (lt_irrefl _), fun _ => (hx.step 0 hn).le⟩]
    exact panelCubicD2_left_succ (hx.step 0 hn)
  · rw [panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin) hi0 hi
      (Icc_subset_extPanel i ⟨(hx.mono (by omega) hi), le_rfl⟩)]
    exact panelCubicD2_right (hx.lt (by omega) hi)

/-- For a partition with $n \ge 1$ and moments that satisfy the interior moment equations, the glued
cubic spline $s$ has the slope
$$s'(a) = -\frac{h_1 M_0}{3} - \frac{h_1 M_1}{6} + \frac{f_1 - f_0}{h_1}$$
at the left endpoint, where $h_1 = x_1 - x_0$. -/
theorem deriv_cubicSplineFun_left :
    deriv (cubicSplineFun n x f M) a = -((x 1 - x 0) * M 0) / 3 - (x 1 - x 0) * M 1 / 6
      + (f 1 - f 0) / (x 1 - x 0) := by
  rw [deriv_cubicSplineFun hx hn hM, ← hx.first,
    panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin) le_rfl hn
      ⟨fun h => absurd h (lt_irrefl _), fun _ => (hx.step 0 hn).le⟩]
  exact panelCubicD1_left (i := 0) (hx.step 0 hn)

/-- For a partition with $n \ge 1$ and moments that satisfy the interior moment equations, the glued
cubic spline $s$ has the slope
$$s'(b) = \frac{h_n M_{n-1}}{6} + \frac{h_n M_n}{3} + \frac{f_n - f_{n-1}}{h_n}$$
at the right endpoint, where $h_n = x_n - x_{n-1}$. -/
theorem deriv_cubicSplineFun_right :
    deriv (cubicSplineFun n x f M) b = (x n - x (n - 1)) * M (n - 1) / 6
      + (x n - x (n - 1)) * M n / 3 + (f n - f (n - 1)) / (x n - x (n - 1)) := by
  rw [deriv_cubicSplineFun hx hn hM, ← hx.last,
    panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin) hn le_rfl
      ⟨fun _ => hx.mono (Nat.sub_le n 1) le_rfl, fun h => absurd h (lt_irrefl _)⟩]
  exact panelCubicD1_right (hx.lt (by omega) le_rfl)

/-- **The glued cubic spline is a cubic spline.** For a partition with $n \ge 1$ and moments that
satisfy the interior moment equations, the restriction of the glued cubic spline to $[a, b]$
lies in the spline space $S_3^2$, `Spline.splineSpace a b n x 3 2`. -/
theorem cubicSplineFun_mem_splineSpace :
    (ContinuousMap.mk _ (contDiff_cubicSplineFun hx hn hM).continuous).restrict (Icc a b) ∈
      splineSpace a b n x 3 2 := by
  refine ⟨cubicSplineFun n x f M, contDiffOn_cubicSplineFun hx hn hM, fun t => rfl,
    fun j hj => ⟨panelCubicPoly x f M (j + 1), degree_panelCubicPoly_le _ _ _ _, fun t ht => ?_⟩⟩
  exact cubicSplineFun_eq_of_mem hx (i := j + 1) (by omega) hj
    (Icc_subset_extPanel (j + 1) (by simpa using ht))

end CubicSplineFun

/-- Let $u < v$ and $t \in [u, v]$. If $g$ has the derivatives $d$ and $d'$ within $[u, v]$ at $t$,
then $d = d'$. -/
theorem eq_of_hasDerivWithinAt_Icc {u v t d d' : ℝ} {g : ℝ → ℝ} (huv : u < v) (ht : t ∈ Icc u v)
    (h : HasDerivWithinAt g d (Icc u v) t) (h' : HasDerivWithinAt g d' (Icc u v) t) : d = d' :=
  (uniqueDiffOn_Icc huv t ht).eq_deriv _ h h'

/-- **The M-continuity system is necessary.** Let $a = x_0 < \dots < x_n = b$ be a partition, and
let $s$ be of class $C^2$ on $[a, b]$ with $s$ equal to the panel cubic
`Spline.panelCubic x f M i` on $[x_{i-1}, x_i]$ for each $1 \le i \le n$. Then the interior
moment equation (8.47) of [quarteroni2000numerical] holds at every $x_i$, $1 \le i < n$.

The two one-sided slopes of $s$ at an interior node agree, and `Spline.isMomentEq_iff` turns
this into the moment equation. -/
theorem moment_eq_of_contDiffOn (hx : IsIntervalPartition a b n x) {s : ℝ → ℝ}
    (hs : ContDiffOn ℝ 2 s (Icc a b)) {f M : ℕ → ℝ}
    (hpanel : ∀ i, 1 ≤ i → i ≤ n → EqOn s (panelCubic x f M i) (Icc (x (i - 1)) (x i)))
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) : IsMomentEq x f M i := by
  have h1 : x (i - 1) < x i := hx.lt (by omega) hin.le
  have h2 : x i < x (i + 1) := hx.step i hin
  have hmem : Icc a b ∈ 𝓝 (x i) :=
    Icc_mem_nhds (hx.first ▸ hx.lt (by omega) hin.le) (hx.last ▸ hx.lt hin le_rfl)
  have hd : HasDerivAt s (deriv s (x i)) (x i) :=
    (((hs.differentiableOn (by norm_num)) (x i) (mem_of_mem_nhds hmem)).differentiableAt
      hmem).hasDerivAt
  rw [isMomentEq_iff h1 h2]
  have hl : deriv s (x i) = panelCubicD1 x f M i (x i) :=
    eq_of_hasDerivWithinAt_Icc h1 ⟨h1.le, le_rfl⟩
      (hd.hasDerivWithinAt.congr (fun y hy => (hpanel i hi1 hin.le hy).symm)
        (hpanel i hi1 hin.le ⟨h1.le, le_rfl⟩).symm)
      (hasDerivAt_panelCubic x f M i (x i)).hasDerivWithinAt
  have hr : deriv s (x i) = panelCubicD1 x f M (i + 1) (x i) :=
    eq_of_hasDerivWithinAt_Icc (by simpa using h2) (by simp [h2.le])
      (hd.hasDerivWithinAt.congr (fun y hy => (hpanel (i + 1) (by omega) hin hy).symm)
        (hpanel (i + 1) (by omega) hin (by simp [h2.le])).symm)
      (hasDerivAt_panelCubic x f M (i + 1) (x i)).hasDerivWithinAt
  rw [← hl, ← hr]

/-! ### Cubic splines and their moments -/

/-- A **cubic spline** on $[a, b]$ for the nodes $x_0, \dots, x_n$: a function
$s : \mathbb{R} \to \mathbb{R}$ of class $C^2$ on $[a, b]$ such that, for each $1 \le i \le n$,
$s$ agrees on $[x_{i-1}, x_i]$ with a polynomial of degree at most $3$. This is Definition 8.1
of [quarteroni2000numerical] with $k = 3$. -/
structure IsCubicSpline (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (s : ℝ → ℝ) : Prop where
  /-- The function $s$ is of class $C^2$ on $[a, b]$. -/
  contDiffOn : ContDiffOn ℝ 2 s (Icc a b)
  /-- For each $1 \le i \le n$, the function $s$ agrees on $[x_{i-1}, x_i]$ with a polynomial of
  degree at most $3$. -/
  piecewise : ∀ i, 1 ≤ i → i ≤ n → ∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x (i - 1)) (x i))

/-- An **interpolatory cubic spline** of the data $f_0, \dots, f_n$: a cubic spline $s$ on $[a, b]$
with $s(x_i) = f_i$ for $0 \le i \le n$. This is the interpolating cubic spline of §8.6.1 of
[quarteroni2000numerical]. -/
structure IsCubicInterp (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (f : ℕ → ℝ) (s : ℝ → ℝ) : Prop
    extends IsCubicSpline a b n x s where
  /-- The spline interpolates the data: $s(x_i) = f_i$ for $0 \le i \le n$. -/
  interp : ∀ i ≤ n, s (x i) = f i

/-- The **moments** $M_i = s''(x_i)$ of a function $s$, where $s''$ is the second derivative of $s$
within $[a, b]$, `iteratedDerivWithin 2 s (Set.Icc a b)`. This is the notation $M_i = s''(x_i)$
of §8.6.1 of [quarteroni2000numerical]. -/
noncomputable def moment (a b : ℝ) (x : ℕ → ℝ) (s : ℝ → ℝ) (i : ℕ) : ℝ :=
  iteratedDerivWithin 2 s (Icc a b) (x i)

/-- Let $a < b$ and let $s$ be of class $C^2$ on $\mathbb{R}$. If $x_i \in [a, b]$, then the moment
$M_i$ is the ordinary second derivative $s''(x_i)$. -/
theorem moment_eq_iteratedDeriv (hab : a < b) {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s) {i : ℕ}
    (hi : x i ∈ Icc a b) : moment a b x s i = iteratedDeriv 2 s (x i) :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hs.contDiffAt hi

/-- **A derivative within $[a, b]$ is read off a local description.** Let $s$ be differentiable
within $[a, b]$ at $t$, let $u < v$ with $t \in [u, v] \subseteq [a, b]$, and let $s = g$ on
$[u, v]$, where $g$ has the derivative $d$ at $t$. Then the derivative of $s$ within $[a, b]$ at
$t$ is $d$. -/
theorem derivWithin_eq_of_eqOn_Icc {s g : ℝ → ℝ} {u v t d : ℝ}
    (hs : DifferentiableWithinAt ℝ s (Icc a b) t) (huv : u < v) (hsub : Icc u v ⊆ Icc a b)
    (ht : t ∈ Icc u v) (heq : EqOn s g (Icc u v)) (hg : HasDerivAt g d t) :
    derivWithin s (Icc a b) t = d :=
  eq_of_hasDerivWithinAt_Icc huv ht
    ((hs.hasDerivWithinAt.mono hsub).congr (fun _ hy => (heq hy).symm) (heq ht).symm)
    hg.hasDerivWithinAt

/-- Let $s$ be of class $C^2$ on $[a, b]$, let $u < v$ with $[u, v] \subseteq [a, b]$, and let $s$
agree with a polynomial $p$ on $[u, v]$. Then at every $t \in [u, v]$ the first and the second
derivatives of $s$ within $[a, b]$ are $p'(t)$ and $p''(t)$. -/
theorem derivWithin_eq_of_eqOn_Icc_of_contDiffOn {s : ℝ → ℝ} (hs : ContDiffOn ℝ 2 s (Icc a b))
    {u v : ℝ} (huv : u < v) (hsub : Icc u v ⊆ Icc a b) {p : ℝ[X]} (heq : EqOn s p.eval (Icc u v))
    {t : ℝ} (ht : t ∈ Icc u v) :
    derivWithin s (Icc a b) t = (derivative p).eval t ∧
      iteratedDerivWithin 2 s (Icc a b) t = (derivative (derivative p)).eval t := by
  have hab : a < b := by
    have := (hsub ⟨le_rfl, huv.le⟩).1; have := (hsub ⟨huv.le, le_rfl⟩).2; linarith
  have hd1 : ∀ t ∈ Icc u v, derivWithin s (Icc a b) t = (derivative p).eval t := fun t ht =>
    derivWithin_eq_of_eqOn_Icc ((hs.differentiableOn (by norm_num)) t (hsub ht)) huv hsub ht heq
      (p.hasDerivAt t)
  refine ⟨hd1 t ht, ?_⟩
  have hs1 : ContDiffOn ℝ 1 (derivWithin s (Icc a b)) (Icc a b) := by
    have := hs
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)] at this
    exact this.2.2
  rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]
  exact derivWithin_eq_of_eqOn_Icc ((hs1.differentiableOn (by norm_num)) t (hsub ht)) huv hsub ht
    (fun _ hy => hd1 _ hy) ((derivative p).hasDerivAt t)

/-- **A cubic is determined by its values and second derivatives at two distinct points.** If $p$
and $q$ are polynomials of degree at most $3$, $u \ne v$, and $p$ and $q$ have the same values
and the same second derivatives at $u$ and at $v$, then $p = q$. -/
theorem eq_of_degree_le_three {p q : ℝ[X]} (hp : p.degree ≤ 3) (hq : q.degree ≤ 3) {u v : ℝ}
    (huv : u ≠ v) (h0 : p.eval u = q.eval u) (h1 : p.eval v = q.eval v)
    (h2 : (derivative (derivative p)).eval u = (derivative (derivative q)).eval u)
    (h3 : (derivative (derivative p)).eval v = (derivative (derivative q)).eval v) : p = q := by
  classical
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hrdeg : r.natDegree ≤ 3 :=
    natDegree_le_of_degree_le ((degree_sub_le _ _).trans (max_le hp hq))
  have hcard : ({u, v} : Finset ℝ).card = 2 := Finset.card_pair huv
  -- the second derivative of `r` is affine with two zeros, hence zero
  have hr2 : derivative (derivative r) = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ {u, v} ?_ ?_
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · simp [hr, derivative_sub, eval_sub, h2]
      · simp [hr, derivative_sub, eval_sub, h3]
    · rw [hcard]
      have := natDegree_derivative_le (derivative r)
      have := natDegree_derivative_le r
      omega
  -- hence `r` is affine with two zeros, hence zero
  have hr1 : r.natDegree ≤ 1 := by
    have := derivative_eq_zero.mp hr2
    rw [natDegree_derivative] at this
    omega
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ {u, v} ?_ (by rw [hcard]; omega)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · simp [hr, eval_sub, h0]
  · simp [hr, eval_sub, h1]

/-- The panel cubic of $[x_{i-1}, x_i]$ depends only on the data and the moments at $i - 1$ and $i$:
if $f$ and $g$ agree at $i - 1$ and $i$, and $M$ and $N$ agree at $i - 1$ and $i$, then the
panel cubics of $(f, M)$ and of $(g, N)$ are equal. -/
theorem panelCubicPoly_congr {f g M N : ℕ → ℝ} {i : ℕ} (hf0 : f (i - 1) = g (i - 1))
    (hf1 : f i = g i) (hM0 : M (i - 1) = N (i - 1)) (hM1 : M i = N i) :
    panelCubicPoly x f M i = panelCubicPoly x g N i := by
  simp only [panelCubicPoly, hf0, hf1, hM0, hM1]

/-- **A cubic spline is the panel cubic of its values and moments on every panel.** Let
$a = x_0 < \dots < x_n = b$ be a partition, and let $s$ be a cubic spline. Then for
$1 \le i \le n$, $s$ equals on $[x_{i-1}, x_i]$ the panel cubic with the data
$s(x_0), \dots, s(x_n)$ and the moments of $s$. This is (8.46) of [quarteroni2000numerical]
integrated. -/
theorem IsCubicSpline.eqOn_panelCubic (hx : IsIntervalPartition a b n x) {s : ℝ → ℝ}
    (hs : IsCubicSpline a b n x s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    EqOn s (panelCubic x (fun i => s (x i)) (moment a b x s) i) (Icc (x (i - 1)) (x i)) := by
  obtain ⟨p, hpd, hpe⟩ := hs.piecewise i hi1 hin
  have hlt : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hpq : p = panelCubicPoly x (fun i => s (x i)) (moment a b x s) i := by
    refine eq_of_degree_le_three hpd (degree_panelCubicPoly_le _ _ _ _) hlt.ne ?_ ?_ ?_ ?_
    · exact (hpe ⟨le_rfl, hlt.le⟩).symm.trans
        (panelCubic_left (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
    · exact (hpe ⟨hlt.le, le_rfl⟩).symm.trans
        (panelCubic_right (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
    · exact (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn hlt hsub hpe
        ⟨le_rfl, hlt.le⟩).2.symm.trans
        (panelCubicD2_left (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
    · exact (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn hlt hsub hpe
        ⟨hlt.le, le_rfl⟩).2.symm.trans
        (panelCubicD2_right (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
  intro t ht
  rw [hpe ht, hpq]
  rfl

/-- **An interpolatory cubic spline is the panel cubic of its data and moments on every panel.** Let
$a = x_0 < \dots < x_n = b$ be a partition, and let $s$ be an interpolatory cubic spline of the
data $f$. Then for $1 \le i \le n$, $s$ equals on $[x_{i-1}, x_i]$ the panel cubic with the data
$f$ and the moments of $s$. -/
theorem IsCubicInterp.eqOn_panelCubic (hx : IsIntervalPartition a b n x) {f : ℕ → ℝ} {s : ℝ → ℝ}
    (hs : IsCubicInterp a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    EqOn s (panelCubic x f (moment a b x s) i) (Icc (x (i - 1)) (x i)) := by
  refine (hs.toIsCubicSpline.eqOn_panelCubic hx hi1 hin).trans fun t _ => ?_
  simp only [panelCubic]
  rw [panelCubicPoly_congr (hs.interp _ (by omega)) (hs.interp _ hin) rfl rfl]

/-- **An interpolatory cubic spline is the glued cubic spline of its data and moments.** For a
partition with $n \ge 1$, an interpolatory cubic spline $s$ of the data $f$ equals on $[a, b]$
the glued cubic spline of $f$ and of the moments of $s$. -/
theorem IsCubicInterp.eqOn_cubicSplineFun (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {f : ℕ → ℝ} {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    EqOn s (cubicSplineFun n x f (moment a b x s)) (Icc a b) := by
  intro t ht
  obtain ⟨i, hi1, hin, hti, -⟩ := hx.exists_mem_panel hn ht
  rw [hs.eqOn_panelCubic hx hi1 hin hti, cubicSplineFun_eqOn hx hi1 hin hti]

/-- **The moments of an interpolatory cubic spline satisfy the M-continuity system.** For a
partition, the moments of an interpolatory cubic spline of the data $f$ satisfy the interior
moment equation (8.47) of [quarteroni2000numerical] at every $x_i$, $1 \le i < n$. -/
theorem IsCubicInterp.isMomentEq (hx : IsIntervalPartition a b n x) {f : ℕ → ℝ} {s : ℝ → ℝ}
    (hs : IsCubicInterp a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    IsMomentEq x f (moment a b x s) i :=
  moment_eq_of_contDiffOn hx hs.contDiffOn (fun _ hi1 hin => hs.eqOn_panelCubic hx hi1 hin) hi1 hin

/-- For a partition with $n \ge 1$, if $M_i = N_i$ for $0 \le i \le n$, then the glued cubic splines
of the data $f$ with the moments $M$ and with the moments $N$ agree on $[a, b]$. -/
theorem cubicSplineFun_eqOn_of_moment_eq (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {f M N : ℕ → ℝ} (hMN : ∀ i ≤ n, M i = N i) :
    EqOn (cubicSplineFun n x f M) (cubicSplineFun n x f N) (Icc a b) := by
  intro t ht
  obtain ⟨i, hi1, hin, hti, -⟩ := hx.exists_mem_panel hn ht
  rw [cubicSplineFun_eqOn hx hi1 hin hti, cubicSplineFun_eqOn hx hi1 hin hti]
  simp only [panelCubic]
  rw [panelCubicPoly_congr rfl rfl (hMN _ (by omega)) (hMN _ hin)]

/-! ### The interpolatory cubic spline with a closure of type (8.48) -/

/-- A function $s$ satisfies a **closure of type (8.48)** with the parameters $\lambda_0, \mu_n$ and
the values $d_0, d_n$ if its moments satisfy
$$2 M_0 + \lambda_0 M_1 = d_0, \qquad \mu_n M_{n-1} + 2 M_n = d_n.$$
These are the first and the last rows of the system (8.48) of [quarteroni2000numerical]. The
moments are `Spline.moment a b x s`. -/
def HasClosure (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (lam0 mun d0 dn : ℝ) (s : ℝ → ℝ) : Prop :=
  2 * moment a b x s 0 + lam0 * moment a b x s 1 = d0 ∧
    mun * moment a b x s (n - 1) + 2 * moment a b x s n = dn

section Closure

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ} {lam0 mun d0 dn : ℝ}
include hx hn

/-- **The full moment system is the interior moment equations plus the closure rows.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $M$ be a vector indexed by
$\{0, \dots, n\}$. Let $A$ be the moment matrix and $d$ the right-hand side for the panel
lengths of the partition, the data $f$ and the closure $(\lambda_0, \mu_n, d_0, d_n)$. Then
$A M = d$ holds if and only if the interior moment equations (8.47) hold at
$x_1, \dots, x_{n-1}$, $2 M_0 + \lambda_0 M_1 = d_0$, and $\mu_n M_{n-1} + 2 M_n = d_n$.

The vector $M$ enters the moment equations through its extension by zero (`Spline.extendFin`). -/
theorem momentMatrix_mulVec_eq_iff (M : Fin (n + 1) → ℝ) :
    (momentMatrix n (panelLength x) lam0 mun).mulVec M = momentRhs n (panelLength x) f d0 dn ↔
      (∀ i, 1 ≤ i → i < n → IsMomentEq x f (extendFin M) i) ∧
        2 * extendFin M 0 + lam0 * extendFin M 1 = d0 ∧
        mun * extendFin M (n - 1) + 2 * extendFin M n = dn := by
  rw [funext_iff]
  simp only [momentMatrix_mulVec_apply, momentRhs]
  constructor
  · intro H
    refine ⟨fun i hi1 hin => ?_, ?_, ?_⟩
    · have := H ⟨i, by omega⟩
      simp only [ite_eq_right (show i ≠ 0 by omega), ite_eq_right (show i ≠ n by omega),
        momentLam, momentMu] at this
      rw [IsMomentEq, extendFin_of_lt M (i := i) (by omega)]
      linear_combination this
    · have := H ⟨0, by omega⟩
      simp only [↓reduceIte, momentLam, zero_add, mul_zero, add_zero] at this
      rw [extendFin_of_lt M (i := 0) (by omega)]
      exact this
    · have := H ⟨n, by omega⟩
      simp only [ite_eq_right (show n ≠ 0 by omega), ↓reduceIte, momentMu,
        extendFin_of_le M (le_refl (n + 1)), mul_zero, add_zero] at this
      rw [extendFin_of_lt M (i := n) (by omega)]
      linear_combination this
  · rintro ⟨hint, h0, hN⟩ ⟨i, hi⟩
    by_cases hi0 : i = 0
    · subst hi0
      simp only [↓reduceIte, momentLam, zero_add, mul_zero, add_zero]
      rw [extendFin_of_lt M (i := 0) (by omega)] at h0
      exact h0
    · by_cases hin : i = n
      · subst hin
        simp only [ite_eq_right hi0, ↓reduceIte, momentMu, extendFin_of_le M (le_refl (i + 1)),
          mul_zero, add_zero]
        rw [extendFin_of_lt M (i := i) (by omega)] at hN
        linear_combination hN
      · have := hint i (by omega) (by omega)
        rw [IsMomentEq, extendFin_of_lt M (i := i) (by omega)] at this
        simp only [ite_eq_right hi0, ite_eq_right hin, momentLam, momentMu]
        linear_combination this

/-- For a partition with $n \ge 1$: if a vector $M$ indexed by $\{0, \dots, n\}$ solves the moment
system $A M = d$ with the closure $(\lambda_0, \mu_n, d_0, d_n)$, then the glued cubic spline of
the data $f$ and of the moments $M$ is an interpolatory cubic spline of $f$ that satisfies this
closure. -/
theorem isCubicInterp_cubicSplineFun_of_mulVec_eq {M : Fin (n + 1) → ℝ}
    (hM : (momentMatrix n (panelLength x) lam0 mun).mulVec M
      = momentRhs n (panelLength x) f d0 dn) :
    IsCubicInterp a b n x f (cubicSplineFun n x f (extendFin M)) ∧
      HasClosure a b n x lam0 mun d0 dn (cubicSplineFun n x f (extendFin M)) := by
  obtain ⟨hint, h0, hN⟩ := (momentMatrix_mulVec_eq_iff hx hn M).mp hM
  have hab : a < b := hx.lt_of_pos hn
  have hmom : ∀ i ≤ n, moment a b x (cubicSplineFun n x f (extendFin M)) i = extendFin M i :=
    fun i hi => by
      rw [moment_eq_iteratedDeriv hab (contDiff_cubicSplineFun hx hn hint)
        ⟨hx.left_le hi, hx.le_right hi⟩, iteratedDeriv_two_cubicSplineFun_node hx hn hint hi]
  refine ⟨⟨⟨contDiffOn_cubicSplineFun hx hn hint, fun i hi1 hin =>
    ⟨panelCubicPoly x f (extendFin M) i, degree_panelCubicPoly_le _ _ _ _,
      cubicSplineFun_eqOn hx hi1 hin⟩⟩, fun i hi => cubicSplineFun_apply_node hx hn hi⟩, ?_, ?_⟩
  · rw [hmom 0 (by omega), hmom 1 hn]
    exact h0
  · rw [hmom (n - 1) (by omega), hmom n le_rfl]
    exact hN

/-- For a partition with $n \ge 1$, the moments $M_0, \dots, M_n$ of an interpolatory cubic spline
of the data $f$ with a closure $(\lambda_0, \mu_n, d_0, d_n)$ of type (8.48) solve the moment
system $A M = d$. -/
theorem IsCubicInterp.momentMatrix_mulVec_eq {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s)
    (hc : HasClosure a b n x lam0 mun d0 dn s) :
    (momentMatrix n (panelLength x) lam0 mun).mulVec
      (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) = momentRhs n (panelLength x) f d0 dn := by
  refine (momentMatrix_mulVec_eq_iff hx hn _).mpr ⟨fun i hi1 hin => ?_, ?_, ?_⟩
  · have := hs.isMomentEq hx hi1 hin
    rwa [IsMomentEq, ← extendFin_of_lt (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) (i := i - 1)
      (by omega), ← extendFin_of_lt (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) (i := i)
      (by omega), ← extendFin_of_lt (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) (i := i + 1)
      (by omega)] at this
  · rw [extendFin_of_lt _ (by omega), extendFin_of_lt _ (by omega)]
    exact hc.1
  · rw [extendFin_of_lt _ (by omega), extendFin_of_lt _ (by omega)]
    exact hc.2

variable (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1)
include hl0 hl1 hm0 hm1

/-- **Uniqueness of the interpolatory cubic spline with a closure of type (8.48).** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $0 \le \lambda_0 \le 1$ and
$0 \le \mu_n \le 1$. Two interpolatory cubic splines of the same data that satisfy the same
closure $(\lambda_0, \mu_n, d_0, d_n)$ agree on $[a, b]$, because their moments solve the same
nonsingular system. -/
theorem IsCubicInterp.eqOn_of_hasClosure {s₁ s₂ : ℝ → ℝ} (h₁ : IsCubicInterp a b n x f s₁)
    (hc₁ : HasClosure a b n x lam0 mun d0 dn s₁) (h₂ : IsCubicInterp a b n x f s₂)
    (hc₂ : HasClosure a b n x lam0 mun d0 dn s₂) : EqOn s₁ s₂ (Icc a b) := by
  have hA := isUnit_momentMatrix (h := panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  have hM : (fun i : Fin (n + 1) => moment a b x s₁ (i : ℕ)) =
      fun i : Fin (n + 1) => moment a b x s₂ (i : ℕ) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hA
      ((h₁.momentMatrix_mulVec_eq hx hn hc₁).trans (h₂.momentMatrix_mulVec_eq hx hn hc₂).symm)
  refine (h₁.eqOn_cubicSplineFun hx hn).trans
    ((cubicSplineFun_eqOn_of_moment_eq hx hn fun i hi => ?_).trans
      (h₂.eqOn_cubicSplineFun hx hn).symm)
  exact congrFun hM (⟨i, by omega⟩ : Fin (n + 1))

/-- **Existence and uniqueness of the interpolatory cubic spline with a closure of type (8.48).**
Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, let $0 \le \lambda_0 \le 1$ and
$0 \le \mu_n \le 1$, and let $f_0, \dots, f_n$ and $d_0, d_n$ be real numbers. Then there is an
interpolatory cubic spline $s$ of the data $f$ whose moments satisfy
$$2 M_0 + \lambda_0 M_1 = d_0, \qquad \mu_n M_{n-1} + 2 M_n = d_n,$$
and any two such splines agree on $[a, b]$. This is the existence and uniqueness statement of
§8.6.1 of [quarteroni2000numerical] for the closures (8.48).

Uniqueness holds on $[a, b]$ only, because the conditions constrain a spline only on $[a, b]$. -/
theorem existsUnique_isCubicInterp_of_closure (f : ℕ → ℝ) (d0 dn : ℝ) :
    (∃ s, IsCubicInterp a b n x f s ∧ HasClosure a b n x lam0 mun d0 dn s) ∧
      ∀ s₁ s₂, IsCubicInterp a b n x f s₁ → HasClosure a b n x lam0 mun d0 dn s₁ →
        IsCubicInterp a b n x f s₂ → HasClosure a b n x lam0 mun d0 dn s₂ →
        EqOn s₁ s₂ (Icc a b) := by
  refine ⟨?_, fun s₁ s₂ h₁ hc₁ h₂ hc₂ => h₁.eqOn_of_hasClosure hx hn hl0 hl1 hm0 hm1 hc₁ h₂ hc₂⟩
  have hA := isUnit_momentMatrix (h := panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  refine ⟨_, isCubicInterp_cubicSplineFun_of_mulVec_eq hx hn
    (M := (momentMatrix n (panelLength x) lam0 mun)⁻¹.mulVec (momentRhs n (panelLength x) f d0 dn))
    ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    Matrix.one_mulVec]

end Closure

/-! ### The interpolatory cubic spline as an explicit function -/

/-- The moment vector of the interpolatory cubic spline with the closure
$(\lambda_0, \mu_n, d_0, d_n)$: the vector $A^{-1} d$, extended by zero to $\mathbb{N}$, where
$A$ is the moment matrix and $d$ is the right-hand side of the system (8.48) for the panel
lengths of the nodes and the data $f$.

The inverse is the matrix inverse of Mathlib, which is $0$ when $A$ is singular. -/
noncomputable def momentVec (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn : ℝ) : ℕ → ℝ :=
  extendFin ((momentMatrix n (panelLength x) lam0 mun)⁻¹.mulVec
    (momentRhs n (panelLength x) f d0 dn))

/-- The **interpolatory cubic spline** with a closure of type (8.48), as an explicit function
$\mathbb{R} \to \mathbb{R}$: the glued cubic spline of the data $f$ and of the moments
`Spline.momentVec n x f lam0 mun d0 dn`, which solve (8.48). For $0 \le \lambda_0, \mu_n \le 1$
it is the spline of `Spline.existsUnique_isCubicInterp_of_closure`
(`Spline.isCubicInterp_cubicInterp`). -/
noncomputable def cubicInterp (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn : ℝ) : ℝ → ℝ :=
  cubicSplineFun n x f (momentVec n x f lam0 mun d0 dn)

/-- The **natural cubic spline** that interpolates the data $f$: the interpolatory cubic spline with
the closure $\lambda_0 = \mu_n = 0$ and $d_0 = d_n = 0$, that is, with $s''(a) = s''(b) = 0$.
This is (8.45) of [quarteroni2000numerical] with $k = 3$. -/
noncomputable def naturalInterp (n : ℕ) (x f : ℕ → ℝ) : ℝ → ℝ :=
  cubicInterp n x f 0 0 0 0

/-- The **clamped** (constrained) cubic spline that interpolates the data $f$ with the prescribed
end slopes $s'(a) = f'_0$ and $s'(b) = f'_n$: the interpolatory cubic spline with the closure
$\lambda_0 = \mu_n = 1$ and
$$d_0 = \frac{6}{h_1} \left( \frac{f_1 - f_0}{h_1} - f'_0 \right), \qquad d_n = \frac{6}{h_n}
  \left( f'_n - \frac{f_n - f_{n-1}}{h_n} \right),$$
where $h_1 = x_1 - x_0$ and $h_n = x_n - x_{n-1}$. This is the spline of Exercise 8.11 of
[quarteroni2000numerical]. -/
noncomputable def clampedInterp (n : ℕ) (x f : ℕ → ℝ) (f'0 f'n : ℝ) : ℝ → ℝ :=
  cubicInterp n x f 1 1 (6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0))
    (6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))))

section CubicInterp

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ} {lam0 mun d0 dn : ℝ}
  (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1)
include hx hl0 hl1 hm0 hm1

/-- For a partition and $0 \le \lambda_0, \mu_n \le 1$, the vector $A^{-1} d$ solves the moment
system $A M = d$. -/
theorem momentMatrix_mulVec_momentVec (f : ℕ → ℝ) (d0 dn : ℝ) :
    (momentMatrix n (panelLength x) lam0 mun).mulVec
      ((momentMatrix n (panelLength x) lam0 mun)⁻¹.mulVec (momentRhs n (panelLength x) f d0 dn))
      = momentRhs n (panelLength x) f d0 dn := by
  have hA := isUnit_momentMatrix (h := panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    Matrix.one_mulVec]

include hn

/-- **The interpolatory cubic spline is an interpolatory cubic spline with its closure.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $0 \le \lambda_0 \le 1$ and
$0 \le \mu_n \le 1$. Then `Spline.cubicInterp n x f lam0 mun d0 dn` is an interpolatory cubic
spline of the data $f$ that satisfies the closure $(\lambda_0, \mu_n, d_0, d_n)$. -/
theorem isCubicInterp_cubicInterp :
    IsCubicInterp a b n x f (cubicInterp n x f lam0 mun d0 dn) ∧
      HasClosure a b n x lam0 mun d0 dn (cubicInterp n x f lam0 mun d0 dn) :=
  isCubicInterp_cubicSplineFun_of_mulVec_eq hx hn
    (momentMatrix_mulVec_momentVec hx hl0 hl1 hm0 hm1 f d0 dn)

/-- For a partition with $n \ge 1$ and $0 \le \lambda_0, \mu_n \le 1$, the moment vector
`Spline.momentVec n x f lam0 mun d0 dn` satisfies the interior moment equations at
$x_1, \dots, x_{n-1}$. -/
theorem isMomentEq_momentVec {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    IsMomentEq x f (momentVec n x f lam0 mun d0 dn) i :=
  ((momentMatrix_mulVec_eq_iff hx hn _).mp
    (momentMatrix_mulVec_momentVec hx hl0 hl1 hm0 hm1 f d0 dn)).1 i hi1 hin

/-- **The interpolatory cubic spline is of class $C^2$ on $\mathbb{R}$**, for a partition with
$n \ge 1$ and $0 \le \lambda_0, \mu_n \le 1$. -/
theorem contDiff_cubicInterp : ContDiff ℝ 2 (cubicInterp n x f lam0 mun d0 dn) :=
  contDiff_cubicSplineFun hx hn fun _ hi1 hin => isMomentEq_momentVec hx hn hl0 hl1 hm0 hm1 hi1 hin

omit hl0 hl1 hm0 hm1 in
/-- **The interpolatory cubic spline interpolates the data.** For a partition with $n \ge 1$ and
every closure, the interpolatory cubic spline $s$ satisfies $s(x_i) = f_i$ for $0 \le i \le n$. -/
theorem cubicInterp_apply_node {i : ℕ} (hi : i ≤ n) :
    cubicInterp n x f lam0 mun d0 dn (x i) = f i :=
  cubicSplineFun_apply_node hx hn hi

/-- **The moments of the interpolatory cubic spline are the solution of the moment system.** For a
partition with $n \ge 1$ and $0 \le \lambda_0, \mu_n \le 1$, the second derivative of the
interpolatory cubic spline at $x_i$, $0 \le i \le n$, is the $i$-th entry of the moment vector. -/
theorem iteratedDeriv_two_cubicInterp_node {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) (x i) = momentVec n x f lam0 mun d0 dn i :=
  iteratedDeriv_two_cubicSplineFun_node hx hn
    (fun _ hi1 hin => isMomentEq_momentVec hx hn hl0 hl1 hm0 hm1 hi1 hin) hi

/-- **Uniqueness.** For a partition with $n \ge 1$ and $0 \le \lambda_0, \mu_n \le 1$, every
interpolatory cubic spline of the data $f$ that satisfies the closure
$(\lambda_0, \mu_n, d_0, d_n)$ equals `Spline.cubicInterp n x f lam0 mun d0 dn` on $[a, b]$. -/
theorem IsCubicInterp.eqOn_cubicInterp {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s)
    (hc : HasClosure a b n x lam0 mun d0 dn s) :
    EqOn s (cubicInterp n x f lam0 mun d0 dn) (Icc a b) :=
  hs.eqOn_of_hasClosure hx hn hl0 hl1 hm0 hm1 hc (isCubicInterp_cubicInterp hx hn hl0 hl1 hm0 hm1).1
    (isCubicInterp_cubicInterp hx hn hl0 hl1 hm0 hm1).2

end CubicInterp

section NaturalClamped

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
include hx hn

/-- For a partition with $n \ge 1$, the natural cubic spline is of class $C^2$ on $\mathbb{R}$. -/
theorem contDiff_naturalInterp : ContDiff ℝ 2 (naturalInterp n x f) :=
  contDiff_cubicInterp hx hn le_rfl zero_le_one le_rfl zero_le_one

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let
$f'_0, f'_n \in \mathbb{R}$. Then the clamped cubic spline of the data $f$ with the end slopes
$f'_0, f'_n$ is of class $C^2$ on $\mathbb{R}$. -/
theorem contDiff_clampedInterp (f'0 f'n : ℝ) : ContDiff ℝ 2 (clampedInterp n x f f'0 f'n) :=
  contDiff_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let
$f'_0, f'_n \in \mathbb{R}$. Then the clamped cubic spline of the data $f$ with the end slopes
$f'_0, f'_n$ is an interpolatory cubic spline of $f$. -/
theorem isCubicInterp_clampedInterp (f : ℕ → ℝ) (f'0 f'n : ℝ) :
    IsCubicInterp a b n x f (clampedInterp n x f f'0 f'n) :=
  (isCubicInterp_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl).1

/-- **The natural spline has vanishing second derivative at the endpoints.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. Then the natural cubic spline $s$ of
the data $f$ satisfies $s''(a) = 0$ and $s''(b) = 0$, with ordinary second derivatives. -/
theorem iteratedDeriv_two_naturalInterp_endpoints :
    iteratedDeriv 2 (naturalInterp n x f) a = 0 ∧ iteratedDeriv 2 (naturalInterp n x f) b = 0 := by
  have h := (isCubicInterp_cubicInterp hx hn (f := f) (d0 := 0) (dn := 0) le_rfl zero_le_one le_rfl
    zero_le_one).2
  have hab := hx.lt_of_pos hn
  have hc := contDiff_cubicInterp hx hn (f := f) (d0 := 0) (dn := 0) le_rfl zero_le_one le_rfl
    zero_le_one
  simp only [HasClosure, moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.zero_le n),
    hx.le_right (Nat.zero_le n)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.sub_le n 1), hx.le_right (Nat.sub_le n 1)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le le_rfl, hx.le_right le_rfl⟩, zero_mul, add_zero,
    zero_add, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, hx.first, hx.last] at h
  exact ⟨h.1, h.2⟩

/-- **The clamped spline has the prescribed slopes at the endpoints.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $f'_0, f'_n \in \mathbb{R}$.
Then the clamped cubic spline $s$ of the data $f$ with the end slopes $f'_0, f'_n$ satisfies
$s'(a) = f'_0$ and $s'(b) = f'_n$, with ordinary derivatives. -/
theorem deriv_clampedInterp_endpoints (f'0 f'n : ℝ) :
    deriv (clampedInterp n x f f'0 f'n) a = f'0 ∧ deriv (clampedInterp n x f f'0 f'n) b = f'n := by
  suffices key : ∀ d0 dn : ℝ, d0 = 6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0) →
      dn = 6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))) →
      deriv (cubicInterp n x f 1 1 d0 dn) a = f'0 ∧ deriv (cubicInterp n x f 1 1 d0 dn) b = f'n from
    key _ _ rfl rfl
  intro d0 dn hd0 hdn
  have hM : ∀ i, 1 ≤ i → i < n → IsMomentEq x f (momentVec n x f 1 1 d0 dn) i :=
    fun _ hi1 hin => isMomentEq_momentVec hx hn zero_le_one le_rfl zero_le_one le_rfl hi1 hin
  have h := (isCubicInterp_cubicInterp hx hn (f := f) (d0 := d0) (dn := dn) zero_le_one le_rfl
    zero_le_one le_rfl).2
  have hab := hx.lt_of_pos hn
  have hc := contDiff_cubicInterp hx hn (f := f) (d0 := d0) (dn := dn) zero_le_one le_rfl
    zero_le_one le_rfl
  simp only [HasClosure] at h
  rw [moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.zero_le n), hx.le_right (Nat.zero_le n)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le hn, hx.le_right hn⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.sub_le n 1), hx.le_right (Nat.sub_le n 1)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le le_rfl, hx.le_right le_rfl⟩,
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl (Nat.zero_le n),
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl hn,
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl (Nat.sub_le n 1),
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl le_rfl] at h
  obtain ⟨h0, hN⟩ := h
  have h1 : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (hx.step 0 hn).ne'
  have hn' : x n - x (n - 1) ≠ 0 :=
    sub_ne_zero.mpr (hx.lt (Nat.sub_one_lt_of_le hn le_rfl) le_rfl).ne'
  constructor
  · rw [cubicInterp, deriv_cubicSplineFun_left hx hn hM]
    calc -((x 1 - x 0) * momentVec n x f 1 1 d0 dn 0) / 3
          - (x 1 - x 0) * momentVec n x f 1 1 d0 dn 1 / 6 + (f 1 - f 0) / (x 1 - x 0)
        = -((x 1 - x 0) / 6) * (2 * momentVec n x f 1 1 d0 dn 0 + 1 * momentVec n x f 1 1 d0 dn 1)
          + (f 1 - f 0) / (x 1 - x 0) := by ring
      _ = -((x 1 - x 0) / 6) * (6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0))
          + (f 1 - f 0) / (x 1 - x 0) := by rw [h0, hd0]
      _ = f'0 := by field_simp; ring
  · rw [cubicInterp, deriv_cubicSplineFun_right hx hn hM]
    calc (x n - x (n - 1)) * momentVec n x f 1 1 d0 dn (n - 1) / 6
          + (x n - x (n - 1)) * momentVec n x f 1 1 d0 dn n / 3
          + (f n - f (n - 1)) / (x n - x (n - 1))
        = (x n - x (n - 1)) / 6 * (1 * momentVec n x f 1 1 d0 dn (n - 1)
            + 2 * momentVec n x f 1 1 d0 dn n) + (f n - f (n - 1)) / (x n - x (n - 1)) := by ring
      _ = (x n - x (n - 1)) / 6 * (6 / (x n - x (n - 1))
            * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))))
          + (f n - f (n - 1)) / (x n - x (n - 1)) := by rw [hN, hdn]
      _ = f'n := by field_simp; ring

end NaturalClamped

/-! ### Linearity of the interpolatory spline in the data, and the cardinal basis -/

section Linearity

variable {f g M N : ℕ → ℝ} {lam0 mun d0 dn e0 en c : ℝ}

/-- For $n \ge 1$, the panel index of every $t \in \mathbb{R}$ lies between $1$ and $n$. -/
theorem panelIndex_mem (hn : 1 ≤ n) (t : ℝ) : 1 ≤ panelIndex n x t ∧ panelIndex n x t ≤ n := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  unfold panelIndex
  have := (Finset.card_filter_le (Finset.Ico 1 n) fun j => x j ≤ t).trans (Nat.card_Ico 1 n).le
  omega

/-- For $n \ge 1$, a glued function depends only on the panel functions of the panels $1, \dots, n$:
if $Q_i = Q'_i$ for $1 \le i \le n$, then the glued functions of $Q$ and of $Q'$ are equal. -/
theorem panelGlue_congr {E : Type*} (hn : 1 ≤ n) {Q Q' : ℕ → ℝ → E}
    (hQ : ∀ i, 1 ≤ i → i ≤ n → Q i = Q' i) :
    panelGlue n x Q = panelGlue n x Q' :=
  funext fun t => by rw [panelGlue, panelGlue, hQ _ (panelIndex_mem hn t).1 (panelIndex_mem hn t).2]

/-- The panel cubic is additive in the data and the moments: the panel cubic of the data $f + g$ and
the moments $M + N$ is the sum of the panel cubics of $(f, M)$ and of $(g, N)$. -/
theorem panelCubic_add (i : ℕ) (t : ℝ) :
    panelCubic x (f + g) (M + N) i t = panelCubic x f M i t + panelCubic x g N i t := by
  simp only [panelCubic_apply, Pi.add_apply]
  ring

/-- The panel cubic is homogeneous in the data and the moments: for $c \in \mathbb{R}$, the panel
cubic of the data $c f$ and the moments $c M$ is $c$ times the panel cubic of $(f, M)$. -/
theorem panelCubic_smul (i : ℕ) (t : ℝ) :
    panelCubic x (c • f) (c • M) i t = c * panelCubic x f M i t := by
  simp only [panelCubic_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The glued cubic spline is additive in the data and the moments: the glued cubic spline of
$(f + g, M + N)$ is the sum of the glued cubic splines of $(f, M)$ and of $(g, N)$. -/
theorem cubicSplineFun_add :
    cubicSplineFun n x (f + g) (M + N) = cubicSplineFun n x f M + cubicSplineFun n x g N :=
  funext fun _ => panelCubic_add _ _

/-- The glued cubic spline is homogeneous in the data and the moments: for $c \in \mathbb{R}$, the
glued cubic spline of $(c f, c M)$ is $c$ times the glued cubic spline of $(f, M)$. -/
theorem cubicSplineFun_smul : cubicSplineFun n x (c • f) (c • M) = c • cubicSplineFun n x f M :=
  funext fun _ => panelCubic_smul _ _

/-- The right-hand side of the moment system is additive in the data and the closure values: the
right-hand side for $(f + g, d_0 + e_0, d_n + e_n)$ is the sum of the right-hand sides for
$(f, d_0, d_n)$ and for $(g, e_0, e_n)$. -/
theorem momentRhs_add (h : ℕ → ℝ) :
    momentRhs n h (f + g) (d0 + e0) (dn + en) = momentRhs n h f d0 dn + momentRhs n h g e0 en := by
  funext i
  simp only [momentRhs, Pi.add_apply]
  split_ifs <;> ring

/-- The right-hand side of the moment system is homogeneous in the data and the closure values: for
$c \in \mathbb{R}$, the right-hand side for $(c f, c d_0, c d_n)$ is $c$ times the right-hand
side for $(f, d_0, d_n)$. -/
theorem momentRhs_smul (h : ℕ → ℝ) :
    momentRhs n h (c • f) (c * d0) (c * dn) = c • momentRhs n h f d0 dn := by
  funext i
  simp only [momentRhs, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The extension by zero is additive: the extension of $v + w$ is the sum of the extensions of $v$
and of $w$. -/
theorem extendFin_add (v w : Fin (n + 1) → ℝ) : extendFin (v + w) = extendFin v + extendFin w := by
  funext i
  rcases lt_or_ge i (n + 1) with hi | hi
  · simp [extendFin_of_lt _ hi]
  · simp [extendFin_of_le _ hi]

/-- The extension by zero is homogeneous: for $c \in \mathbb{R}$, the extension of $c v$ is $c$
times the extension of $v$. -/
theorem extendFin_smul (v : Fin (n + 1) → ℝ) : extendFin (c • v) = c • extendFin v := by
  funext i
  rcases lt_or_ge i (n + 1) with hi | hi
  · simp [extendFin_of_lt _ hi]
  · simp [extendFin_of_le _ hi]

/-- The moment vector is additive in the data and the closure values: for fixed $\lambda_0, \mu_n$,
the moment vector for $(f + g, d_0 + e_0, d_n + e_n)$ is the sum of the moment vectors for
$(f, d_0, d_n)$ and for $(g, e_0, e_n)$. -/
theorem momentVec_add :
    momentVec n x (f + g) lam0 mun (d0 + e0) (dn + en)
      = momentVec n x f lam0 mun d0 dn + momentVec n x g lam0 mun e0 en := by
  rw [momentVec, momentVec, momentVec, momentRhs_add, Matrix.mulVec_add, extendFin_add]

/-- The moment vector is homogeneous in the data and the closure values: for fixed
$\lambda_0, \mu_n$ and $c \in \mathbb{R}$, the moment vector for $(c f, c d_0, c d_n)$ is $c$
times the moment vector for $(f, d_0, d_n)$. -/
theorem momentVec_smul :
    momentVec n x (c • f) lam0 mun (c * d0) (c * dn) = c • momentVec n x f lam0 mun d0 dn := by
  rw [momentVec, momentVec, momentRhs_smul, Matrix.mulVec_smul, extendFin_smul]

/-- **The interpolatory cubic spline is additive in the data and the closure values.** For fixed
$\lambda_0$ and $\mu_n$, the spline of the data $f + g$ with the closure values
$d_0 + e_0, d_n + e_n$ is the sum of the spline of $f$ with $d_0, d_n$ and the spline of $g$
with $e_0, e_n$.

No hypothesis on the nodes is needed. -/
theorem cubicInterp_add :
    cubicInterp n x (f + g) lam0 mun (d0 + e0) (dn + en)
      = cubicInterp n x f lam0 mun d0 dn + cubicInterp n x g lam0 mun e0 en := by
  rw [cubicInterp, momentVec_add, cubicSplineFun_add]
  rfl

/-- **The interpolatory cubic spline is homogeneous in the data and the closure values.** For fixed
$\lambda_0$ and $\mu_n$ and for $c \in \mathbb{R}$, the spline of the data $c f$ with the
closure values $c d_0, c d_n$ is $c$ times the spline of $f$ with $d_0, d_n$.

No hypothesis on the nodes is needed. -/
theorem cubicInterp_smul :
    cubicInterp n x (c • f) lam0 mun (c * d0) (c * dn) = c • cubicInterp n x f lam0 mun d0 dn := by
  rw [cubicInterp, momentVec_smul, cubicSplineFun_smul]
  rfl

/-- The interpolatory cubic spline of the zero data with the closure values $d_0 = d_n = 0$ is the
zero function. -/
theorem cubicInterp_zero : cubicInterp n x 0 lam0 mun 0 0 = 0 := by
  have := cubicInterp_smul (n := n) (x := x) (f := 0) (lam0 := lam0) (mun := mun) (d0 := 0)
    (dn := 0) (c := 0)
  simpa using this

/-- The interpolatory cubic spline of a finite linear combination of data. Let $S$ be a finite index
set, and for $j \in S$ let $c_j \in \mathbb{R}$, let $F_j$ be data and let $D_{0,j}, D_{n,j}$ be
closure values. For fixed $\lambda_0$ and $\mu_n$, the spline of the data
$\sum_{j \in S} c_j F_j$ with the closure values $\sum_{j \in S} c_j D_{0,j}$ and
$\sum_{j \in S} c_j D_{n,j}$ is $\sum_{j \in S} c_j s_j$, where $s_j$ is the spline of $F_j$
with $D_{0,j}, D_{n,j}$. -/
theorem cubicInterp_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → ℕ → ℝ) (D0 Dn : ι → ℝ) :
    cubicInterp n x (∑ i ∈ s, c i • F i) lam0 mun (∑ i ∈ s, c i * D0 i) (∑ i ∈ s, c i * Dn i)
      = ∑ i ∈ s, c i • cubicInterp n x (F i) lam0 mun (D0 i) (Dn i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubicInterp_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
      cubicInterp_add, cubicInterp_smul, ih]

/-- For $n \ge 1$, the interpolatory cubic spline depends only on the data at the nodes
$x_0, \dots, x_n$: if $f_i = g_i$ for $0 \le i \le n$, then the splines of $f$ and of $g$ with
the same closure are equal. -/
theorem cubicInterp_congr (hn : 1 ≤ n) (hfg : ∀ i ≤ n, f i = g i) :
    cubicInterp n x f lam0 mun d0 dn = cubicInterp n x g lam0 mun d0 dn := by
  have hrhs : momentRhs n (panelLength x) f d0 dn = momentRhs n (panelLength x) g d0 dn := by
    funext i
    simp only [momentRhs]
    split_ifs with h0 hN
    · rfl
    · rfl
    · rw [hfg (i + 1) (by have := i.2; omega), hfg i (by omega), hfg (i - 1) (by omega)]
  rw [cubicInterp, cubicInterp, momentVec, momentVec, hrhs]
  refine panelGlue_congr hn fun i hi1 hin => funext fun t => ?_
  simp only [panelCubic]
  rw [panelCubicPoly_congr (hfg _ (by omega)) (hfg _ hin) rfl rfl]

end Linearity

/-! ### The cardinal basis -/

/-- The **cardinal spline basis** of the clamped splines. For $i \le n$, $\varphi_i$ is the clamped
spline with $\varphi_i(x_j) = \delta_{ij}$ for $0 \le j \le n$ and
$\varphi_i'(a) = \varphi_i'(b) = 0$. The function $\varphi_{n+1}$ is the clamped spline that
vanishes at every node with $\varphi_{n+1}'(a) = 1$ and $\varphi_{n+1}'(b) = 0$, and
$\varphi_{n+2}$ is the clamped spline that vanishes at every node with $\varphi_{n+2}'(a) = 0$
and $\varphi_{n+2}'(b) = 1$. This is the basis of §8.6.1 of [quarteroni2000numerical].

For $i > n + 2$ the definition gives $\varphi_{n+2}$ again. -/
noncomputable def cardinalBasis (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i ≤ n then clampedInterp n x (Pi.single i 1) 0 0
  else if i = n + 1 then clampedInterp n x 0 1 0 else clampedInterp n x 0 0 1

section Cardinal

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
include hx hn

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. For every $i \in \mathbb{N}$ and
$0 \le j \le n$, the cardinal function satisfies $\varphi_i(x_j) = \delta_{ij}$. In particular
$\varphi_{n+1}$ and $\varphi_{n+2}$ vanish at the nodes. -/
theorem cardinalBasis_apply_node (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    cardinalBasis n x i (x j) = if i = j then 1 else 0 := by
  by_cases hi : i ≤ n
  · rw [cardinalBasis, ite_eq_left hi, clampedInterp, cubicInterp_apply_node hx hn hj,
      Pi.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · rw [ite_eq_right (show i ≠ j by omega), cardinalBasis, ite_eq_right hi]
    split_ifs <;> rw [clampedInterp, cubicInterp_apply_node hx hn hj] <;> rfl

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. For every $i \in \mathbb{N}$, the
slope of the cardinal function $\varphi_i$ at $a$ is $\varphi_i'(a) = 1$ if $i = n + 1$ and
$\varphi_i'(a) = 0$ otherwise. -/
theorem deriv_cardinalBasis_left (i : ℕ) :
    deriv (cardinalBasis n x i) a = if i = n + 1 then 1 else 0 := by
  unfold cardinalBasis
  by_cases hi : i ≤ n
  · rw [ite_eq_left hi, (deriv_clampedInterp_endpoints hx hn _ _).1, ite_eq_right (by omega)]
  · by_cases hi' : i = n + 1
    · rw [ite_eq_right hi, ite_eq_left hi', (deriv_clampedInterp_endpoints hx hn _ _).1,
        ite_eq_left hi']
    · rw [ite_eq_right hi, ite_eq_right hi', (deriv_clampedInterp_endpoints hx hn _ _).1,
        ite_eq_right hi']

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$. For $i \le n + 2$, the slope of
the cardinal function $\varphi_i$ at $b$ is $\varphi_i'(b) = 1$ if $i = n + 2$ and
$\varphi_i'(b) = 0$ otherwise. -/
theorem deriv_cardinalBasis_right {i : ℕ} (hi2 : i ≤ n + 2) :
    deriv (cardinalBasis n x i) b = if i = n + 2 then 1 else 0 := by
  unfold cardinalBasis
  by_cases hi : i ≤ n
  · rw [ite_eq_left hi, (deriv_clampedInterp_endpoints hx hn _ _).2, ite_eq_right (by omega)]
  · by_cases hi' : i = n + 1
    · rw [ite_eq_right hi, ite_eq_left hi', (deriv_clampedInterp_endpoints hx hn _ _).2,
        ite_eq_right (by omega)]
    · rw [ite_eq_right hi, ite_eq_right hi', (deriv_clampedInterp_endpoints hx hn _ _).2,
        ite_eq_left (by omega)]

omit hx hn in
/-- For $k, l \le n$,
$$\sum_{i=0}^{n} f_i (\delta_{ik} - \delta_{il}) = f_k - f_l.$$
-/
theorem sum_mul_single_sub_single {f : ℕ → ℝ} {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    ∑ i ∈ Finset.range (n + 1), f i * ((Pi.single i 1 : ℕ → ℝ) k - (Pi.single i 1 : ℕ → ℝ) l)
      = f k - f l := by
  simp only [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]

omit hx in
/-- **The clamped spline in the cardinal basis.** For $n \ge 1$, the clamped cubic spline $s_3$ of
the data $f$ with the end slopes $f'_0, f'_n$ is
$$s_3 = \sum_{i=0}^{n} f_i \varphi_i + f'_0 \varphi_{n+1} + f'_n \varphi_{n+2}.$$
This is the representation in §8.6.1 of [quarteroni2000numerical].

The identity follows from the linearity of the spline in the data (`Spline.cubicInterp_sum`). It
needs no hypothesis on the nodes. -/
theorem clampedInterp_eq_sum_cardinalBasis (f : ℕ → ℝ) (f'0 f'n : ℝ) :
    clampedInterp n x f f'0 f'n = ∑ i ∈ Finset.range (n + 1), f i • cardinalBasis n x i
      + f'0 • cardinalBasis n x (n + 1) + f'n • cardinalBasis n x (n + 2) := by
  classical
  -- the closure values are linear in the data
  set D0 : (ℕ → ℝ) → ℝ → ℝ := fun f f'0 => 6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0)
    with hD0def
  set Dn : (ℕ → ℝ) → ℝ → ℝ :=
    fun f f'n => 6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))) with hDndef
  have hsum : ∑ i ∈ Finset.range (n + 1), f i • cardinalBasis n x i
      = cubicInterp n x (∑ i ∈ Finset.range (n + 1), f i • Pi.single i (1 : ℝ)) 1 1
        (∑ i ∈ Finset.range (n + 1), f i * D0 (Pi.single i 1) 0)
        (∑ i ∈ Finset.range (n + 1), f i * Dn (Pi.single i 1) 0) := by
    rw [cubicInterp_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [cardinalBasis, ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rfl
  rw [hsum, show f'0 • cardinalBasis n x (n + 1) = cubicInterp n x (f'0 • (0 : ℕ → ℝ)) 1 1
      (f'0 * D0 0 1) (f'0 * Dn 0 0) by
        rw [cubicInterp_smul, cardinalBasis, ite_eq_right (by omega), ite_eq_left rfl]; rfl,
    show f'n • cardinalBasis n x (n + 2) = cubicInterp n x (f'n • (0 : ℕ → ℝ)) 1 1
      (f'n * D0 0 0) (f'n * Dn 0 1) by
        rw [cubicInterp_smul, cardinalBasis, ite_eq_right (by omega), ite_eq_right (by omega)]; rfl,
    ← cubicInterp_add, ← cubicInterp_add, clampedInterp]
  have hD0 : ∑ i ∈ Finset.range (n + 1), f i * D0 (Pi.single i 1) 0 + f'0 * D0 0 1 + f'n * D0 0 0
      = D0 f f'0 := by
    have : ∀ i, f i * D0 (Pi.single i 1) 0
        = 6 / (x 1 - x 0) / (x 1 - x 0)
          * (f i * ((Pi.single i 1 : ℕ → ℝ) 1 - (Pi.single i 1 : ℕ → ℝ) 0)) := by
      intro i; simp only [hD0def]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_mul_single_sub_single hn (Nat.zero_le n)]
    simp only [hD0def, Pi.zero_apply]
    ring
  have hDn : ∑ i ∈ Finset.range (n + 1), f i * Dn (Pi.single i 1) 0 + f'0 * Dn 0 0 + f'n * Dn 0 1
      = Dn f f'n := by
    have : ∀ i, f i * Dn (Pi.single i 1) 0
        = -(6 / (x n - x (n - 1)) / (x n - x (n - 1)))
          * (f i * ((Pi.single i 1 : ℕ → ℝ) n - (Pi.single i 1 : ℕ → ℝ) (n - 1))) := by
      intro i; simp only [hDndef]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_mul_single_sub_single le_rfl (Nat.sub_le n 1)]
    simp only [hDndef, Pi.zero_apply]
    ring
  rw [hD0, hDn]
  refine cubicInterp_congr hn fun i hi => ?_
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    Pi.zero_apply, mul_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_range]
  rw [ite_eq_left (by omega)]

end Cardinal

/-!
### Calculus of $C^2$ functions on a compact interval

The derivatives of a function $f$ of class $C^2$ on $[a, b]$ are the derivatives within $[a, b]$:
$f'$ is `derivWithin f (Set.Icc a b)` and $f''$ is `iteratedDerivWithin 2 f (Set.Icc a b)`. At
interior points they are the ordinary derivatives, and both are continuous on $[a, b]$.
-/

section C2

variable {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ 2 f (Icc a b))
include hab hf

/-- Let $a < b$, and let $f$ be of class $C^2$ on $[a, b]$. Then the derivative of $f$ within
$[a, b]$ is of class $C^1$ on $[a, b]$. -/
theorem contDiffOn_derivWithin_of_contDiffOn_two :
    ContDiffOn ℝ 1 (derivWithin f (Icc a b)) (Icc a b) := by
  have := hf
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
    contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)] at this
  exact this.2.2

/-- Let $a < b$, and let $f$ be of class $C^2$ on $[a, b]$. Then the derivative of $f$ within
$[a, b]$ is continuous on $[a, b]$. -/
theorem continuousOn_derivWithin_of_contDiffOn_two :
    ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
  (contDiffOn_derivWithin_of_contDiffOn_two hab hf).continuousOn

/-- Let $a < b$, and let $f$ be of class $C^2$ on $[a, b]$. Then the second derivative of $f$ within
$[a, b]$ is continuous on $[a, b]$. -/
theorem continuousOn_iteratedDerivWithin_two :
    ContinuousOn (iteratedDerivWithin 2 f (Icc a b)) (Icc a b) :=
  hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hab)

omit hab in
/-- Let $f$ be of class $C^2$ on $[a, b]$. At every $t \in (a, b)$, $f$ has the ordinary derivative
`derivWithin f (Set.Icc a b) t`. -/
theorem hasDerivAt_of_contDiffOn_two {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt f (derivWithin f (Icc a b) t) t :=
  ((hf.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Let $a < b$, and let $f$ be of class $C^2$ on $[a, b]$. At every $t \in (a, b)$, the derivative
of $f$ within $[a, b]$ has the ordinary derivative `iteratedDerivWithin 2 f (Set.Icc a b) t`. -/
theorem hasDerivAt_derivWithin_of_contDiffOn_two {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (derivWithin f (Icc a b)) (iteratedDerivWithin 2 f (Icc a b) t) t := by
  rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]
  exact (((contDiffOn_derivWithin_of_contDiffOn_two hab hf).differentiableOn (by norm_num) t
    (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Let $a < b$, and let $f$ be of class $C^2$ on $[a, b]$. At every $t \in (a, b)$, the ordinary
second derivative of $f$ equals the second derivative of $f$ within $[a, b]$. -/
theorem iteratedDeriv_two_eq_iteratedDerivWithin_of_contDiffOn {t : ℝ} (ht : t ∈ Ioo a b) :
    iteratedDeriv 2 f t = iteratedDerivWithin 2 f (Icc a b) t :=
  (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    (hf.contDiffAt (Icc_mem_nhds ht.1 ht.2)) (Ioo_subset_Icc_self ht)).symm

end C2

/-! ### Holladay's identity and the minimum-norm property -/

section Holladay

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f s g : ℝ → ℝ}
  (hf : ContDiffOn ℝ 2 f (Icc a b)) (hs : IsCubicInterp a b n x (fun i => f (x i)) s)
  (hg : IsCubicSpline a b n x g)
include hx hn hf hs hg

/-- **Holladay's identity on one panel.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, let $s$ be an interpolatory cubic spline of
the values $f(x_0), \dots, f(x_n)$, and let $g$ be a cubic spline. Then for $1 \le i \le n$,
$$\int_{x_{i-1}}^{x_i} (f'' - s'') g'' \, dt = \Big[ (f' - s') g'' \Big]_{x_{i-1}}^{x_i}.$$
All derivatives are taken within $[a, b]$.

The proof integrates by parts. The term $\int (f' - s') g'''$ vanishes, because $g'''$ is
constant on the panel and $f - s$ vanishes at its ends. -/
theorem integral_sub_deriv2_mul_deriv2_panel {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∫ t in (x (i - 1))..(x i), (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 g (Icc a b) t
    = (derivWithin f (Icc a b) (x i) - derivWithin s (Icc a b) (x i))
        * iteratedDerivWithin 2 g (Icc a b) (x i)
      - (derivWithin f (Icc a b) (x (i - 1)) - derivWithin s (Icc a b) (x (i - 1)))
        * iteratedDerivWithin 2 g (Icc a b) (x (i - 1)) := by
  have hab := hx.lt_of_pos hn
  have huv : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hsubo : Ioo (x (i - 1)) (x i) ⊆ Ioo a b :=
    Ioo_subset_Ioo (hx.left_le (by omega)) (hx.le_right hin)
  obtain ⟨p, hpd, hpe⟩ := hg.piecewise i hi1 hin
  -- the third derivative of the panel cubic is a constant `c`
  set c : ℝ := (derivative (derivative (derivative p))).coeff 0 with hc
  have hc' : ∀ t, (derivative (derivative (derivative p))).eval t = c := by
    intro t
    have hdeg : (derivative (derivative (derivative p))).natDegree = 0 := by
      have h0 : p.natDegree ≤ 3 := natDegree_le_of_degree_le hpd
      have h1 : (derivative p).natDegree ≤ 2 := (natDegree_derivative_le p).trans (by omega)
      have h2 : (derivative (derivative p)).natDegree ≤ 1 :=
        (natDegree_derivative_le _).trans (by omega)
      have h3 : (derivative (derivative (derivative p))).natDegree ≤ 0 :=
        (natDegree_derivative_le _).trans (by omega)
      omega
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C]
  -- the second derivative of `g` on the panel
  have hG2 : ∀ t ∈ Icc (x (i - 1)) (x i),
      iteratedDerivWithin 2 g (Icc a b) t = (derivative (derivative p)).eval t :=
    fun t ht => (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hg.contDiffOn huv hsub hpe ht).2
  have hG2' : ∀ t ∈ Ioo (x (i - 1)) (x i), HasDerivAt (iteratedDerivWithin 2 g (Icc a b)) c t := by
    intro t ht
    have : iteratedDerivWithin 2 g (Icc a b) =ᶠ[𝓝 t]
        fun t => (derivative (derivative p)).eval t := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hG2 u (Ioo_subset_Icc_self hu)
    rw [← hc' t]
    exact ((derivative (derivative p)).hasDerivAt t).congr_of_eventuallyEq this
  -- continuity of the pieces on the closed panel
  have hF1c := (continuousOn_derivWithin_of_contDiffOn_two hab hf).mono hsub
  have hF2c := (continuousOn_iteratedDerivWithin_two hab hf).mono hsub
  have hS1c := (continuousOn_derivWithin_of_contDiffOn_two hab hs.contDiffOn).mono hsub
  have hS2c := (continuousOn_iteratedDerivWithin_two hab hs.contDiffOn).mono hsub
  have hG2c := (continuousOn_iteratedDerivWithin_two hab hg.contDiffOn).mono hsub
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := fun t => derivWithin f (Icc a b) t - derivWithin s (Icc a b) t)
    (v := iteratedDerivWithin 2 g (Icc a b))
    (u' := fun t => iteratedDerivWithin 2 f (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t)
    (v' := fun _ => c) (a := x (i - 1)) (b := x i)
    (by rw [uIcc_of_le huv.le]; exact hF1c.sub hS1c) (by rw [uIcc_of_le huv.le]; exact hG2c)
    (fun t ht => by
      rw [min_eq_left huv.le, max_eq_right huv.le] at ht
      exact ((hasDerivAt_derivWithin_of_contDiffOn_two hab hf (hsubo ht)).sub
        (hasDerivAt_derivWithin_of_contDiffOn_two hab hs.contDiffOn (hsubo ht))).hasDerivWithinAt)
    (fun t ht => by
      rw [min_eq_left huv.le, max_eq_right huv.le] at ht
      exact (hG2' t ht).hasDerivWithinAt)
    (by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le huv.le]; exact hF2c.sub hS2c)
    (continuous_const.intervalIntegrable _ _)
  -- the term `∫ (f' - s') c` vanishes
  have hz : ∫ t in (x (i - 1))..(x i), (derivWithin f (Icc a b) t - derivWithin s (Icc a b) t) * c
      = 0 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv.le (f := fun t => f t - s t)
        ((hf.continuousOn.mono hsub).sub (hs.contDiffOn.continuousOn.mono hsub))
        (fun t ht => ((hasDerivAt_of_contDiffOn_two hf (hsubo ht)).sub
          (hasDerivAt_of_contDiffOn_two hs.contDiffOn (hsubo ht))).hasDerivWithinAt)
        (by
          refine ContinuousOn.intervalIntegrable ?_
          rw [uIcc_of_le huv.le]; exact hF1c.sub hS1c)]
    rw [hs.interp i hin, hs.interp (i - 1) (by omega)]
    ring
  rw [hz] at hibp
  linarith

/-- **Holladay's identity, summed over the panels.** Let $a = x_0 < \dots < x_n = b$ be a partition
with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, let $s$ be an interpolatory cubic spline
of the values $f(x_0), \dots, f(x_n)$, and let $g$ be a cubic spline. Then
$$\int_a^b (f'' - s'') g'' \, dt = \Big[ (f' - s') g'' \Big]_a^b.$$
All derivatives are taken within $[a, b]$. -/
theorem integral_sub_deriv2_mul_deriv2_eq :
    ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t)
      * iteratedDerivWithin 2 g (Icc a b) t
    = (derivWithin f (Icc a b) b - derivWithin s (Icc a b) b) * iteratedDerivWithin 2 g (Icc a b) b
      - (derivWithin f (Icc a b) a - derivWithin s (Icc a b) a)
        * iteratedDerivWithin 2 g (Icc a b) a := by
  have hab := hx.lt_of_pos hn
  set G : ℝ → ℝ := fun t => (iteratedDerivWithin 2 f (Icc a b) t
    - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 g (Icc a b) t with hG
  have hGc : ContinuousOn G (Icc a b) :=
    ((continuousOn_iteratedDerivWithin_two hab hf).sub
      (continuousOn_iteratedDerivWithin_two hab hs.contDiffOn)).mul
      (continuousOn_iteratedDerivWithin_two hab hg.contDiffOn)
  set B : ℕ → ℝ := fun i => (derivWithin f (Icc a b) (x i) - derivWithin s (Icc a b) (x i))
    * iteratedDerivWithin 2 g (Icc a b) (x i) with hB
  have hsplit : ∫ t in a..b, G t = ∑ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), G t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals, hx.first, hx.last]
    intro k hk
    exact (hGc.mono (hx.Icc_subset hk)).intervalIntegrable_of_Icc (hx.step k hk).le
  have hpanel : ∀ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), G t = B (k + 1) - B k := by
    intro k hk
    have := integral_sub_deriv2_mul_deriv2_panel hx hn hf hs hg (i := k + 1) (by omega)
      (Finset.mem_range.mp hk)
    simpa using this
  rw [hsplit, Finset.sum_congr rfl hpanel, Finset.sum_range_sub B n, hB]
  simp only [hx.first, hx.last]

omit hg in
/-- **Holladay's orthogonality identity**: let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and let $s$ be an interpolatory cubic spline
of the values $f(x_0), \dots, f(x_n)$ that is either natural ($s''(a) = s''(b) = 0$) or clamped
($s'(a) = f'(a)$ and $s'(b) = f'(b)$). Then
$$\int_a^b (f'' - s'') s'' \, dt = 0.$$
This is Exercise 8.11 of [quarteroni2000numerical].

All derivatives are taken within $[a, b]$. Under either end condition the boundary terms
$[(f' - s') s'']_a^b$ of `Spline.integral_sub_deriv2_mul_deriv2_eq` vanish. -/
theorem integral_sub_deriv2_mul_deriv2_eq_zero
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b)) :
    ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t)
      * iteratedDerivWithin 2 s (Icc a b) t = 0 := by
  rw [integral_sub_deriv2_mul_deriv2_eq hx hn hf hs hs.toIsCubicSpline]
  rcases hend with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]; ring
  · rw [h0, h1]; ring

omit hg in
/-- **Pythagoras for a natural or clamped interpolatory spline.** Under the hypotheses of
`Spline.integral_sub_deriv2_mul_deriv2_eq_zero`,
$$\int_a^b (f'')^2 \, dt = \int_a^b (f'' - s'')^2 \, dt + \int_a^b (s'')^2 \, dt,$$
with derivatives within $[a, b]$. It follows from $\int (f'')^2 = \int (f'' - s'')^2 + \int
(s'')^2 + 2 \int (f'' - s'') s''$ and the orthogonality identity. -/
theorem integral_sq_deriv2_eq_add
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b)) :
    ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2
      = (∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 s (Icc a b) t) ^ 2)
        + ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2 := by
  have hab := hx.lt_of_pos hn
  have hF2c := continuousOn_iteratedDerivWithin_two hab hf
  have hS2c := continuousOn_iteratedDerivWithin_two hab hs.contDiffOn
  have horth := integral_sub_deriv2_mul_deriv2_eq_zero hx hn hf hs hend
  have hint : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) →
      IntervalIntegrable g MeasureTheory.volume a b :=
    fun g hg => hg.intervalIntegrable_of_Icc hab.le
  have hexp : ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2
      = (∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 s (Icc a b) t) ^ 2)
        + (∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2)
        + 2 * ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 s (Icc a b) t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact hint _ (((hF2c.sub hS2c).pow 2).add (hS2c.pow 2))
    · exact hint _ (continuousOn_const.mul ((hF2c.sub hS2c).mul hS2c))
    · exact hint _ ((hF2c.sub hS2c).pow 2)
    · exact hint _ (hS2c.pow 2)
  rw [hexp, horth, mul_zero, add_zero]

omit hg in
/-- **The minimum-norm property for a natural or clamped interpolatory spline.** Under the
hypotheses of `Spline.integral_sub_deriv2_mul_deriv2_eq_zero`,
$$\int_a^b (s'')^2 \, dt \le \int_a^b (f'')^2 \, dt,$$
with derivatives within $[a, b]$. This is Property 8.2 of [quarteroni2000numerical] (Holladay).
It follows from `Spline.integral_sq_deriv2_eq_add`. -/
theorem integral_sq_deriv2_le_of_end
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b)) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2 := by
  have hab := hx.lt_of_pos hn
  rw [integral_sq_deriv2_eq_add hx hn hf hs hend]
  have : 0 ≤ ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 s (Icc a b) t) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun t _ => sq_nonneg _
  linarith

omit hg in
/-- **Equality in the minimum-norm property forces $f = s$.** Under the hypotheses of
`Spline.integral_sub_deriv2_mul_deriv2_eq_zero`, if $\int_a^b (s'')^2 = \int_a^b (f'')^2$, then
$f = s$ on $[a, b]$.

The equality gives $f'' = s''$ on $[a, b]$, so $f - s$ is affine. It vanishes at the
$n + 1 \ge 2$ nodes, hence on $[a, b]$. -/
theorem eqOn_of_integral_sq_deriv2_eq
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b))
    (heq : ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2) : EqOn f s (Icc a b) := by
  have hab := hx.lt_of_pos hn
  have hF2c := continuousOn_iteratedDerivWithin_two hab hf
  have hS2c := continuousOn_iteratedDerivWithin_two hab hs.contDiffOn
  have hint : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) →
      IntervalIntegrable g MeasureTheory.volume a b :=
    fun g hg => hg.intervalIntegrable_of_Icc hab.le
  -- the integral of `(f'' - s'')²` vanishes
  have hzero : ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 s (Icc a b) t) ^ 2 = 0 := by
    have hexp := integral_sq_deriv2_eq_add hx hn hf hs hend
    linarith
  -- hence `f'' = s''` on `[a, b]`
  have hFS : EqOn (iteratedDerivWithin 2 f (Icc a b)) (iteratedDerivWithin 2 s (Icc a b))
      (Icc a b) := by
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (hint _ ((hF2c.sub hS2c).pow 2))).mp hzero
    have hsq : EqOn (fun t => (iteratedDerivWithin 2 f (Icc a b) t
        - iteratedDerivWithin 2 s (Icc a b) t) ^ 2) 0 (Ioc a b) :=
      MeasureTheory.Measure.eqOn_of_ae_eq hae (((hF2c.sub hS2c).pow 2).mono Ioc_subset_Icc_self)
        continuousOn_const (by rw [interior_Ioc, closure_Ioo hab.ne]; exact Ioc_subset_Icc_self)
    have hIoo : EqOn (iteratedDerivWithin 2 f (Icc a b)) (iteratedDerivWithin 2 s (Icc a b))
        (Ioo a b) := fun t ht => by
      have := hsq (Ioo_subset_Ioc_self ht)
      simp only [Pi.zero_apply, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        sub_eq_zero] at this
      exact this
    exact hIoo.of_subset_closure hF2c hS2c Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  -- `e = f - s` has `e'' = 0` inside, so `e'` is constant inside, and it vanishes somewhere
  set e : ℝ → ℝ := fun t => f t - s t with he
  set E1 : ℝ → ℝ := fun t => derivWithin f (Icc a b) t - derivWithin s (Icc a b) t with hE1
  have hec : ContinuousOn e (Icc a b) := hf.continuousOn.sub hs.contDiffOn.continuousOn
  have hed : ∀ t ∈ Ioo a b, HasDerivAt e (E1 t) t := fun t ht =>
    (hasDerivAt_of_contDiffOn_two hf ht).sub (hasDerivAt_of_contDiffOn_two hs.contDiffOn ht)
  have hE1d : ∀ t ∈ Ioo a b, HasDerivAt E1 0 t := fun t ht => by
    have := (hasDerivAt_derivWithin_of_contDiffOn_two hab hf ht).sub
      (hasDerivAt_derivWithin_of_contDiffOn_two hab hs.contDiffOn ht)
    rwa [hFS (Ioo_subset_Icc_self ht), sub_self] at this
  have hea : e a = 0 := by
    simp only [he, ← hx.first]
    rw [hs.interp 0 (Nat.zero_le n), sub_self]
  have heb : e b = 0 := by
    simp only [he, ← hx.last]
    rw [hs.interp n le_rfl, sub_self]
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hab hec (hea.trans heb.symm) hed
  have hE1const : ∀ t ∈ Ioo a b, E1 t = 0 := fun t ht => by
    rw [← hξ0]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun u hu => (hE1d u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hE1d u hu).deriv) ht hξ
  -- so `e` is constant on `[a, b]`, equal to `e a = 0`
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact sub_eq_zero.mp hea
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope e hat (hec.mono (Icc_subset_Icc le_rfl ht.2))
    (fun u hu => (hed u ⟨hu.1, hu.2.trans_le ht.2⟩).differentiableAt.differentiableWithinAt)
  rw [(hed c ⟨hc.1, hc.2.trans_le ht.2⟩).deriv, hE1const c ⟨hc.1, hc.2.trans_le ht.2⟩, hea,
    sub_zero, eq_comm, div_eq_zero_iff] at hc'
  rcases hc' with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (sub_ne_zero.mpr hat.ne')

end Holladay

section HolladayNamed

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℝ → ℝ}
  (hf : ContDiffOn ℝ 2 f (Icc a b))
include hx hn

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let
$f : \mathbb{R} \to \mathbb{R}$. The natural cubic spline $s$ of the values
$f(x_0), \dots, f(x_n)$ is an interpolatory cubic spline of these values, and its second
derivative within $[a, b]$ vanishes at $a$ and at $b$. -/
theorem isCubicInterp_naturalInterp_and_end :
    IsCubicInterp a b n x (fun i => f (x i)) (naturalInterp n x fun i => f (x i)) ∧
      iteratedDerivWithin 2 (naturalInterp n x fun i => f (x i)) (Icc a b) a = 0 ∧
      iteratedDerivWithin 2 (naturalInterp n x fun i => f (x i)) (Icc a b) b = 0 := by
  have hab := hx.lt_of_pos hn
  have hc : ContDiff ℝ 2 (naturalInterp n x fun i => f (x i)) :=
    contDiff_cubicInterp hx hn (f := fun i => f (x i)) (d0 := 0) (dn := 0) le_rfl zero_le_one
      le_rfl zero_le_one
  obtain ⟨h0, h1⟩ := iteratedDeriv_two_naturalInterp_endpoints hx hn (f := fun i => f (x i))
  refine ⟨(isCubicInterp_cubicInterp hx hn le_rfl zero_le_one le_rfl zero_le_one).1, ?_, ?_⟩
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hc.contDiffAt
      (left_mem_Icc.mpr hab.le)]
    exact h0
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hc.contDiffAt
      (right_mem_Icc.mpr hab.le)]
    exact h1

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let
$f : \mathbb{R} \to \mathbb{R}$. Let $s$ be the clamped cubic spline of the values
$f(x_0), \dots, f(x_n)$ with the end slopes $f'(a)$ and $f'(b)$, where $f'$ is the derivative
within $[a, b]$. Then $s$ is an interpolatory cubic spline of these values, and the derivative
of $s$ within $[a, b]$ is $f'(a)$ at $a$ and $f'(b)$ at $b$. -/
theorem isCubicInterp_clampedInterp_and_end :
    IsCubicInterp a b n x (fun i => f (x i)) (clampedInterp n x (fun i => f (x i))
        (derivWithin f (Icc a b) a) (derivWithin f (Icc a b) b)) ∧
      derivWithin (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
        (derivWithin f (Icc a b) b)) (Icc a b) a = derivWithin f (Icc a b) a ∧
      derivWithin (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
        (derivWithin f (Icc a b) b)) (Icc a b) b = derivWithin f (Icc a b) b := by
  have hab := hx.lt_of_pos hn
  have hc : ContDiff ℝ 2 (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
      (derivWithin f (Icc a b) b)) :=
    contDiff_cubicInterp hx hn (f := fun i => f (x i))
      (d0 := 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - derivWithin f (Icc a b) a))
      (dn := 6 / (x n - x (n - 1)) * (derivWithin f (Icc a b) b
        - (f (x n) - f (x (n - 1))) / (x n - x (n - 1)))) zero_le_one le_rfl zero_le_one le_rfl
  obtain ⟨h0, h1⟩ := deriv_clampedInterp_endpoints hx hn (f := fun i => f (x i))
    (derivWithin f (Icc a b) a) (derivWithin f (Icc a b) b)
  refine ⟨(isCubicInterp_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl).1, ?_, ?_⟩
  · rw [(hc.differentiable (by norm_num) a).derivWithin
      (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le))]
    exact h0
  · rw [(hc.differentiable (by norm_num) b).derivWithin
      (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le))]
    exact h1

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, let $s$ be of class $C^2$ on
$\mathbb{R}$, and let $\Phi : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$. Then
$\int_a^b \Phi(t, s''(t)) \, dt$ is the same for the second derivative $s''$ within $[a, b]$ and
for the ordinary second derivative. -/
theorem intervalIntegral_iteratedDerivWithin_two_eq {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s)
    (Φ : ℝ → ℝ → ℝ) :
    ∫ t in a..b, Φ t (iteratedDerivWithin 2 s (Icc a b) t)
      = ∫ t in a..b, Φ t (iteratedDeriv 2 s t) := by
  have hab := hx.lt_of_pos hn
  refine intervalIntegral.integral_congr_Ioo hab.le fun t ht => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hs.contDiffAt
    (Ioo_subset_Icc_self ht)]

include hf

/-- **The minimum-norm property of the natural spline** (Holladay): let $a = x_0 < \dots < x_n = b$
be a partition with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and let $s_3$ be the
natural cubic spline that interpolates $f$ at the nodes. Then
$$\int_a^b (s_3'')^2 \, dt \le \int_a^b (f'')^2 \, dt.$$
This is Property 8.2 of [quarteroni2000numerical].

Here $s_3''$ is the ordinary second derivative and $f''$ is the second derivative within
$[a, b]$. -/
theorem holladay :
    ∫ t in a..b, iteratedDeriv 2 (naturalInterp n x fun i => f (x i)) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2 := by
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_naturalInterp_and_end hx hn (f := f)
  rw [← intervalIntegral_iteratedDerivWithin_two_eq hx hn (contDiff_naturalInterp hx hn)
    fun _ y => y ^ 2]
  exact integral_sq_deriv2_le_of_end hx hn hf hs (Or.inl ⟨h0, h1⟩)

/-- **Equality in the minimum-norm property.** Let $a = x_0 < \dots < x_n = b$ be a partition with
$n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and let $s_3$ be the natural cubic spline that
interpolates $f$ at the nodes. Then
$$\int_a^b (s_3'')^2 \, dt = \int_a^b (f'')^2 \, dt$$
if and only if $f = s_3$ on $[a, b]$. This is the equality case of Property 8.2 of
[quarteroni2000numerical].

Here $s_3''$ is the ordinary second derivative and $f''$ is the second derivative within
$[a, b]$. -/
theorem holladay_eq_iff :
    ∫ t in a..b, iteratedDeriv 2 (naturalInterp n x fun i => f (x i)) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2
    ↔ EqOn f (naturalInterp n x fun i => f (x i)) (Icc a b) := by
  have hab := hx.lt_of_pos hn
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_naturalInterp_and_end hx hn (f := f)
  rw [← intervalIntegral_iteratedDerivWithin_two_eq hx hn (contDiff_naturalInterp hx hn)
    fun _ y => y ^ 2]
  constructor
  · exact eqOn_of_integral_sq_deriv2_eq hx hn hf hs (Or.inl ⟨h0, h1⟩)
  · intro heq
    refine intervalIntegral.integral_congr_Ioo hab.le fun t ht => ?_
    rw [Filter.EventuallyEq.iteratedDerivWithin_eq (x := t) (s := Icc a b) (n := 2)
      (f := naturalInterp n x fun i => f (x i)) (g := f)
      (eventually_nhdsWithin_of_forall fun u hu => (heq hu).symm)
      (heq (Ioo_subset_Icc_self ht)).symm]

/-- **The minimum-norm property of the clamped spline**: let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 1$, let $f$ be of class $C^2$ on $[a, b]$, and let $s_f$ be the cubic
spline that interpolates $f$ at the nodes with $s_f'(a) = f'(a)$ and $s_f'(b) = f'(b)$. Then
$$\int_a^b (s_f'')^2 \, dt \le \int_a^b (f'')^2 \, dt.$$
This is Exercise 8.11 of [quarteroni2000numerical].

Here $s_f''$ is the ordinary second derivative, and $f'$ and $f''$ are the derivatives within
$[a, b]$. The spline $s_f$ is `Spline.clampedInterp`. -/
theorem holladay_clamped :
    ∫ t in a..b, iteratedDeriv 2 (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
        (derivWithin f (Icc a b) b)) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2 := by
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_clampedInterp_and_end hx hn (f := f)
  rw [← intervalIntegral_iteratedDerivWithin_two_eq hx hn (contDiff_clampedInterp hx hn _ _)
    fun _ y => y ^ 2]
  exact integral_sq_deriv2_le_of_end hx hn hf hs (Or.inr ⟨h0, h1⟩)

/-- **The clamped spline gives the best $L^2$ approximation of $f''$ by second derivatives of cubic
splines.** Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, let $f$ be of class
$C^2$ on $[a, b]$, let $s_f$ be the clamped cubic spline that interpolates $f$ at the nodes with
$s_f'(a) = f'(a)$ and $s_f'(b) = f'(b)$, and let $g$ be a cubic spline on the partition. Then
$$\int_a^b (f'' - s_f'')^2 \, dt \le \int_a^b (f'' - g'')^2 \, dt.$$
This is the display after Property 8.2 in §8.6.1 of [quarteroni2000numerical].

All derivatives are taken within $[a, b]$. The cross term $\int (f'' - s_f'')(s_f'' - g'')$
vanishes by Holladay's identity, whose boundary terms vanish under the clamped end conditions. -/
theorem integral_sq_sub_deriv2_clampedInterp_le {g : ℝ → ℝ} (hg : IsCubicSpline a b n x g) :
    ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
        - iteratedDerivWithin 2 (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
            (derivWithin f (Icc a b) b)) (Icc a b) t) ^ 2
      ≤ ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
          - iteratedDerivWithin 2 g (Icc a b) t) ^ 2 := by
  have hab := hx.lt_of_pos hn
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_clampedInterp_and_end hx hn (f := f)
  set sf := clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
    (derivWithin f (Icc a b) b) with hsf
  have hF2c := continuousOn_iteratedDerivWithin_two hab hf
  have hS2c := continuousOn_iteratedDerivWithin_two hab hs.contDiffOn
  have hG2c := continuousOn_iteratedDerivWithin_two hab hg.contDiffOn
  have hint : ∀ u : ℝ → ℝ, ContinuousOn u (Icc a b) →
      IntervalIntegrable u MeasureTheory.volume a b :=
    fun u hu => hu.intervalIntegrable_of_Icc hab.le
  -- the two orthogonality identities
  have ho1 := integral_sub_deriv2_mul_deriv2_eq hx hn hf hs hs.toIsCubicSpline
  have ho2 := integral_sub_deriv2_mul_deriv2_eq hx hn hf hs hg
  rw [h0, h1, sub_self, sub_self, zero_mul, zero_mul, sub_zero] at ho1 ho2
  have hcross : ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 sf (Icc a b) t)
      * (iteratedDerivWithin 2 sf (Icc a b) t - iteratedDerivWithin 2 g (Icc a b) t) = 0 := by
    rw [← sub_eq_zero.mpr (ho1.trans ho2.symm), ← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact hint _ ((hF2c.sub hS2c).mul hS2c)
    · exact hint _ ((hF2c.sub hS2c).mul hG2c)
  have hexp : ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
        - iteratedDerivWithin 2 g (Icc a b) t) ^ 2
      = (∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 sf (Icc a b) t) ^ 2)
        + (∫ t in a..b, (iteratedDerivWithin 2 sf (Icc a b) t
            - iteratedDerivWithin 2 g (Icc a b) t) ^ 2)
        + 2 * ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 sf (Icc a b) t)
            * (iteratedDerivWithin 2 sf (Icc a b) t - iteratedDerivWithin 2 g (Icc a b) t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact hint _ (((hF2c.sub hS2c).pow 2).add ((hS2c.sub hG2c).pow 2))
    · exact hint _ (continuousOn_const.mul ((hF2c.sub hS2c).mul (hS2c.sub hG2c)))
    · exact hint _ ((hF2c.sub hS2c).pow 2)
    · exact hint _ ((hS2c.sub hG2c).pow 2)
  rw [hexp, hcross, mul_zero, add_zero]
  have : 0 ≤ ∫ t in a..b, (iteratedDerivWithin 2 sf (Icc a b) t
      - iteratedDerivWithin 2 g (Icc a b) t) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun t _ => sq_nonneg _
  linarith

end HolladayNamed

/-!
### Vector-valued data and affine equivariance

The interpolatory cubic spline of data in a real vector space $E$ is built by the same formulas,
with moments in $E$ and the moment matrix acting through its entries. The parametric splines of §8.7
of [quarteroni2000numerical] are made of it, and its affine equivariance
(`Spline.cubicInterpVec_affine`) is the geometric invariance of the cumulative-length spline.
-/

section Vec

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The panel cubic with the data $P_j$ and the moments $M_j$ in $E$:
$$\frac{(x_i - t)^3}{6 h_i} M_{i-1} + \frac{(t - x_{i-1})^3}{6 h_i} M_i + \frac{t -
  x_{i-1}}{h_i} (P_i - P_{i-1}) - \frac{h_i}{6} (t - x_{i-1}) (M_i - M_{i-1}) + P_{i-1} -
  \frac{h_i^2}{6} M_{i-1},$$
where $h_i = x_i - x_{i-1}$. -/
noncomputable def panelCubicVec (x : ℕ → ℝ) (P M : ℕ → E) (i : ℕ) (t : ℝ) : E :=
  ((x i - t) ^ 3 / (6 * (x i - x (i - 1)))) • M (i - 1)
    + ((t - x (i - 1)) ^ 3 / (6 * (x i - x (i - 1)))) • M i
    + ((t - x (i - 1)) / (x i - x (i - 1))) • (P i - P (i - 1))
    - ((x i - x (i - 1)) / 6 * (t - x (i - 1))) • (M i - M (i - 1))
    + P (i - 1) - ((x i - x (i - 1)) ^ 2 / 6) • M (i - 1)

/-- The right-hand side of the moment system for the data $P$ in $E$:
$$d_i = \frac{6}{h_i + h_{i+1}} \left( \frac{1}{h_{i+1}} (P_{i+1} - P_i) - \frac{1}{h_i} (P_i -
  P_{i-1}) \right)$$
for $0 < i < n$, and the closure values $d_0, d_n \in E$ at $i = 0$ and $i = n$. -/
noncomputable def momentRhsVec (n : ℕ) (h : ℕ → ℝ) (P : ℕ → E) (d0 dn : E) : Fin (n + 1) → E :=
  fun i =>
    if (i : ℕ) = 0 then d0 else if (i : ℕ) = n then dn
    else (6 / (h i + h (i + 1))) • ((1 / h (i + 1)) • (P (i + 1) - P i)
      - (1 / h i) • (P i - P (i - 1)))

/-- The moment vector for the data $P$ in $E$: its $i$-th entry is $\sum_j (A^{-1})_{ij} d_j$, where
$A$ is the moment matrix and $d$ is `Spline.momentRhsVec`, and it is extended by zero to
$\mathbb{N}$. -/
noncomputable def momentVecVec (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E) :
    ℕ → E :=
  extendFin fun i : Fin (n + 1) => ∑ j, (momentMatrix n (panelLength x) lam0 mun)⁻¹ i j •
    momentRhsVec n (panelLength x) P d0 dn j

/-- The **interpolatory cubic spline of data in a real vector space** $E$: for data
$P_0, \dots, P_n \in E$ and a closure of type (8.48) with the parameters
$\lambda_0, \mu_n \in \mathbb{R}$ and the values $d_0, d_n \in E$, the glued function of the
panel cubics `Spline.panelCubicVec` with the moments `Spline.momentVecVec`. For real data it is
the spline `Spline.cubicInterp`, by `Spline.cubicInterpVec_real`. -/
noncomputable def cubicInterpVec (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E) :
    ℝ → E :=
  panelGlue n x (panelCubicVec x P (momentVecVec n x P lam0 mun d0 dn))

/-- For real data, the vector-valued interpolatory spline is the real interpolatory spline
`Spline.cubicInterp`. -/
theorem cubicInterpVec_real (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn : ℝ) :
    cubicInterpVec n x f lam0 mun d0 dn = cubicInterp n x f lam0 mun d0 dn := by
  have hM : momentVecVec n x f lam0 mun d0 dn = momentVec n x f lam0 mun d0 dn := by
    unfold momentVecVec momentVec
    congr 1
    funext i
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp only [momentRhsVec, momentRhs, smul_eq_mul]
    split_ifs <;> ring
  funext t
  simp only [cubicInterpVec, cubicInterp, cubicSplineFun, panelGlue, hM, panelCubicVec,
    panelCubic_apply, smul_eq_mul]
  ring

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The right-hand side of the moment system is affinely equivariant: for a linear map $L : E \to F$
and $c \in F$, the right-hand side for the data $L(P_i) + c$ and the closure values
$L(d_0), L(d_n)$ is $L$ applied entrywise to the right-hand side for $P$, $d_0$, $d_n$. The
shift by $c$ cancels. -/
theorem momentRhsVec_affine (n : ℕ) (h : ℕ → ℝ) (P : ℕ → E) (d0 dn : E) (L : E →ₗ[ℝ] F) (c : F) :
    momentRhsVec n h (fun i => L (P i) + c) (L d0) (L dn)
      = fun i => L (momentRhsVec n h P d0 dn i) := by
  funext i
  simp only [momentRhsVec]
  split_ifs
  · rfl
  · rfl
  · simp only [map_smul, map_sub, add_sub_add_right_eq_sub]

/-- The moment vector is affinely equivariant: for a linear map $L : E \to F$ and $c \in F$, the
moment vector for the data $L(P_i) + c$ and the closure values $L(d_0), L(d_n)$ is $L$ applied
entrywise to the moment vector for $P$, $d_0$, $d_n$. -/
theorem momentVecVec_affine (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E)
    (L : E →ₗ[ℝ] F) (c : F) :
    momentVecVec n x (fun i => L (P i) + c) lam0 mun (L d0) (L dn)
      = fun i => L (momentVecVec n x P lam0 mun d0 dn i) := by
  funext i
  unfold momentVecVec
  rw [momentRhsVec_affine]
  rcases lt_or_ge i (n + 1) with hi | hi
  · rw [extendFin_of_lt _ hi, extendFin_of_lt _ hi, map_sum]
    simp only [map_smul]
  · rw [extendFin_of_le _ hi, extendFin_of_le _ hi, map_zero]

/-- **Affine equivariance of cubic spline interpolation**: let $L : E \to F$ be linear, let
$c \in F$, and let $Q = L + c$. For every $t \in \mathbb{R}$, the interpolatory spline of the
data $Q(P_0), \dots, Q(P_n)$ with the closure values $L(d_0), L(d_n)$ takes at $t$ the value
$Q(s(t)) = L(s(t)) + c$, where $s$ is the interpolatory spline of $P$ with $d_0, d_n$. This is
the geometric invariance of the cumulative-length parametric spline of §8.7 of
[quarteroni2000numerical].

The closure values are transformed by the linear part $L$ only. No hypothesis on the nodes is
needed. -/
theorem cubicInterpVec_affine (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E)
    (L : E →ₗ[ℝ] F) (c : F) (t : ℝ) :
    cubicInterpVec n x (fun i => L (P i) + c) lam0 mun (L d0) (L dn) t
      = L (cubicInterpVec n x P lam0 mun d0 dn t) + c := by
  simp only [cubicInterpVec, panelGlue, momentVecVec_affine, panelCubicVec, map_add, map_sub,
    map_smul, add_sub_add_right_eq_sub]
  abel

/-- The interpolatory spline of the constant data $P_i = c$ with the closure values $d_0 = d_n = 0$
is the constant function $c$. -/
theorem cubicInterpVec_const (n : ℕ) (x : ℕ → ℝ) (lam0 mun : ℝ) (c : E) (t : ℝ) :
    cubicInterpVec n x (fun _ => c) lam0 mun 0 0 t = c := by
  have := cubicInterpVec_affine n x (fun _ : ℕ => (0 : E)) lam0 mun 0 0 (LinearMap.id) c t
  simp only [LinearMap.id_apply, zero_add, map_zero] at this
  rw [this]
  have hz : cubicInterpVec n x (fun _ : ℕ => (0 : E)) lam0 mun 0 0 t = 0 := by
    have h0 := cubicInterpVec_affine n x (fun _ : ℕ => (0 : E)) lam0 mun 0 0 (0 : E →ₗ[ℝ] E) 0 t
    simp only [LinearMap.zero_apply, add_zero, map_zero] at h0
    exact h0
  rw [hz, zero_add]

end Vec

/-- **Affine equivariance of real cubic spline interpolation**: for $l, c \in \mathbb{R}$, the
interpolatory spline of the data $l f_i + c$ with the closure values $l d_0, l d_n$ takes at
every $t \in \mathbb{R}$ the value $l\, s(t) + c$, where $s$ is the interpolatory spline of $f$
with $d_0, d_n$. -/
theorem cubicInterp_affine (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn l c : ℝ) (t : ℝ) :
    cubicInterp n x (fun i => l * f i + c) lam0 mun (l * d0) (l * dn) t
      = l * cubicInterp n x f lam0 mun d0 dn t + c := by
  rw [← cubicInterpVec_real, ← cubicInterpVec_real]
  have := cubicInterpVec_affine n x f lam0 mun d0 dn (LinearMap.lsmul ℝ ℝ l) c t
  simpa using this

/-! ### The not-a-knot spline -/

/-- **Two cubics agreeing to third order at a point are equal.** If $p$ and $q$ are polynomials of
degree at most $3$ with $p^{(m)}(c) = q^{(m)}(c)$ for $m = 0, 1, 2, 3$, then $p = q$. -/
theorem eq_of_degree_le_three_of_deriv {p q : ℝ[X]} (hp : p.degree ≤ 3) (hq : q.degree ≤ 3) {c : ℝ}
    (h0 : p.eval c = q.eval c) (h1 : (derivative p).eval c = (derivative q).eval c)
    (h2 : (derivative (derivative p)).eval c = (derivative (derivative q)).eval c)
    (h3 : (derivative (derivative (derivative p))).eval c
      = (derivative (derivative (derivative q))).eval c) : p = q := by
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hrdeg : r.natDegree ≤ 3 :=
    natDegree_le_of_degree_le ((degree_sub_le _ _).trans (max_le hp hq))
  -- a polynomial of `natDegree 0` vanishing at `c` is zero
  have key : ∀ u : ℝ[X], u.natDegree = 0 → u.eval c = 0 → u = 0 := fun u hu hc => by
    rw [eq_C_of_natDegree_eq_zero hu] at hc ⊢
    rw [eval_C] at hc
    rw [hc, C_0]
  have e3 : derivative (derivative (derivative r)) = 0 := by
    refine key _ ?_ (by simp [hr, derivative_sub, eval_sub, h3])
    have h1' : (derivative r).natDegree ≤ 2 := (natDegree_derivative_le r).trans (by omega)
    have h2' : (derivative (derivative r)).natDegree ≤ 1 :=
      (natDegree_derivative_le _).trans (by omega)
    have h3' : (derivative (derivative (derivative r))).natDegree ≤ 0 :=
      (natDegree_derivative_le _).trans (by omega)
    omega
  have e2 : derivative (derivative r) = 0 :=
    key _ (derivative_eq_zero.mp e3) (by simp [hr, derivative_sub, eval_sub, h2])
  have e1 : derivative r = 0 := key _ (derivative_eq_zero.mp e2) (by simp [hr, eval_sub, h1])
  exact key _ (derivative_eq_zero.mp e1) (by simp [hr, eval_sub, h0])

/-- **A cubic spline is a single cubic across the node $x_i$ if and only if its third derivative has
no jump there.** Let $a = x_0 < \dots < x_n = b$ be a partition, let $s$ be a cubic spline with
the moments $M_j$, and let $1 \le i < n$. Then $s$ agrees with one polynomial of degree at most
$3$ on $[x_{i-1}, x_{i+1}]$ if and only if
$$\frac{M_i - M_{i-1}}{h_i} = \frac{M_{i+1} - M_i}{h_{i+1}}.$$
-/
theorem IsCubicSpline.exists_eqOn_Icc_two_iff (hx : IsIntervalPartition a b n x) {s : ℝ → ℝ}
    (hs : IsCubicSpline a b n x s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    (∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x (i - 1)) (x (i + 1)))) ↔
      (moment a b x s i - moment a b x s (i - 1)) / panelLength x i
        = (moment a b x s (i + 1) - moment a b x s i) / panelLength x (i + 1) := by
  set F : ℕ → ℝ := fun j => s (x j) with hF
  set M : ℕ → ℝ := moment a b x s with hM
  have h1 : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le
  have h2 : x i < x (i + 1) := hx.step i hin
  have hp1 := hs.eqOn_panelCubic hx hi1 hin.le
  have hp2 := hs.eqOn_panelCubic hx (i := i + 1) (by omega) hin
  simp only [add_tsub_cancel_right] at hp2
  have hd3 : (derivative (derivative (derivative (panelCubicPoly x F M i)))).eval (x i)
      = (M i - M (i - 1)) / panelLength x i := panelCubicD3_apply x F M h1 (x i)
  have hd3' : (derivative (derivative (derivative (panelCubicPoly x F M (i + 1))))).eval (x i)
      = (M (i + 1) - M i) / panelLength x (i + 1) := by
    have := panelCubicD3_apply x F M (i := i + 1) (by simpa using h2) (x i)
    rw [show i + 1 - 1 = i by omega] at this
    exact this
  constructor
  · rintro ⟨p, -, hpe⟩
    have hq1 : p = panelCubicPoly x F M i := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ ((Icc_infinite h1).mono fun t ht => ?_)
      exact (hpe (Icc_subset_Icc le_rfl h2.le ht)).symm.trans (hp1 ht)
    have hq2 : p = panelCubicPoly x F M (i + 1) := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ ((Icc_infinite h2).mono fun t ht => ?_)
      exact (hpe (Icc_subset_Icc h1.le le_rfl ht)).symm.trans (hp2 ht)
    rw [← hd3, ← hd3', ← hq1, ← hq2]
  · intro heq
    have hmom : IsMomentEq x F M i :=
      moment_eq_of_contDiffOn hx hs.contDiffOn (fun j hj1 hjn => hs.eqOn_panelCubic hx hj1 hjn)
        hi1 hin
    have hq : panelCubicPoly x F M i = panelCubicPoly x F M (i + 1) := by
      refine eq_of_degree_le_three_of_deriv (degree_panelCubicPoly_le _ _ _ _)
        (degree_panelCubicPoly_le _ _ _ _) (c := x i) ?_ ?_ ?_ ?_
      · exact (panelCubic_right h1).trans (panelCubic_left_succ h2).symm
      · exact (isMomentEq_iff h1 h2).mp hmom
      · exact (panelCubicD2_right h1).trans (panelCubicD2_left_succ h2).symm
      · rw [hd3, hd3']; exact heq
    refine ⟨panelCubicPoly x F M i, degree_panelCubicPoly_le _ _ _ _, ?_⟩
    rw [← Icc_union_Icc_eq_Icc h1.le h2.le]
    intro t ht
    rcases ht with ht | ht
    · exact hp1 ht
    · rw [hp2 ht, hq]
      rfl

/-- The **not-a-knot condition**: $s$ agrees with a polynomial of degree at most $3$ on $[x_0, x_2]$
and with a polynomial of degree at most $3$ on $[x_{n-2}, x_n]$. For a cubic spline this means
that $s'''$ is continuous at $x_1$ and at $x_{n-1}$
(`Spline.IsCubicSpline.exists_eqOn_Icc_two_iff`). This is the not-a-knot condition of §8.6.1 of
[quarteroni2000numerical]. -/
def IsNotAKnot (n : ℕ) (x : ℕ → ℝ) (s : ℝ → ℝ) : Prop :=
  (∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x 0) (x 2))) ∧
    ∃ q : ℝ[X], q.degree ≤ 3 ∧ EqOn s q.eval (Icc (x (n - 2)) (x n))

section NotAKnot

variable (hx : IsIntervalPartition a b n x) (hn : 3 ≤ n) {f : ℕ → ℝ}
include hx hn

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 3$, and let $s$ be an interpolatory
cubic spline of the data $f$ with the moments $M_j$. Then $s$ satisfies the not-a-knot condition
if and only if
$$M_0 = \left( 1 + \frac{h_1}{h_2} \right) M_1 - \frac{h_1}{h_2} M_2 \quad \text{and} \quad
  M_n = M_{n-1} + \frac{h_n}{h_{n-1}} (M_{n-1} - M_{n-2}).$$
-/
theorem IsCubicInterp.isNotAKnot_iff {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    IsNotAKnot n x s ↔
      moment a b x s 0 = (1 + panelLength x 1 / panelLength x 2) * moment a b x s 1
        - panelLength x 1 / panelLength x 2 * moment a b x s 2 ∧
      moment a b x s n = moment a b x s (n - 1) + panelLength x n / panelLength x (n - 1)
        * (moment a b x s (n - 1) - moment a b x s (n - 2)) := by
  have h1 := hx.panelLength_pos le_rfl (by omega)
  have h2 := hx.panelLength_pos (i := 2) (by omega) (by omega)
  have hn1 := hx.panelLength_pos (i := n - 1) (by omega) (by omega)
  have hnn := hx.panelLength_pos (i := n) (by omega) le_rfl
  have hA := hs.toIsCubicSpline.exists_eqOn_Icc_two_iff hx (i := 1) le_rfl (by omega)
  have hB := hs.toIsCubicSpline.exists_eqOn_Icc_two_iff hx (i := n - 1) (by omega) (by omega)
  simp only [Nat.sub_self, show n - 1 + 1 = n by omega, show n - 1 - 1 = n - 2 by omega] at hA hB
  rw [IsNotAKnot, hA, hB]
  constructor
  · rintro ⟨hA', hB'⟩
    rw [div_eq_iff h1.ne'] at hA'
    rw [eq_comm, div_eq_iff hnn.ne'] at hB'
    constructor
    · have : moment a b x s 0 = moment a b x s 1
          - (moment a b x s 2 - moment a b x s 1) / panelLength x 2 * panelLength x 1 := by
        linarith
      rw [this]; ring
    · have : moment a b x s n = moment a b x s (n - 1)
          + (moment a b x s (n - 1) - moment a b x s (n - 2)) / panelLength x (n - 1)
            * panelLength x n := by
        linarith
      rw [this]; ring
  · rintro ⟨hA', hB'⟩
    constructor
    · rw [hA', div_eq_div_iff h1.ne' h2.ne']; field_simp; ring
    · rw [hB', div_eq_div_iff hn1.ne' hnn.ne']; field_simp; ring

end NotAKnot

section NotAKnotExistence

variable {m : ℕ} (hx : IsIntervalPartition a b (m + 2) x) (hm : 1 ≤ m) {f : ℕ → ℝ}
include hx hm

omit hx hm in
/-- The interior moment equation at $x_i$ depends only on $M_{i-1}, M_i, M_{i+1}$: if $M$ and $N$
agree at these three indices, then the equation holds for $M$ if and only if it holds for $N$. -/
theorem isMomentEq_congr {M N : ℕ → ℝ} {i : ℕ} (h0 : M (i - 1) = N (i - 1)) (h1 : M i = N i)
    (h2 : M (i + 1) = N (i + 1)) : IsMomentEq x f M i ↔ IsMomentEq x f N i := by
  simp only [IsMomentEq, h0, h1, h2]

omit hx hm in
/-- For $j \ge 1$, the interior moment equation at the node $j$ for the shifted nodes
$x_1, x_2, \dots$, the shifted data $f_1, f_2, \dots$ and the shifted moments $M_1, M_2, \dots$
is the interior moment equation at the node $j + 1$ for the original nodes, data and moments. -/
theorem isMomentEq_shift {M : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ j) :
    IsMomentEq (fun i => x (i + 1)) (fun i => f (i + 1)) (fun i => M (i + 1)) j ↔
      IsMomentEq x f M (j + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [IsMomentEq, panelLength, add_tsub_cancel_right]

/-- **The reduced system of the not-a-knot spline.** Let $a = x_0 < \dots < x_n = b$ be a partition
with $n = m + 2$ and $m \ge 1$, and let $M$ satisfy the not-a-knot relations
$$M_0 = \left( 1 + \frac{h_1}{h_2} \right) M_1 - \frac{h_1}{h_2} M_2, \qquad M_n = M_{n-1} +
  \frac{h_n}{h_{n-1}} (M_{n-1} - M_{n-2}).$$
Then the interior moment equations at $x_1, \dots, x_{n-1}$ hold if and only if
$(M_1, \dots, M_{n-1})$ solves the moment system of the nodes $x_1 < \dots < x_{n-1}$ and the
data $f_1, \dots, f_{n-1}$ with the closure
$$\lambda_0' = \frac{2 (h_2 - h_1)}{2 h_2 + h_1}, \quad \mu_n' = \frac{2 (h_{n-1} - h_n)}{2
  h_{n-1} + h_n}, \quad d_0' = \frac{2 h_2}{2 h_2 + h_1} d_1, \quad d_n' = \frac{2 h_{n-1}}{2
  h_{n-1} + h_n} d_{n-1},$$
where $d_1$ and $d_{n-1}$ are the right-hand sides (8.47) of the original system at $x_1$ and
$x_{n-1}$. -/
theorem notAKnot_reduced_iff (M : ℕ → ℝ)
    (hM0 : M 0 = (1 + panelLength x 1 / panelLength x 2) * M 1
      - panelLength x 1 / panelLength x 2 * M 2)
    (hMn : M (m + 2) = M (m + 1)
      + panelLength x (m + 2) / panelLength x (m + 1) * (M (m + 1) - M m)) :
    (momentMatrix m (panelLength fun i => x (i + 1))
        (2 * (panelLength x 2 - panelLength x 1) / (2 * panelLength x 2 + panelLength x 1))
        (2 * (panelLength x (m + 1) - panelLength x (m + 2))
          / (2 * panelLength x (m + 1) + panelLength x (m + 2)))).mulVec
      (fun j : Fin (m + 1) => M (j + 1))
    = momentRhs m (panelLength fun i => x (i + 1)) (fun i => f (i + 1))
        (2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
          * (6 / (panelLength x 1 + panelLength x 2)
            * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1)))
        (2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
          * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
            * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
              - (f (m + 1) - f m) / panelLength x (m + 1))))
    ↔ ∀ i, 1 ≤ i → i < m + 2 → IsMomentEq x f M i := by
  have hx' : IsIntervalPartition (x 1) (x (m + 1)) m fun i => x (i + 1) :=
    ⟨fun j hj => hx.step (j + 1) (by omega), rfl, rfl⟩
  have h1 := hx.panelLength_pos le_rfl (by omega)
  have h2 := hx.panelLength_pos (i := 2) (by omega) (by omega)
  have hn1 := hx.panelLength_pos (i := m + 1) (by omega) (by omega)
  have hnn := hx.panelLength_pos (i := m + 2) (by omega) le_rfl
  rw [momentMatrix_mulVec_eq_iff hx' hm]
  have hext : ∀ j ≤ m, extendFin (fun j : Fin (m + 1) => M (j + 1)) j = M (j + 1) := fun j hj =>
    extendFin_of_lt _ (by omega)
  -- the two modified rows
  have hrow0 : 2 * M 1 + 2 * (panelLength x 2 - panelLength x 1)
      / (2 * panelLength x 2 + panelLength x 1) * M 2
      = 2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
        * (6 / (panelLength x 1 + panelLength x 2)
          * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1))
      ↔ IsMomentEq x f M 1 := by
    simp only [IsMomentEq, Nat.sub_self, hM0]
    rw [← sub_eq_zero, ← sub_eq_zero (a := _ / _ * _ + _ + _)]
    have key : panelLength x 1 / (panelLength x 1 + panelLength x (1 + 1))
        * ((1 + panelLength x 1 / panelLength x 2) * M 1 - panelLength x 1 / panelLength x 2 * M 2)
        + 2 * M 1 + panelLength x (1 + 1) / (panelLength x 1 + panelLength x (1 + 1)) * M (1 + 1)
        - 6 / (panelLength x 1 + panelLength x (1 + 1))
          * ((f (1 + 1) - f 1) / panelLength x (1 + 1) - (f 1 - f (1 - 1)) / panelLength x 1)
        = ((2 * panelLength x 2 + panelLength x 1) / (2 * panelLength x 2))
          * (2 * M 1 + 2 * (panelLength x 2 - panelLength x 1)
              / (2 * panelLength x 2 + panelLength x 1) * M 2
            - 2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
              * (6 / (panelLength x 1 + panelLength x 2)
                * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1))) := by
      simp only [Nat.reduceAdd, Nat.sub_self]
      field_simp
      ring
    rw [key, mul_eq_zero, or_iff_right (by positivity)]
  have hrowm : 2 * (panelLength x (m + 1) - panelLength x (m + 2))
      / (2 * panelLength x (m + 1) + panelLength x (m + 2)) * M m + 2 * M (m + 1)
      = 2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
        * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
          * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
            - (f (m + 1) - f m) / panelLength x (m + 1)))
      ↔ IsMomentEq x f M (m + 1) := by
    simp only [IsMomentEq, add_tsub_cancel_right, hMn]
    rw [← sub_eq_zero, ← sub_eq_zero (a := _ / _ * _ + _ + _)]
    have key : panelLength x (m + 1) / (panelLength x (m + 1) + panelLength x (m + 1 + 1)) * M m
        + 2 * M (m + 1) + panelLength x (m + 1 + 1)
          / (panelLength x (m + 1) + panelLength x (m + 1 + 1))
          * (M (m + 1) + panelLength x (m + 2) / panelLength x (m + 1) * (M (m + 1) - M m))
        - 6 / (panelLength x (m + 1) + panelLength x (m + 1 + 1))
          * ((f (m + 1 + 1) - f (m + 1)) / panelLength x (m + 1 + 1)
            - (f (m + 1) - f m) / panelLength x (m + 1))
        = ((2 * panelLength x (m + 1) + panelLength x (m + 2)) / (2 * panelLength x (m + 1)))
          * (2 * (panelLength x (m + 1) - panelLength x (m + 2))
              / (2 * panelLength x (m + 1) + panelLength x (m + 2)) * M m + 2 * M (m + 1)
            - 2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
              * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
                * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
                  - (f (m + 1) - f m) / panelLength x (m + 1)))) := by
      simp only [show m + 1 + 1 = m + 2 by omega]
      field_simp
      ring
    rw [key, mul_eq_zero, or_iff_right (by positivity)]
  constructor
  · rintro ⟨hint, h0, hN⟩ i hi1 hin
    rcases Nat.lt_or_ge i 2 with hi | hi
    · obtain rfl : i = 1 := by omega
      rw [hext 0 (by omega), hext 1 hm] at h0
      exact hrow0.mp h0
    rcases Nat.lt_or_ge i (m + 1) with hi' | hi'
    · have := hint (i - 1) (by omega) (by omega)
      rw [isMomentEq_congr (N := fun j => M (j + 1)) (hext _ (by omega)) (hext _ (by omega))
        (hext _ (by omega)), isMomentEq_shift (by omega), show i - 1 + 1 = i by omega] at this
      exact this
    · obtain rfl : i = m + 1 := by omega
      rw [hext (m - 1) (by omega), hext m le_rfl, show m - 1 + 1 = m by omega] at hN
      exact hrowm.mp hN
  · intro hint
    refine ⟨fun j hj1 hjm => ?_, ?_, ?_⟩
    · rw [isMomentEq_congr (N := fun j => M (j + 1)) (hext _ (by omega)) (hext _ (by omega))
        (hext _ (by omega)), isMomentEq_shift hj1]
      exact hint (j + 1) (by omega) (by omega)
    · rw [hext 0 (by omega), hext 1 hm]
      exact hrow0.mpr (hint 1 le_rfl (by omega))
    · rw [hext (m - 1) (by omega), hext m le_rfl, show m - 1 + 1 = m by omega]
      exact hrowm.mpr (hint (m + 1) (by omega) (by omega))

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n = m + 2$ and $m \ge 1$. Then the matrix
of the reduced not-a-knot system of `Spline.notAKnot_reduced_iff` is invertible. Its closure
parameters satisfy $|\lambda_0'| < 2$ and $|\mu_n'| < 2$, so it is strictly diagonally dominant
(`Spline.isStrictDiagDominant_momentMatrix_of_abs_lt`). -/
theorem isUnit_notAKnot_reduced :
    IsUnit (momentMatrix m (panelLength fun i => x (i + 1))
      (2 * (panelLength x 2 - panelLength x 1) / (2 * panelLength x 2 + panelLength x 1))
      (2 * (panelLength x (m + 1) - panelLength x (m + 2))
        / (2 * panelLength x (m + 1) + panelLength x (m + 2)))) := by
  have h1 := hx.panelLength_pos le_rfl (by omega)
  have h2 := hx.panelLength_pos (i := 2) (by omega) (by omega)
  have hn1 := hx.panelLength_pos (i := m + 1) (by omega) (by omega)
  have hnn := hx.panelLength_pos (i := m + 2) (by omega) le_rfl
  refine (isStrictDiagDominant_momentMatrix_of_abs_lt (fun i hi1 him => ?_) ?_ ?_).isUnit
  · simp only [panelLength]
    rw [show i - 1 + 1 = i by omega]
    exact sub_pos.mpr (hx.step i (by omega))
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * panelLength x 2 + panelLength x 1 by positivity),
      div_lt_iff₀ (by positivity), abs_mul, abs_two]
    have : |panelLength x 2 - panelLength x 1| < 2 * panelLength x 2 + panelLength x 1 :=
      abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    linarith
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * panelLength x (m + 1) + panelLength x (m + 2) by
      positivity), div_lt_iff₀ (by positivity), abs_mul, abs_two]
    have : |panelLength x (m + 1) - panelLength x (m + 2)|
        < 2 * panelLength x (m + 1) + panelLength x (m + 2) :=
      abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    linarith

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n = m + 2$ and $m \ge 1$. For all data $f$
there is an interpolatory cubic spline of $f$ that satisfies the not-a-knot condition, and any
two such splines agree on $[a, b]$. This is `Spline.existsUnique_isCubicInterp_notAKnot` with
$n$ written as $m + 2$. -/
theorem existsUnique_isCubicInterp_notAKnot_aux (f : ℕ → ℝ) :
    (∃ s, IsCubicInterp a b (m + 2) x f s ∧ IsNotAKnot (m + 2) x s) ∧
      ∀ s₁ s₂, IsCubicInterp a b (m + 2) x f s₁ → IsNotAKnot (m + 2) x s₁ →
        IsCubicInterp a b (m + 2) x f s₂ → IsNotAKnot (m + 2) x s₂ → EqOn s₁ s₂ (Icc a b) := by
  have hn : 3 ≤ m + 2 := by omega
  have hn' : 1 ≤ m + 2 := by omega
  have hab := hx.lt_of_pos hn'
  have hA := isUnit_notAKnot_reduced hx hm
  set A := momentMatrix m (panelLength fun i => x (i + 1))
    (2 * (panelLength x 2 - panelLength x 1) / (2 * panelLength x 2 + panelLength x 1))
    (2 * (panelLength x (m + 1) - panelLength x (m + 2))
      / (2 * panelLength x (m + 1) + panelLength x (m + 2))) with hAdef
  set rhs := momentRhs m (panelLength fun i => x (i + 1)) (fun i => f (i + 1))
    (2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
      * (6 / (panelLength x 1 + panelLength x 2)
        * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1)))
    (2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
      * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
        * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
          - (f (m + 1) - f m) / panelLength x (m + 1)))) with hrhsdef
  -- the not-a-knot conditions in moment form, with `n - 1 = m + 1` and `n - 2 = m`
  have hnak : ∀ s, IsCubicInterp a b (m + 2) x f s → (IsNotAKnot (m + 2) x s ↔
      moment a b x s 0 = (1 + panelLength x 1 / panelLength x 2) * moment a b x s 1
        - panelLength x 1 / panelLength x 2 * moment a b x s 2 ∧
      moment a b x s (m + 2) = moment a b x s (m + 1)
        + panelLength x (m + 2) / panelLength x (m + 1)
          * (moment a b x s (m + 1) - moment a b x s m)) := fun s hs => by
    have := hs.isNotAKnot_iff hx hn
    rwa [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl] at this
  constructor
  · -- existence
    set N : Fin (m + 1) → ℝ := A⁻¹.mulVec rhs with hNdef
    set M : ℕ → ℝ := fun i => if i = 0 then
        (1 + panelLength x 1 / panelLength x 2) * extendFin N 0
          - panelLength x 1 / panelLength x 2 * extendFin N 1
      else if i = m + 2 then
        extendFin N m + panelLength x (m + 2) / panelLength x (m + 1)
          * (extendFin N m - extendFin N (m - 1))
      else extendFin N (i - 1) with hMdef
    have hMi : ∀ i, 1 ≤ i → i ≤ m + 1 → M i = extendFin N (i - 1) := fun i hi1 hi2 => by
      simp only [hMdef, ite_eq_right (show i ≠ 0 by omega), ite_eq_right (show i ≠ m + 2 by omega)]
    have hM0 : M 0 = (1 + panelLength x 1 / panelLength x 2) * M 1
        - panelLength x 1 / panelLength x 2 * M 2 := by
      rw [hMi 1 le_rfl (by omega), hMi 2 (by omega) (by omega)]
      simp only [hMdef, ↓reduceIte]
    have hMn : M (m + 2) = M (m + 1)
        + panelLength x (m + 2) / panelLength x (m + 1) * (M (m + 1) - M m) := by
      rw [hMi (m + 1) (by omega) le_rfl, hMi m hm (by omega)]
      simp only [hMdef, ite_eq_right (show m + 2 ≠ 0 by omega), ↓reduceIte, add_tsub_cancel_right]
    have hN : (fun j : Fin (m + 1) => M (j + 1)) = N := funext fun j => by
      rw [hMi (j + 1) (by omega) (by have := j.2; omega), add_tsub_cancel_right, extendFin_val]
    have hsolve : A.mulVec N = rhs := by
      rw [hNdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
    have hint : ∀ i, 1 ≤ i → i < m + 2 → IsMomentEq x f M i :=
      (notAKnot_reduced_iff hx hm M hM0 hMn).mp (by rw [hN]; exact hsolve)
    set s := cubicSplineFun (m + 2) x f M with hsdef
    have hs : IsCubicInterp a b (m + 2) x f s :=
      ⟨⟨contDiffOn_cubicSplineFun hx hn' hint, fun i hi1 hin =>
        ⟨panelCubicPoly x f M i, degree_panelCubicPoly_le _ _ _ _, cubicSplineFun_eqOn hx hi1 hin⟩⟩,
        fun i hi => cubicSplineFun_apply_node hx hn' hi⟩
    have hmom : ∀ i ≤ m + 2, moment a b x s i = M i := fun i hi => by
      rw [moment_eq_iteratedDeriv hab (contDiff_cubicSplineFun hx hn' hint)
        ⟨hx.left_le hi, hx.le_right hi⟩, iteratedDeriv_two_cubicSplineFun_node hx hn' hint hi]
    refine ⟨s, hs, (hnak s hs).mpr ⟨?_, ?_⟩⟩
    · rw [hmom 0 (by omega), hmom 1 (by omega), hmom 2 (by omega)]; exact hM0
    · rw [hmom (m + 2) le_rfl, hmom (m + 1) (by omega), hmom m (by omega)]; exact hMn
  · -- uniqueness
    intro s₁ s₂ h₁ hk₁ h₂ hk₂
    obtain ⟨hM0₁, hMn₁⟩ := (hnak s₁ h₁).mp hk₁
    obtain ⟨hM0₂, hMn₂⟩ := (hnak s₂ h₂).mp hk₂
    have e₁ := (notAKnot_reduced_iff hx hm (moment a b x s₁) hM0₁ hMn₁).mpr
      fun i hi1 hin => h₁.isMomentEq hx hi1 hin
    have e₂ := (notAKnot_reduced_iff hx hm (moment a b x s₂) hM0₂ hMn₂).mpr
      fun i hi1 hin => h₂.isMomentEq hx hi1 hin
    have hNeq : (fun j : Fin (m + 1) => moment a b x s₁ (j + 1))
        = fun j : Fin (m + 1) => moment a b x s₂ (j + 1) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hA (e₁.trans e₂.symm)
    have hmid : ∀ i, 1 ≤ i → i ≤ m + 1 → moment a b x s₁ i = moment a b x s₂ i :=
        fun i hi1 hi2 => by
      have := congrFun hNeq (⟨i - 1, by omega⟩ : Fin (m + 1))
      simpa only [show i - 1 + 1 = i by omega] using this
    have hall : ∀ i ≤ m + 2, moment a b x s₁ i = moment a b x s₂ i := fun i hi => by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hM0₁, hM0₂, hmid 1 le_rfl (by omega), hmid 2 (by omega) (by omega)]
      rcases Nat.lt_or_ge i (m + 2) with hi' | hi'
      · exact hmid i hi0 (by omega)
      · obtain rfl : i = m + 2 := by omega
        rw [hMn₁, hMn₂, hmid (m + 1) (by omega) le_rfl, hmid m hm (by omega)]
    exact (h₁.eqOn_cubicSplineFun hx hn').trans
      ((cubicSplineFun_eqOn_of_moment_eq hx hn' hall).trans (h₂.eqOn_cubicSplineFun hx hn').symm)

end NotAKnotExistence

/-- **Existence and uniqueness of the not-a-knot cubic spline.** Let $a = x_0 < \dots < x_n = b$ be
a partition with $n \ge 3$, and let $f_0, \dots, f_n \in \mathbb{R}$. Then there is an
interpolatory cubic spline of the data $f$ that satisfies the not-a-knot condition, that is,
whose cubic pieces coincide on the first two and on the last two panels, and any two such
splines agree on $[a, b]$. This is the closure "continuity of $s'''$ at $x_1$ and $x_{n-1}$" of
§8.6.1 of [quarteroni2000numerical].

For $n = 2$ the two conditions coincide and the spline is not unique; this is why $n \ge 3$ is
needed.

The proof eliminates $M_0$ and $M_n$ through the not-a-knot conditions. This turns the moment
system into the strictly diagonally dominant reduced system of `Spline.notAKnot_reduced_iff`. -/
theorem existsUnique_isCubicInterp_notAKnot (hx : IsIntervalPartition a b n x) (hn : 3 ≤ n)
    (f : ℕ → ℝ) :
    (∃ s, IsCubicInterp a b n x f s ∧ IsNotAKnot n x s) ∧
      ∀ s₁ s₂, IsCubicInterp a b n x f s₁ → IsNotAKnot n x s₁ →
        IsCubicInterp a b n x f s₂ → IsNotAKnot n x s₂ → EqOn s₁ s₂ (Icc a b) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact existsUnique_isCubicInterp_notAKnot_aux hx (by omega) f

/-!
### The periodic spline

The periodic closure $s'(a) = s'(b)$, $s''(a) = s''(b)$ identifies the moments $M_0 = M_n$ and adds
the continuity of $s'$ across $a = b$ as an $n$-th equation. The system is cyclic: indices are read
modulo $n$, with $h_0 := h_n$.
-/

/-- The cyclic index: $\operatorname{cyc}_n(i) = i$ for $i \ne 0$, and
$\operatorname{cyc}_n(0) = n$. With it, $h_{\operatorname{cyc}_n(i)}$ is the length of the panel
before the node $x_i$ on the circle. -/
def cyc (n i : ℕ) : ℕ := if i = 0 then n else i

/-- The **cyclic moment matrix** $A$ of the periodic spline, of order $n$, with the rows and the
columns indexed by $0, \dots, n - 1$. Row $i$ is the sum of three terms: $2$ in the column $i$,
$\lambda_i = h_{i+1} / (h_i + h_{i+1})$ in the column $(i + 1) \bmod n$, and
$\mu_i = h_i / (h_i + h_{i+1})$ in the column $i - 1$ (the column $n - 1$ for $i = 0$), where
$h_0 := h_n$. For $n = 2$ the two off-diagonal terms lie in the same column and add up. This is
the cyclic system of the periodic spline in §8.6.1 of [quarteroni2000numerical].

The index $h_0 := h_n$ is implemented with `Spline.cyc`. -/
noncomputable def periodicMomentMatrix (n : ℕ) (h : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    (if j = i then 2 else 0)
      + (if (j : ℕ) = (i + 1) % n then h (i + 1) / (h (cyc n i) + h (i + 1)) else 0)
      + (if (j : ℕ) = cyc n i - 1 then h (cyc n i) / (h (cyc n i) + h (i + 1)) else 0)

/-- The right-hand side of the cyclic moment system: for $1 \le i < n$ the value $d_i$ of (8.47),
and
$$d_0 = \frac{6}{h_n + h_1} \left( \frac{f_1 - f_0}{h_1} - \frac{f_n - f_{n-1}}{h_n} \right),$$
which expresses the continuity of $s'$ across $a = b$. -/
noncomputable def periodicMomentRhs (n : ℕ) (h f : ℕ → ℝ) : Fin n → ℝ :=
  fun i => 6 / (h (cyc n i) + h (i + 1)) * ((f (i + 1) - f i) / h (i + 1)
    - (f (cyc n i) - f (cyc n i - 1)) / h (cyc n i))

/-- For $c \in \mathbb{R}$, a vector $v$ indexed by $\{0, \dots, n - 1\}$ and $k < n$,
$\sum_{j=0}^{n-1} \delta_{jk}\, c\, v_j = c\, v_k$. -/
theorem sum_ite_val_eq_mul' {n : ℕ} (c : ℝ) (v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    ∑ j : Fin n, (if (j : ℕ) = k then c else 0) * v j = c * v ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => by
    rw [ite_eq_right, zero_mul]; intro h; exact hj (Fin.ext h))
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

section Periodic

variable {h f : ℕ → ℝ}

/-- For $n \ge 1$ and $i < n$, the predecessor of the cyclic index lies below $n$:
$\operatorname{cyc}_n(i) - 1 < n$. -/
theorem cyc_sub_one_lt {i : ℕ} (hn : 1 ≤ n) (hi : i < n) : cyc n i - 1 < n := by
  unfold cyc; split_ifs <;> omega

/-- For $n \ge 1$, the cyclic moment matrix applied to a vector $v$ indexed by $\{0, \dots, n - 1\}$
is
$$(A v)_i = 2 v_i + \lambda_i v_{(i+1) \bmod n} + \mu_i v_{\operatorname{cyc}_n(i) - 1},$$
with $\lambda_i = h_{i+1} / (h_{\operatorname{cyc}_n(i)} + h_{i+1})$ and $\mu_i =
h_{\operatorname{cyc}_n(i)} / (h_{\operatorname{cyc}_n(i)} + h_{i+1})$. -/
theorem periodicMomentMatrix_mulVec_apply (hn : 1 ≤ n) (v : Fin n → ℝ) (i : Fin n) :
    (periodicMomentMatrix n h).mulVec v i
      = 2 * v i + h (i + 1) / (h (cyc n i) + h (i + 1)) * v ⟨(i + 1) % n, Nat.mod_lt _ hn⟩
        + h (cyc n i) / (h (cyc n i) + h (i + 1)) * v ⟨cyc n i - 1, cyc_sub_one_lt hn i.2⟩ := by
  simp only [Matrix.mulVec, dotProduct, periodicMomentMatrix, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib]
  rw [sum_ite_val_eq_mul' _ _ (Nat.mod_lt _ hn), sum_ite_val_eq_mul' _ _ (cyc_sub_one_lt hn i.2),
    Finset.sum_eq_single i (fun j _ hj => by rw [ite_eq_right hj, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- Let $n \ge 2$ and $h_i > 0$ for $1 \le i \le n$. Then the cyclic moment matrix is strictly
diagonally dominant by rows: each off-diagonal row sum is at most $\lambda_i + \mu_i = 1 < 2$. -/
theorem isStrictDiagDominant_periodicMomentMatrix (hn2 : 2 ≤ n)
    (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i) : (periodicMomentMatrix n h).IsStrictDiagDominant := by
  have hn : 1 ≤ n := by omega
  intro i
  have hi := i.2
  have hc1 : 0 < h (cyc n i) := hh (cyc n i) (by unfold cyc; split_ifs <;> omega)
    (by unfold cyc; split_ifs <;> omega)
  have hc2 : 0 < h (i + 1) := hh (i + 1) (by omega) (by omega)
  have hlam : 0 ≤ h (i + 1) / (h (cyc n i) + h (i + 1)) := by positivity
  have hmu : 0 ≤ h (cyc n i) / (h (cyc n i) + h (i + 1)) := by positivity
  have hii : ‖periodicMomentMatrix n h i i‖ = 2 := by
    have h1 : ¬ ((i : ℕ) = (i + 1) % n) := by
      intro h
      rcases Nat.lt_or_ge ((i : ℕ) + 1) n with hi' | hi'
      · rw [Nat.mod_eq_of_lt hi'] at h; omega
      · have : (i : ℕ) + 1 = n := by omega
        rw [this, Nat.mod_self] at h; omega
    have h2 : ¬ ((i : ℕ) = cyc n i - 1) := by unfold cyc; split_ifs <;> omega
    simp [periodicMomentMatrix, h1, h2]
  rw [hii]
  calc ∑ j ∈ Finset.univ.erase i, ‖periodicMomentMatrix n h i j‖
      ≤ ∑ j ∈ Finset.univ.erase i, ((if (j : ℕ) = (i + 1) % n then
            h (i + 1) / (h (cyc n i) + h (i + 1)) else 0)
          + (if (j : ℕ) = cyc n i - 1 then h (cyc n i) / (h (cyc n i) + h (i + 1)) else 0)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [periodicMomentMatrix, Matrix.of_apply, ite_eq_right hji, zero_add, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (by split_ifs <;> simp [hlam]) (by split_ifs <;> simp [hmu]))]
    _ ≤ ∑ j : Fin n, ((if (j : ℕ) = (i + 1) % n then
            h (i + 1) / (h (cyc n i) + h (i + 1)) else 0)
          + (if (j : ℕ) = cyc n i - 1 then h (cyc n i) / (h (cyc n i) + h (i + 1)) else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
          add_nonneg (by split_ifs <;> simp [hlam]) (by split_ifs <;> simp [hmu])
    _ = h (i + 1) / (h (cyc n i) + h (i + 1)) + h (cyc n i) / (h (cyc n i) + h (i + 1)) := by
        rw [Finset.sum_add_distrib]
        have e1 := sum_ite_val_eq_mul' (h (i + 1) / (h (cyc n i) + h (i + 1))) (fun _ => (1 : ℝ))
          (Nat.mod_lt (i + 1) hn)
        have e2 := sum_ite_val_eq_mul' (h (cyc n i) / (h (cyc n i) + h (i + 1))) (fun _ => (1 : ℝ))
          (cyc_sub_one_lt hn i.2)
        simp only [mul_one] at e1 e2
        rw [e1, e2]
    _ = 1 := by rw [← add_div, add_comm, div_self (by positivity)]
    _ < 2 := by norm_num

/-- Let $n \ge 2$ and $h_i > 0$ for $1 \le i \le n$. Then the cyclic moment matrix is invertible. -/
theorem isUnit_periodicMomentMatrix (hn2 : 2 ≤ n) (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i) :
    IsUnit (periodicMomentMatrix n h) :=
  (isStrictDiagDominant_periodicMomentMatrix hn2 hh).isUnit

/-- For $n \ge 1$, the periodic extension of a vector $v$ indexed by $\{0, \dots, n - 1\}$ to
$\mathbb{N}$: the sequence $i \mapsto v_{i \bmod n}$. -/
noncomputable def cycExtend (hn : 1 ≤ n) (v : Fin n → ℝ) (i : ℕ) : ℝ := v ⟨i % n, Nat.mod_lt _ hn⟩

/-- For $i < n$, the periodic extension of $v$ takes the value $v_i$. -/
theorem cycExtend_of_lt (hn : 1 ≤ n) (v : Fin n → ℝ) {i : ℕ} (hi : i < n) :
    cycExtend hn v i = v ⟨i, hi⟩ := by
  simp only [cycExtend, Nat.mod_eq_of_lt hi]

/-- The periodic extension of $v$ takes the same value at $n$ and at $0$. -/
theorem cycExtend_self (hn : 1 ≤ n) (v : Fin n → ℝ) : cycExtend hn v n = cycExtend hn v 0 := by
  simp only [cycExtend, Nat.mod_self, Nat.zero_mod]

end Periodic

section PeriodicSpline

variable (hx : IsIntervalPartition a b n x) (hn : 2 ≤ n) {f : ℕ → ℝ}
include hx hn

/-- **The cyclic system is the interior moment equations plus the periodicity of $s'$.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 2$, let $v$ be a vector indexed by
$\{0, \dots, n - 1\}$, and let $M$ be its periodic extension, so that $M_n = M_0$. Then
$A v = d$, for the cyclic moment matrix $A$ and the right-hand side $d$ of the panel lengths and
the data $f$, holds if and only if the interior moment equations for the moments $M$ hold at
$x_1, \dots, x_{n-1}$ and the slope of the first panel cubic at $a$ equals the slope of the last
panel cubic at $b$. -/
theorem periodicMomentMatrix_mulVec_eq_iff (v : Fin n → ℝ) :
    (periodicMomentMatrix n (panelLength x)).mulVec v = periodicMomentRhs n (panelLength x) f ↔
      (∀ i, 1 ≤ i → i < n → IsMomentEq x f (cycExtend (by omega) v) i) ∧
        panelCubicD1 x f (cycExtend (by omega) v) 1 (x 0)
          = panelCubicD1 x f (cycExtend (by omega) v) n (x n) := by
  have hn1 : 1 ≤ n := by omega
  have h1 := hx.panelLength_pos le_rfl hn1
  have hnn := hx.panelLength_pos hn1 le_rfl
  set M := cycExtend hn1 v with hM
  have hMv : ∀ i (hi : i < n), v ⟨i, hi⟩ = M i := fun i hi => (cycExtend_of_lt hn1 v hi).symm
  -- the slope condition is the `0`-th row
  have hrow0 : panelCubicD1 x f M 1 (x 0) = panelCubicD1 x f M n (x n) ↔
      2 * M 0 + panelLength x 1 / (panelLength x n + panelLength x 1) * M 1
        + panelLength x n / (panelLength x n + panelLength x 1) * M (n - 1)
      = 6 / (panelLength x n + panelLength x 1)
        * ((f 1 - f 0) / panelLength x 1 - (f n - f (n - 1)) / panelLength x n) := by
    rw [panelCubicD1_left (i := 0) (hx.step 0 hn1), panelCubicD1_right (hx.lt (by omega) le_rfl)]
    have hMn : M n = M 0 := cycExtend_self hn1 v
    simp only [panelLength, hMn] at *
    have hc : 6 / (x n - x (n - 1) + (x 1 - x 0)) ≠ 0 := div_ne_zero (by norm_num) (by linarith)
    have key : 2 * M 0 + (x 1 - x 0) / (x n - x (n - 1) + (x 1 - x 0)) * M 1
        + (x n - x (n - 1)) / (x n - x (n - 1) + (x 1 - x 0)) * M (n - 1)
        - 6 / (x n - x (n - 1) + (x 1 - x 0))
          * ((f 1 - f 0) / (x 1 - x 0) - (f n - f (n - 1)) / (x n - x (n - 1)))
        = 6 / (x n - x (n - 1) + (x 1 - x 0)) * (((x n - x (n - 1)) * M (n - 1) / 6
            + (x n - x (n - 1)) * M 0 / 3 + (f n - f (n - 1)) / (x n - x (n - 1)))
          - (-((x 1 - x 0) * M 0) / 3 - (x 1 - x 0) * M 1 / 6 + (f 1 - f 0) / (x 1 - x 0))) := by
      have : x n - x (n - 1) ≠ 0 := by linarith
      have : x 1 - x 0 ≠ 0 := by linarith
      field_simp
      ring
    rw [eq_comm, ← sub_eq_zero, ← sub_eq_zero (a := 2 * M 0 + _ + _), key, mul_eq_zero,
      or_iff_right hc]
  have hMmod : ∀ k, v ⟨k % n, Nat.mod_lt _ hn1⟩ = M k := fun _ => rfl
  rw [funext_iff]
  constructor
  · intro H
    refine ⟨fun i hi1 hin => ?_, ?_⟩
    · have := H ⟨i, hin⟩
      rw [periodicMomentMatrix_mulVec_apply hn1, periodicMomentRhs, hMmod, hMv, hMv] at this
      simp only [cyc, ite_eq_right (show i ≠ 0 by omega)] at this
      rw [IsMomentEq]
      linear_combination this
    · have := H ⟨0, by omega⟩
      rw [periodicMomentMatrix_mulVec_apply hn1, periodicMomentRhs, hMmod, hMv, hMv] at this
      simp only [cyc, ↓reduceIte, Nat.zero_add] at this
      rw [hrow0]
      linear_combination this
  · rintro ⟨hint, h0⟩ ⟨i, hi⟩
    rw [periodicMomentMatrix_mulVec_apply hn1, periodicMomentRhs, hMmod, hMv, hMv]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [cyc, ↓reduceIte, Nat.zero_add]
      rw [hrow0] at h0
      linear_combination h0
    · have := hint i (by omega) hi
      simp only [cyc, ite_eq_right hi0]
      rw [IsMomentEq] at this
      linear_combination this

end PeriodicSpline

/-- The **periodic end conditions** $s'(a) = s'(b)$ and $s''(a) = s''(b)$, with the derivatives
within $[a, b]$. These are the two derivative conditions of (8.44) of [quarteroni2000numerical]
with $k = 3$. -/
def IsPeriodicEnd (a b : ℝ) (s : ℝ → ℝ) : Prop :=
  derivWithin s (Icc a b) a = derivWithin s (Icc a b) b ∧
    iteratedDerivWithin 2 s (Icc a b) a = iteratedDerivWithin 2 s (Icc a b) b

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $s$ be an interpolatory
cubic spline of the data $f$. Then the derivative of $s$ within $[a, b]$ at $a$ is the slope at
$x_0$ of the first panel cubic with the data $f$ and the moments of $s$. -/
theorem IsCubicInterp.derivWithin_left (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
    {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    derivWithin s (Icc a b) a = panelCubicD1 x f (moment a b x s) 1 (x 0) := by
  have := (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn (u := x 0) (v := x 1)
    (hx.step 0 hn) (Icc_subset_Icc (hx.left_le (Nat.zero_le n)) (hx.le_right hn))
    (hs.eqOn_panelCubic hx le_rfl hn) (left_mem_Icc.mpr (hx.step 0 hn).le)).1
  calc derivWithin s (Icc a b) a = derivWithin s (Icc a b) (x 0) := by rw [hx.first]
    _ = _ := this

/-- Let $a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, and let $s$ be an interpolatory
cubic spline of the data $f$. Then the derivative of $s$ within $[a, b]$ at $b$ is the slope at
$x_n$ of the last panel cubic with the data $f$ and the moments of $s$. -/
theorem IsCubicInterp.derivWithin_right (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
    {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    derivWithin s (Icc a b) b = panelCubicD1 x f (moment a b x s) n (x n) := by
  have hlt : x (n - 1) < x n := hx.lt (Nat.sub_one_lt_of_le hn le_rfl) le_rfl
  have := (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn (u := x (n - 1)) (v := x n)
    hlt (Icc_subset_Icc (hx.left_le (Nat.sub_le n 1)) (hx.le_right le_rfl))
    (hs.eqOn_panelCubic hx hn le_rfl) (right_mem_Icc.mpr hlt.le)).1
  calc derivWithin s (Icc a b) b = derivWithin s (Icc a b) (x n) := by rw [hx.last]
    _ = _ := this

/-- **The clamped end conditions are a closure of type (8.48).** Let $a = x_0 < \dots < x_n = b$ be
a partition with $n \ge 1$, and let $s$ be an interpolatory cubic spline of the data $f$ with
$s'(a) = f'_0$ and $s'(b) = f'_n$, for the derivatives within $[a, b]$. Then the moments of $s$
satisfy
$$2 M_0 + M_1 = \frac{6}{h_1} \left( \frac{f_1 - f_0}{h_1} - f'_0 \right), \qquad M_{n-1} + 2
  M_n = \frac{6}{h_n} \left( f'_n - \frac{f_n - f_{n-1}}{h_n} \right),$$
which is the closure of `Spline.clampedInterp`.

The proof uses the slope formulas `Spline.IsCubicInterp.derivWithin_left` and
`Spline.IsCubicInterp.derivWithin_right`. -/
theorem IsCubicInterp.hasClosure_of_derivWithin (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {f : ℕ → ℝ} {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) {f'0 f'n : ℝ}
    (h0 : derivWithin s (Icc a b) a = f'0) (h1 : derivWithin s (Icc a b) b = f'n) :
    HasClosure a b n x 1 1 (6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0))
      (6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1)))) s := by
  have hA := hs.derivWithin_left hx hn
  have hB := hs.derivWithin_right hx hn
  have hl : x 0 < x 1 := hx.step 0 hn
  have hr : x (n - 1) < x n := hx.lt (Nat.sub_one_lt_of_le hn le_rfl) le_rfl
  rw [h0, panelCubicD1_left hl] at hA
  rw [h1, panelCubicD1_right hr] at hB
  have hl' : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr hl.ne'
  have hr' : x n - x (n - 1) ≠ 0 := sub_ne_zero.mpr hr.ne'
  refine ⟨?_, ?_⟩
  · rw [hA]; field_simp; ring
  · rw [hB]; field_simp; ring

/-- **Existence and uniqueness of the periodic cubic spline.** Let $a = x_0 < \dots < x_n = b$ be a
partition with $n \ge 2$, and let $f_0, \dots, f_n \in \mathbb{R}$. Then there is an
interpolatory cubic spline $s$ of the data $f$ with $s'(a) = s'(b)$ and $s''(a) = s''(b)$, for
the derivatives within $[a, b]$, and any two such splines agree on $[a, b]$. This is the
periodic spline of (8.44) of [quarteroni2000numerical] with $k = 3$.

The remaining condition $s(a) = s(b)$ of (8.44) holds exactly when $f_0 = f_n$; the theorem does
not assume it.

The moments satisfy $M_0 = M_n$ and the cyclic system `Spline.periodicMomentMatrix`, which is
strictly diagonally dominant. -/
theorem existsUnique_isCubicInterp_periodic (hx : IsIntervalPartition a b n x) (hn : 2 ≤ n)
    (f : ℕ → ℝ) :
    (∃ s, IsCubicInterp a b n x f s ∧ IsPeriodicEnd a b s) ∧
      ∀ s₁ s₂, IsCubicInterp a b n x f s₁ → IsPeriodicEnd a b s₁ →
        IsCubicInterp a b n x f s₂ → IsPeriodicEnd a b s₂ → EqOn s₁ s₂ (Icc a b) := by
  have hn1 : 1 ≤ n := by omega
  have hab := hx.lt_of_pos hn1
  have hA := isUnit_periodicMomentMatrix (h := panelLength x) hn
    fun i hi1 hin => hx.panelLength_pos hi1 hin
  -- the moments of a periodic interpolatory spline solve the cyclic system
  have hsolve : ∀ s, IsCubicInterp a b n x f s → IsPeriodicEnd a b s →
      (periodicMomentMatrix n (panelLength x)).mulVec
        (fun j : Fin n => moment a b x s (j : ℕ)) = periodicMomentRhs n (panelLength x) f := by
    intro s hs hp
    set M := moment a b x s with hM
    have hMn : M n = M 0 := by
      change iteratedDerivWithin 2 s (Icc a b) (x n) = iteratedDerivWithin 2 s (Icc a b) (x 0)
      rw [hx.first, hx.last]; exact hp.2.symm
    set v : Fin n → ℝ := fun j => M (j : ℕ) with hv
    have hext : ∀ i ≤ n, cycExtend hn1 v i = M i := fun i hi => by
      rcases lt_or_eq_of_le hi with hi | rfl
      · rw [cycExtend_of_lt hn1 v hi]
      · rw [cycExtend_self, cycExtend_of_lt hn1 v (by omega), hMn]
    refine (periodicMomentMatrix_mulVec_eq_iff hx hn v).mpr ⟨fun i hi1 hin => ?_, ?_⟩
    · rw [isMomentEq_congr (N := M) (hext _ (by omega)) (hext _ (by omega)) (hext _ (by omega))]
      exact hs.isMomentEq hx hi1 hin
    · have h1 := hs.derivWithin_left hx hn1
      have h2 := hs.derivWithin_right hx hn1
      have : panelCubicD1 x f (cycExtend hn1 v) 1 (x 0) = panelCubicD1 x f M 1 (x 0) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hext 0 (by omega)) (hext 1 hn1)]
      have h' : panelCubicD1 x f (cycExtend hn1 v) n (x n) = panelCubicD1 x f M n (x n) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hext (n - 1) (by omega)) (hext n le_rfl)]
      rw [this, h', ← h1, ← h2]
      exact hp.1
  constructor
  · -- existence
    set v : Fin n → ℝ := (periodicMomentMatrix n (panelLength x))⁻¹.mulVec
      (periodicMomentRhs n (panelLength x) f) with hv
    set M := cycExtend hn1 v with hM
    have hAv : (periodicMomentMatrix n (panelLength x)).mulVec v
        = periodicMomentRhs n (panelLength x) f := by
      rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
    obtain ⟨hint, hslope⟩ := (periodicMomentMatrix_mulVec_eq_iff hx hn v).mp hAv
    set s := cubicSplineFun n x f M with hs
    have hc := contDiff_cubicSplineFun hx hn1 hint
    have hsi : IsCubicInterp a b n x f s :=
      ⟨⟨contDiffOn_cubicSplineFun hx hn1 hint, fun i hi1 hin =>
        ⟨panelCubicPoly x f M i, degree_panelCubicPoly_le _ _ _ _, cubicSplineFun_eqOn hx hi1 hin⟩⟩,
        fun i hi => cubicSplineFun_apply_node hx hn1 hi⟩
    have hmom : ∀ i ≤ n, moment a b x s i = M i := fun i hi => by
      rw [moment_eq_iteratedDeriv hab hc ⟨hx.left_le hi, hx.le_right hi⟩,
        iteratedDeriv_two_cubicSplineFun_node hx hn1 hint hi]
    refine ⟨s, hsi, ?_, ?_⟩
    · rw [hsi.derivWithin_left hx hn1, hsi.derivWithin_right hx hn1]
      have e1 : panelCubicD1 x f (moment a b x s) 1 (x 0) = panelCubicD1 x f M 1 (x 0) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hmom 0 (by omega)) (hmom 1 hn1)]
      have e2 : panelCubicD1 x f (moment a b x s) n (x n) = panelCubicD1 x f M n (x n) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hmom (n - 1) (by omega)) (hmom n le_rfl)]
      rw [e1, e2]
      exact hslope
    · have e0 : iteratedDerivWithin 2 s (Icc a b) a = M 0 := by
        rw [← hmom 0 (Nat.zero_le n), moment, hx.first]
      have eb : iteratedDerivWithin 2 s (Icc a b) b = M n := by
        rw [← hmom n le_rfl, moment, hx.last]
      rw [e0, eb, hM, cycExtend_self]
  · -- uniqueness
    intro s₁ s₂ h₁ hp₁ h₂ hp₂
    have hveq : (fun j : Fin n => moment a b x s₁ (j : ℕ))
        = fun j : Fin n => moment a b x s₂ (j : ℕ) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hA ((hsolve s₁ h₁ hp₁).trans (hsolve s₂ h₂ hp₂).symm)
    have hlt : ∀ i < n, moment a b x s₁ i = moment a b x s₂ i := fun i hi =>
      congrFun hveq (⟨i, hi⟩ : Fin n)
    have hall : ∀ i ≤ n, moment a b x s₁ i = moment a b x s₂ i := fun i hi => by
      rcases lt_or_eq_of_le hi with hi | rfl
      · exact hlt i hi
      · have e₁ : moment a b x s₁ 0 = moment a b x s₁ i := by
          simp only [moment, hx.first, hx.last]; exact hp₁.2
        have e₂ : moment a b x s₂ 0 = moment a b x s₂ i := by
          simp only [moment, hx.first, hx.last]; exact hp₂.2
        exact e₁.symm.trans ((hlt 0 (by omega)).trans e₂)
    exact (h₁.eqOn_cubicSplineFun hx hn1).trans
      ((cubicSplineFun_eqOn_of_moment_eq hx hn1 hall).trans (h₂.eqOn_cubicSplineFun hx hn1).symm)

/-!
### Error bounds for the clamped interpolatory spline

Let $f$ be of class $C^4$ with $|f^{(4)}| \le K$ on $[a, b]$, and let all panel lengths be at most
$h$. Then the clamped interpolatory cubic spline $s$ of $f$ satisfies
$|f'' - s''| \le \frac74 h^2 K$, $|f' - s'| \le \frac74 h^3 K$ and $|f - s| \le \frac78 h^4 K$ on
$[a, b]$.

The argument is the classical one of Stoer and Bulirsch, *Introduction to Numerical Analysis*,
Theorem 2.4.3.3. The vector of the exact values $f''(x_i)$ satisfies the moment system (8.48) up to
a residual that Taylor expansion bounds by $\frac34 h^2 K$. Since $\|A^{-1}\|_\infty \le 1$
(`Spline.linfty_opNorm_inv_momentMatrix_le`), the moments are within $\frac34 h^2 K$ of $f''$ at the
nodes. On a panel $s''$ is the linear interpolant of two moments, so it is within
$\frac34 h^2 K + h^2 K$ of $f''$. Finally $f - s$ vanishes at the nodes, and two applications of the
mean value theorem, with Rolle's theorem in between, give the bounds of order $h^3$ and $h^4$.

The constants are not sharp. The sharp constants $5/384$, $1/24$ and $3/8$ for the function, its
slope and its second derivative are the theorem of Hall and Meyer, *Optimal error bounds for cubic
spline interpolation* (J. Approx. Theory 16, 1976), which is not formalized here.

The function is assumed of class $C^4$ on all of $\mathbb{R}$ rather than on $[a, b]$. This matches
`norm_sub_piecewiseLinearInterpCLM_le` in `Numlib.Approximation.Interpolation`, and it avoids
derivatives within $[a, b]$ at the two endpoints in every Taylor expansion.
-/

section ClampedError

/-- The third-order Taylor bound: for $g$ of class $C^4$ with $|g^{(4)}| \le K$ on $[a, b]$ and
$c, t \in [a, b]$, the remainder of the cubic Taylor polynomial of $g$ at $c$ is at most
$K |t - c|^4 / 24$ at $t$. -/
private theorem abs_sub_taylor_three_le {g : ℝ → ℝ} {K c t : ℝ} (hg : ContDiff ℝ 4 g)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 g y| ≤ K) :
    |g t - (g c + (t - c) * deriv g c + (t - c) ^ 2 / 2 * iteratedDeriv 2 g c
        + (t - c) ^ 3 / 6 * iteratedDeriv 3 g c)| ≤ K * |t - c| ^ 4 / 24 := by
  have hg' : ContDiff ℝ ((3 : ℕ) + 1) g := by norm_num; exact hg
  have hK' : ∀ y ∈ Icc a b, |iteratedDeriv ((3 : ℕ) + 1) g y| ≤ K := by simpa using hK
  have h1 := abs_sub_sum_taylor_le_of_convex (convex_Icc a b) hg' hc ht hK'
  have hsum : ∑ k ∈ Finset.range ((3 : ℕ) + 1),
      (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c
      = g c + (t - c) * deriv g c + (t - c) ^ 2 / 2 * iteratedDeriv 2 g c
        + (t - c) ^ 3 / 6 * iteratedDeriv 3 g c := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum] at h1
  calc |g t - (g c + (t - c) * deriv g c + (t - c) ^ 2 / 2 * iteratedDeriv 2 g c
        + (t - c) ^ 3 / 6 * iteratedDeriv 3 g c)|
      ≤ K * |t - c| ^ ((3 : ℕ) + 1) / (((3 : ℕ) + 1).factorial : ℝ) := h1
    _ = K * |t - c| ^ 4 / 24 := by norm_num [Nat.factorial]

/-- The first-order Taylor bound: for $g$ of class $C^2$ with $|g''| \le K$ on $[a, b]$ and
$c, t \in [a, b]$, $|g(t) - g(c) - (t - c) g'(c)| \le K |t - c|^2 / 2$. -/
private theorem abs_sub_taylor_one_le {g : ℝ → ℝ} {K c t : ℝ} (hg : ContDiff ℝ 2 g)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 2 g y| ≤ K) :
    |g t - (g c + (t - c) * deriv g c)| ≤ K * |t - c| ^ 2 / 2 := by
  have hg' : ContDiff ℝ ((1 : ℕ) + 1) g := by norm_num; exact hg
  have hK' : ∀ y ∈ Icc a b, |iteratedDeriv ((1 : ℕ) + 1) g y| ≤ K := by simpa using hK
  have h1 := abs_sub_sum_taylor_le_of_convex (convex_Icc a b) hg' hc ht hK'
  have hsum : ∑ k ∈ Finset.range ((1 : ℕ) + 1),
      (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c
      = g c + (t - c) * deriv g c := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum] at h1
  calc |g t - (g c + (t - c) * deriv g c)|
      ≤ K * |t - c| ^ ((1 : ℕ) + 1) / (((1 : ℕ) + 1).factorial : ℝ) := h1
    _ = K * |t - c| ^ 2 / 2 := by norm_num [Nat.factorial]

/-- The second derivative of a function of class $C^4$ is of class $C^2$. -/
private theorem contDiff_iteratedDeriv_two {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    ContDiff ℝ 2 (iteratedDeriv 2 f) := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  exact (hf.deriv' (n := 3)).deriv' (n := 2)

/-- The $j$-th derivative of $f''$ is $f^{(j+2)}$. -/
private theorem iteratedDeriv_iteratedDeriv_two (f : ℝ → ℝ) (j : ℕ) :
    iteratedDeriv j (iteratedDeriv 2 f) = iteratedDeriv (j + 2) f := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, show j + 2 = j + 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ']

/-- For $g$ of class $C^2$, the derivative $g'$ has the derivative $g''(y)$ at every $y$. -/
private theorem hasDerivAt_deriv_of_contDiff_two {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (y : ℝ) :
    HasDerivAt (deriv g) (iteratedDeriv 2 g y) y := by
  have h : ContDiff ℝ 1 (deriv g) := hg.deriv' (n := 1)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact ((h.differentiable (by norm_num)) y).hasDerivAt

/-- The two Taylor remainders of the residual estimates, of $f$ to order three and of $f''$ to order
one, both about $c \in [a, b]$ and evaluated at $c + w \in [a, b]$, are at most $K |w|^4 / 24$
and $K |w|^2 / 2$ when $|f^{(4)}| \le K$ on $[a, b]$. -/
private theorem abs_taylor_pair {f : ℝ → ℝ} {K c : ℝ} (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    {w : ℝ} (hc : c ∈ Icc a b) (hcw : c + w ∈ Icc a b) :
    |f (c + w) - (f c + w * deriv f c + w ^ 2 / 2 * iteratedDeriv 2 f c
        + w ^ 3 / 6 * iteratedDeriv 3 f c)| ≤ K * |w| ^ 4 / 24 ∧
    |iteratedDeriv 2 f (c + w) - (iteratedDeriv 2 f c + w * iteratedDeriv 3 f c)|
      ≤ K * |w| ^ 2 / 2 := by
  have hw : c + w - c = w := by ring
  refine ⟨?_, ?_⟩
  · have h := abs_sub_taylor_three_le hf hc hcw hK
    rwa [hw] at h
  · have hKg : ∀ y ∈ Icc a b, |iteratedDeriv 2 (iteratedDeriv 2 f) y| ≤ K := by
      intro y hy
      rw [iteratedDeriv_iteratedDeriv_two]
      exact hK y hy
    have h := abs_sub_taylor_one_le (contDiff_iteratedDeriv_two hf) hc hcw hKg
    rw [hw, ← iteratedDeriv_succ] at h
    exact h

/-- For $0 < u \le h$ and $0 < v \le h$, $u^2 - uv + v^2 \le h^2$. -/
private theorem sq_sub_mul_add_sq_le {u v hm : ℝ} (hu : 0 < u) (hv : 0 < v) (huh : u ≤ hm)
    (hvh : v ≤ hm) : u ^ 2 - u * v + v ^ 2 ≤ hm ^ 2 := by
  rcases le_total u v with h | h
  · nlinarith
  · nlinarith

section Residual

variable {f : ℝ → ℝ} {K c u v hm : ℝ}

/-- **The residual of an interior moment row** at the exact second derivatives of $f$: for a node
$c$ with the left panel length $v$ and the right panel length $u$, both in $(0, h]$, the row
$\mu f''(c - v) + 2 f''(c) + \lambda f''(c + u) - d$ of (8.47) is at most $\frac34 h^2 K$ in
absolute value. -/
private theorem abs_interior_residual_le (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hu : 0 < u) (hv : 0 < v) (huh : u ≤ hm) (hvh : v ≤ hm)
    (hcv : c - v ∈ Icc a b) (hc : c ∈ Icc a b) (hcu : c + u ∈ Icc a b) :
    |v / (u + v) * iteratedDeriv 2 f (c - v) + 2 * iteratedDeriv 2 f c
        + u / (u + v) * iteratedDeriv 2 f (c + u)
        - 6 / (u + v) * ((f (c + u) - f c) / u - (f c - f (c - v)) / v)|
      ≤ 3 / 4 * hm ^ 2 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
  obtain ⟨e1, E1⟩ := abs_taylor_pair hf hK (w := u) hc hcu
  obtain ⟨e2, E2⟩ := abs_taylor_pair hf hK (w := -v) hc (by rw [← sub_eq_add_neg]; exact hcv)
  rw [← sub_eq_add_neg] at e2 E2
  rw [abs_of_pos hu] at e1 E1
  rw [abs_neg, abs_of_pos hv] at e2 E2
  set F0 := f c
  set F1 := deriv f c
  set F2 := iteratedDeriv 2 f c
  set F3 := iteratedDeriv 3 f c
  set P := f (c + u)
  set N := f (c - v)
  set Gp := iteratedDeriv 2 f (c + u)
  set Gn := iteratedDeriv 2 f (c - v)
  set A := Gn - (F2 + -v * F3) with hA
  set B := Gp - (F2 + u * F3) with hB
  set p := P - (F0 + u * F1 + u ^ 2 / 2 * F2 + u ^ 3 / 6 * F3) with hp
  set q := N - (F0 + -v * F1 + (-v) ^ 2 / 2 * F2 + (-v) ^ 3 / 6 * F3) with hq
  have key : v / (u + v) * Gn + 2 * F2 + u / (u + v) * Gp
      - 6 / (u + v) * ((P - F0) / u - (F0 - N) / v)
      = v / (u + v) * A + u / (u + v) * B - 6 / (u + v) * (p / u + q / v) := by
    rw [hA, hB, hp, hq]
    field_simp
    ring
  rw [key]
  have t3 : |p / u + q / v| ≤ K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v := by
    calc |p / u + q / v| ≤ |p / u| + |q / v| := abs_add_le _ _
      _ = |p| / u + |q| / v := by rw [abs_div, abs_div, abs_of_pos hu, abs_of_pos hv]
      _ ≤ K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v := by gcongr
  have hfin : v / (u + v) * (K * v ^ 2 / 2) + u / (u + v) * (K * u ^ 2 / 2)
      + 6 / (u + v) * (K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v)
      = 3 / 4 * K * (u ^ 2 - u * v + v ^ 2) := by
    field_simp
    ring
  calc |v / (u + v) * A + u / (u + v) * B - 6 / (u + v) * (p / u + q / v)|
      ≤ |v / (u + v) * A| + |u / (u + v) * B| + |6 / (u + v) * (p / u + q / v)| := by
        rw [sub_eq_add_neg, ← abs_neg (6 / (u + v) * (p / u + q / v))]
        exact abs_add_three _ _ _
    _ = v / (u + v) * |A| + u / (u + v) * |B| + 6 / (u + v) * |p / u + q / v| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < v / (u + v)),
          abs_of_pos (by positivity : (0:ℝ) < u / (u + v)),
          abs_of_pos (by positivity : (0:ℝ) < 6 / (u + v))]
    _ ≤ v / (u + v) * (K * v ^ 2 / 2) + u / (u + v) * (K * u ^ 2 / 2)
        + 6 / (u + v) * (K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v) := by gcongr
    _ = 3 / 4 * K * (u ^ 2 - u * v + v ^ 2) := hfin
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        have := sq_sub_mul_add_sq_le hu hv huh hvh
        nlinarith

/-- **The residual of the left clamped closure row** at the exact derivatives of $f$: for
$0 < u \le h$, $\left| 2 f''(c) + f''(c + u) - \frac{6}{u} \left( \frac{f(c + u) - f(c)}{u} -
f'(c) \right) \right| \le \frac34 h^2 K$. -/
private theorem abs_left_residual_le (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hu : 0 < u) (huh : u ≤ hm) (hc : c ∈ Icc a b) (hcu : c + u ∈ Icc a b) :
    |2 * iteratedDeriv 2 f c + iteratedDeriv 2 f (c + u)
        - 6 / u * ((f (c + u) - f c) / u - deriv f c)| ≤ 3 / 4 * hm ^ 2 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
  obtain ⟨e1, E1⟩ := abs_taylor_pair hf hK (w := u) hc hcu
  rw [abs_of_pos hu] at e1 E1
  set F0 := f c
  set F1 := deriv f c
  set F2 := iteratedDeriv 2 f c
  set F3 := iteratedDeriv 3 f c
  set P := f (c + u)
  set Gp := iteratedDeriv 2 f (c + u)
  set B := Gp - (F2 + u * F3) with hB
  set p := P - (F0 + u * F1 + u ^ 2 / 2 * F2 + u ^ 3 / 6 * F3) with hp
  have key : 2 * F2 + Gp - 6 / u * ((P - F0) / u - F1) = B - 6 / u ^ 2 * p := by
    rw [hB, hp]; field_simp; ring
  rw [key]
  calc |B - 6 / u ^ 2 * p| ≤ |B| + |6 / u ^ 2 * p| := by
        rw [sub_eq_add_neg, ← abs_neg (6 / u ^ 2 * p)]; exact abs_add_le _ _
    _ = |B| + 6 / u ^ 2 * |p| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 / u ^ 2)]
    _ ≤ K * u ^ 2 / 2 + 6 / u ^ 2 * (K * u ^ 4 / 24) := by gcongr
    _ = 3 / 4 * u ^ 2 * K := by field_simp; ring
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        have h2 : u ^ 2 ≤ hm ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 huh) (by linarith : (0:ℝ) ≤ hm + u)]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) hK0]

/-- **The residual of the right clamped closure row** at the exact derivatives of $f$: for
$0 < v \le h$, $\left| f''(c - v) + 2 f''(c) - \frac{6}{v} \left( f'(c) - \frac{f(c) - f(c -
v)}{v} \right) \right| \le \frac34 h^2 K$. -/
private theorem abs_right_residual_le (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hv : 0 < v) (hvh : v ≤ hm) (hcv : c - v ∈ Icc a b) (hc : c ∈ Icc a b) :
    |iteratedDeriv 2 f (c - v) + 2 * iteratedDeriv 2 f c
        - 6 / v * (deriv f c - (f c - f (c - v)) / v)| ≤ 3 / 4 * hm ^ 2 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
  obtain ⟨e2, E2⟩ := abs_taylor_pair hf hK (w := -v) hc (by rw [← sub_eq_add_neg]; exact hcv)
  rw [← sub_eq_add_neg] at e2 E2
  rw [abs_neg, abs_of_pos hv] at e2 E2
  set F0 := f c
  set F1 := deriv f c
  set F2 := iteratedDeriv 2 f c
  set F3 := iteratedDeriv 3 f c
  set N := f (c - v)
  set Gn := iteratedDeriv 2 f (c - v)
  set A := Gn - (F2 + -v * F3) with hA
  set q := N - (F0 + -v * F1 + (-v) ^ 2 / 2 * F2 + (-v) ^ 3 / 6 * F3) with hq
  have key : Gn + 2 * F2 - 6 / v * (F1 - (F0 - N) / v) = A - 6 / v ^ 2 * q := by
    rw [hA, hq]; field_simp; ring
  rw [key]
  calc |A - 6 / v ^ 2 * q| ≤ |A| + |6 / v ^ 2 * q| := by
        rw [sub_eq_add_neg, ← abs_neg (6 / v ^ 2 * q)]; exact abs_add_le _ _
    _ = |A| + 6 / v ^ 2 * |q| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 / v ^ 2)]
    _ ≤ K * v ^ 2 / 2 + 6 / v ^ 2 * (K * v ^ 4 / 24) := by gcongr
    _ = 3 / 4 * v ^ 2 * K := by field_simp; ring
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        have h2 : v ^ 2 ≤ hm ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hvh) (by linarith : (0:ℝ) ≤ hm + v)]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) hK0]

/-- **A crude bound on the error of linear interpolation**: for $g$ of class $C^2$ with
$|g''| \le K$ on $[a, b]$ and $[p, q] \subseteq [a, b]$ with $p < q$, the affine interpolant of
$g$ at $p$ and $q$ differs from $g$ on $[p, q]$ by at most $K (q - p)^2$; the sharp constant
$K (q - p)^2 / 8$ is not needed. -/
private theorem abs_linearInterp_sub_le {g : ℝ → ℝ} {K p q t : ℝ} (hg : ContDiff ℝ 2 g)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 2 g y| ≤ K) (hpq : p < q)
    (hsub : Icc p q ⊆ Icc a b) (ht : t ∈ Icc p q) :
    |g p * (q - t) / (q - p) + g q * (t - p) / (q - p) - g t| ≤ K * (q - p) ^ 2 := by
  have hp : p ∈ Icc a b := hsub ⟨le_rfl, hpq.le⟩
  have hq : q ∈ Icc a b := hsub ⟨hpq.le, le_rfl⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK p hp)
  have hd : (0 : ℝ) < q - p := sub_pos.mpr hpq
  have e1 := abs_sub_taylor_one_le hg hp hq hK
  have e2 := abs_sub_taylor_one_le hg hp (hsub ht) hK
  rw [abs_of_pos hd] at e1
  rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - p)] at e2
  set eq' := g q - (g p + (q - p) * deriv g p) with heq'
  set et := g t - (g p + (t - p) * deriv g p) with het
  have key : g p * (q - t) / (q - p) + g q * (t - p) / (q - p) - g t
      = (t - p) / (q - p) * eq' - et := by
    rw [heq', het]; field_simp; ring
  rw [key]
  have hθ : (t - p) / (q - p) ≤ 1 := (div_le_one hd).mpr (by linarith [ht.2])
  have hθ0 : (0 : ℝ) ≤ (t - p) / (q - p) := div_nonneg (by linarith [ht.1]) hd.le
  calc |(t - p) / (q - p) * eq' - et| ≤ |(t - p) / (q - p) * eq'| + |et| := by
        rw [sub_eq_add_neg, ← abs_neg et]; exact abs_add_le _ _
    _ = (t - p) / (q - p) * |eq'| + |et| := by rw [abs_mul, abs_of_nonneg hθ0]
    _ ≤ 1 * (K * (q - p) ^ 2 / 2) + K * (t - p) ^ 2 / 2 := by gcongr
    _ ≤ 1 * (K * (q - p) ^ 2 / 2) + K * (q - p) ^ 2 / 2 := by
        gcongr
        · linarith [ht.1]
        · linarith [ht.2]
    _ = K * (q - p) ^ 2 := by ring

end Residual

/-- **The second derivative of the interpolatory cubic spline is linear on every panel.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$, let $0 \le \lambda_0 \le 1$ and
$0 \le \mu_n \le 1$, and let $s$ be the interpolatory cubic spline of the data $f$ with the
closure $(\lambda_0, \mu_n, d_0, d_n)$. Then for $1 \le i \le n$ and $t \in [x_{i-1}, x_i]$,
$$s''(t) = s''(x_{i-1}) \frac{x_i - t}{h_i} + s''(x_i) \frac{t - x_{i-1}}{h_i},$$
where $h_i = x_i - x_{i-1}$. So $s''$ takes the moments at the ends of each panel and is linear
in between, as in (8.46) of [quarteroni2000numerical]. -/
theorem iteratedDeriv_two_cubicInterp_eq_of_mem (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n)
    {f : ℕ → ℝ} {lam0 mun d0 dn : ℝ} (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun)
    (hm1 : mun ≤ 1) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : t ∈ Icc (x (i - 1)) (x i)) :
    iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) t
      = iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) (x (i - 1)) * (x i - t)
          / (x i - x (i - 1))
        + iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) (x i) * (t - x (i - 1))
          / (x i - x (i - 1)) := by
  have hM : ∀ j, 1 ≤ j → j < n → IsMomentEq x f (momentVec n x f lam0 mun d0 dn) j :=
    fun _ h1 h2 => isMomentEq_momentVec hx hn hl0 hl1 hm0 hm1 h1 h2
  rw [iteratedDeriv_two_cubicInterp_node hx hn hl0 hl1 hm0 hm1 (show i - 1 ≤ n by omega),
    iteratedDeriv_two_cubicInterp_node hx hn hl0 hl1 hm0 hm1 hin, cubicInterp,
    iteratedDeriv_two_cubicSplineFun hx hn hM,
    panelGlue_eq_of_mem hx (fun _ h1 h2 => panelCubicD2_apply_node_succ hx h1 h2) hi1 hin
      (Icc_subset_extPanel i ht),
    panelCubicD2_apply _ _ _ (hx.lt (by omega) hin)]

/-- The second derivative of the clamped spline is linear on every panel, as in
`Spline.iteratedDeriv_two_cubicInterp_eq_of_mem`. -/
private theorem iteratedDeriv_two_clampedInterp_eq_of_mem (hx : IsIntervalPartition a b n x)
    (hn : 1 ≤ n) {f : ℕ → ℝ} (f'0 f'n : ℝ) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : t ∈ Icc (x (i - 1)) (x i)) :
    iteratedDeriv 2 (clampedInterp n x f f'0 f'n) t
      = iteratedDeriv 2 (clampedInterp n x f f'0 f'n) (x (i - 1)) * (x i - t)
          / (x i - x (i - 1))
        + iteratedDeriv 2 (clampedInterp n x f f'0 f'n) (x i) * (t - x (i - 1))
          / (x i - x (i - 1)) :=
  iteratedDeriv_two_cubicInterp_eq_of_mem hx hn zero_le_one le_rfl zero_le_one le_rfl hi1 hin ht

section Bounds

open scoped Matrix.Norms.Operator

variable (hx : IsIntervalPartition a b n x) (hn : 1 ≤ n) {f : ℝ → ℝ} {K hm : ℝ}
  (hf : ContDiff ℝ 4 f)
  (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
  (hmesh : ∀ i, 1 ≤ i → i ≤ n → panelLength x i ≤ hm)
include hx hn hf hK hmesh

/-- **The moments of the clamped spline approximate $f''$ to second order.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$ and all panel lengths at most $h$, let
$f$ be of class $C^4$ on $\mathbb{R}$ with $|f^{(4)}| \le K$ on $[a, b]$, and let $s$ be the
clamped cubic spline of the values $f(x_0), \dots, f(x_n)$ with the end slopes $f'(a)$ and
$f'(b)$. Then for $0 \le i \le n$,
$$|s''(x_i) - f''(x_i)| \le \tfrac34 h^2 K.$$
This is part of Theorem 2.4.3.3 of Stoer and Bulirsch, *Introduction to Numerical Analysis*.

The vector of the exact values $f''(x_i)$ satisfies the moment system (8.48) up to a residual
bounded by $\frac34 h^2 K$. Taylor expansion of $f$ and of $f''$ about $x_i$ gives this for the
interior rows, and the two clamped closure rows are bounded separately. The bound
$\|A^{-1}\|_\infty \le 1$ of `Spline.linfty_opNorm_inv_momentMatrix_le` then transfers the
residual to the moments. -/
theorem norm_deriv2_sub_clampedInterp_le {i : ℕ} (hi : i ≤ n) :
    |iteratedDeriv 2 (clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) (x i)
      - iteratedDeriv 2 f (x i)| ≤ 3 / 4 * hm ^ 2 * K := by
  classical
  rw [← hx.first, ← hx.last]
  suffices key : ∀ d0 dn : ℝ,
      d0 = 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - deriv f (x 0)) →
      dn = 6 / (x n - x (n - 1))
        * (deriv f (x n) - (f (x n) - f (x (n - 1))) / (x n - x (n - 1))) →
      |iteratedDeriv 2 (cubicInterp n x (fun j => f (x j)) 1 1 d0 dn) (x i)
        - iteratedDeriv 2 f (x i)| ≤ 3 / 4 * hm ^ 2 * K from key _ _ rfl rfl
  intro d0 dn hd0 hdn
  have hpos : ∀ j, 1 ≤ j → j ≤ n → 0 < panelLength x j := fun j h1 h2 => hx.panelLength_pos h1 h2
  have hmem : ∀ j, j ≤ n → x j ∈ Icc a b := fun j hj => ⟨hx.left_le hj, hx.le_right hj⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  set fd : ℕ → ℝ := fun j => f (x j) with hfd
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := momentMatrix n (panelLength x) 1 1 with hA
  set d : Fin (n + 1) → ℝ := momentRhs n (panelLength x) fd d0 dn with hd
  set Mv : Fin (n + 1) → ℝ := A⁻¹.mulVec d with hMv
  set Fv : Fin (n + 1) → ℝ := fun j => iteratedDeriv 2 f (x j) with hFv
  have hmv : momentVec n x fd 1 1 d0 dn = extendFin Mv := rfl
  rw [iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl hi, hmv,
    extendFin_of_lt (i := i) _ (show i < n + 1 by omega),
    show iteratedDeriv 2 f (x i) = Fv ⟨i, by omega⟩ from rfl]
  have hrow : ∀ j : Fin (n + 1), |d j - (A.mulVec Fv) j| ≤ 3 / 4 * hm ^ 2 * K := by
    intro j
    rw [hA, momentMatrix_mulVec_apply]
    rcases eq_or_ne (j : ℕ) 0 with hj0 | hj0
    · -- the left closure row
      have h1n : (1 : ℕ) < n + 1 := by omega
      have hdj : d j = d0 := by simp only [hd, momentRhs, hj0, reduceIte]
      have hlam : momentLam (panelLength x) 1 (j : ℕ) = 1 := by
        simp only [momentLam, hj0, reduceIte]
      have hext : extendFin Fv ((j : ℕ) + 1) = iteratedDeriv 2 f (x 1) := by
        rw [hj0, extendFin_of_lt _ h1n]
      have hFvj : Fv j = iteratedDeriv 2 f (x 0) := by rw [hFv]; simp [hj0]
      have hmu : (if (j : ℕ) = 0 then (0 : ℝ) else extendFin Fv ((j : ℕ) - 1)) = 0 := by
        simp [hj0]
      rw [hdj, hlam, hext, hFvj, hmu, hd0]
      have hu : 0 < x 1 - x 0 := sub_pos.mpr (hx.step 0 (by omega))
      have hcu : x 0 + (x 1 - x 0) ∈ Icc a b := by
        rw [show x 0 + (x 1 - x 0) = x 1 from by ring]; exact hmem 1 hn
      have hres := abs_left_residual_le (a := a) (b := b) (hm := hm) hf hK hu
        (by simpa [panelLength] using hmesh 1 le_rfl hn) (hmem 0 (by omega)) hcu
      rw [show x 0 + (x 1 - x 0) = x 1 from by ring] at hres
      rw [show 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - deriv f (x 0))
          - (2 * iteratedDeriv 2 f (x 0) + 1 * iteratedDeriv 2 f (x 1) + _ * 0)
          = -(2 * iteratedDeriv 2 f (x 0) + iteratedDeriv 2 f (x 1)
              - 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - deriv f (x 0)))
        from by ring, abs_neg]
      exact hres
    · rcases eq_or_ne (j : ℕ) n with hjn | hjn
      · -- the right closure row
        have hdj : d j = dn := by
          simp only [hd, momentRhs]
          rw [ite_eq_right hj0, ite_eq_left hjn]
        have hext : extendFin Fv ((j : ℕ) + 1) = 0 := extendFin_of_le _ (by omega)
        have hmu : momentMu n (panelLength x) 1 (j : ℕ) = 1 := by
          simp only [momentMu, hjn, reduceIte]
        have hext2 : (if (j : ℕ) = 0 then (0 : ℝ) else extendFin Fv ((j : ℕ) - 1))
            = iteratedDeriv 2 f (x (n - 1)) := by
          rw [ite_eq_right hj0, hjn, extendFin_of_lt _ (show n - 1 < n + 1 by omega)]
        have hFvj : Fv j = iteratedDeriv 2 f (x n) := by rw [hFv]; simp [hjn]
        rw [hdj, hext, hmu, hext2, hFvj, hdn, mul_zero]
        have hv : 0 < x n - x (n - 1) := sub_pos.mpr (hx.lt (by omega) le_rfl)
        have hcv : x n - (x n - x (n - 1)) ∈ Icc a b := by
          rw [show x n - (x n - x (n - 1)) = x (n - 1) from by ring]; exact hmem _ (by omega)
        have hres := abs_right_residual_le (a := a) (b := b) (hm := hm) hf hK hv
          (by simpa [panelLength] using hmesh n hn le_rfl) hcv (hmem n le_rfl)
        rw [show x n - (x n - x (n - 1)) = x (n - 1) from by ring] at hres
        rw [show 6 / (x n - x (n - 1))
              * (deriv f (x n) - (f (x n) - f (x (n - 1))) / (x n - x (n - 1)))
            - (2 * iteratedDeriv 2 f (x n) + 0 + 1 * iteratedDeriv 2 f (x (n - 1)))
            = -(iteratedDeriv 2 f (x (n - 1)) + 2 * iteratedDeriv 2 f (x n)
                - 6 / (x n - x (n - 1))
                  * (deriv f (x n) - (f (x n) - f (x (n - 1))) / (x n - x (n - 1))))
          from by ring, abs_neg]
        exact hres
      · -- an interior row
        have hjn' : (j : ℕ) < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.2) hjn
        have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have hdj : d j = 6 / (panelLength x (j : ℕ) + panelLength x ((j : ℕ) + 1))
            * ((f (x ((j : ℕ) + 1)) - f (x (j : ℕ))) / panelLength x ((j : ℕ) + 1)
              - (f (x (j : ℕ)) - f (x ((j : ℕ) - 1))) / panelLength x (j : ℕ)) := by
          simp only [hd, momentRhs, hfd]
          rw [ite_eq_right hj0, ite_eq_right hjn]
        have hlam : momentLam (panelLength x) 1 (j : ℕ)
            = panelLength x ((j : ℕ) + 1)
              / (panelLength x (j : ℕ) + panelLength x ((j : ℕ) + 1)) := by
          simp only [momentLam, ite_eq_right hj0]
        have hmu : momentMu n (panelLength x) 1 (j : ℕ)
            = panelLength x (j : ℕ)
              / (panelLength x (j : ℕ) + panelLength x ((j : ℕ) + 1)) := by
          simp only [momentMu, ite_eq_right hjn]
        have hext : extendFin Fv ((j : ℕ) + 1) = iteratedDeriv 2 f (x ((j : ℕ) + 1)) :=
          extendFin_of_lt _ (by omega)
        have hext2 : (if (j : ℕ) = 0 then (0 : ℝ) else extendFin Fv ((j : ℕ) - 1))
            = iteratedDeriv 2 f (x ((j : ℕ) - 1)) := by
          rw [ite_eq_right hj0, extendFin_of_lt _ (show (j : ℕ) - 1 < n + 1 by omega)]
        have hFvj : Fv j = iteratedDeriv 2 f (x (j : ℕ)) := rfl
        have hpl1 : panelLength x (j : ℕ) = x (j : ℕ) - x ((j : ℕ) - 1) := rfl
        have hpl2 : panelLength x ((j : ℕ) + 1) = x ((j : ℕ) + 1) - x (j : ℕ) := by
          simp [panelLength]
        rw [hdj, hlam, hmu, hext, hext2, hFvj, hpl1, hpl2]
        have hu : 0 < x ((j : ℕ) + 1) - x (j : ℕ) := sub_pos.mpr (hx.step _ hjn')
        have hv : 0 < x (j : ℕ) - x ((j : ℕ) - 1) := sub_pos.mpr (hx.lt (by omega) (by omega))
        have hcu : x (j : ℕ) + (x ((j : ℕ) + 1) - x (j : ℕ)) ∈ Icc a b := by
          rw [show x (j : ℕ) + (x ((j : ℕ) + 1) - x (j : ℕ)) = x ((j : ℕ) + 1) from by ring]
          exact hmem _ (by omega)
        have hcv : x (j : ℕ) - (x (j : ℕ) - x ((j : ℕ) - 1)) ∈ Icc a b := by
          rw [show x (j : ℕ) - (x (j : ℕ) - x ((j : ℕ) - 1)) = x ((j : ℕ) - 1) from by ring]
          exact hmem _ (by omega)
        have hres := abs_interior_residual_le (a := a) (b := b) (hm := hm) hf hK hu hv
          (by simpa [panelLength] using hmesh ((j : ℕ) + 1) (by omega) (by omega))
          (by simpa [panelLength] using hmesh (j : ℕ) hj1 (by omega))
          hcv (hmem _ (by omega)) hcu
        rw [show x (j : ℕ) + (x ((j : ℕ) + 1) - x (j : ℕ)) = x ((j : ℕ) + 1) from by ring,
          show x (j : ℕ) - (x (j : ℕ) - x ((j : ℕ) - 1)) = x ((j : ℕ) - 1) from by ring] at hres
        rw [show (6 / (x (j : ℕ) - x ((j : ℕ) - 1) + (x ((j : ℕ) + 1) - x (j : ℕ)))
              * ((f (x ((j : ℕ) + 1)) - f (x (j : ℕ))) / (x ((j : ℕ) + 1) - x (j : ℕ))
                - (f (x (j : ℕ)) - f (x ((j : ℕ) - 1))) / (x (j : ℕ) - x ((j : ℕ) - 1)))
            - (2 * iteratedDeriv 2 f (x (j : ℕ))
              + (x ((j : ℕ) + 1) - x (j : ℕ))
                / (x (j : ℕ) - x ((j : ℕ) - 1) + (x ((j : ℕ) + 1) - x (j : ℕ)))
                * iteratedDeriv 2 f (x ((j : ℕ) + 1))
              + (x (j : ℕ) - x ((j : ℕ) - 1))
                / (x (j : ℕ) - x ((j : ℕ) - 1) + (x ((j : ℕ) + 1) - x (j : ℕ)))
                * iteratedDeriv 2 f (x ((j : ℕ) - 1))))
            = -((x (j : ℕ) - x ((j : ℕ) - 1))
                  / ((x ((j : ℕ) + 1) - x (j : ℕ)) + (x (j : ℕ) - x ((j : ℕ) - 1)))
                  * iteratedDeriv 2 f (x ((j : ℕ) - 1))
                + 2 * iteratedDeriv 2 f (x (j : ℕ))
                + (x ((j : ℕ) + 1) - x (j : ℕ))
                  / ((x ((j : ℕ) + 1) - x (j : ℕ)) + (x (j : ℕ) - x ((j : ℕ) - 1)))
                  * iteratedDeriv 2 f (x ((j : ℕ) + 1))
                - 6 / ((x ((j : ℕ) + 1) - x (j : ℕ)) + (x (j : ℕ) - x ((j : ℕ) - 1)))
                  * ((f (x ((j : ℕ) + 1)) - f (x (j : ℕ))) / (x ((j : ℕ) + 1) - x (j : ℕ))
                    - (f (x (j : ℕ)) - f (x ((j : ℕ) - 1))) / (x (j : ℕ) - x ((j : ℕ) - 1))))
          from by ring, abs_neg]
        exact hres
  calc |Mv ⟨i, by omega⟩ - Fv ⟨i, by omega⟩| = ‖(Mv - Fv) ⟨i, by omega⟩‖ := by
        rw [Pi.sub_apply, Real.norm_eq_abs]
    _ ≤ ‖Mv - Fv‖ := norm_le_pi_norm _ _
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        refine le_trans
          (norm_le_norm_momentMatrix_mulVec hpos zero_le_one le_rfl zero_le_one le_rfl _) ?_
        have hmul : A.mulVec (Mv - Fv) = d - A.mulVec Fv := by
          rw [Matrix.mulVec_sub, hMv, hA,
            momentMatrix_mulVec_momentVec hx zero_le_one le_rfl zero_le_one le_rfl fd d0 dn]
        rw [hmul]
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
        rw [Pi.sub_apply, Real.norm_eq_abs]
        exact hrow j

/-- **The second derivative of the clamped spline approximates $f''$ to second order on all of
$[a, b]$.** Let the partition with $n \ge 1$ and panel lengths at most $h$, the function $f$ of
class $C^4$ with $|f^{(4)}| \le K$ on $[a, b]$, and the clamped spline $s$ be as in
`Spline.norm_deriv2_sub_clampedInterp_le`. Then for every $t \in [a, b]$,
$$|s''(t) - f''(t)| \le \tfrac74 h^2 K.$$

On a panel $s''$ is the linear interpolant of its two end moments. These are within
$\frac34 h^2 K$ of $f''$ (`Spline.norm_deriv2_sub_clampedInterp_le`), and the linear interpolant
of $f''$ is within $h^2 K$ of $f''$. -/
theorem norm_deriv2_sub_clampedInterp_le_of_mem {t : ℝ} (ht : t ∈ Icc a b) :
    |iteratedDeriv 2 (clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) t
      - iteratedDeriv 2 f t| ≤ 7 / 4 * hm ^ 2 * K := by
  obtain ⟨i, hi1, hin, hmem, -⟩ := hx.exists_mem_panel hn ht
  have hpq : x (i - 1) < x i := hx.lt (by omega) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  have hd : (0 : ℝ) < x i - x (i - 1) := sub_pos.mpr hpq
  have hmesh' : x i - x (i - 1) ≤ hm := by simpa [panelLength] using hmesh i hi1 hin
  have hlin := iteratedDeriv_two_clampedInterp_eq_of_mem hx hn (f := fun j => f (x j))
    (deriv f a) (deriv f b) hi1 hin hmem
  set s := clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) with hs
  set p := x (i - 1) with hp
  set q := x i with hq
  have hlin' : iteratedDeriv 2 s t
      = iteratedDeriv 2 s p * (q - t) / (q - p) + iteratedDeriv 2 s q * (t - p) / (q - p) := hlin
  have hα : (0 : ℝ) ≤ (q - t) / (q - p) := div_nonneg (by linarith [hmem.2]) hd.le
  have hβ : (0 : ℝ) ≤ (t - p) / (q - p) := div_nonneg (by linarith [hmem.1]) hd.le
  have hαβ : (q - t) / (q - p) + (t - p) / (q - p) = 1 := by field_simp; ring
  have h1 : |iteratedDeriv 2 s p - iteratedDeriv 2 f p| ≤ 3 / 4 * hm ^ 2 * K :=
    norm_deriv2_sub_clampedInterp_le hx hn hf hK hmesh (by omega)
  have h2 : |iteratedDeriv 2 s q - iteratedDeriv 2 f q| ≤ 3 / 4 * hm ^ 2 * K :=
    norm_deriv2_sub_clampedInterp_le hx hn hf hK hmesh hin
  have h3 : |iteratedDeriv 2 f p * (q - t) / (q - p) + iteratedDeriv 2 f q * (t - p) / (q - p)
      - iteratedDeriv 2 f t| ≤ K * (q - p) ^ 2 :=
    abs_linearInterp_sub_le (contDiff_iteratedDeriv_two hf)
      (fun y hy => by rw [iteratedDeriv_iteratedDeriv_two]; exact hK y hy) hpq hsub hmem
  calc |iteratedDeriv 2 s t - iteratedDeriv 2 f t|
      = |((iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))
            + (iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p)))
          + (iteratedDeriv 2 f p * (q - t) / (q - p) + iteratedDeriv 2 f q * (t - p) / (q - p)
            - iteratedDeriv 2 f t)| := by
        congr 1
        rw [hlin']
        ring
    _ ≤ |(iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))
            + (iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p))|
          + |iteratedDeriv 2 f p * (q - t) / (q - p) + iteratedDeriv 2 f q * (t - p) / (q - p)
            - iteratedDeriv 2 f t| := abs_add_le _ _
    _ ≤ (3 / 4 * hm ^ 2 * K * ((q - t) / (q - p)) + 3 / 4 * hm ^ 2 * K * ((t - p) / (q - p)))
          + K * (q - p) ^ 2 := by
        refine add_le_add ?_ h3
        calc |(iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))
              + (iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p))|
            ≤ |(iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))|
              + |(iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p))| :=
              abs_add_le _ _
          _ = |iteratedDeriv 2 s p - iteratedDeriv 2 f p| * ((q - t) / (q - p))
              + |iteratedDeriv 2 s q - iteratedDeriv 2 f q| * ((t - p) / (q - p)) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
          _ ≤ 3 / 4 * hm ^ 2 * K * ((q - t) / (q - p))
              + 3 / 4 * hm ^ 2 * K * ((t - p) / (q - p)) := by gcongr
    _ = 3 / 4 * hm ^ 2 * K + K * (q - p) ^ 2 := by rw [← mul_add, hαβ, mul_one]
    _ ≤ 3 / 4 * hm ^ 2 * K + K * hm ^ 2 := by
        have : (q - p) ^ 2 ≤ hm ^ 2 := by nlinarith
        nlinarith
    _ = 7 / 4 * hm ^ 2 * K := by ring

/-- **The slope of the clamped spline approximates $f'$ to third order.** Let the partition with
$n \ge 1$ and panel lengths at most $h$, the function $f$ of class $C^4$ with $|f^{(4)}| \le K$
on $[a, b]$, and the clamped spline $s$ be as in `Spline.norm_deriv2_sub_clampedInterp_le`. Then
for every $t \in [a, b]$,
$$|s'(t) - f'(t)| \le \tfrac74 h^3 K.$$

The error $f - s$ vanishes at both ends of every panel, so by Rolle's theorem its derivative
vanishes somewhere inside. The mean value theorem with the bound of
`Spline.norm_deriv2_sub_clampedInterp_le_of_mem` then costs one factor $h$. -/
theorem norm_deriv_sub_clampedInterp_le {t : ℝ} (ht : t ∈ Icc a b) :
    |deriv (clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) t - deriv f t|
      ≤ 7 / 4 * hm ^ 3 * K := by
  obtain ⟨i, hi1, hin, hmem, -⟩ := hx.exists_mem_panel hn ht
  have hpq : x (i - 1) < x i := hx.lt (by omega) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  have hmesh' : x i - x (i - 1) ≤ hm := by simpa [panelLength] using hmesh i hi1 hin
  set s := clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) with hs
  have hs2 : ContDiff ℝ 2 s := contDiff_clampedInterp hx hn _ _
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hde : ∀ y, HasDerivAt (fun z => s z - f z) (deriv s y - deriv f y) y := fun y =>
    ((hs2.differentiable (by norm_num)) y).hasDerivAt.sub
      ((hf.differentiable (by norm_num)) y).hasDerivAt
  have hdde : ∀ y, HasDerivAt (fun z => deriv s z - deriv f z)
      (iteratedDeriv 2 s y - iteratedDeriv 2 f y) y := fun y =>
    (hasDerivAt_deriv_of_contDiff_two hs2 y).sub (hasDerivAt_deriv_of_contDiff_two hf2 y)
  have hderiv_e : deriv (fun z => s z - f z) = fun y => deriv s y - deriv f y :=
    funext fun y => (hde y).deriv
  have hnode : ∀ j ≤ n, s (x j) - f (x j) = 0 := fun j hj => by
    rw [hs, sub_eq_zero]; exact cubicInterp_apply_node hx hn hj
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero (f := fun z => s z - f z) hpq
    (fun y _ => ((hde y).continuousAt).continuousWithinAt)
    (by rw [hnode (i - 1) (by omega), hnode i hin])
  rw [hderiv_e] at hξ0
  have hξm : ξ ∈ Icc (x (i - 1)) (x i) := Ioo_subset_Icc_self hξ
  have hbound : ∀ y ∈ Icc (x (i - 1)) (x i),
      ‖iteratedDeriv 2 s y - iteratedDeriv 2 f y‖ ≤ 7 / 4 * hm ^ 2 * K := fun y hy => by
    rw [Real.norm_eq_abs]
    exact norm_deriv2_sub_clampedInterp_le_of_mem hx hn hf hK hmesh (hsub hy)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => deriv s z - deriv f z)
    (f' := fun z => iteratedDeriv 2 s z - iteratedDeriv 2 f z)
    (fun y _ => (hdde y).hasDerivWithinAt) hbound (convex_Icc _ _) hξm hmem
  simp only [hξ0, sub_zero, Real.norm_eq_abs] at hmvt
  calc |deriv s t - deriv f t| ≤ 7 / 4 * hm ^ 2 * K * |t - ξ| := hmvt
    _ ≤ 7 / 4 * hm ^ 2 * K * hm := by
        have habs : |t - ξ| ≤ hm := by
          rw [abs_sub_le_iff]
          constructor <;> [linarith [hmem.2, hξm.1]; linarith [hmem.1, hξm.2]]
        gcongr
    _ = 7 / 4 * hm ^ 3 * K := by ring

/-- **An error bound of order $h^4$ for the clamped cubic spline with explicit constants.** Let
$a = x_0 < \dots < x_n = b$ be a partition with $n \ge 1$ and all panel lengths at most $h$, let
$f$ be of class $C^4$ on $\mathbb{R}$ with $|f^{(4)}| \le K$ on $[a, b]$, and let $s$ be the
clamped cubic spline of the values $f(x_0), \dots, f(x_n)$ with the end slopes $f'(a)$ and
$f'(b)$. Then for every $t \in [a, b]$,
$$|s(t) - f(t)| \le \tfrac78 h^4 K.$$
This is the bound behind Property 8.3 of [quarteroni2000numerical].

The error vanishes at both ends of every panel, so the mean value theorem with
`Spline.norm_deriv_sub_clampedInterp_le`, applied from the nearer end, gives
$|s - f| \le \frac74 h^3 K \cdot h / 2$. The constants are those of Stoer and Bulirsch,
*Introduction to Numerical Analysis*, Theorem 2.4.3.3, not the sharp constants $5/384$, $1/24$,
$3/8$ of Hall and Meyer, *Optimal error bounds for cubic spline interpolation* (J. Approx.
Theory 16, 1976). -/
theorem norm_sub_clampedInterp_le {t : ℝ} (ht : t ∈ Icc a b) :
    |clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) t - f t|
      ≤ 7 / 8 * hm ^ 4 * K := by
  obtain ⟨i, hi1, hin, hmem, -⟩ := hx.exists_mem_panel hn ht
  have hpq : x (i - 1) < x i := hx.lt (by omega) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  have hmesh' : x i - x (i - 1) ≤ hm := by simpa [panelLength] using hmesh i hi1 hin
  have hm0 : (0 : ℝ) ≤ hm := le_trans (by linarith) hmesh'
  set s := clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) with hs
  have hs2 : ContDiff ℝ 2 s := contDiff_clampedInterp hx hn _ _
  have hde : ∀ y, HasDerivAt (fun z => s z - f z) (deriv s y - deriv f y) y := fun y =>
    ((hs2.differentiable (by norm_num)) y).hasDerivAt.sub
      ((hf.differentiable (by norm_num)) y).hasDerivAt
  have hnode : ∀ j ≤ n, s (x j) - f (x j) = 0 := fun j hj => by
    rw [hs, sub_eq_zero]; exact cubicInterp_apply_node hx hn hj
  have hbound : ∀ y ∈ Icc (x (i - 1)) (x i), ‖deriv s y - deriv f y‖ ≤ 7 / 4 * hm ^ 3 * K :=
    fun y hy => by
      rw [Real.norm_eq_abs]
      exact norm_deriv_sub_clampedInterp_le hx hn hf hK hmesh (hsub hy)
  have hmvt : ∀ y ∈ Icc (x (i - 1)) (x i), ∀ z ∈ Icc (x (i - 1)) (x i),
      ‖(s z - f z) - (s y - f y)‖ ≤ 7 / 4 * hm ^ 3 * K * ‖z - y‖ := fun y hy z hz =>
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun w => s w - f w)
      (f' := fun w => deriv s w - deriv f w) (fun w _ => (hde w).hasDerivWithinAt) hbound
      (convex_Icc _ _) hy hz
  have h1 := hmvt _ ⟨le_rfl, hpq.le⟩ t hmem
  have h2 := hmvt _ ⟨hpq.le, le_rfl⟩ t hmem
  rw [hnode (i - 1) (by omega), sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [hmem.1] : (0:ℝ) ≤ t - x (i - 1))] at h1
  rw [hnode i hin, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm t (x i),
    abs_of_nonneg (by linarith [hmem.2] : (0:ℝ) ≤ x i - t)] at h2
  have hC : (0 : ℝ) ≤ 7 / 4 * hm ^ 3 * K := by positivity
  nlinarith [h1, h2, mul_le_mul_of_nonneg_left hmesh' hC]

end Bounds

end ClampedError

end Spline
