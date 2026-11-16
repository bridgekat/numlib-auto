/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Interpolation
import Numlib.Analysis.Sobolev.Interval

/-!
# Piecewise Lagrange interpolation in $L^2$ and $H^m$ seminorms

This module bounds the error of piecewise polynomial interpolation in the $L^2$ norms of the
derivatives, rather than in the supremum norm. Let $a = x_0 < x_1 < \dots < x_{n+1} = b$ be a
partition of $[a, b]$ whose panels $[x_j, x_{j+1}]$ have length at most $h$, and let $\Pi_h^k f$ be
the continuous function that agrees on each panel with a polynomial of degree at most $k$ that
interpolates $f$ at $k + 1$ distinct nodes of the panel. For every derivative order $m \le k$,
$$\|(f - \Pi_h^k f)^{(m)}\|_{L^2(a, b)} \le h^{k+1-m} \|f^{(k+1)}\|_{L^2(a, b)}.$$
This is Theorem 8.3 of [quarteroni2000numerical], which proves it there for $k = 1$ in (8.27). It is
the approximation estimate behind the convergence of the finite element method with elements $P_k$
in one dimension. The constant is $1$ for every $k$ and $m$, which is sharper than the unspecified
constant $C$ of the source. For $m \ge 2$ the left side is a sum of integrals over the panels.

The core statements do not mention a Sobolev space. They use only the following properties of $f$:
$f$ is of class $C^k$, and $f^{(k)}(t) - f^{(k)}(s) = \int_s^t g$ for a square-integrable function
$g$. This describes the absolutely continuous representative of a function in $H^{k+1}(a, b)$, with
$g = f^{(k+1)}$. The theorem `SobolevInterval.exists_contDiff_ae_eq` of
`Numlib.Analysis.Sobolev.Interval` gives such a representative for every element of $H^{k+1}(a, b)$.
The last two theorems restate the estimate for such an element, with the $H^{k+1}$ seminorm
`SobolevInterval.seminorm` on the right.

## Main results

* `abs_iteratedDeriv_sub_le`: on one panel of length at most $h$, $|f^{(m)}(t) - p^{(m)}(t)| \le
  h^{k-m} \sqrt{h} \, \|g\|_{L^2}$ for the interpolating polynomial $p$ of degree at most $k$.
* `integral_sq_iteratedDeriv_sub_le`: on one panel, $\int (f^{(m)} - p^{(m)})^2 \le h^{2(k+1-m)}
  \int g^2$.
* `sum_integral_sq_sub_panelPoly_le`: Theorem 8.3 as a sum over the panels, $\sum_j
  \int_{x_j}^{x_{j+1}} (f^{(m)} - (\Pi_h^k f)^{(m)})^2 \le h^{2(k+1-m)} \int_a^b g^2$.
* `integral_sq_sub_piecewisePolyInterpCLM_le`: the case $m = 0$, $\|f - \Pi_h^k f\|_{L^2(a, b)}^2
  \le h^{2(k+1)} \int_a^b g^2$.
* `integral_sq_deriv_sub_piecewisePolyInterpCLM_le`: the case $m = 1$ for $k \ge 1$, $\|(f - \Pi_h^k
  f)'\|_{L^2(a, b)}^2 \le h^{2k} \int_a^b g^2$.
* `integral_sq_sub_piecewiseLinearInterpCLM_le`: (8.27) for piecewise linear interpolation, $\|f -
  \Pi_h^1 f\|_{L^2(a, b)}^2 \le h^4 \int_a^b g^2$.
* `integral_sq_deriv_sub_piecewiseLinearInterpCLM_le`: (8.27) for the derivative, $\|(f - \Pi_h^1
  f)'\|_{L^2(a, b)}^2 \le h^2 \int_a^b g^2$.
* `sobolevSeminorm_sub_piecewisePolyInterp_le`: Theorem 8.3 for $u \in H^{k+1}(a, b)$, with the
  right side $h^{2(k+1-m)} |u|_{H^{k+1}(a, b)}^2$.
* `integral_sq_sub_piecewisePolyInterpCLM_le_seminorm`: the case $m = 0$ for $u \in H^{k+1}(a, b)$,
  $\|F - \Pi_h^k F\|_{L^2(a, b)}^2 \le h^{2(k+1)} |u|_{H^{k+1}(a, b)}^2$.

## Proof outline

On one panel $[u, v]$ of length at most $h$, let $e = f - p$, where $p$ interpolates $f$ at $k + 1$
distinct nodes of the panel. The generalized Rolle theorem
`exists_iteratedDeriv_eq_zero_of_forall_eq_zero` gives a zero $\xi_j$ of $e^{(j)}$ in the panel for
every $j \le k$. Since $p^{(k)}$ is constant, $e^{(k)}(t) = \int_{\xi_k}^t g$, so the Cauchy–Schwarz
inequality gives $|e^{(k)}(t)| \le \sqrt{h} \, \|g\|_{L^2(u, v)}$. Each of the $k - m$ integrations
$e^{(j)}(t) = \int_{\xi_j}^t e^{(j+1)}$ gains a factor $h$. Squaring and integrating over the panel
gives $\int_u^v |e^{(m)}|^2 \le h^{2(k+1-m)} \int_u^v g^2$, and the sum over the panels gives the
theorem.

## Implementation notes

* The core statements `abs_iteratedDeriv_sub_le`, `integral_sq_iteratedDeriv_sub_le`,
  `sum_integral_sq_sub_panelPoly_le`, `integral_sq_sub_piecewisePolyInterpCLM_le`,
  `integral_sq_deriv_sub_piecewisePolyInterpCLM_le`, `integral_sq_sub_piecewiseLinearInterpCLM_le`
  and `integral_sq_deriv_sub_piecewiseLinearInterpCLM_le` assume exactly that $f$ is of class $C^k$
  and that $f^{(k)}(t) - f^{(k)}(s) = \int_s^t g$ on $[a, b]$.
* The interpolant on the panel $j$ is the polynomial `panelPoly node j F` of
  `Numlib.Approximation.Interpolation`, where `F : C(Set.Icc a b, ℝ)` is the restriction of $f$ to
  $[a, b]$. With $p_j$ = `panelPoly node j F`, the sum $\sum_j \int_{x_j}^{x_{j+1}} |f^{(m)} -
  p_j^{(m)}|^2$ over the panels is the statement for every $m \le k$. For $m = 0$ and $m = 1$ it is
  the $L^2(a, b)$ norm of $(f - \Pi_h^k f)^{(m)}$, and `integral_sq_sub_piecewisePolyInterpCLM_le`
  and `integral_sq_deriv_sub_piecewisePolyInterpCLM_le` state it with the interpolation operator
  `piecewisePolyInterpCLM`.
* The square integrability of $g$ is the pair of hypotheses `IntervalIntegrable g` and
  `IntervalIntegrable (g ^ 2)`. With the first alone, the right side $\int g^2$ could be the value
  $0$ that Lean gives to the integral of a non-integrable function.
-/

open Polynomial MeasureTheory intervalIntegral Set
open scoped Interval Topology

/-! ### The panel estimates -/

/-- Let $u < v$ and $v - u \le h$, and let $m \le k$ be natural numbers. Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^k$, and let $g$ be a function such that $g$
and $g^2$ are integrable on $[u, v]$ and
$$f^{(k)}(t) - f^{(k)}(s) = \int_s^t g(r) \, dr \quad \text{for all } s, t \in [u, v].$$
Let $p$ be a polynomial of degree at most $k$ with $p(y_i) = f(y_i)$ at $k + 1$ distinct points
$y_0, \dots, y_k$ of $[u, v]$. Then for every $t \in [u, v]$,
$$|f^{(m)}(t) - p^{(m)}(t)| \le h^{k-m} \sqrt{h} \left( \int_u^v g^2 \right)^{1/2}.$$
This is the estimate (8.30)–(8.31) of [quarteroni2000numerical] for general $k$.

The proof is a downward induction on $m$ from $m = k$. The generalized Rolle theorem gives a
zero $\xi_j$ of $e^{(j)} = (f - p)^{(j)}$ in the panel for every $j \le k$. Since $p^{(k)}$ is
constant, $e^{(k)}(t) = \int_{\xi_k}^t g$, which the Cauchy–Schwarz inequality bounds by
$\sqrt{h} \, \|g\|_{L^2(u, v)}$. Each step $e^{(m)}(t) = \int_{\xi_m}^t e^{(m+1)}$ gains a
factor $h$. -/
theorem abs_iteratedDeriv_sub_le {k m : ℕ} {u v h : ℝ} (huv : u < v) (hh : v - u ≤ h)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ k f) (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume u v)
    (hfg : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {p : ℝ[X]} (hp : p.degree ≤ k) {y : Fin (k + 1) → ℝ} (hy : Function.Injective y)
    (hymem : ∀ i, y i ∈ Icc u v) (hpy : ∀ i, p.eval (y i) = f (y i)) (hm : m ≤ k) {t : ℝ}
    (ht : t ∈ Icc u v) :
    |iteratedDeriv m f t - (derivative^[m] p).eval t|
      ≤ h ^ (k - m) * √h * √(∫ t in u..v, g t ^ 2) := by
  have h0 : 0 ≤ h := (sub_pos.2 huv).le.trans hh
  set e : ℝ → ℝ := fun t => f t - p.eval t with he_def
  have he : ContDiff ℝ k e := hf.sub (contDiff_eval p k)
  have heval : ∀ j ≤ k, ∀ t,
      iteratedDeriv j e t = iteratedDeriv j f t - (derivative^[j] p).eval t := by
    intro j hj t
    rw [he_def, iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by exact_mod_cast hj))
      ((contDiff_eval p k).contDiffAt.of_le (by exact_mod_cast hj)), iteratedDeriv_eval]
  -- the zeros of the derivatives of the error, by the generalized Rolle theorem
  have hzero : ∀ j ≤ k, ∃ ξ ∈ Icc u v, iteratedDeriv j e ξ = 0 := by
    intro j hj
    cases j with
    | zero => exact ⟨y 0, hymem 0, by simp [he_def, hpy]⟩
    | succ i =>
      obtain ⟨c, hc, hc0⟩ := exists_iteratedDeriv_eq_zero_of_forall_eq_zero
        (he.of_le (by exact_mod_cast hj)) (s := Finset.univ.image y)
        (by rw [Finset.card_image_of_injective _ hy, Finset.card_univ, Fintype.card_fin]; omega)
        (fun t ht => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht; exact hymem i)
        (fun t ht => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht; simp [he_def, hpy])
      exact ⟨c, Ioo_subset_Icc_self hc, hc0⟩
  -- the top derivative of `p` is constant
  have hpk : ∀ s t, (derivative^[k] p).eval s = (derivative^[k] p).eval t := by
    intro s t
    have : (derivative^[k] p).natDegree ≤ 0 :=
      (natDegree_iterate_derivative p k).trans (by
        have := natDegree_le_of_degree_le hp; omega)
    rw [eq_C_of_natDegree_le_zero this, eval_C, eval_C]
  -- downward induction
  suffices H : ∀ d j, j + d = k → ∀ t ∈ Icc u v,
      |iteratedDeriv j e t| ≤ h ^ (k - j) * √h * √(∫ t in u..v, g t ^ 2) by
    rw [← heval m hm]
    exact H (k - m) m (by omega) t ht
  intro d
  induction d with
  | zero =>
    intro j hj t ht
    obtain rfl : k = j := by omega
    obtain ⟨ξ, hξ, hξ0⟩ := hzero k le_rfl
    have : iteratedDeriv k e t = ∫ r in ξ..t, g r := by
      rw [← sub_zero (iteratedDeriv k e t), ← hξ0, heval k le_rfl, heval k le_rfl, hpk ξ t,
        ← hfg ξ hξ t ht]
      ring
    rw [this, Nat.sub_self, pow_zero, one_mul]
    exact (abs_intervalIntegral_le_sqrt_mul_sqrt huv.le hg hg2 hξ ht).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hh) (Real.sqrt_nonneg _))
  | succ d ih =>
    intro j hj t ht
    have hjk : j < k := by omega
    have ih' := ih (j + 1) (by omega)
    obtain ⟨ξ, hξ, hξ0⟩ := hzero j hjk.le
    -- the fundamental theorem of calculus for `e^{(j)}`
    have hderiv : ∀ x, HasDerivAt (iteratedDeriv j e) (iteratedDeriv (j + 1) e x) x := fun x => by
      rw [iteratedDeriv_succ]
      exact (he.differentiable_iteratedDeriv j (by exact_mod_cast hjk) x).hasDerivAt
    have hcont : Continuous (iteratedDeriv (j + 1) e) :=
      he.continuous_iteratedDeriv (j + 1) (by exact_mod_cast hjk)
    have hftc : iteratedDeriv j e t = ∫ r in ξ..t, iteratedDeriv (j + 1) e r := by
      rw [integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont.intervalIntegrable _ _), hξ0,
        sub_zero]
    -- the bound on the integrand, over an interval of length at most `h`
    have hbound : ∀ x ∈ Ι ξ t, ‖iteratedDeriv (j + 1) e x‖
        ≤ h ^ (k - (j + 1)) * √h * √(∫ t in u..v, g t ^ 2) := fun x hx =>
      ih' x (Icc_subset_Icc (le_min hξ.1 ht.1) (max_le hξ.2 ht.2) (Ioc_subset_Icc_self hx))
    have hlen : |t - ξ| ≤ h := by
      rw [abs_sub_le_iff]; constructor <;> linarith [hξ.1, hξ.2, ht.1, ht.2]
    calc |iteratedDeriv j e t| = ‖∫ r in ξ..t, iteratedDeriv (j + 1) e r‖ := by
          rw [hftc, Real.norm_eq_abs]
      _ ≤ h ^ (k - (j + 1)) * √h * √(∫ t in u..v, g t ^ 2) * |t - ξ| :=
          norm_integral_le_of_norm_le_const hbound
      _ ≤ h ^ (k - (j + 1)) * √h * √(∫ t in u..v, g t ^ 2) * h :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = h ^ (k - j) * √h * √(∫ t in u..v, g t ^ 2) := by
          rw [show k - j = k - (j + 1) + 1 by omega, pow_succ]; ring

/-- Let $u < v$ and $v - u \le h$, and let $m \le k$ be natural numbers. Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^k$, and let $g$ be a function such that $g$
and $g^2$ are integrable on $[u, v]$ and $f^{(k)}(t) - f^{(k)}(s) = \int_s^t g$ for all
$s, t \in [u, v]$. Let $p$ be a polynomial of degree at most $k$ that interpolates $f$ at
$k + 1$ distinct points of $[u, v]$. Then
$$\int_u^v \bigl(f^{(m)}(t) - p^{(m)}(t)\bigr)^2 \, dt \le h^{2(k+1-m)} \int_u^v g^2.$$
This is Theorem 8.3 of [quarteroni2000numerical] on one panel, with the constant $1$.

For $m = k + 1$ the statement would be the trivial $\int g^2 \le \int g^2$. The proof squares
and integrates `abs_iteratedDeriv_sub_le`. -/
theorem integral_sq_iteratedDeriv_sub_le {k m : ℕ} {u v h : ℝ} (huv : u < v) (hh : v - u ≤ h)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ k f) (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume u v)
    (hfg : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {p : ℝ[X]} (hp : p.degree ≤ k) {y : Fin (k + 1) → ℝ} (hy : Function.Injective y)
    (hymem : ∀ i, y i ∈ Icc u v) (hpy : ∀ i, p.eval (y i) = f (y i)) (hm : m ≤ k) :
    ∫ t in u..v, (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * ∫ t in u..v, g t ^ 2 := by
  have h0 : 0 ≤ h := (sub_pos.2 huv).le.trans hh
  have hI : 0 ≤ ∫ t in u..v, g t ^ 2 := integral_nonneg huv.le fun _ _ => sq_nonneg _
  set C := h ^ (k - m) * √h * √(∫ t in u..v, g t ^ 2) with hC
  have hpt : ∀ t ∈ Icc u v, (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2 ≤ C ^ 2 :=
    fun t ht => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_iteratedDeriv_sub_le huv hh hf hg hg2 hfg hp hy hymem hpy hm ht) 2
  have hcont : Continuous fun t => (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2 :=
    ((hf.continuous_iteratedDeriv m (by exact_mod_cast hm)).sub
      (Polynomial.continuous _)).pow 2
  calc ∫ t in u..v, (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2
      ≤ ∫ _ in u..v, C ^ 2 :=
        integral_mono_on huv.le (hcont.intervalIntegrable _ _) intervalIntegrable_const hpt
    _ = (v - u) * C ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ h * C ^ 2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    _ = h ^ (2 * (k + 1 - m)) * ∫ t in u..v, g t ^ 2 := by
        rw [hC, mul_pow, mul_pow, Real.sq_sqrt h0, Real.sq_sqrt hI, ← pow_mul,
          show 2 * (k + 1 - m) = 2 * (k - m) + 1 + 1 by omega, pow_succ, pow_succ]
        ring

/-! ### Theorem 8.3 -/

/-- Let $a = x_0 < x_1 < \dots < x_{n+1} = b$, with nodes `node`, be a panel node system of degree
$k$ on $[a, b]$, and let $x_{j+1} - x_j \le h$ for $j = 0, \dots, n$. Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^k$, and let $g$ be a function such that $g$
and $g^2$ are integrable on $[a, b]$ and $f^{(k)}(t) - f^{(k)}(s) = \int_s^t g$ for all
$s, t \in [a, b]$. Let $F \in C([a, b])$ be the restriction of $f$, and let $m \le k$. Then
$$\sum_{j=0}^{n} \int_{x_j}^{x_{j+1}} \bigl(f^{(m)} - (\Pi_h^k f)^{(m)}\bigr)^2 \le h^{2(k+1-m)}
  \int_a^b g^2,$$
where on the panel $j$ the interpolant $\Pi_h^k f$ is the polynomial `panelPoly node j F`. This
is Theorem 8.3 of [quarteroni2000numerical] as a sum over the panels, with the constant $1$.

The panel node system is `IsPanelNodes n k x node`. The proof sums the panel estimate
`integral_sq_iteratedDeriv_sub_le` over the panels. -/
theorem sum_integral_sq_sub_panelPoly_le {a b : ℝ} {n k m : ℕ} {x : ℕ → Icc a b}
    {node : ℕ → Fin (k + 1) → Icc a b} (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) (hm : m ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (iteratedDeriv m f t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * ∫ t in a..b, g t ^ 2 := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  -- the right-hand side over the whole interval is the sum over the panels
  have hsplit : ∫ t in a..b, g t ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j _ =>
      hg2.mono_set (hsub' j)]
    simp only [hnode.first, hnode.last]
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine integral_sq_iteratedDeriv_sub_le (hnode.step j hj) (hmesh j hj) hf (hg.mono_set (hsub' j))
    (hg2.mono_set (hsub' j)) (fun s hs t ht => hfg s (hsub j s hs) t (hsub j t ht)) ?_
    (hnode.injective j hj) (hnode.mem j hj) (fun i => ?_) hm
  · refine (Lagrange.degree_interpolate_le _ (hnode.injective j hj).injOn).trans ?_
    simp
  · rw [panelPoly, Lagrange.eval_interpolate_at_node _ (hnode.injective j hj).injOn
      (Finset.mem_univ i), hF]

section PiecewisePolynomial

variable {a b : ℝ} {n k : ℕ} {x : ℕ → Icc a b} {node : ℕ → Fin (k + 1) → Icc a b}

/-- Let $a = x_0 < x_1 < \dots < x_{n+1} = b$, with nodes `node`, be a panel node system of degree
$k$ on $[a, b]$, and let $x_{j+1} - x_j \le h$ for $j = 0, \dots, n$. Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^k$, and let $g$ be a function such that $g$
and $g^2$ are integrable on $[a, b]$ and $f^{(k)}(t) - f^{(k)}(s) = \int_s^t g$ for all
$s, t \in [a, b]$. Let $F \in C([a, b])$ be the restriction of $f$, and let
$G \colon \mathbb{R} \to \mathbb{R}$ be any function that agrees on $[a, b]$ with the piecewise
polynomial interpolant $\Pi_h^k F$. Then
$$\int_a^b (f - G)^2 \le h^{2(k+1)} \int_a^b g^2.$$
This is (8.26) of [quarteroni2000numerical] with $m = 0$ and the constant $1$.

The panel node system is `IsPanelNodes n k x node`, and $\Pi_h^k F$ is
`piecewisePolyInterpCLM n k x node F`. -/
theorem integral_sq_sub_piecewisePolyInterpCLM_le (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) {G : ℝ → ℝ}
    (hG : ∀ t : Icc a b, G t = piecewisePolyInterpCLM n k x node F t) :
    ∫ t in a..b, (f t - G t) ^ 2 ≤ h ^ (2 * (k + 1)) * ∫ t in a..b, g t ^ 2 := by
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  -- on a panel, `G` is the panel polynomial
  have hpanel : ∀ j ≤ n, EqOn (fun t => (f t - G t) ^ 2)
      (fun t => (iteratedDeriv 0 f t - (derivative^[0] (panelPoly node j F)).eval t) ^ 2)
      (Icc (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
    rw [hG ⟨t, hsub j t ht⟩, piecewisePolyInterpCLM_apply_of_mem hnode F hj ht.1 ht.2]
  have hint : ∀ j ≤ n, IntervalIntegrable (fun t => (f t - G t) ^ 2) volume (x j) (x (j + 1)) :=
    fun j hj => by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hnode.step j hj).le]
      refine ContinuousOn.integrableOn_Icc ?_
      exact ((((hf.continuous.sub (Polynomial.continuous _)).pow 2).continuousOn).congr
        (hpanel j hj))
  have hsplit : ∫ t in a..b, (f t - G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (f t - G t) ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j hj =>
      hint j (Nat.lt_succ_iff.1 hj)]
    simp only [hnode.first, hnode.last]
  rw [hsplit]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (f t - G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (iteratedDeriv 0 f t - (derivative^[0] (panelPoly node j F)).eval t) ^ 2 :=
        Finset.sum_congr rfl fun j hj => integral_congr ((uIcc_of_le
          (hnode.step j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).le).symm ▸
          hpanel j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    _ ≤ h ^ (2 * (k + 1 - 0)) * ∫ t in a..b, g t ^ 2 :=
        sum_integral_sq_sub_panelPoly_le hnode hmesh hf hg hg2 hfg hF (Nat.zero_le k)
    _ = h ^ (2 * (k + 1)) * ∫ t in a..b, g t ^ 2 := by rw [Nat.sub_zero]

/-- Let $a = x_0 < x_1 < \dots < x_{n+1} = b$, with nodes `node`, be a panel node system of degree
$k \ge 1$ on $[a, b]$, and let $x_{j+1} - x_j \le h$ for $j = 0, \dots, n$. Let
$f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^k$, and let $g$ be a function such that $g$
and $g^2$ are integrable on $[a, b]$ and $f^{(k)}(t) - f^{(k)}(s) = \int_s^t g$ for all
$s, t \in [a, b]$. Let $F \in C([a, b])$ be the restriction of $f$, and let
$G \colon \mathbb{R} \to \mathbb{R}$ be any function that agrees on $[a, b]$ with the piecewise
polynomial interpolant $\Pi_h^k F$. Then
$$\sum_{j=0}^{n} \int_{x_j}^{x_{j+1}} (f' - G')^2 \le h^{2k} \int_a^b g^2.$$
This is (8.26) of [quarteroni2000numerical] with $m = 1$ and the constant $1$.

The panel node system is `IsPanelNodes n k x node`, $\Pi_h^k F$ is
`piecewisePolyInterpCLM n k x node F`, and $G'$ is `deriv G`. Inside a panel, $G$ is the panel
polynomial, so $G'$ is the derivative of that polynomial. The values of $G'$ at the breakpoints
do not change the integrals. -/
theorem integral_sq_deriv_sub_piecewisePolyInterpCLM_le (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) {G : ℝ → ℝ}
    (hG : ∀ t : Icc a b, G t = piecewisePolyInterpCLM n k x node F t) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (deriv f t - deriv G t) ^ 2
      ≤ h ^ (2 * k) * ∫ t in a..b, g t ^ 2 := by
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  -- inside a panel, `G'` is the derivative of the panel polynomial
  have hpanel : ∀ j ≤ n, EqOn (fun t => (deriv f t - deriv G t) ^ 2)
      (fun t => (iteratedDeriv 1 f t - (derivative^[1] (panelPoly node j F)).eval t) ^ 2)
      (Ioo (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    have hev : G =ᶠ[𝓝 t] fun s => (panelPoly node j F).eval s := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      rw [hG ⟨s, hsub j s hs⟩, piecewisePolyInterpCLM_apply_of_mem hnode F hj hs.1 hs.2]
    simp only [iteratedDeriv_one, Function.iterate_one]
    rw [hev.deriv_eq, Polynomial.deriv]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (deriv f t - deriv G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (iteratedDeriv 1 f t - (derivative^[1] (panelPoly node j F)).eval t) ^ 2 :=
        Finset.sum_congr rfl fun j hj => integral_congr_Ioo
          (hnode.step j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).le
          (hpanel j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    _ ≤ h ^ (2 * (k + 1 - 1)) * ∫ t in a..b, g t ^ 2 :=
        sum_integral_sq_sub_panelPoly_le hnode hmesh hf hg hg2 hfg hF hk
    _ = h ^ (2 * k) * ∫ t in a..b, g t ^ 2 := by rw [Nat.add_sub_cancel]

end PiecewisePolynomial

section PiecewiseLinear

variable {a b : ℝ} {n : ℕ} {x : ℕ → Icc a b}

/-- The affine interpolant of $f$ at $u < v$ is a polynomial $p$ of degree at most $1$ with
$p(t) = f(u) + (f(v) - f(u))(t - u)/(v - u)$ and the constant derivative
$(f(v) - f(u))/(v - u)$. -/
private theorem exists_linear_interp {u v : ℝ} (huv : u < v) (f : ℝ → ℝ) :
    ∃ p : ℝ[X], p.degree ≤ 1 ∧ (∀ t, p.eval t = f u + (f v - f u) * ((t - u) / (v - u))) ∧
      (∀ t, (derivative p).eval t = (f v - f u) / (v - u)) ∧ p.eval u = f u ∧ p.eval v = f v := by
  have hne : v - u ≠ 0 := sub_ne_zero.2 huv.ne'
  set β := (f v - f u) / (v - u) with hβ
  have heval : ∀ t,
      (C β * X + C (f u - β * u)).eval t = f u + (f v - f u) * ((t - u) / (v - u)) := by
    intro t
    simp only [eval_add, eval_mul, eval_C, eval_X, hβ]
    field_simp
    ring
  refine ⟨C β * X + C (f u - β * u), degree_linear_le, heval, fun t => ?_, ?_, ?_⟩
  · simp [derivative_mul]
  · rw [heval, sub_self, zero_div, mul_zero, add_zero]
  · rw [heval, div_self hne, mul_one, add_sub_cancel]

/-- On the panel $j$, the affine interpolant $p$ of $f$ at $x_j$ and $x_{j+1}$ satisfies
$\int_{x_j}^{x_{j+1}} (f^{(m)} - p^{(m)})^2 \le h^{2(2-m)} \int_{x_j}^{x_{j+1}} g^2$ for
$m \le 1$. -/
private theorem integral_sq_sub_linear_le (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, deriv f t - deriv f s = ∫ r in s..t, g r) {j : ℕ}
    (hj : j ≤ n) {p : ℝ[X]} (hp : p.degree ≤ 1) (hpu : p.eval (x j : ℝ) = f (x j))
    (hpv : p.eval (x (j + 1) : ℝ) = f (x (j + 1))) {m : ℕ} (hm : m ≤ 1) :
    ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2
      ≤ h ^ (2 * (1 + 1 - m)) * ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub : ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  have hsub' : [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  have hlt := hstep j hj
  refine integral_sq_iteratedDeriv_sub_le (k := 1) hlt (hmesh j hj) hf (hg.mono_set hsub')
    (hg2.mono_set hsub') (fun s hs t ht => by
      simpa only [iteratedDeriv_one] using hfg s (hsub s hs) t (hsub t ht))
    (by exact_mod_cast hp) (y := ![(x j : ℝ), (x (j + 1) : ℝ)]) ?_ ?_ ?_ hm
  · intro i i' hii'
    fin_cases i <;> fin_cases i' <;> simp_all [hlt.ne, hlt.ne']
  · intro i
    fin_cases i
    · exact left_mem_Icc.2 hlt.le
    · exact right_mem_Icc.2 hlt.le
  · intro i
    fin_cases i
    · exact hpu
    · exact hpv

/-- Let $a = x_0 < x_1 < \dots < x_{n+1} = b$ be a partition of $[a, b]$ with $x_{j+1} - x_j \le h$
for $j = 0, \dots, n$. Let $f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^1$, and let $g$
be a function such that $g$ and $g^2$ are integrable on $[a, b]$ and
$f'(t) - f'(s) = \int_s^t g$ for all $s, t \in [a, b]$. Let $F \in C([a, b])$ be the restriction
of $f$, and let $G \colon \mathbb{R} \to \mathbb{R}$ be any function that agrees on $[a, b]$
with the piecewise linear interpolant $\Pi_h^1 F$. Then
$$\int_a^b (f - G)^2 \le h^4 \int_a^b g^2.$$
This is (8.27) of [quarteroni2000numerical] with the constant $C_1 = 1$.

The partition is `IsIntervalPartition a b (n + 1)`, and $\Pi_h^1 F$ is
`piecewiseLinearInterpCLM n x F`. -/
theorem integral_sq_sub_piecewiseLinearInterpCLM_le
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, deriv f t - deriv f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) {G : ℝ → ℝ}
    (hG : ∀ t : Icc a b, G t = piecewiseLinearInterpCLM n x F t) :
    ∫ t in a..b, (f t - G t) ^ 2 ≤ h ^ 4 * ∫ t in a..b, g t ^ 2 := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  -- the affine interpolants of the panels
  choose p hp hpeval _hpderiv hpu hpv using fun j (hj : j ≤ n) =>
    exists_linear_interp (hstep j hj) f
  have hpanel : ∀ j (hj : j ≤ n), EqOn (fun t => (f t - G t) ^ 2)
      (fun t => (iteratedDeriv 0 f t - (derivative^[0] (p j hj)).eval t) ^ 2)
      (Icc (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
    rw [hG ⟨t, hsub j t ht⟩, piecewiseLinearInterpCLM_apply_of_mem hstep F hj ht.1 ht.2, hpeval,
      hF, hF]
  have hint : ∀ j ≤ n, IntervalIntegrable (fun t => (f t - G t) ^ 2) volume (x j) (x (j + 1)) :=
    fun j hj => by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hstep j hj).le]
      exact ContinuousOn.integrableOn_Icc
        ((((hf.continuous.sub (Polynomial.continuous _)).pow 2).continuousOn).congr (hpanel j hj))
  have hsplit : ∫ t in a..b, (f t - G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (f t - G t) ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j hj =>
      hint j (Nat.lt_succ_iff.1 hj)]
    simp only [hx.first, hx.last]
  have hsplit' : ∫ t in a..b, g t ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j _ => hg2.mono_set (hsub' j)]
    simp only [hx.first, hx.last]
  rw [hsplit, hsplit', Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [integral_congr ((uIcc_of_le (hstep j hj).le).symm ▸ hpanel j hj)]
  exact integral_sq_sub_linear_le hstep hmesh hf hg hg2 hfg hj (hp j hj) (hpu j hj) (hpv j hj)
    (Nat.zero_le 1)

/-- Let $a = x_0 < x_1 < \dots < x_{n+1} = b$ be a partition of $[a, b]$ with $x_{j+1} - x_j \le h$
for $j = 0, \dots, n$. Let $f \colon \mathbb{R} \to \mathbb{R}$ be of class $C^1$, and let $g$
be a function such that $g$ and $g^2$ are integrable on $[a, b]$ and
$f'(t) - f'(s) = \int_s^t g$ for all $s, t \in [a, b]$. On the panel $j$, the derivative of the
piecewise linear interpolant $\Pi_h^1 f$ is the difference quotient
$(f(x_{j+1}) - f(x_j))/(x_{j+1} - x_j)$, and
$$\sum_{j=0}^{n} \int_{x_j}^{x_{j+1}} \left( f'(t) - \frac{f(x_{j+1}) - f(x_j)}{x_{j+1} - x_j}
  \right)^2 dt \le h^2 \int_a^b g^2.$$
This is (8.27) of [quarteroni2000numerical] with the constant $C_2 = 1$.

The partition is `IsIntervalPartition a b (n + 1)`. -/
theorem integral_sq_deriv_sub_piecewiseLinearInterpCLM_le
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, deriv f t - deriv f s = ∫ r in s..t, g r) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (deriv f t - (f (x (j + 1)) - f (x j)) / ((x (j + 1) : ℝ) - (x j : ℝ))) ^ 2
      ≤ h ^ 2 * ∫ t in a..b, g t ^ 2 := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  choose p hp _hpeval hpderiv hpu hpv using fun j (hj : j ≤ n) =>
    exists_linear_interp (hstep j hj) f
  have hsplit' : ∫ t in a..b, g t ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j _ => hg2.mono_set (hsub' j)]
    simp only [hx.first, hx.last]
  rw [hsplit', Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := integral_sq_sub_linear_le hstep hmesh hf hg hg2 hfg hj (hp j hj) (hpu j hj) (hpv j hj)
    le_rfl
  simpa only [iteratedDeriv_one, Function.iterate_one, hpderiv] using this

end PiecewiseLinear

/-! ### Theorem 8.3 over $H^{k+1}(a, b)$ -/

section Sobolev

variable {a b : ℝ}

open SobolevInterval in
/-- Let $a < b$, let $u \in H^{k+1}(a, b)$, and let $F \in C([a, b])$ agree with $u$ almost
everywhere on $(a, b)$. Let $a = x_0 < x_1 < \dots < x_{n+1} = b$, with nodes `node`, be a panel
node system of degree $k$ on $[a, b]$, with $x_{j+1} - x_j \le h$ for $j = 0, \dots, n$, and let
$m \le k$. Let $\tilde F$ be the extension of $F$ to $\mathbb{R}$ by its endpoint values:
$\tilde F(t) = F(a)$ for $t < a$ and $\tilde F(t) = F(b)$ for $t > b$. Then
$$\sum_{j=0}^{n} \int_{x_j}^{x_{j+1}} \bigl(\tilde F^{(m)} - (\Pi_h^k F)^{(m)}\bigr)^2 \le
  h^{2(k+1-m)} |u|_{H^{k+1}(a, b)}^2,$$
where on the panel $j$ the interpolant $\Pi_h^k F$ is the polynomial `panelPoly node j F`, and
$|u|_{H^{k+1}(a, b)} = \|u^{(k+1)}\|_{L^2(a, b)}$. This is Theorem 8.3 of
[quarteroni2000numerical] for $u \in H^{k+1}(a, b)$, which is (8.26) with the constant $1$, as a
sum over the panels.

The panel node system is `IsPanelNodes n k x node`, and the function of $u$ is
`SobolevIntervalLp.fn u`. The extension of $F$ is `Set.IccExtend`. The seminorm is
`SobolevInterval.seminorm (k + 1) a b`. Inside $(a, b)$, $\tilde F^{(m)}$ is the $m$-th
derivative of the $C^k$ representative of $u$ from `SobolevInterval.exists_contDiff_ae_eq`. For
$m = 0$ and $m = 1$ the left side is the square of the $L^2(a, b)$ norm of
$(F - \Pi_h^k F)^{(m)}$, that is, of the $H^m(a, b)$ seminorm of the error.
`integral_sq_sub_piecewisePolyInterpCLM_le_seminorm` states the case $m = 0$ with the
interpolation operator on $[a, b]$. -/
theorem sobolevSeminorm_sub_piecewisePolyInterp_le (hab : a < b) {k : ℕ}
    (u : SobolevInterval (k + 1) a b) {n : ℕ} {x : ℕ → Icc a b}
    {node : ℕ → Fin (k + 1) → Icc a b} (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {F : C(Icc a b, ℝ)}
    (hF : fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hab.le F) {m : ℕ} (hm : m ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (iteratedDeriv m (IccExtend hab.le F) t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * seminorm (k + 1) a b u ^ 2 := by
  obtain ⟨f, hf, hae, hftc⟩ := exists_contDiff_ae_eq hab u
  have hf0 : fn u =ᵐ[volume.restrict (Ioo a b)] f := by
    rw [← deriv_zero u]; simpa using hae 0
  -- the continuous representative is the `C^k` representative on `[a, b]`
  have hFf : EqOn (IccExtend hab.le F) f (Icc a b) :=
    eqOn_Icc_of_ae_eq hab F.continuous.Icc_extend'.continuousOn hf.continuous.continuousOn
      (hF.symm.trans hf0)
  have hF' : ∀ t, F t = f t := fun t => by rw [← IccExtend_val hab.le F t, hFf t.2]
  have hpanel : ∀ j ≤ n, EqOn
      (fun t => (iteratedDeriv m (IccExtend hab.le F) t
        - (derivative^[m] (panelPoly node j F)).eval t) ^ 2)
      (fun t => (iteratedDeriv m f t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2)
      (Ioo (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    have hev : IccExtend hab.le F =ᶠ[𝓝 t] f := by
      filter_upwards [Icc_mem_nhds ((x j).2.1.trans_lt ht.1) (ht.2.trans_le (x (j + 1)).2.2)]
        with s hs using hFf hs
    simp only [hev.iteratedDeriv_eq m]
  rw [seminorm_sq_eq_integral hab.le]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (iteratedDeriv m (IccExtend hab.le F) t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (iteratedDeriv m f t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2 :=
        Finset.sum_congr rfl fun j hj => integral_congr_Ioo
          (hnode.step j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).le
          (hpanel j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    _ ≤ _ := sum_integral_sq_sub_panelPoly_le hnode hmesh hf (intervalIntegrable_deriv hab.le u _)
        (intervalIntegrable_deriv_sq hab.le u _) hftc hF' hm

open SobolevInterval in
/-- Let $a < b$, let $u \in H^{k+1}(a, b)$, and let $F \in C([a, b])$ agree with $u$ almost
everywhere on $(a, b)$. Let $a = x_0 < x_1 < \dots < x_{n+1} = b$, with nodes `node`, be a panel
node system of degree $k$ on $[a, b]$, with $x_{j+1} - x_j \le h$ for $j = 0, \dots, n$. Then
$$\|F - \Pi_h^k F\|_{L^2(a, b)}^2 \le h^{2(k+1)} |u|_{H^{k+1}(a, b)}^2.$$
This is (8.26) of [quarteroni2000numerical] for $u \in H^{k+1}(a, b)$, with $m = 0$ and the
constant $1$.

The panel node system is `IsPanelNodes n k x node`, and $\Pi_h^k F$ is
`piecewisePolyInterpCLM n k x node F`. The left side is the integral over $[a, b]$ of the square
of the difference of the extensions `Set.IccExtend` of $F$ and $\Pi_h^k F$. The seminorm is
`SobolevInterval.seminorm (k + 1) a b`. -/
theorem integral_sq_sub_piecewisePolyInterpCLM_le_seminorm (hab : a < b) {k : ℕ}
    (u : SobolevInterval (k + 1) a b) {n : ℕ} {x : ℕ → Icc a b}
    {node : ℕ → Fin (k + 1) → Icc a b} (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {F : C(Icc a b, ℝ)}
    (hF : fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hab.le F) :
    ∫ t in a..b,
        (IccExtend hab.le F t - IccExtend hab.le (piecewisePolyInterpCLM n k x node F) t) ^ 2
      ≤ h ^ (2 * (k + 1)) * seminorm (k + 1) a b u ^ 2 := by
  obtain ⟨f, hf, hae, hftc⟩ := exists_contDiff_ae_eq hab u
  have hf0 : fn u =ᵐ[volume.restrict (Ioo a b)] f := by
    rw [← deriv_zero u]; simpa using hae 0
  have hFf : EqOn (IccExtend hab.le F) f (Icc a b) :=
    eqOn_Icc_of_ae_eq hab F.continuous.Icc_extend'.continuousOn hf.continuous.continuousOn
      (hF.symm.trans hf0)
  have hF' : ∀ t, F t = f t := fun t => by rw [← IccExtend_val hab.le F t, hFf t.2]
  rw [seminorm_sq_eq_integral hab.le, integral_congr_Ioo hab.le
    (h := fun t => (f t - IccExtend hab.le (piecewisePolyInterpCLM n k x node F) t) ^ 2)
    (fun t ht => by simp only [hFf (Ioo_subset_Icc_self ht)])]
  exact integral_sq_sub_piecewisePolyInterpCLM_le hnode hmesh hf
    (intervalIntegrable_deriv hab.le u _) (intervalIntegrable_deriv_sq hab.le u _) hftc hF'
    fun t => IccExtend_val hab.le _ t

end Sobolev
