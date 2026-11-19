/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.SobolevInterpolation
import Numlib.Approximation.Spline
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 8.3: Piecewise Lagrange interpolation

This module formalizes Section 8.3 of [quarteroni2000numerical]. A partition $\mathcal{T}_h$ of
$[a, b]$ divides it into $K$ subintervals $I_j = [x_j, x_{j+1}]$ of length $h_j \le h$. On each
$I_j$ take the $k + 1$ equally spaced nodes $x_j^{(i)} = x_j + (i/k)(x_{j+1} - x_j)$,
$0 \le i \le k$. The piecewise interpolation polynomial $\Pi_h^k f$ is, on each $I_j$, the Lagrange
interpolant of $f$ at these nodes, and it lies in the space $X_h^k$ of continuous piecewise
polynomials of degree $k$ (8.22). The module proves the uniform error estimate
$$\|f - \Pi_h^k f\|_\infty \le C h^{k+1} \|f^{(k+1)}\|_\infty \tag{8.23}$$
with $C = 1/(k+1)!$, the $L^2$ estimates $\|(f - \Pi_h^k f)^{(m)}\|_{L^2(a,b)} \le C h^{k+1-m}
\|f^{(k+1)}\|_{L^2(a,b)}$ of Theorem 8.3 with $C = 1$, and their case $k = 1$ (8.27).

The piecewise interpolation operator is `piecewisePolyInterpCLM` of
`Numlib.Approximation.Interpolation`, whose node systems `IsPanelNodes` are here the equally spaced
nodes. The space $X_h^k$ is the spline space of degree $k$ and smoothness $C^0$,
`Spline.splineSpace a b K x k 0` of `Numlib.Approximation.Spline`. The $L^2$ estimates come from
`Numlib.Approximation.SobolevInterpolation`, over the Sobolev space $H^{k+1}(a, b)$ of
`Numlib.Analysis.Sobolev.Interval`.

## Main definitions

* Section 8.3, `QuarteroniSaccoSaleri.Chapter08.equispacedPanelNodes`: the $k + 1$ equally spaced
  nodes of the subinterval $I_j$.
* Section 8.3, `QuarteroniSaccoSaleri.Chapter08.piecewiseLagrangeInterp`: the piecewise
  interpolation operator $\Pi_h^k$ on $C([a, b])$.
* (8.22), `QuarteroniSaccoSaleri.Chapter08.equation_8_22`: the space $X_h^k$ of continuous piecewise
  polynomials.

## Main results

* Section 8.3, `QuarteroniSaccoSaleri.Chapter08.isPanelNodes_equispacedPanelNodes`: the equally
  spaced nodes form a node system for each subinterval.
* Section 8.3, `QuarteroniSaccoSaleri.Chapter08.piecewiseLagrangeInterp_apply_of_mem`: on $I_j$,
  $\Pi_h^k f$ is the Lagrange interpolant of $f$ at the nodes of $I_j$.
* (8.22), `QuarteroniSaccoSaleri.Chapter08.mem_equation_8_22_iff`: $v \in X_h^k$ if and only if $v$
  is a polynomial of degree at most $k$ on each $I_j$.
* Section 8.3, `QuarteroniSaccoSaleri.Chapter08.range_piecewiseLagrangeInterp`: $X_h^k$ is the range
  of $\Pi_h^k$.
* (8.23), `QuarteroniSaccoSaleri.Chapter08.equation_8_23_of_forall_le`: the uniform estimate with a
  bound $M$ on $|f^{(k+1)}|$.
* (8.23), `QuarteroniSaccoSaleri.Chapter08.equation_8_23`: $\|f - \Pi_h^k f\|_\infty \le h^{k+1}
  \|f^{(k+1)}\|_\infty / (k+1)!$.
* Theorem 8.3, `QuarteroniSaccoSaleri.Chapter08.theorem_8_3_sq`: the squared form of the $L^2$
  estimates.
* Theorem 8.3, `QuarteroniSaccoSaleri.Chapter08.theorem_8_3`: $\|(f - \Pi_h^k f)^{(m)}\|_{L^2(a,b)}
  \le h^{k+1-m} \|f^{(k+1)}\|_{L^2(a,b)}$ for $0 \le m \le k + 1$.
* Theorem 8.3, `QuarteroniSaccoSaleri.Chapter08.theorem_8_3_L2`: the case $m = 0$ as an $L^2(a, b)$
  norm.
* (8.27), `QuarteroniSaccoSaleri.Chapter08.equation_8_27`: $\|f - \Pi_h^1 f\|_{L^2(a,b)} \le h^2
  \|f''\|_{L^2(a,b)}$.
* (8.27), `QuarteroniSaccoSaleri.Chapter08.equation_8_27_deriv`: $\|(f - \Pi_h^1 f)'\|_{L^2(a,b)}
  \le h \|f''\|_{L^2(a,b)}$.

## Conventions

* The breakpoints are a sequence `x : ℕ → Icc a b` of points of $[a, b]$ with
  `IsIntervalPartition a b K (fun j => (x j : ℝ))`, that is, $a = x_0 < x_1 < \cdots < x_K = b$,
  with $K \ge 1$ subintervals.
* The book's local degree $n$ is written $k \ge 1$ throughout, as the book does from (8.22) on.
* The mesh size $h = \max_j h_j$ enters as a bound $h_j \le h$ for every $j$, which is what the
  estimates use.
* A function $f \in C^{k+1}([a, b])$ is a function $f : \mathbb{R} \to \mathbb{R}$ of class
  $C^{k+1}$ on an open set that contains $[a, b]$, as in Theorem 8.2, and $F$ is its restriction to
  $[a, b]$. The norm $\|g\|_\infty$ is the supremum of $|g|$ over $[a, b]$.
* In Theorem 8.3, the hypothesis "$f^{(m)} \in L^2(a, b)$ for $0 \le m \le k + 1$" is
  $f \in H^{k+1}(a, b)$, an element of `SobolevInterval (k + 1) a b`. Its $m$-th weak derivative
  $f^{(m)}$ is `SobolevInterval.deriv u m`, and $\Pi_h^k$ is applied to its continuous
  representative `F : C(Icc a b, ℝ)`. The derivative $(\Pi_h^k f)^{(m)}$ is the classical $m$-th
  derivative of $\Pi_h^k F$, extended to $\mathbb{R}$ by its endpoint values; for $m \ge 2$ it
  exists only inside the subintervals. The $L^2(a, b)$ norm of such a broken function is the square
  root of the sum over the subintervals of the integrals of its square. The seminorm
  $\|f^{(k+1)}\|_{L^2(a,b)}$ is `SobolevInterval.seminorm (k + 1) a b u`.
* The space $L^2(a, b)$ and its norm, defined in (8.24)–(8.25), are Mathlib's
  `Lp ℝ 2 (volume.restrict (Ioo a b))` and its norm.

## Deviations from the source

* **Representation.** The continuous interpolation operator uses equispaced panel nodes and is
  characterized for positive degree. See `QuarteroniSaccoSaleri.Chapter08.equispacedPanelNodes`,
  `QuarteroniSaccoSaleri.Chapter08.equispacedPanelNodes_val`,
  `QuarteroniSaccoSaleri.Chapter08.isPanelNodes_equispacedPanelNodes`,
  `QuarteroniSaccoSaleri.Chapter08.piecewiseLagrangeInterp`,
  `QuarteroniSaccoSaleri.Chapter08.piecewiseLagrangeInterp_apply_of_mem`.
* **Generalization.** The uniform error estimate gives the explicit constant $1/(k+1)!$. See
  `QuarteroniSaccoSaleri.Chapter08.equation_8_23_of_forall_le`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_23`.
* **Reading.** The interpolation estimate uses panelwise derivatives of the interpolant and gives
  constant one. See `QuarteroniSaccoSaleri.Chapter08.theorem_8_3_sq`,
  `QuarteroniSaccoSaleri.Chapter08.theorem_8_3`, `QuarteroniSaccoSaleri.Chapter08.theorem_8_3_L2`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_27`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_27_deriv`.

## Not formalized

* **Example 8.5.** It is a table of computed errors.
-/

open MeasureTheory Polynomial Set
open scoped Interval Topology

namespace QuarteroniSaccoSaleri.Chapter08

variable {a b : ℝ} {K k : ℕ} {x : ℕ → Icc a b}

/-! ### The equally spaced nodes and the piecewise interpolation operator -/

/-- **Section 8.3** of [quarteroni2000numerical], the equally spaced nodes of a subinterval. On
$I_j = [x_j, x_{j+1}]$, the $k + 1$ nodes are
$$x_j^{(i)} = x_j + \frac{i}{k} (x_{j+1} - x_j), \qquad 0 \le i \le k,$$
as points of $[a, b]$.

For $k = 0$ the single node is $x_j$, by the Lean convention $a / 0 = 0$.

**Reading.** The implementation uses equally spaced local nodes and a continuous linear map. Its
node definition uses the left endpoint at degree zero, while the panel interpolation theorem assumes
degree at least one and a nonempty partition.
-/
noncomputable def equispacedPanelNodes (x : ℕ → Icc a b) (k : ℕ) (j : ℕ) (i : Fin (k + 1)) :
    Icc a b :=
  ⟨(x j : ℝ) + ((i : ℕ) : ℝ) / k * ((x (j + 1) : ℝ) - x j), by
    have hi : ((i : ℕ) : ℝ) / k ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.2) (by positivity)⟩
    simpa only [smul_eq_mul] using (convex_Icc a b).add_smul_sub_mem (x j).2 (x (j + 1)).2 hi⟩

/-- The value of the equally spaced node: $x_j^{(i)} = x_j + (i/k)(x_{j+1} - x_j)$.

**Reading.** The implementation uses equally spaced local nodes and a continuous linear map. Its
node definition uses the left endpoint at degree zero, while the panel interpolation theorem assumes
degree at least one and a nonempty partition.
-/
@[simp]
theorem equispacedPanelNodes_val (x : ℕ → Icc a b) (k j : ℕ) (i : Fin (k + 1)) :
    (equispacedPanelNodes x k j i : ℝ) = (x j : ℝ) + ((i : ℕ) : ℝ) / k * ((x (j + 1) : ℝ) - x j) :=
  rfl

/-- **Section 8.3** of [quarteroni2000numerical], the equally spaced nodes as a node system. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$, and let $k \ge 1$. Then for every subinterval $I_j$
the nodes $x_j^{(0)}, \ldots, x_j^{(k)}$ lie in $I_j$, are distinct, and start and end at the
endpoints of $I_j$.

The node system is `IsPanelNodes (K - 1) k x (equispacedPanelNodes x k)` of
`Numlib.Approximation.Interpolation`, whose subintervals are numbered $0, \ldots, K - 1$.

**Reading.** The implementation uses equally spaced local nodes and a continuous linear map. Its
node definition uses the left endpoint at degree zero, while the panel interpolation theorem assumes
degree at least one and a nonempty partition.
-/
theorem isPanelNodes_equispacedPanelNodes (hx : IsIntervalPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) : IsPanelNodes (K - 1) k x (equispacedPanelNodes x k) where
  step i hi := hx.step i (by omega)
  first := hx.first
  last := by rw [Nat.sub_add_cancel hK]; exact hx.last
  mem j hj i := by
    have hd : 0 ≤ (x (j + 1) : ℝ) - x j := sub_nonneg.mpr (hx.step j (by omega)).le
    have hθ : ((i : ℕ) : ℝ) / k ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp i.2) (by positivity)
    refine ⟨le_add_of_nonneg_right (mul_nonneg (by positivity) hd), ?_⟩
    rw [equispacedPanelNodes_val]
    nlinarith [mul_le_of_le_one_left hd hθ]
  injective j hj i i' hii' := by
    have hd : (x (j + 1) : ℝ) - x j ≠ 0 := sub_ne_zero.mpr (hx.step j (by omega)).ne'
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp only [equispacedPanelNodes_val, add_right_inj, mul_eq_mul_right_iff, hd, or_false,
      div_left_inj' hk', Nat.cast_inj] at hii'
    exact Fin.ext hii'
  node_zero j hj := Subtype.ext (by simp)
  node_last j hj := Subtype.ext (by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp [div_self hk'])

/-- **Section 8.3** of [quarteroni2000numerical], the piecewise interpolation polynomial. For a
partition $a = x_0 < \cdots < x_K = b$, the operator $\Pi_h^k$ on $C([a, b])$ maps $f$ to the
continuous function that on each subinterval $I_j$ is the Lagrange interpolant of $f$ at the
$k + 1$ equally spaced nodes of $I_j$.

The operator is `piecewisePolyInterpCLM` of `Numlib.Approximation.Interpolation` with the node
system `QuarteroniSaccoSaleri.Chapter08.equispacedPanelNodes x k`.

**Reading.** The implementation uses equally spaced local nodes and a continuous linear map. Its
node definition uses the left endpoint at degree zero, while the panel interpolation theorem assumes
degree at least one and a nonempty partition.
-/
noncomputable def piecewiseLagrangeInterp (x : ℕ → Icc a b) (K k : ℕ) :
    C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  piecewisePolyInterpCLM (K - 1) k x (equispacedPanelNodes x k)

/-- **Section 8.3** of [quarteroni2000numerical], $\Pi_h^k f$ on a subinterval. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$, let $k \ge 1$, let $f \in C([a, b])$ and $j < K$.
Then for every $t \in I_j = [x_j, x_{j+1}]$, $\Pi_h^k f(t)$ is the value at $t$ of the
polynomial that interpolates $f$ at the nodes $x_j^{(0)}, \ldots, x_j^{(k)}$. In the words of
the book, "the piecewise interpolation polynomial $\Pi_h^k f$ coincides on each $I_j$ with the
interpolating polynomial of $f|_{I_j}$ at the $k + 1$ nodes $x_j^{(i)}$".

The proof specializes `piecewisePolyInterpCLM_apply_of_mem`.

**Reading.** The implementation uses equally spaced local nodes and a continuous linear map. Its
node definition uses the left endpoint at degree zero, while the panel interpolation theorem assumes
degree at least one and a nonempty partition.
-/
theorem piecewiseLagrangeInterp_apply_of_mem (hx : IsIntervalPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) (f : C(Icc a b, ℝ)) {j : ℕ} (hj : j < K) {t : Icc a b}
    (h1 : (x j : ℝ) ≤ t) (h2 : (t : ℝ) ≤ x (j + 1)) :
    piecewiseLagrangeInterp x K k f t
      = (Lagrange.interpolate Finset.univ (fun i => (equispacedPanelNodes x k j i : ℝ))
          fun i => f (equispacedPanelNodes x k j i)).eval (t : ℝ) :=
  piecewisePolyInterpCLM_apply_of_mem (isPanelNodes_equispacedPanelNodes hx hK hk) f
    (by omega) h1 h2

/-! ### (8.22): the space $X_h^k$ -/

/-- **Equation (8.22)** of [quarteroni2000numerical], the piecewise polynomial space
$$X_h^k = \{v \in C^0([a, b]) : v|_{I_j} \in \mathbb{P}_k(I_j) \ \forall I_j \in
  \mathcal{T}_h\},$$
the continuous functions on $[a, b]$ whose restrictions to the subintervals
$I_j = [x_j, x_{j+1}]$, $j < K$, are polynomials of degree at most $k$.

The space is the spline space of degree $k$ and smoothness $C^0$,
`Spline.splineSpace a b K x k 0` of `Numlib.Approximation.Spline`. The result
`QuarteroniSaccoSaleri.Chapter08.mem_equation_8_22_iff` gives the phrasing of the book. -/
noncomputable def equation_8_22 (a b : ℝ) (K : ℕ) (x : ℕ → Icc a b) (k : ℕ) :
    Submodule ℝ C(Icc a b, ℝ) :=
  Spline.splineSpace a b K (fun j => (x j : ℝ)) k 0

/-- **Equation (8.22)** of [quarteroni2000numerical], membership. A function $v \in C([a, b])$ lies
in $X_h^k$ if and only if for every $j < K$ there is a polynomial $p$ of degree at most $k$ with
$v(t) = p(t)$ for all $t \in [a, b] \cap [x_j, x_{j+1}]$. -/
theorem mem_equation_8_22_iff (v : C(Icc a b, ℝ)) :
    v ∈ equation_8_22 a b K x k ↔
      ∀ j < K, ∃ p : ℝ[X], p.degree ≤ k ∧
        ∀ t : Icc a b, (t : ℝ) ∈ Icc (x j : ℝ) (x (j + 1) : ℝ) → v t = p.eval (t : ℝ) := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  constructor
  · rintro ⟨g, -, hv, hp⟩ j hj
    obtain ⟨p, hpd, hpe⟩ := hp j hj
    exact ⟨p, hpd, fun t ht => (hv t).trans (hpe ht)⟩
  · intro hv
    refine ⟨IccExtend hab v, contDiffOn_zero.mpr v.continuous.Icc_extend'.continuousOn,
      fun t => (IccExtend_val hab v t).symm, fun j hj => ?_⟩
    obtain ⟨p, hpd, hpe⟩ := hv j hj
    refine ⟨p, hpd, fun t ht => ?_⟩
    have ht' : t ∈ Icc a b := ⟨(x j).2.1.trans ht.1, ht.2.trans (x (j + 1)).2.2⟩
    rw [IccExtend_of_mem hab v ht', hpe ⟨t, ht'⟩ ht]

/-- **Section 8.3** of [quarteroni2000numerical], the range of $\Pi_h^k$. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$, and let $k \ge 1$. Then the range of $\Pi_h^k$ is
$X_h^k$: the piecewise interpolation polynomials are exactly the elements of $X_h^k$.

$\Pi_h^k f$ is a polynomial of degree at most $k$ on each subinterval, by
`QuarteroniSaccoSaleri.Chapter08.piecewiseLagrangeInterp_apply_of_mem`. An element of $X_h^k$ is
its own Lagrange interpolant on each subinterval, by `Lagrange.eq_interpolate_of_eval_eq`, so
$\Pi_h^k$ reproduces it. -/
theorem range_piecewiseLagrangeInterp (hx : IsIntervalPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) :
    LinearMap.range (piecewiseLagrangeInterp x K k : C(Icc a b, ℝ) →ₗ[ℝ] C(Icc a b, ℝ))
      = equation_8_22 a b K x k := by
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hcard : (Finset.univ : Finset (Fin (k + 1))).card = k + 1 := by simp
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    refine (mem_equation_8_22_iff _).mpr fun j hj => ⟨panelPoly (equispacedPanelNodes x k) j f,
      ?_, fun t ht => ?_⟩
    · have := Lagrange.degree_interpolate_le (s := Finset.univ)
        (fun i => f (equispacedPanelNodes x k j i)) (hnode.injective j (by omega)).injOn
      rwa [hcard, Nat.add_sub_cancel] at this
    · exact piecewisePolyInterpCLM_apply_of_mem hnode f (by omega) ht.1 ht.2
  · intro v hv
    refine ⟨v, ContinuousMap.ext fun t => ?_⟩
    obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hnode.first hnode.last t
    obtain ⟨p, hpd, hpe⟩ := (mem_equation_8_22_iff v).mp hv j (by omega)
    have hp : p = panelPoly (equispacedPanelNodes x k) j v := by
      refine Lagrange.eq_interpolate_of_eval_eq _ (hnode.injective j hj).injOn ?_ fun i _ => ?_
      · rw [hcard]
        exact hpd.trans_lt (by exact_mod_cast Nat.lt_succ_self k)
      · exact (hpe _ (hnode.mem j hj i)).symm
    change piecewisePolyInterpCLM (K - 1) k x (equispacedPanelNodes x k) v t = v t
    rw [piecewisePolyInterpCLM_apply_of_mem hnode v hj h1 h2, ← hp, hpe t ⟨h1, h2⟩]

/-! ### (8.23): the uniform error estimate -/

/-- **Equation (8.23)** of [quarteroni2000numerical], with an explicit bound on $f^{(k+1)}$. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$ subintervals of length at most $h$, and let
$k \ge 1$. Let $f$ be of class $C^{k+1}$ on an open set $U \supseteq [a, b]$, let $F$ be its
restriction to $[a, b]$, and let $|f^{(k+1)}| \le M$ on $[a, b]$. Then
$$\|F - \Pi_h^k F\|_\infty \le \frac{h^{k+1}}{(k+1)!} M.$$

The proof applies Theorem 8.2 on each subinterval, by
`exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn`, and bounds the nodal polynomial of a
subinterval by $h^{k+1}$ there.

**Generalization.** The theorem gives the explicit constant $1/(k+1)!$ and uses any upper bound on
the panel lengths. The derivatives are taken on an open neighborhood and evaluated on the closed
interval.
-/
theorem equation_8_23_of_forall_le (hx : IsIntervalPartition a b K fun j => (x j : ℝ))
    (hK : 1 ≤ K) (hk : 1 ≤ k) {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUsub : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f U) {F : C(Icc a b, ℝ)}
    (hF : ∀ t, F t = f t) {M : ℝ} (hM : ∀ s ∈ Icc a b, |iteratedDeriv (k + 1) f s| ≤ M) :
    ‖F - piecewiseLagrangeInterp x K k F‖ ≤ h ^ (k + 1) / (k + 1).factorial * M := by
  have hab := hx.lt_of_pos hK
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_rfl, hab.le⟩)
  have hh0 : 0 ≤ h := (sub_pos.mpr (hx.step 0 hK)).le.trans (hmesh 0 hK)
  have hfact : (0 : ℝ) < (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hnode.first hnode.last t
  have hsub : Icc (x j : ℝ) (x (j + 1) : ℝ) ⊆ U :=
    (Icc_subset_Icc (x j).2.1 (x (j + 1)).2.2).trans hUsub
  obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn hnode hU hj
    hsub hf hF h1 h2
  have hξmem : ξ ∈ Icc a b := ⟨(x j).2.1.trans hξ.1.le, hξ.2.le.trans (x (j + 1)).2.2⟩
  have hprod : |∏ i, ((t : ℝ) - (equispacedPanelNodes x k j i : ℝ))| ≤ h ^ (k + 1) := by
    rw [Finset.abs_prod]
    calc ∏ i, |(t : ℝ) - (equispacedPanelNodes x k j i : ℝ)| ≤ ∏ _i : Fin (k + 1), h := by
          refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
          rw [← Real.dist_eq]
          exact (Real.dist_le_of_mem_Icc ⟨h1, h2⟩ (hnode.mem j hj i)).trans (hmesh j (by omega))
      _ = h ^ (k + 1) := by simp
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, piecewiseLagrangeInterp, hξeq, abs_mul, abs_div,
    abs_of_pos hfact]
  calc |iteratedDeriv (k + 1) f ξ| / ((k + 1).factorial : ℝ)
        * |∏ i, ((t : ℝ) - (equispacedPanelNodes x k j i : ℝ))|
      ≤ M / ((k + 1).factorial : ℝ) * h ^ (k + 1) :=
        mul_le_mul (by gcongr; exact hM ξ hξmem) hprod (abs_nonneg _) (by positivity)
    _ = h ^ (k + 1) / (k + 1).factorial * M := by ring

/-- **Equation (8.23)** of [quarteroni2000numerical]. Let $a = x_0 < \cdots < x_K = b$ with
$K \ge 1$ subintervals of length at most $h$, and let $k \ge 1$. Let $f \in C^{k+1}([a, b])$,
that is, of class $C^{k+1}$ on an open set $U \supseteq [a, b]$, and let $F$ be its restriction
to $[a, b]$. Then
$$\|F - \Pi_h^k F\|_\infty \le C h^{k+1} \|f^{(k+1)}\|_\infty, \qquad C = \frac{1}{(k+1)!},$$
where $\|f^{(k+1)}\|_\infty = \max_{[a,b]} |f^{(k+1)}|$.

The maximum is written as the supremum `sSup` of $|f^{(k+1)}|$ over $[a, b]$.

**Generalization.** The theorem gives the explicit constant $1/(k+1)!$ and uses any upper bound on
the panel lengths. The derivatives are taken on an open neighborhood and evaluated on the closed
interval.
-/
theorem equation_8_23 (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f U) {F : C(Icc a b, ℝ)}
    (hF : ∀ t, F t = f t) :
    ‖F - piecewiseLagrangeInterp x K k F‖
      ≤ 1 / (k + 1).factorial * h ^ (k + 1)
        * sSup ((fun s => |iteratedDeriv (k + 1) f s|) '' Icc a b) := by
  have hcont : ContinuousOn (iteratedDeriv (k + 1) f) (Icc a b) :=
    ((hf.continuousOn_iteratedDerivWithin le_rfl hU.uniqueDiffOn).congr
      (iteratedDerivWithin_of_isOpen hU).symm).mono hUsub
  have hbdd : BddAbove ((fun s => |iteratedDeriv (k + 1) f s|) '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  rw [show 1 / ((k + 1).factorial : ℝ) * h ^ (k + 1) = h ^ (k + 1) / (k + 1).factorial by ring]
  exact equation_8_23_of_forall_le hx hK hk hmesh hU hUsub hf hF
    fun s hs => le_csSup hbdd (mem_image_of_mem _ hs)

/-! ### Theorem 8.3: the $L^2$ estimates -/

/-- Inside a subinterval $I_j$, $j < K$, the $m$-th derivative of $\Pi_h^k F$, extended to
$\mathbb{R}$ by its endpoint values, is the $m$-th derivative of the Lagrange interpolant of $F$
on $I_j$. -/
theorem iteratedDeriv_IccExtend_piecewiseLagrangeInterp
    (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    (F : C(Icc a b, ℝ)) (m : ℕ) {j : ℕ} (hj : j < K) {t : ℝ}
    (ht : t ∈ Ioo (x j : ℝ) (x (j + 1) : ℝ)) :
    iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t
      = (derivative^[m] (panelPoly (equispacedPanelNodes x k) j F)).eval t := by
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hev : IccExtend hx.le (piecewiseLagrangeInterp x K k F)
      =ᶠ[𝓝 t] fun s => (panelPoly (equispacedPanelNodes x k) j F).eval s := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    have hs' : s ∈ Icc a b := ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
    rw [IccExtend_of_mem hx.le _ hs']
    exact piecewisePolyInterpCLM_apply_of_mem hnode F (by omega) hs.1 hs.2
  rw [hev.iteratedDeriv_eq m, Polynomial.iteratedDeriv_eval]

/-- **Theorem 8.3** of [quarteroni2000numerical], squared form of (8.26) with $C = 1$. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$ subintervals of length at most $h$, let $k \ge 1$,
let $f \in H^{k+1}(a, b)$ with continuous representative $F$, and let $0 \le m \le k + 1$. Then
$$\|(f - \Pi_h^k f)^{(m)}\|_{L^2(a,b)}^2 = \sum_{j < K} \int_{x_j}^{x_{j+1}} \big|f^{(m)} -
  (\Pi_h^k F)^{(m)}\big|^2 \le h^{2(k+1-m)} \|f^{(k+1)}\|_{L^2(a,b)}^2,$$
where $f^{(m)}$ is the $m$-th weak derivative of $f$ and $(\Pi_h^k F)^{(m)}$ is the classical
$m$-th derivative of the piecewise interpolant inside the subintervals.

For $m \le k$ the proof specializes `sobolevSeminorm_sub_piecewisePolyInterp_le` of
`Numlib.Approximation.SobolevInterpolation`, with the weak derivative equal almost everywhere to
the derivative of the $C^k$ representative, by `SobolevInterval.exists_contDiff_ae_eq`. For
$m = k + 1$ the derivative of the interpolant is $0$ and the two sides are equal.

**Reading.** The input is a Sobolev function represented by a continuous function; the interpolant
derivatives are taken separately inside each panel. For order at least two this distinction matters
because the interpolant need not have a global weak derivative of that order. The estimates supply
constant one.
-/
theorem theorem_8_3_sq (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K)
    (hk : 1 ≤ k) {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h)
    (u : SobolevInterval (k + 1) a b) {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) {m : ℕ}
    (hm : m ≤ k + 1) :
    ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
          - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * SobolevInterval.seminorm (k + 1) a b u ^ 2 := by
  have hab := hx.lt_of_pos hK
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hmesh' : ∀ j ≤ K - 1, (x (j + 1) : ℝ) - x j ≤ h := fun j hj => hmesh j (by omega)
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab.le]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  -- a panel integral only sees the open panel, almost everywhere
  have hpanel_congr : ∀ j < K, ∀ {φ ψ : ℝ → ℝ},
      (∀ᵐ t, t ∈ Ioo (x j : ℝ) (x (j + 1) : ℝ) → φ t = ψ t) →
      ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), φ t = ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), ψ t := by
    intro j hj φ ψ hae
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t : ℝ, t ≠ (x (j + 1) : ℝ) := by simp [ae_iff, measure_singleton]
    filter_upwards [hae, hne] with t ht htne htI
    rw [uIoc_of_le (hx.step j hj).le] at htI
    exact ht ⟨htI.1, lt_of_le_of_ne htI.2 htne⟩
  have hIoo : ∀ j < K, Ioo (x j : ℝ) (x (j + 1) : ℝ) ⊆ Ioo a b := fun j _ =>
    Ioo_subset_Ioo (x j).2.1 (x (j + 1)).2.2
  have hrange : ∀ j ∈ Finset.range K, j < K := fun j hj => Finset.mem_range.mp hj
  rcases eq_or_lt_of_le hm with rfl | hmk
  · -- `m = k + 1`: the derivative of the interpolant vanishes, and the two sides agree
    have hzero : ∀ j < K, ∀ t ∈ Ioo (x j : ℝ) (x (j + 1) : ℝ),
        iteratedDeriv (k + 1) (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t = 0 := by
      intro j hj t ht
      rw [iteratedDeriv_IccExtend_piecewiseLagrangeInterp hx hK hk F (k + 1) hj ht,
        Polynomial.iterate_derivative_eq_zero, eval_zero]
      have := Lagrange.degree_interpolate_le (s := Finset.univ)
        (fun i => F (equispacedPanelNodes x k j i)) (hnode.injective j (by omega)).injOn
      rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at this
      exact Nat.lt_succ_of_le (natDegree_le_of_degree_le this)
    have hint : ∀ j < K, IntervalIntegrable
        (fun t => SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2) volume (x j) (x (j + 1)) :=
      fun j _ => (SobolevInterval.intervalIntegrable_deriv_sq hab.le u _).mono_set (hsub' j)
    refine le_of_eq ?_
    calc ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (SobolevInterval.deriv u ⟨k + 1, Nat.lt_succ_of_le le_rfl⟩ t
            - iteratedDeriv (k + 1) (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2
        = ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
            SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2 :=
          Finset.sum_congr rfl fun j hj => hpanel_congr j (hrange j hj)
            (Filter.Eventually.of_forall fun t ht => by
              rw [hzero j (hrange j hj) t ht, sub_zero]; rfl)
      _ = ∫ t in a..b, SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2 := by
          rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun j => (x j : ℝ))
            fun j hj => hint j hj]
          simp only [hx.first, hx.last]
      _ = h ^ (2 * (k + 1 - (k + 1))) * SobolevInterval.seminorm (k + 1) a b u ^ 2 := by
          rw [SobolevInterval.seminorm_sq_eq_integral hab.le, Nat.sub_self, mul_zero, pow_zero,
            one_mul]
  · -- `m ≤ k`: the backbone estimate, after replacing the weak derivative by the derivative of
    -- the `C^k` representative
    have hmk' : m ≤ k := Nat.lt_succ_iff.mp hmk
    obtain ⟨f, hf, hae, hftc⟩ := SobolevInterval.exists_contDiff_ae_eq hab u
    have hf0 : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] f := by
      rw [← SobolevInterval.deriv_zero u]; simpa using hae 0
    have hFf : EqOn (IccExtend hab.le F) f (Icc a b) :=
      eqOn_Icc_of_ae_eq hab F.continuous.Icc_extend'.continuousOn hf.continuous.continuousOn
        (hF.symm.trans hf0)
    have hF' : ∀ t, F t = f t := fun t => by rw [← IccExtend_val hab.le F t, hFf t.2]
    have haem : ∀ᵐ t, t ∈ Ioo a b →
        SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t = iteratedDeriv m f t := by
      have := (ae_restrict_iff' measurableSet_Ioo).1 (hae ⟨m, Nat.lt_succ_of_le hmk'⟩)
      simpa only [Fin.castSucc_mk] using this
    calc ∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
            - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2
        = ∑ j ∈ Finset.range (K - 1 + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
            (iteratedDeriv m f t
              - (derivative^[m] (panelPoly (equispacedPanelNodes x k) j F)).eval t) ^ 2 := by
          rw [Nat.sub_add_cancel hK]
          refine Finset.sum_congr rfl fun j hj => hpanel_congr j (hrange j hj) ?_
          filter_upwards [haem] with t ht htI
          rw [ht (hIoo j (hrange j hj) htI),
            iteratedDeriv_IccExtend_piecewiseLagrangeInterp hx hK hk F m (hrange j hj) htI]
      _ ≤ h ^ (2 * (k + 1 - m)) * ∫ t in a..b, SobolevInterval.deriv u (Fin.last (k + 1)) t ^ 2 :=
          sum_integral_sq_sub_panelPoly_le hnode hmesh' hf
            (SobolevInterval.intervalIntegrable_deriv hab.le u _)
            (SobolevInterval.intervalIntegrable_deriv_sq hab.le u _) hftc hF' hmk'
      _ = h ^ (2 * (k + 1 - m)) * SobolevInterval.seminorm (k + 1) a b u ^ 2 := by
          rw [SobolevInterval.seminorm_sq_eq_integral hab.le]

/-- The mesh bound $h$ of a partition with at least one subinterval is nonnegative. -/
theorem mesh_nonneg (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) {h : ℝ}
    (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) : 0 ≤ h :=
  (sub_pos.mpr (hx.step 0 hK)).le.trans (hmesh 0 hK)

/-- **Theorem 8.3** of [quarteroni2000numerical], estimate (8.26) with $C = 1$. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$ subintervals of length at most $h$, and let
$k \ge 1$. Let $f^{(m)} \in L^2(a, b)$ for $0 \le m \le k + 1$, that is, $f \in H^{k+1}(a, b)$,
with continuous representative $F$. Then for $0 \le m \le k + 1$,
$$\|(f - \Pi_h^k f)^{(m)}\|_{L^2(a,b)} \le C h^{k+1-m} \|f^{(k+1)}\|_{L^2(a,b)}, \qquad C = 1.$$

The left side is the square root of $\sum_{j < K} \int_{x_j}^{x_{j+1}} |f^{(m)} - (\Pi_h^k
F)^{(m)}|^2$, with $f^{(m)}$ the $m$-th weak derivative of $f$ and $(\Pi_h^k F)^{(m)}$ the
classical $m$-th derivative of the piecewise interpolant inside the subintervals; for $m \le 1$
it is the $L^2(a, b)$ norm of $(f - \Pi_h^k f)^{(m)}$ itself. The right side is the
$H^{k+1}(a, b)$ seminorm of $f$. The book proves the case $k = 1$ and refers to Quarteroni and
Valli for the general case. The proof takes the square root in
`QuarteroniSaccoSaleri.Chapter08.theorem_8_3_sq`.

**Reading.** The input is a Sobolev function represented by a continuous function; the interpolant
derivatives are taken separately inside each panel. For order at least two this distinction matters
because the interpolant need not have a global weak derivative of that order. The estimates supply
constant one.
-/
theorem theorem_8_3 (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval (k + 1) a b)
    {F : C(Icc a b, ℝ)} (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F)
    {m : ℕ} (hm : m ≤ k + 1) :
    √(∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
          - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2)
      ≤ h ^ (k + 1 - m) * SobolevInterval.seminorm (k + 1) a b u := by
  have hh0 := mesh_nonneg hx hK hmesh
  have hs0 : 0 ≤ SobolevInterval.seminorm (k + 1) a b u := apply_nonneg _ _
  calc √(∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (SobolevInterval.deriv u ⟨m, Nat.lt_succ_of_le hm⟩ t
            - iteratedDeriv m (IccExtend hx.le (piecewiseLagrangeInterp x K k F)) t) ^ 2)
      ≤ √((h ^ (k + 1 - m) * SobolevInterval.seminorm (k + 1) a b u) ^ 2) := by
        refine Real.sqrt_le_sqrt ((theorem_8_3_sq hx hK hk hmesh u hF hm).trans_eq ?_)
        rw [mul_pow, ← pow_mul']
    _ = h ^ (k + 1 - m) * SobolevInterval.seminorm (k + 1) a b u :=
        Real.sqrt_sq (by positivity)

/-- **Theorem 8.3** of [quarteroni2000numerical], the case $m = 0$ as an $L^2(a, b)$ norm. Under the
hypotheses of `QuarteroniSaccoSaleri.Chapter08.theorem_8_3`,
$$\|f - \Pi_h^k f\|_{L^2(a,b)} = \Big( \int_a^b |f - \Pi_h^k F|^2 \Big)^{1/2} \le h^{k+1}
  \|f^{(k+1)}\|_{L^2(a,b)},$$
where $f$ is the element of $H^{k+1}(a, b)$ itself.

The proof specializes `integral_sq_sub_piecewisePolyInterpCLM_le_seminorm`.

**Reading.** The input is a Sobolev function represented by a continuous function; the interpolant
derivatives are taken separately inside each panel. For order at least two this distinction matters
because the interpolant need not have a global weak derivative of that order. The estimates supply
constant one.
-/
theorem theorem_8_3_L2 (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) (hk : 1 ≤ k)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval (k + 1) a b)
    {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) :
    √(∫ t in a..b,
        (SobolevInterval.fn u t - IccExtend hx.le (piecewiseLagrangeInterp x K k F) t) ^ 2)
      ≤ h ^ (k + 1) * SobolevInterval.seminorm (k + 1) a b u := by
  have hab := hx.lt_of_pos hK
  have hnode := isPanelNodes_equispacedPanelNodes hx hK hk
  have hh0 := mesh_nonneg hx hK hmesh
  have hs0 : 0 ≤ SobolevInterval.seminorm (k + 1) a b u := apply_nonneg _ _
  have hmesh' : ∀ j ≤ K - 1, (x (j + 1) : ℝ) - x j ≤ h := fun j hj => hmesh j (by omega)
  have hkey := integral_sq_sub_piecewisePolyInterpCLM_le_seminorm hab u hnode hmesh' hF
  rw [intervalIntegral.integral_congr_ae_Ioo_of_mem (g := fun t =>
      (IccExtend hab.le F t - IccExtend hab.le (piecewisePolyInterpCLM (K - 1) k x
        (equispacedPanelNodes x k) F) t) ^ 2) ?_ (left_mem_Icc.mpr hab.le)
      (right_mem_Icc.mpr hab.le)]
  · calc √(∫ t in a..b, (IccExtend hab.le F t - IccExtend hab.le
          (piecewisePolyInterpCLM (K - 1) k x (equispacedPanelNodes x k) F) t) ^ 2)
        ≤ √((h ^ (k + 1) * SobolevInterval.seminorm (k + 1) a b u) ^ 2) := by
          refine Real.sqrt_le_sqrt (hkey.trans_eq ?_)
          rw [mul_pow, ← pow_mul']
      _ = h ^ (k + 1) * SobolevInterval.seminorm (k + 1) a b u := Real.sqrt_sq (by positivity)
  · filter_upwards [hF] with t ht
    rw [ht]
    rfl

/-! ### (8.27): the case $k = 1$ -/

/-- **Equation (8.27)** of [quarteroni2000numerical], first estimate, with $C_1 = 1$. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$ subintervals of length at most $h$, and let
$f \in H^2(a, b)$ with continuous representative $F$. Then
$$\|f - \Pi_h^1 f\|_{L^2(a,b)} \le C_1 h^2 \|f''\|_{L^2(a,b)}.$$

This is Theorem 8.3 with $k = 1$ and $m = 0$, in the form
`QuarteroniSaccoSaleri.Chapter08.theorem_8_3_L2`.

**Reading.** The input is a Sobolev function represented by a continuous function; the interpolant
derivatives are taken separately inside each panel. For order at least two this distinction matters
because the interpolant need not have a global weak derivative of that order. The estimates supply
constant one.
-/
theorem equation_8_27 (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K) {h : ℝ}
    (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval 2 a b) {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) :
    √(∫ t in a..b,
        (SobolevInterval.fn u t - IccExtend hx.le (piecewiseLagrangeInterp x K 1 F) t) ^ 2)
      ≤ h ^ 2 * SobolevInterval.seminorm 2 a b u :=
  theorem_8_3_L2 (k := 1) hx hK le_rfl hmesh u hF

/-- **Equation (8.27)** of [quarteroni2000numerical], second estimate, with $C_2 = 1$. Let
$a = x_0 < \cdots < x_K = b$ with $K \ge 1$ subintervals of length at most $h$, and let
$f \in H^2(a, b)$ with continuous representative $F$. Then
$$\|(f - \Pi_h^1 f)'\|_{L^2(a,b)} \le C_2 h \|f''\|_{L^2(a,b)}.$$

The left side is $\big(\sum_{j < K} \int_{x_j}^{x_{j+1}} |f' - (\Pi_h^1 F)'|^2\big)^{1/2}$, with
$f'$ the weak derivative and $(\Pi_h^1 F)'$ the slope of the interpolant on each subinterval.
This is Theorem 8.3 with $k = 1$ and $m = 1$.

**Reading.** The input is a Sobolev function represented by a continuous function; the interpolant
derivatives are taken separately inside each panel. For order at least two this distinction matters
because the interpolant need not have a global weak derivative of that order. The estimates supply
constant one.
-/
theorem equation_8_27_deriv (hx : IsIntervalPartition a b K fun j => (x j : ℝ)) (hK : 1 ≤ K)
    {h : ℝ} (hmesh : ∀ j < K, (x (j + 1) : ℝ) - x j ≤ h) (u : SobolevInterval 2 a b)
    {F : C(Icc a b, ℝ)}
    (hF : SobolevInterval.fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hx.le F) :
    √(∑ j ∈ Finset.range K, ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (SobolevInterval.deriv u 1 t
          - deriv (IccExtend hx.le (piecewiseLagrangeInterp x K 1 F)) t) ^ 2)
      ≤ h * SobolevInterval.seminorm 2 a b u := by
  have := theorem_8_3 (k := 1) hx hK le_rfl hmesh u hF (m := 1) (by norm_num)
  rw [Nat.add_sub_cancel, pow_one] at this
  simp only [iteratedDeriv_one] at this
  exact this

end QuarteroniSaccoSaleri.Chapter08
