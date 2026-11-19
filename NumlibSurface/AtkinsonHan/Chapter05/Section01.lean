/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Nonlinear.FixedPoint

/-!
# Atkinson and Han, Section 5.1: The Banach fixed-point theorem

This module formalizes Section 5.1 of [han2009theoretical]. Let $K$ be a subset of a real Banach
space $V$ and $T : K \to K$. The map $T$ is contractive on $K$ with constant $\alpha \in [0, 1)$ if
$\|Tu - Tv\| \le \alpha \|u - v\|$ for all $u, v \in K$. The Banach fixed-point theorem (Theorem
5.1.3) says that a contractive self-map of a nonempty closed set $K$ has a unique fixed point
$u \in K$, and that the iteration $u_{n+1} = T u_n$ converges to $u$ from every $u_0 \in K$ with the
error bounds (5.1.4)–(5.1.6). The module also proves the variant in which only an iterate $T^m$ is
contractive (Exercise 5.1.2), and Theorem 5.1.4: a strongly monotone Lipschitz operator on a real
Hilbert space is a bijection with a Lipschitz inverse.

The proofs specialize `Numlib.Nonlinear.FixedPoint` and Mathlib. The module translates between the
book's normed form of contractivity and Mathlib's `LipschitzOnWith` and `ContractingWith`.

## Main definitions

* Definition 5.1.2, `AtkinsonHan.Chapter05.ContractiveOn`, `AtkinsonHan.Chapter05.NonExpansiveOn`
  and `AtkinsonHan.Chapter05.LipschitzOn`: contractive, non-expansive and Lipschitz continuous maps
  on a set, in the book's normed form.
* Equation (5.1.8), `AtkinsonHan.Chapter05.StronglyMonotoneWith`:
  $(Tv_1 - Tv_2, v_1 - v_2) \ge c \|v_1 - v_2\|^2$ for all $v_1, v_2$.

## Main results

* Example 5.1.1, `AtkinsonHan.Chapter05.example_5_1_1` and
  `AtkinsonHan.Chapter05.example_5_1_1_tendsto_iff`: the closed form of the iteration
  $x \mapsto ax + b$ on $\mathbb{R}$, and its convergence from every starting point if and only if
  $|a| < 1$.
* Definition 5.1.2, `AtkinsonHan.Chapter05.ContractiveOn.nonExpansiveOn`,
  `AtkinsonHan.Chapter05.NonExpansiveOn.lipschitzOn` and
  `AtkinsonHan.Chapter05.LipschitzOn.continuousOn`: contractive maps are non-expansive,
  non-expansive maps are Lipschitz, and Lipschitz maps are continuous.
* Theorem 5.1.3 (Banach fixed-point theorem), `AtkinsonHan.Chapter05.theorem_5_1_3`: existence and
  uniqueness of the fixed point, convergence of the iteration, and the bounds (5.1.4)–(5.1.6). Its
  parts are `AtkinsonHan.Chapter05.theorem_5_1_3_existsUnique`,
  `AtkinsonHan.Chapter05.theorem_5_1_3_tendsto`, `AtkinsonHan.Chapter05.equation_5_1_4` (the a
  priori bound), `AtkinsonHan.Chapter05.equation_5_1_5` (the a posteriori bound) and
  `AtkinsonHan.Chapter05.equation_5_1_6` (the linear rate).
* Theorem 5.1.4, `AtkinsonHan.Chapter05.theorem_5_1_4`: a strongly monotone Lipschitz operator on a
  real Hilbert space is a bijection, with the stability estimate (5.1.11).
* Exercise 5.1.2, `AtkinsonHan.Chapter05.exercise_5_1_2`: a continuous map with a contractive
  iterate has a unique fixed point, and the iteration converges to it. Theorem 5.2.3 uses this
  result for the Volterra equation.

## Implementation notes

* The book states Section 5.1 in a Banach space and Theorem 5.1.4 in a Hilbert space. Several of the
  arguments are metric and do not use the vector space structure. The hypotheses on $V$ are kept
  because they are part of the book's setting, and the linter for unused section variables is turned
  off for the file.
* `AtkinsonHan.Chapter05.StronglyMonotoneWith` is the backbone predicate `IsStronglyMonotoneWith ℝ`
  by definition. For a bounded linear operator it is the coercivity `LinearMap.IsCoerciveWith`
  (`AtkinsonHan.Chapter05.stronglyMonotoneWith_iff_isCoerciveWith`).

## Deviations from the source

* **Equations (5.1.5)–(5.1.6)** (scope). The separate estimates assume a fixed point in
  $K$ and use the self-map and contraction properties. Closedness is used in Theorem 5.1.3
  to obtain the fixed point.
* **Proof of Theorem 5.1.4** (typo). The contraction estimate after (5.1.11) interchanges
  the monotonicity and Lipschitz constants. The coefficient is
  $1 - 2c_1\theta + c_2^2\theta^2$ with the conventions in (5.1.8)–(5.1.9).
-/

open Filter Metric Set Topology

namespace AtkinsonHan.Chapter05

-- See the implementation notes above: the section variables carrying the vector space structure
-- are unused in the purely metric arguments, and are kept because the book's setting has them.
set_option linter.unusedSectionVars false

section Banach

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 5.1.2** of [han2009theoretical], contractive maps. Let $V$ be a real normed space,
$K \subseteq V$, $T : V \to V$ and $\alpha \in \mathbb{R}$. The map $T$ is **contractive** on
$K$ with **contractivity constant** $\alpha$ if $0 \le \alpha < 1$ and
$$\|Tu - Tv\| \le \alpha \|u - v\| \qquad \text{for all } u, v \in K.$$

The map is defined on all of $V$, and the condition involves only its values on $K$. That $T$
maps $K$ into $K$ is a separate hypothesis (`Set.MapsTo T K K`) of the theorems below. -/
def ContractiveOn (T : V → V) (K : Set V) (α : ℝ) : Prop :=
  0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ α * ‖u - v‖

/-- **Definition 5.1.2** of [han2009theoretical], non-expansive maps. Let $V$ be a real normed
space, $K \subseteq V$ and $T : V \to V$. The map $T$ is **non-expansive** on $K$ if
$$\|Tu - Tv\| \le \|u - v\| \qquad \text{for all } u, v \in K.$$
This is the case $\alpha = 1$ of the contraction estimate. -/
def NonExpansiveOn (T : V → V) (K : Set V) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ ‖u - v‖

/-- **Definition 5.1.2** of [han2009theoretical], Lipschitz continuous maps. Let $V$ be a real
normed space, $K \subseteq V$ and $T : V \to V$. The map $T$ is **Lipschitz continuous** on $K$
if there is a constant $L \ge 0$ with
$$\|Tu - Tv\| \le L \|u - v\| \qquad \text{for all } u, v \in K.$$
-/
def LipschitzOn (T : V → V) (K : Set V) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ L * ‖u - v‖

variable {T : V → V} {K : Set V} {α : ℝ}

namespace ContractiveOn

/-- A contractivity constant $\alpha$ of a contractive map satisfies $\alpha \ge 0$. -/
theorem nonneg (h : ContractiveOn T K α) : 0 ≤ α := h.1

/-- A contractivity constant $\alpha$ of a contractive map satisfies $\alpha < 1$. -/
theorem lt_one (h : ContractiveOn T K α) : α < 1 := h.2.1

/-- If $T$ is contractive on $K$ with constant $\alpha$ and $u, v \in K$, then
$\|Tu - Tv\| \le \alpha \|u - v\|$. -/
theorem norm_sub_le (h : ContractiveOn T K α) {u v : V} (hu : u ∈ K) (hv : v ∈ K) :
    ‖T u - T v‖ ≤ α * ‖u - v‖ := h.2.2 u hu v hv

/-- If $T$ is contractive on $K$ with constant $\alpha$, then $d(Tu, Tv) \le \alpha \, d(u, v)$ for
all $u, v \in K$, with the distance $d$ of the norm. This is the metric form of the hypothesis
in `Numlib.Nonlinear.FixedPoint`. -/
theorem dist_le (h : ContractiveOn T K α) :
    ∀ u ∈ K, ∀ v ∈ K, dist (T u) (T v) ≤ α * dist u v := fun _ hu _ hv => by
  simpa only [dist_eq_norm] using h.norm_sub_le hu hv

/-- **Definition 5.1.2** of [han2009theoretical]: a map that is contractive on $K$ is non-expansive
on $K$. -/
theorem nonExpansiveOn (h : ContractiveOn T K α) : NonExpansiveOn T K := fun _ hu _ hv =>
  (h.norm_sub_le hu hv).trans (mul_le_of_le_one_left (norm_nonneg _) h.lt_one.le)

/-- If $T$ is contractive on $K$ with constant $\alpha$ and maps $K$ into $K$, then its restriction
$K \to K$ is a contraction with constant $\alpha$ in the sense of Mathlib's `ContractingWith`. -/
theorem contractingWith_restrict (h : ContractiveOn T K α) (hT : MapsTo T K K) :
    ContractingWith ⟨α, h.nonneg⟩ (hT.restrict T K K) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · exact_mod_cast h.lt_one
  · exact h.dist_le _ x.2 _ y.2

end ContractiveOn

/-- Let $\alpha \ge 0$. Then $T$ is contractive on $K$ with constant $\alpha$ if and only if
$\alpha < 1$ and $T$ is Lipschitz continuous on $K$ with constant $\alpha$ in the sense of
Mathlib's `LipschitzOnWith`. -/
theorem contractiveOn_iff (hα : 0 ≤ α) :
    ContractiveOn T K α ↔ α < 1 ∧ LipschitzOnWith ⟨α, hα⟩ T K := by
  refine ⟨fun h => ⟨h.lt_one, lipschitzOnWith_iff_norm_sub_le.2 fun _ hx _ hy => ?_⟩,
    fun h => ⟨hα, h.1, fun _ hx _ hy => ?_⟩⟩
  · exact h.norm_sub_le hx hy
  · exact lipschitzOnWith_iff_norm_sub_le.1 h.2 hx hy

/-- **Definition 5.1.2** of [han2009theoretical]: a map that is non-expansive on $K$ is Lipschitz
continuous on $K$. -/
theorem NonExpansiveOn.lipschitzOn (h : NonExpansiveOn T K) : LipschitzOn T K :=
  ⟨1, zero_le_one, fun u hu v hv => by simpa using h u hu v hv⟩

/-- The map $T$ is Lipschitz continuous on $K$ in the sense of Definition 5.1.2 if and only if there
is a constant $L \ge 0$ such that $T$ is `LipschitzOnWith L` on $K$ in Mathlib's sense. -/
theorem lipschitzOn_iff : LipschitzOn T K ↔ ∃ L : NNReal, LipschitzOnWith L T K := by
  constructor
  · rintro ⟨L, hL, h⟩
    exact ⟨⟨L, hL⟩, lipschitzOnWith_iff_norm_sub_le.2 fun _ hx _ hy => h _ hx _ hy⟩
  · rintro ⟨L, h⟩
    exact ⟨L, L.coe_nonneg, fun _ hx _ hy => lipschitzOnWith_iff_norm_sub_le.1 h hx hy⟩

/-- **Definition 5.1.2** of [han2009theoretical]: a map that is Lipschitz continuous on $K$ is
continuous on $K$. -/
theorem LipschitzOn.continuousOn (h : LipschitzOn T K) : ContinuousOn T K := by
  obtain ⟨L, hL⟩ := lipschitzOn_iff.1 h
  exact hL.continuousOn

section ScalarExample

/-- **Example 5.1.1** of [han2009theoretical], the closed form. Let $a, b, x_0 \in \mathbb{R}$ with
$a \ne 1$, and let $x_n$ be the iterates of $x \mapsto ax + b$ from $x_0$. Then for every
$n \ge 0$,
$$x_n = a^n x_0 + \frac{1 - a^n}{1 - a} \, b.$$
-/
theorem example_5_1_1 {a : ℝ} (ha : a ≠ 1) (b x₀ : ℝ) (n : ℕ) :
    (fun x => a * x + b)^[n] x₀ = a ^ n * x₀ + (1 - a ^ n) / (1 - a) * b := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    field_simp
    ring

/-- **Example 5.1.1** of [han2009theoretical], convergence. Let $a, b \in \mathbb{R}$ with
$a \ne 1$. The iterates of $x \mapsto ax + b$ converge from every starting point
$x_0 \in \mathbb{R}$ if and only if $|a| < 1$. -/
theorem example_5_1_1_tendsto_iff {a : ℝ} (ha : a ≠ 1) (b : ℝ) :
    (∀ x₀ : ℝ, ∃ x, Tendsto (fun n => (fun x => a * x + b)^[n] x₀) atTop (𝓝 x)) ↔ |a| < 1 := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  constructor
  · intro hconv
    obtain ⟨x, hx⟩ := hconv 1
    obtain ⟨y, hy⟩ := hconv 0
    have heq : (fun n : ℕ => (fun x => a * x + b)^[n] 1 - (fun x => a * x + b)^[n] 0)
        = fun n => a ^ n := by
      funext n
      rw [example_5_1_1 ha, example_5_1_1 ha]
      ring
    have hd : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 (x - y)) := heq ▸ hx.sub hy
    have hs : Tendsto (fun n : ℕ => a ^ (n + 1)) atTop (𝓝 (x - y)) :=
      hd.comp (tendsto_add_atTop_nat 1)
    have hs' : Tendsto (fun n : ℕ => a ^ (n + 1)) atTop (𝓝 (a * (x - y))) := by
      simpa only [pow_succ, mul_comm] using hd.const_mul a
    have hfix : (1 - a) * (x - y) = 0 := by
      linear_combination tendsto_nhds_unique hs hs'
    have hxy : x - y = 0 := by
      rcases mul_eq_zero.1 hfix with h | h
      · exact absurd h h1
      · exact h
    rw [hxy] at hd
    exact tendsto_pow_atTop_nhds_zero_iff.1 hd
  · intro haa x₀
    refine ⟨b / (1 - a), ?_⟩
    have hz : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_iff.2 haa
    have hlim := (hz.mul_const x₀).add
      (((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hz).div_const
        (1 - a) |>.mul_const b)
    have hgoal : b / (1 - a) = 0 * x₀ + (1 - 0) / (1 - a) * b := by ring
    rw [hgoal]
    simp only [example_5_1_1 ha]
    exact hlim

end ScalarExample

section Complete

variable [CompleteSpace V]

/-- **Theorem 5.1.3(a)** of [han2009theoretical]. Let $V$ be a real Banach space, let
$K \subseteq V$ be nonempty and closed, and let $T : V \to V$ map $K$ into $K$ and be
contractive on $K$ with constant $\alpha$. Then $T$ has a unique fixed point in $K$: there is
exactly one $u \in K$ with $Tu = u$. -/
theorem theorem_5_1_3_existsUnique (hK : IsClosed K) (hne : K.Nonempty) (hT : MapsTo T K K)
    (hα : ContractiveOn T K α) : ∃! u, u ∈ K ∧ T u = u :=
  exists_unique_fixedPoint_of_mapsTo hK hne hT hα.nonneg hα.lt_one hα.dist_le

/-- **Equation (5.1.4)** of [han2009theoretical], the a priori error bound. Let $V$ be a real Banach
space, let $K \subseteq V$ be closed, and let $T : V \to V$ map $K$ into $K$ and be contractive
on $K$ with constant $\alpha$. Let $u \in K$ be a fixed point of $T$, let $u_0 \in K$, and let
$u_n = T^n u_0$. Then for every $n \ge 0$,
$$\|u_n - u\| \le \frac{\alpha^n}{1 - \alpha} \, \|u_0 - u_1\|.$$
-/
theorem equation_5_1_4 (hK : IsClosed K) (hT : MapsTo T K K) (hα : ContractiveOn T K α) {u : V}
    (hu : u ∈ K) (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) (n : ℕ) :
    ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖ := by
  have h := dist_iterate_le_of_mapsTo hK hT hα.nonneg hα.lt_one hα.dist_le hu hfix hu₀ n
  rwa [dist_eq_norm, dist_eq_norm, norm_sub_rev (T u₀)] at h

/-- For a contractive map $T$ on $K$ with constant $\alpha$, a fixed point $u \in K$, and a point
$a \in K$ with $Ta \in K$: $\|Ta - u\| \le \frac{\alpha}{1 - \alpha} \|a - Ta\|$. -/
private theorem norm_step_sub_fixed_le (hα : ContractiveOn T K α) {u : V} (hu : u ∈ K)
    (hfix : T u = u) {a : V} (ha : a ∈ K) (hTa : T a ∈ K) :
    ‖T a - u‖ ≤ α / (1 - α) * ‖a - T a‖ := by
  have h1 : ‖T a - u‖ ≤ ‖T a - T (T a)‖ + ‖T (T a) - u‖ := by
    simpa only [dist_eq_norm] using dist_triangle (T a) (T (T a)) u
  have h2 : ‖T a - T (T a)‖ ≤ α * ‖a - T a‖ := hα.norm_sub_le ha hTa
  have h3 : ‖T (T a) - u‖ ≤ α * ‖T a - u‖ := by
    have h := hα.norm_sub_le hTa hu
    rwa [hfix] at h
  have hlt : 0 < 1 - α := by linarith [hα.lt_one]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlt]
  linarith

/-- **Equation (5.1.5)** of [han2009theoretical], the a posteriori error bound. Let $V$ be a real
Banach space, let $K \subseteq V$, and let $T : V \to V$ map $K$ into $K$ and be contractive on
$K$ with constant $\alpha$. Let $u \in K$ be a fixed point of $T$, let $u_0 \in K$, and let
$u_n = T^n u_0$. Then for every $n \ge 0$,
$$\|u_{n+1} - u\| \le \frac{\alpha}{1 - \alpha} \, \|u_n - u_{n+1}\|.$$

**Reading.** Drops closedness by supplying the fixed point and uses shifted index.
-/
theorem equation_5_1_5 (hT : MapsTo T K K) (hα : ContractiveOn T K α) {u : V} (hu : u ∈ K)
    (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) (n : ℕ) :
    ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖ := by
  rw [Function.iterate_succ_apply']
  exact norm_step_sub_fixed_le hα hu hfix (hT.iterate n hu₀) (hT (hT.iterate n hu₀))

/-- **Equation (5.1.6)** of [han2009theoretical], the linear rate of convergence. Let $V$ be a real
Banach space, let $K \subseteq V$, and let $T : V \to V$ map $K$ into $K$ and be contractive on
$K$ with constant $\alpha$. Let $u \in K$ be a fixed point of $T$, let $u_0 \in K$, and let
$u_n = T^n u_0$. Then for every $n \ge 0$,
$$\|u_{n+1} - u\| \le \alpha \, \|u_n - u\|.$$

**Reading.** Drops closedness by supplying the fixed point and uses shifted index.
-/
theorem equation_5_1_6 (hT : MapsTo T K K) (hα : ContractiveOn T K α) {u : V} (hu : u ∈ K)
    (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) (n : ℕ) :
    ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖ := by
  have h := hα.norm_sub_le (hT.iterate n hu₀) hu
  rw [hfix] at h
  rwa [Function.iterate_succ_apply']

/-- **Theorem 5.1.3(b)** of [han2009theoretical]. Let $V$ be a real Banach space, let
$K \subseteq V$ be closed, and let $T : V \to V$ map $K$ into $K$ and be contractive on $K$. Let
$u \in K$ be a fixed point of $T$. Then for every $u_0 \in K$ the iterates $u_n = T^n u_0$
converge to $u$. -/
theorem theorem_5_1_3_tendsto (hK : IsClosed K) (hT : MapsTo T K K) (hα : ContractiveOn T K α)
    {u : V} (hu : u ∈ K) (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) :
    Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => equation_5_1_4 hK hT hα hu hfix hu₀ n) ?_
  have h1 : Tendsto (fun n : ℕ => α ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα.nonneg hα.lt_one
  simpa using (h1.div_const (1 - α)).mul_const ‖u₀ - T u₀‖

/-- **Theorem 5.1.3** of [han2009theoretical] (Banach fixed-point theorem). Let $V$ be a real Banach
space, let $K \subseteq V$ be nonempty and closed, and let $T : V \to V$ map $K$ into $K$ and be
contractive on $K$ with constant $\alpha \in [0, 1)$. Then:

1. $T$ has a unique fixed point $u \in K$;
2. for every $u_0 \in K$, the iterates $u_n = T^n u_0$ converge to this fixed point $u$, and for
   every $n \ge 0$ they satisfy the bounds (5.1.4)–(5.1.6):
$$\|u_n - u\| \le \frac{\alpha^n}{1 - \alpha} \|u_0 - u_1\|, \qquad \|u_{n+1} - u\| \le
  \frac{\alpha}{1 - \alpha} \|u_n - u_{n+1}\|, \qquad \|u_{n+1} - u\| \le \alpha \|u_n - u\|.$$

The theorem combines `AtkinsonHan.Chapter05.theorem_5_1_3_existsUnique`,
`AtkinsonHan.Chapter05.theorem_5_1_3_tendsto`, `AtkinsonHan.Chapter05.equation_5_1_4`,
`AtkinsonHan.Chapter05.equation_5_1_5` and `AtkinsonHan.Chapter05.equation_5_1_6`. -/
theorem theorem_5_1_3 (hK : IsClosed K) (hne : K.Nonempty) (hT : MapsTo T K K)
    (hα : ContractiveOn T K α) :
    (∃! u, u ∈ K ∧ T u = u) ∧
      ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) := by
  obtain ⟨u, ⟨hu, hfix⟩, -⟩ := theorem_5_1_3_existsUnique hK hne hT hα
  exact ⟨theorem_5_1_3_existsUnique hK hne hT hα, fun u₀ hu₀ =>
    ⟨u, hu, hfix, theorem_5_1_3_tendsto hK hT hα hu hfix hu₀,
      fun n => equation_5_1_4 hK hT hα hu hfix hu₀ n, fun n => equation_5_1_5 hT hα hu hfix hu₀ n,
      fun n => equation_5_1_6 hT hα hu hfix hu₀ n⟩⟩

/-- **Exercise 5.1.2** of [han2009theoretical]. Let $V$ be a real Banach space, let $K \subseteq V$
be nonempty and closed, and let $T : V \to V$ map $K$ into $K$ and be continuous on $K$. Let
$m \ge 1$, and let the iterate $T^m$ be contractive on $K$. Then:

1. $T$ has a unique fixed point $u \in K$;
2. for every $u_0 \in K$, the iterates $T^n u_0$ converge to this fixed point.

Theorem 5.2.3 uses this result for the Volterra integral equation. -/
theorem exercise_5_1_2 (hK : IsClosed K) (hne : K.Nonempty) (hT : MapsTo T K K)
    (hc : ContinuousOn T K) {m : ℕ} (hm : 0 < m) (hα : ContractiveOn T^[m] K α) :
    (∃! u, u ∈ K ∧ T u = u) ∧
      ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  have hcomplete : CompleteSpace K := hK.completeSpace_coe
  have hnonempty : Nonempty K := hne.to_subtype
  have hcont : Continuous (hT.restrict T K K) := hc.mapsToRestrict hT
  have hcw : ContractingWith ⟨α, hα.nonneg⟩ (hT.restrict T K K)^[m] := by
    rw [hT.iterate_restrict m]
    exact hα.contractingWith_restrict (hT.iterate m)
  have hkey : ∀ x : K, hT.restrict T K K x = x ↔ T (x : V) = (x : V) := fun x => by
    rw [Subtype.ext_iff, MapsTo.val_restrict_apply]
  constructor
  · obtain ⟨x, hx, hxu⟩ := exists_unique_fixedPoint_of_iterate_contractingWith hcont hm hcw
    refine ⟨(x : V), ⟨x.2, (hkey x).1 hx⟩, ?_⟩
    rintro y ⟨hy, hfy⟩
    exact congrArg Subtype.val (hxu ⟨y, hy⟩ ((hkey ⟨y, hy⟩).2 hfy))
  · intro u₀ hu₀
    obtain ⟨x, hx, htend⟩ :=
      tendsto_iterate_of_iterate_contractingWith hcont hm hcw ⟨u₀, hu₀⟩
    refine ⟨(x : V), x.2, (hkey x).1 hx, ?_⟩
    have h := (continuous_subtype_val.tendsto x).comp htend
    simpa only [Function.comp_def, MapsTo.coe_iterate_restrict] using h

end Complete

end Banach

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Equation (5.1.8)** of [han2009theoretical], strongly monotone operators. Let $V$ be a real
Hilbert space, $T : V \to V$ and $c \in \mathbb{R}$. The operator $T$ is **strongly monotone**
with constant $c$ if
$$(Tv_1 - Tv_2, v_1 - v_2) \ge c \, \|v_1 - v_2\|^2 \qquad \text{for all } v_1, v_2 \in V.$$

This is the backbone predicate `IsStronglyMonotoneWith ℝ T c`, which is the hypothesis of the
backbone theorem `zarantonello`. `AtkinsonHan.Chapter05.stronglyMonotoneWith_iff` states the
inequality with the real inner product. -/
def StronglyMonotoneWith (T : V → V) (c : ℝ) : Prop :=
  IsStronglyMonotoneWith ℝ T c

/-- **Equation (5.1.8)** of [han2009theoretical], unfolded: $T$ is strongly monotone with constant
$c$ if and only if $c \|v_1 - v_2\|^2 \le (Tv_1 - Tv_2, v_1 - v_2)$ for all $v_1, v_2 \in V$. -/
theorem stronglyMonotoneWith_iff {T : V → V} {c : ℝ} :
    StronglyMonotoneWith T c ↔ ∀ v₁ v₂, c * ‖v₁ - v₂‖ ^ 2 ≤ inner ℝ (T v₁ - T v₂) (v₁ - v₂) :=
  isStronglyMonotoneWith_real_iff T c

/-- Let $A$ be a bounded linear operator on a real Hilbert space $V$. Then $A$ is strongly monotone
with constant $c$ if and only if $A$ is coercive with constant $c$, that is,
$c \|v\|^2 \le (Av, v)$ for all $v \in V$ (`LinearMap.IsCoerciveWith`). -/
theorem stronglyMonotoneWith_iff_isCoerciveWith (A : V →L[ℝ] V) (c : ℝ) :
    StronglyMonotoneWith (A : V → V) c ↔ (A : V →ₗ[ℝ] V).IsCoerciveWith c := by
  constructor
  · intro h x
    simpa [RCLike.re_to_real] using h x 0
  · intro h v₁ v₂
    simpa only [map_sub, ContinuousLinearMap.coe_coe] using h (v₁ - v₂)

/-- **Equation (5.1.9)** of [han2009theoretical], the Lipschitz condition. Let $c \ge 0$. Then
$\|Tv_1 - Tv_2\| \le c \|v_1 - v_2\|$ for all $v_1, v_2 \in V$ if and only if $T$ is Lipschitz
continuous with constant $c$ in the sense of Mathlib's `LipschitzWith`. -/
theorem lipschitzWith_toNNReal_iff {T : V → V} {c : ℝ} (hc : 0 ≤ c) :
    (∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c * ‖v₁ - v₂‖) ↔ LipschitzWith (Real.toNNReal c) T := by
  rw [lipschitzWith_iff_norm_sub_le]
  simp [Real.coe_toNNReal _ hc]

/-- **Theorem 5.1.4** of [han2009theoretical]. Let $V$ be a real Hilbert space, and let
$T : V \to V$ be strongly monotone (5.1.8) with a constant $c_1 > 0$ and Lipschitz continuous
(5.1.9) with a constant $c_2 > 0$:
$$(Tv_1 - Tv_2, v_1 - v_2) \ge c_1 \|v_1 - v_2\|^2, \qquad \|Tv_1 - Tv_2\| \le c_2 \|v_1 - v_2\|
  \qquad \text{for all } v_1, v_2 \in V.$$
Then:

1. for every $b \in V$ the equation (5.1.10) $Tu = b$ has a unique solution $u \in V$;
2. the solution depends Lipschitz continuously on the data: if $Tu_1 = b_1$ and $Tu_2 = b_2$,
   then
$$\|u_1 - u_2\| \le \frac{1}{c_1} \|b_1 - b_2\|. \qquad (5.1.11)$$

The proof specializes the backbone theorem `zarantonello`. -/
theorem theorem_5_1_4 {T : V → V} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hmono : StronglyMonotoneWith T c₁) (hlip : ∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖) :
    (∀ b, ∃! u, T u = b) ∧
      ∀ u₁ u₂ b₁ b₂, T u₁ = b₁ → T u₂ = b₂ → ‖u₁ - u₂‖ ≤ 1 / c₁ * ‖b₁ - b₂‖ := by
  refine ⟨fun b => zarantonello (𝕜 := ℝ) hc₁ hmono ((lipschitzWith_toNNReal_iff hc₂.le).1 hlip) b,
    fun u₁ u₂ b₁ b₂ h₁ h₂ => ?_⟩
  have h := norm_sub_le_of_strongly_monotone (𝕜 := ℝ) hc₁ hmono h₁ h₂
  rwa [one_div, inv_mul_eq_div]

end Hilbert

end AtkinsonHan.Chapter05
