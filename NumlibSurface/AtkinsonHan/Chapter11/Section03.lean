/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.Obstacle
import Numlib.Variational.Inequality.Basic
import NumlibSurface.AtkinsonHan.Chapter05.Section01
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter11.Section01

/-!
# Atkinson and Han, Section 11.3: Existence and uniqueness for elliptic variational inequalities

This module formalizes Section 11.3 of [han2009theoretical]. Let $V$ be a real Hilbert space,
$K \subseteq V$ a nonempty closed convex set, $A \colon V \to V$ an operator,
$j \colon V \to \mathbb{R}$ a convex functional and $f \in V$. The section studies the elliptic
variational inequality (11.3.3),
$$u \in K, \qquad (A u, v - u) + j(v) - j(u) \ge (f, v - u) \quad \text{for all } v \in K.$$
The inequality of the first kind (11.3.8) is the case $j = 0$, and the inequality of the second kind
(11.3.9) is the case $K = V$. The displays (11.3.12)–(11.3.14) are the same three problems with $A$
the operator of a bounded $V$-elliptic bilinear form $a$, written
$a(u, v - u) + j(v) - j(u) \ge \ell(v - u)$. Theorem 11.3.1 says that (11.3.3) has exactly one
solution when $A$ is strongly monotone and Lipschitz continuous, and that the solution depends
Lipschitz continuously on $f$. Theorems 11.3.6, 11.3.7 and 11.3.9 are its special cases, and Lemma
11.3.8 (Minty's lemma) gives an equivalent form with $A$ evaluated at the test point.

Examples 11.3.10 and 11.3.11 apply Theorem 11.3.9 to the obstacle problem on $H^1_0(\Omega)$ and to
the simplified friction problem on $H^1(\Omega)$ of Section 11.1. Theorem 11.3.12, the regularity of
the solution of the obstacle problem, is proved for $p = 2$ and the Laplacian on a $C^2$ domain. The
abstract results specialize `existsUnique_isVariationalInequalitySolution_on` and
`IsVariationalInequalitySolution.norm_sub_le` of `Numlib.Variational.Inequality.Basic`, and the
regularity result specializes `Elliptic.regularity_obstacle_sobolev_two` of
`Numlib.Analysis.PDE.Elliptic.Obstacle`.

## Main definitions

* (11.3.3), (11.3.8), (11.3.9) and (11.3.12)–(11.3.14),
  `AtkinsonHan.Chapter11.IsVariationalInequalitySolution`: $u \in K$ and
  $(A u, v - u) + j(v) - j(u) \ge (f, v - u)$ for all $v \in K$.
* Theorem 11.3.12, `AtkinsonHan.Chapter11.obstacleOfH2`: an obstacle in $H^2(\Omega)$, viewed as an
  element of $H^1(\Omega)$.

## Main results

* Theorem 11.3.1, `AtkinsonHan.Chapter11.theorem_11_3_1`: for a strongly monotone Lipschitz
  operator, (11.3.3) has exactly one solution for every $f$, and
  $\|u_1 - u_2\| \le c_0^{-1} \|f_1 - f_2\|$.
* Lemma 11.3.5, `AtkinsonHan.Chapter11.lemma_11_3_5`: a convex lower semicontinuous functional on a
  nonempty closed convex set has a continuous affine minorant.
* Theorem 11.3.6, `AtkinsonHan.Chapter11.theorem_11_3_6` (Stampacchia's theorem): the inequality of
  the first kind (11.3.8) is uniquely solvable, with Lipschitz dependence on $f$.
* Theorem 11.3.7, `AtkinsonHan.Chapter11.theorem_11_3_7`: the inequality of the second kind (11.3.9)
  is uniquely solvable, with Lipschitz dependence on $f$.
* Lemma 11.3.8, `AtkinsonHan.Chapter11.lemma_11_3_8` (Minty's lemma): for a monotone operator,
  (11.3.3) is equivalent to (11.3.10), $(A v, v - u) + j(v) - j(u) \ge (f, v - u)$ for all
  $v \in K$.
* Theorem 11.3.9, `AtkinsonHan.Chapter11.theorem_11_3_9`: for a bounded $V$-elliptic bilinear form,
  (11.3.12) is uniquely solvable, with $\|u_1 - u_2\| \le \alpha^{-1} \|\ell_1 - \ell_2\|$; this
  covers (11.3.13) and (11.3.14).
* Theorem 11.3.9 with $j = 0$, `AtkinsonHan.Chapter11.theorem_11_3_9_zero_existsUnique` and
  `AtkinsonHan.Chapter11.theorem_11_3_9_zero_lipschitz`: unique solvability of (11.3.13) and
  Lipschitz dependence on $\ell$.
* Example 11.3.10, `AtkinsonHan.Chapter11.example_11_3_10`: the obstacle problem is uniquely
  solvable for every $f \in L^2(\Omega)$, with Lipschitz dependence on $f$.
* Example 11.3.11, `AtkinsonHan.Chapter11.example_11_3_11`: the simplified friction problem is
  uniquely solvable for every $f \in L^2(\Omega)$, with Lipschitz dependence on $f$.
* Remark after Example 11.3.11, `AtkinsonHan.Chapter11.isBestApprox_energy_of_theorem_11_3_9`: for a
  symmetric form and $j = 0$, the solution of (11.3.13) is the best approximation in $K$, in the
  energy norm, to the solution of the variational equation.
* Theorem 11.3.12, `AtkinsonHan.Chapter11.theorem_11_3_12_two`: for $p = 2$ and the Laplacian on a
  bounded $C^2$ domain, the solution of the obstacle problem lies in $H^2(\Omega)$, with
  $\|u\|_{H^2} \le C (\|f\|_{L^2} + \|\psi\|_{H^2})$.
* Theorem 11.3.12, `AtkinsonHan.Chapter11.isObstacleSolution_of_example_11_3_10` and
  `AtkinsonHan.Chapter11.norm_le_of_obstacle_solution`: the solution of Example 11.3.10 is an
  obstacle solution in the sense of the backbone, and it satisfies an a priori $H^1$ bound.
* Exercise 11.3.1, `AtkinsonHan.Chapter11.exercise_11_3_1`: Theorem 11.3.1 holds with the Lipschitz
  condition (11.3.2) replaced by a local Lipschitz condition; part (a) is
  `AtkinsonHan.Chapter11.exercise_11_3_1_growth`.
* Exercise 11.3.2, `AtkinsonHan.Chapter11.exercise_11_3_2`: the Lax–Milgram lemma as the case
  $K = V$, $j = 0$ of Theorem 11.3.6.
* Exercise 11.3.3, `AtkinsonHan.Chapter11.exercise_11_3_3`: on a convex cone, (11.3.13) is
  equivalent to $a(u, v) \ge \ell(v)$ for all $v \in K$ together with $a(u, u) = \ell(u)$.
* Exercise 11.3.10, `AtkinsonHan.Chapter11.exercise_11_3_10`: for a positively homogeneous $j$,
  (11.3.14) is equivalent to $a(u, v) + j(v) \ge \ell(v)$ for all $v$ together with
  $a(u, u) + j(u) = \ell(u)$.
* Exercise 11.3.13, `AtkinsonHan.Chapter11.exercise_11_3_13`: the equation $A u = f$ with $A$
  strongly monotone and Lipschitz is uniquely solvable, with Lipschitz dependence on $f$.

## Conventions

* Strong monotonicity (11.3.1) is `AtkinsonHan.Chapter05.StronglyMonotoneWith` of Section 5.1. The
  Lipschitz condition (11.3.2) is written out as $\|A v_1 - A v_2\| \le M \|v_1 - v_2\|$;
  `AtkinsonHan.Chapter05.lipschitzWith_toNNReal_iff` relates it to Mathlib's `LipschitzWith`. The
  $V$-ellipticity of a bilinear form is `AtkinsonHan.BilinForm.IsEllipticWith` of Section 8.3.

## Implementation notes

* All six displays (11.3.3), (11.3.8), (11.3.9) and (11.3.12)–(11.3.14) are the one predicate
  `AtkinsonHan.Chapter11.IsVariationalInequalitySolution` with different arguments. It is the
  backbone's `IsVariationalInequalitySolution` written with $\ge$, by
  `AtkinsonHan.Chapter11.isVariationalInequalitySolution_iff`. Hence Theorem 11.3.9 is one theorem
  that covers (11.3.12), (11.3.13) and (11.3.14), and Theorem 11.3.6 is Theorem 11.3.1 at $j = 0$.
* Remark 11.3.2, which the source states without proof, is the backbone theorem
  `existsUnique_isVariationalInequalitySolution_on`: the hypotheses on $A$ are needed on $K$ only,
  because every iterate of the fixed-point argument stays in $K$. Exercise 11.3.1 is proved through
  it.

## Deviations from the source

* **Lemma 11.3.8** (generalization). The source assumes that $A$ is continuous on the
  finite-dimensional subspaces of $V$. The library assumes only that $A$ is right-continuous along
  the segments of $K$ that start at $u$, which the continuity of the source implies. See
  `AtkinsonHan.Chapter11.lemma_11_3_8`.
* **Example 11.3.10 and Theorem 11.3.12** (reading). The condition "$\psi \le 0$ on $\Gamma$" on the
  obstacle is read as: $\max\{\psi, 0\}$ is the function of an element of $H^1_0(\Omega)$. See
  `AtkinsonHan.Chapter11.example_11_3_10`.
* **Example 11.3.11** (reading). The Lipschitz domain of the source is a domain with a boundary
  trace in the sense of `BoundaryData.TraceFamily`, for example a bounded $C^1$ domain or a polygon
  without slits. See `AtkinsonHan.Chapter11.example_11_3_11`.

## Not formalized

* **Theorem 11.3.12 in the generality of the source** ($1 < p < \infty$, uniformly elliptic
  coefficients $a_{ij} \in C(\overline\Omega)$, a $C^{1,1}$ domain). Only the case $p = 2$,
  $a_{ij} = \delta_{ij}$ on a $C^2$ domain is formalized, as
  `AtkinsonHan.Chapter11.theorem_11_3_12_two`. The source quotes the theorem without proof from
  Brezis–Stampacchia and from Theorem 9.14 of Gilbarg–Trudinger. The remaining generality needs
  $W^{2,p}$ and $L^p$ regularity for $p \neq 2$, which rests on the Calderón–Zygmund theory; the
  linear regularity theory for general uniformly elliptic coefficients, since
  `Elliptic.regularity_dirichlet` is for $-\Delta + 1$ only; and the $C^{1,1}$ boundary class in
  place of $C^2$.
* **The one-dimensional solution formula after Example 11.3.11.** It names a domain and hence a
  Sobolev space.
* **Exercises 11.3.4–11.3.9, 11.3.11 and 11.3.12.** Each of them names a domain and hence a Sobolev
  space.
-/

open Filter Set TopologicalSpace Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Chapter11

/-! ### Lemma 11.3.5: the affine minorant -/

/-- **Lemma 11.3.5** of [han2009theoretical]. Let $W$ be a real normed space, let $K \subseteq W$ be
nonempty and closed, and let $j \colon W \to \mathbb{R}$ be convex and lower semicontinuous on
$K$. Then there are $\ell \in W'$ and $c \in \mathbb{R}$ with
$$j(v) \ge \ell(v) + c \quad \text{for all } v \in K.$$

The convexity of $K$ is part of `ConvexOn ℝ K j`. The function
$j \colon V \to \mathbb{R} \cup \{+\infty\}$ of the source is proper, so it is real-valued on
its effective domain, and that set is the $K$ here. The source proves the lemma by separating
the epigraph of $j$ from a point below its graph; that separation is Mathlib's
`ConvexOn.exists_affine_le_of_lt`. -/
theorem lemma_11_3_5 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {K : Set W}
    (hKne : K.Nonempty) (hKcl : IsClosed K) {j : W → ℝ} (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) : ∃ (ℓ : W →L[ℝ] ℝ) (c : ℝ), ∀ v ∈ K, ℓ v + c ≤ j v := by
  obtain ⟨x₀, hx₀⟩ := hKne
  obtain ⟨l, c, hle, -⟩ :=
    ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (a := j x₀ - 1) hx₀ (by linarith) hKcl hjlsc hj
  exact ⟨l, c, fun z hz => by simpa using hle ⟨z, hz⟩⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The variational inequality (11.3.3) and its five variants -/

/-- **Equation (11.3.3)** of [han2009theoretical], the elliptic variational inequality. Let $V$ be a
real inner product space, $A \colon V \to V$, $j \colon V \to \mathbb{R}$, $f \in V$ and
$K \subseteq V$. A point $u$ is a **solution of the variational inequality** if $u \in K$ and
$$(A u, v - u) + j(v) - j(u) \ge (f, v - u) \quad \text{for all } v \in K.$$

The inequality of the first kind (11.3.8) is the case $j = 0$, and that of the second kind
(11.3.9) is the case $K = V$, that is `Set.univ`. The displays (11.3.12)–(11.3.14) are the same
three with $A$ the operator of a bilinear form. The datum is a vector $f$ rather than a
functional, as in Remark 11.3.4 of the source. This is the backbone's
`IsVariationalInequalitySolution`, by
`AtkinsonHan.Chapter11.isVariationalInequalitySolution_iff`. -/
def IsVariationalInequalitySolution (A : V → V) (j : V → ℝ) (f : V) (K : Set V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, ⟪A u, v - u⟫_ℝ + j v - j u ≥ ⟪f, v - u⟫_ℝ

/-- The predicate (11.3.3) is equivalent to the backbone's `IsVariationalInequalitySolution` with
the same arguments. -/
theorem isVariationalInequalitySolution_iff (A : V → V) (j : V → ℝ) (f : V) (K : Set V) (u : V) :
    IsVariationalInequalitySolution A j f K u ↔
      _root_.IsVariationalInequalitySolution A j f K u := Iff.rfl

/-- **Equation (11.3.8)** of [han2009theoretical], the inequality of the first kind. With $j = 0$,
$u$ solves the variational inequality if and only if $u \in K$ and $(A u, v - u) \ge (f, v - u)$
for all $v \in K$. -/
theorem isVariationalInequalitySolution_zero_iff (A : V → V) (f : V) (K : Set V) (u : V) :
    IsVariationalInequalitySolution A 0 f K u ↔
      u ∈ K ∧ ∀ v ∈ K, ⟪A u, v - u⟫_ℝ ≥ ⟪f, v - u⟫_ℝ := by
  simp [IsVariationalInequalitySolution]

/-- **Equation (11.3.9)** of [han2009theoretical], the inequality of the second kind. With $K = V$,
$u$ solves the variational inequality if and only if $(A u, v - u) + j(v) - j(u) \ge (f, v - u)$
for all $v \in V$. -/
theorem isVariationalInequalitySolution_univ_iff (A : V → V) (j : V → ℝ) (f : V) (u : V) :
    IsVariationalInequalitySolution A j f univ u ↔
      ∀ v, ⟪A u, v - u⟫_ℝ + j v - j u ≥ ⟪f, v - u⟫_ℝ := by
  simp [IsVariationalInequalitySolution]

/-- With $K = V$ and $j = 0$, $u$ solves the variational inequality if and only if $A u = f$. The
proof tests the inequality at $u + w$ and at $u - w$. This makes Exercises 11.3.2 and 11.3.13
corollaries of Theorem 11.3.6. -/
theorem isVariationalInequalitySolution_univ_zero_iff (A : V → V) (f : V) (u : V) :
    IsVariationalInequalitySolution A 0 f univ u ↔ A u = f := by
  rw [isVariationalInequalitySolution_zero_iff]
  constructor
  · rintro ⟨-, h⟩
    refine (ext_inner_right ℝ fun w => ?_).symm
    have h₁ := h (u + w) (mem_univ _)
    have h₂ := h (u - w) (mem_univ _)
    rw [show u + w - u = w by abel] at h₁
    rw [show u - w - u = -w by abel, inner_neg_right, inner_neg_right] at h₂
    linarith
  · rintro rfl
    exact ⟨mem_univ _, fun v _ => le_rfl⟩

/-! ### Theorem 11.3.1 and its two specializations -/

section Existence

variable [CompleteSpace V] {A : V → V} {c₀ M : ℝ} {j : V → ℝ} {K : Set V}

/-- **Theorem 11.3.1** of [han2009theoretical]. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Let $A \colon V \to V$ be strongly monotone with
constant $c_0 > 0$, that is $(A v_1 - A v_2, v_1 - v_2) \ge c_0 \|v_1 - v_2\|^2$ (11.3.1), and
Lipschitz continuous with constant $M \ge 0$, that is $\|A v_1 - A v_2\| \le M \|v_1 - v_2\|$
(11.3.2), for all $v_1, v_2 \in V$. Let $j \colon V \to \mathbb{R}$ be convex and lower
semicontinuous on $K$. Then for every $f \in V$ the variational inequality (11.3.3) has exactly
one solution. If $u_1$ solves it with datum $f_1$ and $u_2$ with datum $f_2$, then
$$\|u_1 - u_2\| \le \frac{1}{c_0} \|f_1 - f_2\|.$$

The second claim uses neither the Lipschitz continuity of $A$ nor the convexity of $j$; it is
the backbone's `IsVariationalInequalitySolution.norm_sub_le`. -/
theorem theorem_11_3_1 (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hc₀ : 0 < c₀)
    (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A j f K u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A j f₁ K u₁ →
        IsVariationalInequalitySolution A j f₂ K u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ := by
  refine ⟨fun f => existsUnique_isVariationalInequalitySolution hKne hKcl hKcv hc₀
      hmono ((Chapter05.lipschitzWith_toNNReal_iff hM).1 hlip) hj hjlsc
    f, fun f₁ f₂ u₁ u₂ h₁ h₂ => ?_⟩
  have h := IsVariationalInequalitySolution.norm_sub_le hc₀ hmono
    h₁ h₂
  rwa [one_div, inv_mul_eq_div]

/-- **Theorem 11.3.6** of [han2009theoretical] (Stampacchia's theorem). Let $V$ be a real Hilbert
space and let $K \subseteq V$ be nonempty, closed and convex. Let $A \colon V \to V$ be strongly
monotone with constant $c_0 > 0$ and Lipschitz continuous with constant $M \ge 0$. Then for
every $f \in V$ the inequality of the first kind (11.3.8),
$$u \in K, \qquad (A u, v - u) \ge (f, v - u) \quad \text{for all } v \in K,$$
has exactly one solution, and two solutions with data $f_1$, $f_2$ satisfy
$\|u_1 - u_2\| \le c_0^{-1} \|f_1 - f_2\|$.

This is Theorem 11.3.1 at $j = 0$.
`AtkinsonHan.Chapter11.isVariationalInequalitySolution_zero_iff` unfolds the statement to the
display of the source. -/
theorem theorem_11_3_6 (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hc₀ : 0 < c₀)
    (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A 0 f K u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A 0 f₁ K u₁ →
        IsVariationalInequalitySolution A 0 f₂ K u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ :=
  theorem_11_3_1 hKne hKcl hKcv hc₀ hM hmono hlip (convexOn_const 0 hKcv)
    lowerSemicontinuousOn_const

/-- **Theorem 11.3.7** of [han2009theoretical]. Let $V$ be a real Hilbert space. Let
$A \colon V \to V$ be strongly monotone with constant $c_0 > 0$ and Lipschitz continuous with
constant $M \ge 0$, and let $j \colon V \to \mathbb{R}$ be convex and lower semicontinuous on
$V$. Then for every $f \in V$ the inequality of the second kind (11.3.9),
$$(A u, v - u) + j(v) - j(u) \ge (f, v - u) \quad \text{for all } v \in V,$$
has exactly one solution $u \in V$, and two solutions with data $f_1$, $f_2$ satisfy
$\|u_1 - u_2\| \le c_0^{-1} \|f_1 - f_2\|$.

The function $j$ of the source takes values in $\mathbb{R} \cup \{+\infty\}$ and is proper. A
real-valued $j$ on the whole space is this hypothesis with effective domain $V$, which is why
the theorem is stated for $K = V$. -/
theorem theorem_11_3_7 (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hj : ConvexOn ℝ univ j)
    (hjlsc : LowerSemicontinuous j) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A j f univ u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A j f₁ univ u₁ →
        IsVariationalInequalitySolution A j f₂ univ u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ :=
  theorem_11_3_1 univ_nonempty isClosed_univ convex_univ hc₀ hM hmono hlip hj
    (hjlsc.lowerSemicontinuousOn univ)

/-- **Exercise 11.3.13** of [han2009theoretical]. Let $V$ be a real Hilbert space, and let
$A \colon V \to V$ be strongly monotone with constant $c_0 > 0$ and Lipschitz continuous with
constant $M \ge 0$. Then for every $f \in V$ the equation $A u = f$ has exactly one solution,
and two solutions with data $f_1$, $f_2$ satisfy $\|u_1 - u_2\| \le c_0^{-1} \|f_1 - f_2\|$.

This is Theorem 11.3.6 at $K = V$, and it is the statement of Theorem 5.1.4. -/
theorem exercise_11_3_13 (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Chapter05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) :
    (∀ f : V, ∃! u, A u = f) ∧
      ∀ f₁ f₂ u₁ u₂ : V, A u₁ = f₁ → A u₂ = f₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ := by
  obtain ⟨hex, hlipdep⟩ :=
    theorem_11_3_6 (K := (univ : Set V)) univ_nonempty isClosed_univ convex_univ hc₀ hM hmono hlip
  refine ⟨fun f => ?_, fun f₁ f₂ u₁ u₂ h₁ h₂ => ?_⟩
  · simpa only [isVariationalInequalitySolution_univ_zero_iff] using hex f
  · exact hlipdep f₁ f₂ u₁ u₂ ((isVariationalInequalitySolution_univ_zero_iff A f₁ u₁).2 h₁)
      ((isVariationalInequalitySolution_univ_zero_iff A f₂ u₂).2 h₂)

/-! ### Exercise 11.3.1: a locally Lipschitz operator -/

omit [CompleteSpace V] in
/-- **Exercise 11.3.1(a)** of [han2009theoretical]. Let $V$ be a real inner product space, and let
$m \colon \mathbb{R} \to \mathbb{R}$ be nondecreasing and nonnegative. Let $A \colon V \to V$
satisfy $\|A v_1 - A v_2\| \le m(r) \|v_1 - v_2\|$ for all $r$ and all $v_1, v_2$ with
$\|v_1\|, \|v_2\| \le r$. Then there is a function $\tilde m$, nondecreasing on $[0, \infty)$,
with
$$|(A v, w)| \le \tilde m(\|v\|) \, \|w\| \quad \text{for all } v, w \in V.$$

The proof takes $\tilde m(s) = m(s) s + \|A 0\|$ and compares $A v$ with $A 0$ on the ball of
radius $\|v\|$. -/
theorem exercise_11_3_1_growth {m : ℝ → ℝ} (hm : Monotone m) (hm0 : ∀ r, 0 ≤ m r)
    (hlip : ∀ r : ℝ, ∀ v₁ ∈ Metric.closedBall (0 : V) r, ∀ v₂ ∈ Metric.closedBall (0 : V) r,
      ‖A v₁ - A v₂‖ ≤ m r * ‖v₁ - v₂‖) :
    ∃ mt : ℝ → ℝ, MonotoneOn mt (Ici 0) ∧ ∀ v w : V, |⟪A v, w⟫_ℝ| ≤ mt ‖v‖ * ‖w‖ := by
  refine ⟨fun s => m s * s + ‖A 0‖, fun a ha b hb hab => ?_, fun v w => ?_⟩
  · have h : m a * a ≤ m b * b := mul_le_mul (hm hab) hab ha (hm0 b)
    linarith
  · have h := hlip ‖v‖ v (by simp) 0 (by simp [norm_nonneg v])
    rw [sub_zero] at h
    have hA : ‖A v‖ ≤ m ‖v‖ * ‖v‖ + ‖A 0‖ := by
      have h' : ‖A v‖ - ‖A 0‖ ≤ ‖A v - A 0‖ := norm_sub_norm_le _ _
      linarith
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg w))

omit [CompleteSpace V] in
/-- The a priori bound of Exercise 11.3.1(c): if $A$ is strongly monotone with constant $c_0 > 0$,
$\ell(v) + c \le j(v)$ on $K$, $u_0 \in K' \subseteq K$ and $u$ solves (11.3.3) over $K'$ with
datum $f$, then $\|u - u_0\| < (j(u_0) - \ell(u_0) - c + \|\ell\| + \|f - A u_0\|)/c_0 + 1$, a
bound that does not depend on $K'$. -/
private theorem norm_sub_lt_of_isVariationalInequalitySolution (hc₀ : 0 < c₀)
    (hmono : Chapter05.StronglyMonotoneWith A c₀) {ℓ : V →L[ℝ] ℝ} {cmin : ℝ}
    (hmin : ∀ v ∈ K, ℓ v + cmin ≤ j v) {u₀ : V} (hu₀ : u₀ ∈ K) {K' : Set V} (hK' : K' ⊆ K)
    (hu₀' : u₀ ∈ K') {f u : V} (hu : IsVariationalInequalitySolution A j f K' u) :
    ‖u - u₀‖ < (j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖)) / c₀ + 1 := by
  have ht0 : (0 : ℝ) ≤ ‖u - u₀‖ := norm_nonneg _
  have hB : 0 ≤ j u₀ - ℓ u₀ - cmin := by linarith [hmin u₀ hu₀]
  have hC : 0 ≤ ‖ℓ‖ + ‖f - A u₀‖ := by positivity
  have hmono' : c₀ * ‖u - u₀‖ ^ 2 ≤ ⟪A u - A u₀, u - u₀⟫_ℝ :=
    (isStronglyMonotoneWith_real_iff A c₀).1 hmono u u₀
  have hvi := hu.2 u₀ hu₀'
  have hneg : ∀ w : V, ⟪w, u₀ - u⟫_ℝ = -⟪w, u - u₀⟫_ℝ := fun w => by
    rw [← inner_neg_right]
    congr 1
    abel
  rw [hneg (A u), hneg f] at hvi
  have hjlow : ℓ u + cmin ≤ j u := hmin u (hK' hu.1)
  have hlsub : ℓ u = ℓ u₀ + ℓ (u - u₀) := by
    rw [← map_add]
    congr 1
    abel
  have hlb : -(‖ℓ‖ * ‖u - u₀‖) ≤ ℓ (u - u₀) := by
    have h : |ℓ (u - u₀)| ≤ ‖ℓ‖ * ‖u - u₀‖ := by
      simpa [Real.norm_eq_abs] using ℓ.le_opNorm (u - u₀)
    linarith [(abs_le.mp h).1]
  have hf : ⟪f, u - u₀⟫_ℝ - ⟪A u₀, u - u₀⟫_ℝ ≤ ‖f - A u₀‖ * ‖u - u₀‖ := by
    have h := real_inner_le_norm (f - A u₀) (u - u₀)
    rwa [inner_sub_left] at h
  rw [inner_sub_left] at hmono'
  have hkey : c₀ * ‖u - u₀‖ ^ 2
      ≤ j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖) * ‖u - u₀‖ := by nlinarith [hvi, hmono']
  by_contra hcon
  push Not at hcon
  have ht1 : (1 : ℝ) ≤ ‖u - u₀‖ := by
    have : 0 ≤ (j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖)) / c₀ := by positivity
    linarith
  have hmul : c₀ * ((j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖)) / c₀ + 1)
      = j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖) + c₀ := by
    field_simp
  have hct : j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖) + c₀ ≤ c₀ * ‖u - u₀‖ := by
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left hcon hc₀.le
  nlinarith [hkey, hct, ht1, hB, hC]

/-- **Exercise 11.3.1** of [han2009theoretical]. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Let $A \colon V \to V$ be strongly monotone with
constant $c_0 > 0$, and let $A$ be locally Lipschitz continuous: for a function
$m \colon \mathbb{R} \to \mathbb{R}$,
$$\|A v_1 - A v_2\| \le m(r) \|v_1 - v_2\| \quad \text{for all } r \text{ and all } v_1, v_2 \in
  V_r = \{v : \|v\| \le r\}.$$
Let $j \colon V \to \mathbb{R}$ be convex and lower semicontinuous on $K$. Then for every
$f \in V$ the variational inequality (11.3.3) has exactly one solution, and two solutions with
data $f_1$, $f_2$ satisfy $\|u_1 - u_2\| \le c_0^{-1} \|f_1 - f_2\|$.

The exercise asks for $m$ nondecreasing. That is used only in part (a),
`AtkinsonHan.Chapter11.exercise_11_3_1_growth`, and is not a hypothesis here. The proof follows
the source. On $K_r = K \cap V_r$ the operator is Lipschitz continuous, so Theorem 11.3.1
applies there in the form of Remark 11.3.2, `existsUnique_isVariationalInequalitySolution_on`,
whose hypotheses are needed on the constraint set only. By part (c), the solution $u_r$
satisfies $\|u_r\| < R_0$ for a radius $R_0$ that does not depend on $r$. In part (d), for
$v \in K$ with $\|v\| > R_0$, the point $(1 - \lambda) u + \lambda v$ with
$\lambda = (R_0 - \|u\|)/(\|v\| - \|u\|)$ lies in $K_{R_0}$, and the convexity of $j$ turns the
inequality at that point into the inequality at $v$. -/
theorem exercise_11_3_1 (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hc₀ : 0 < c₀)
    (hmono : Chapter05.StronglyMonotoneWith A c₀) {m : ℝ → ℝ}
    (hlip : ∀ r : ℝ, ∀ v₁ ∈ Metric.closedBall (0 : V) r, ∀ v₂ ∈ Metric.closedBall (0 : V) r,
      ‖A v₁ - A v₂‖ ≤ m r * ‖v₁ - v₂‖)
    (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A j f K u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A j f₁ K u₁ →
        IsVariationalInequalitySolution A j f₂ K u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ := by
  obtain ⟨u₀, hu₀⟩ := hKne
  obtain ⟨ℓ, cmin, hmin⟩ := lemma_11_3_5 ⟨u₀, hu₀⟩ hKcl hj hjlsc
  refine ⟨fun f => ?_, fun f₁ f₂ u₁ u₂ h₁ h₂ => ?_⟩
  · -- the radius `R₀ = ‖u₀‖ + ρ` of part (c), which does not depend on the truncation
    obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (K' : Set V) (u : V), K' ⊆ K → u₀ ∈ K' →
        IsVariationalInequalitySolution A j f K' u → ‖u - u₀‖ < ρ := by
      refine ⟨(j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖)) / c₀ + 1, ?_,
        fun K' u hK' hu₀' hu =>
          norm_sub_lt_of_isVariationalInequalitySolution hc₀ hmono hmin hu₀ hK' hu₀' hu⟩
      have hB : 0 ≤ j u₀ - ℓ u₀ - cmin := by linarith [hmin u₀ hu₀]
      have : 0 ≤ (j u₀ - ℓ u₀ - cmin + (‖ℓ‖ + ‖f - A u₀‖)) / c₀ := by positivity
      linarith
    -- part (b): the truncated problem on `K_{R₀} = K ∩ V_{R₀}` is uniquely solvable
    have hKRcv : Convex ℝ (K ∩ Metric.closedBall (0 : V) (‖u₀‖ + ρ)) :=
      hKcv.inter (convex_closedBall 0 _)
    have hu₀R : u₀ ∈ K ∩ Metric.closedBall (0 : V) (‖u₀‖ + ρ) :=
      ⟨hu₀, by simpa [mem_closedBall_zero_iff] using (by linarith : ‖u₀‖ ≤ ‖u₀‖ + ρ)⟩
    obtain ⟨u, hu, -⟩ := existsUnique_isVariationalInequalitySolution_on ⟨u₀, hu₀R⟩
      (hKcl.inter Metric.isClosed_closedBall) hKRcv hc₀
      (IsStronglyMonotoneWith.isStronglyMonotoneOnWith hmono _)
      (fun x hx y hy => hlip (‖u₀‖ + ρ) x hx.2 y hy.2)
      (hj.subset inter_subset_left hKRcv) (hjlsc.mono inter_subset_left) f
    -- part (c): the solution of the truncated problem is interior to the ball
    have hunorm : ‖u‖ < ‖u₀‖ + ρ := by
      have h := hρ _ u inter_subset_left hu₀R hu
      have htri : ‖u‖ ≤ ‖u₀‖ + ‖u - u₀‖ := by
        calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by congr 1; abel
          _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
      linarith
    -- part (d): it therefore solves the inequality on all of `K`
    have hsol : IsVariationalInequalitySolution A j f K u := by
      refine ⟨hu.1.1, fun v hv => ?_⟩
      rcases le_or_gt ‖v‖ (‖u₀‖ + ρ) with hvle | hvgt
      · exact hu.2 v ⟨hv, by simpa [mem_closedBall_zero_iff] using hvle⟩
      · have hden : 0 < ‖v‖ - ‖u‖ := by linarith
        have hlam0 : 0 < (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖) := div_pos (by linarith) hden
        have hlam1 : (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖) < 1 := by
          rw [div_lt_one hden]
          linarith
        have hlamv : (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖) * (‖v‖ - ‖u‖) = ‖u₀‖ + ρ - ‖u‖ :=
          div_mul_cancel₀ _ hden.ne'
        have hcomb : u + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u)
            = (1 - (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • u
              + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • v := by
          rw [sub_smul, one_smul, smul_sub]
          abel
        have hmemK : u + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u) ∈ K := by
          rw [hcomb]
          exact hKcv hu.1.1 hv (by linarith) hlam0.le (by ring)
        have hmemball : u + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u)
            ∈ Metric.closedBall (0 : V) (‖u₀‖ + ρ) := by
          rw [mem_closedBall_zero_iff, hcomb]
          have h := norm_add_le ((1 - (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • u)
            (((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • v)
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)),
            abs_of_nonneg hlam0.le] at h
          nlinarith [h, hlamv]
        have hvi := hu.2 _ ⟨hmemK, hmemball⟩
        have hjw : j (u + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u))
            ≤ (1 - (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) * j u
              + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) * j v := by
          rw [hcomb]
          exact hj.2 hu.1.1 hv (by linarith) hlam0.le (by ring)
        have hinner : ∀ w : V,
            ⟪w, u + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u) - u⟫_ℝ
              = (‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖) * ⟪w, v - u⟫_ℝ := by
          intro w
          rw [show u + ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u) - u
              = ((‖u₀‖ + ρ - ‖u‖) / (‖v‖ - ‖u‖)) • (v - u) by abel, real_inner_smul_right]
        rw [hinner (A u), hinner f] at hvi
        rw [ge_iff_le]
        refine le_of_mul_le_mul_left ?_ hlam0
        linarith [hvi, hjw]
    exact ⟨u, hsol, fun y hy =>
      IsVariationalInequalitySolution.unique hc₀ hmono hy hsol⟩
  · have h := IsVariationalInequalitySolution.norm_sub_le hc₀ hmono
      h₁ h₂
    rwa [one_div, inv_mul_eq_div]

end Existence

/-! ### Lemma 11.3.8: Minty's lemma -/

/-- Let $V$ be a real inner product space and let $A \colon V \to V$ be continuous. Then for all
$u, v \in V$ the map $t \mapsto A(u + t (v - u))$ is right-continuous at $t = 0$, which is the
hypothesis of Minty's lemma, `AtkinsonHan.Chapter11.lemma_11_3_8`. In particular, the Lipschitz
operators of Theorem 11.3.1 satisfy it. -/
theorem continuousWithinAt_segment_of_continuous {A : V → V} (hA : Continuous A) (u v : V) :
    ContinuousWithinAt (fun t : ℝ => A (u + t • (v - u))) (Ioi 0) 0 :=
  (hA.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousWithinAt

/-- **Lemma 11.3.8** of [han2009theoretical] (Minty's lemma). Let $V$ be a real inner product space,
let $K \subseteq V$ be convex, let $j \colon V \to \mathbb{R}$ be convex on $K$, let $f \in V$,
and let $A \colon V \to V$ be monotone, that is $(A v_1 - A v_2, v_1 - v_2) \ge 0$ for all
$v_1, v_2$. Let $u \in K$, and assume that for every $v \in K$ the map
$t \mapsto A(u + t (v - u))$ is right-continuous at $t = 0$. Then $u$ solves the variational
inequality (11.3.3) if and only if
$$(A v, v - u) + j(v) - j(u) \ge (f, v - u) \quad \text{for all } v \in K,$$
which is (11.3.10).

**Generalization.** The source assumes that $A$ is continuous on the finite-dimensional
subspaces of $V$. This implies the hypothesis here, because the segment from $u$ to $v$ lies in
the span of $u$ and $v$. The weaker hypothesis is what the proof uses, and
`AtkinsonHan.Chapter11.continuousWithinAt_segment_of_continuous` gives it for every continuous
$A$.

Monotonicity is `AtkinsonHan.Chapter05.StronglyMonotoneWith A 0`. One direction follows from
monotonicity. The other tests the inequality at $u + t (v - u)$, uses the convexity of $j$, and
lets $t \to 0^+$. -/
theorem lemma_11_3_8 {A : V → V} {j : V → ℝ} {f : V} {K : Set V} (hKcv : Convex ℝ K)
    (hj : ConvexOn ℝ K j) (hmono : Chapter05.StronglyMonotoneWith A 0) {u : V} (hu : u ∈ K)
    (hA : ∀ v ∈ K, ContinuousWithinAt (fun t : ℝ => A (u + t • (v - u))) (Ioi 0) 0) :
    IsVariationalInequalitySolution A j f K u ↔
      ∀ v ∈ K, ⟪A v, v - u⟫_ℝ + j v - j u ≥ ⟪f, v - u⟫_ℝ :=
  IsVariationalInequalitySolution.iff_minty hKcv hj hmono hu hA

/-! ### Theorem 11.3.9 and the bilinear-form problems -/

section BilinearForm

variable [CompleteSpace V] {a : BilinForm V} {M α : ℝ}

/-- Let $a$ be a bilinear form on a real Hilbert space $V$, bounded with constant $M$, let
$\ell \in V'$, $j \colon V \to \mathbb{R}$ and $K \subseteq V$. Then $u$ solves the variational
inequality (11.3.3) for the operator $A$ of $a$ and the Riesz representative of $\ell$ if and
only if $u \in K$ and
$$a(u, v - u) + j(v) - j(u) \ge \ell(v - u) \quad \text{for all } v \in K.$$
This is (11.3.12), and (11.3.13) and (11.3.14) are its cases $j = 0$ and $K = V$.

The operator is `AtkinsonHan.BilinForm.toOperator`, with $(A u, v) = a(u, v)$, and the Riesz
representative is `SesqForm.rieszRep`. -/
theorem isVariationalInequalitySolution_toOperator_iff (hM : a.IsBoundedWith M) (j : V → ℝ)
    (ℓ : StrongDual ℝ V) (K : Set V) (u : V) :
    IsVariationalInequalitySolution (BilinForm.toOperator a hM) j (SesqForm.rieszRep ℓ) K u ↔
      u ∈ K ∧ ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u) := by
  simp only [IsVariationalInequalitySolution, BilinForm.inner_toOperator,
    BilinForm.inner_rieszRep]

/-- **Theorem 11.3.9** of [han2009theoretical]. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Let $a$ be a bilinear form on $V$, bounded with
constant $M$ and $V$-elliptic with constant $\alpha > 0$; $a$ need not be symmetric. Let
$j \colon V \to \mathbb{R}$ be convex and lower semicontinuous on $K$. Then for every
$\ell \in V'$ the variational inequality (11.3.12),
$$u \in K, \qquad a(u, v - u) + j(v) - j(u) \ge \ell(v - u) \quad \text{for all } v \in K,$$
has exactly one solution. If $u_1$ solves it with $\ell_1$ and $u_2$ with $\ell_2$, then
$$\|u_1 - u_2\| \le \frac{1}{\alpha} \|\ell_1 - \ell_2\|.$$

This one statement covers (11.3.12), (11.3.13) and (11.3.14): the three displays differ only in
$j$ and $K$, and (11.3.13) is the case $j = 0$, (11.3.14) the case $K = V$. -/
theorem theorem_11_3_9 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) {j : V → ℝ}
    (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K) :
    (∀ ℓ : StrongDual ℝ V, ∃! u, u ∈ K ∧ ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u)) ∧
      ∀ (ℓ₁ ℓ₂ : StrongDual ℝ V) (u₁ u₂ : V),
        (u₁ ∈ K ∧ ∀ v ∈ K, a u₁ (v - u₁) + j v - j u₁ ≥ ℓ₁ (v - u₁)) →
        (u₂ ∈ K ∧ ∀ v ∈ K, a u₂ (v - u₂) + j v - j u₂ ≥ ℓ₂ (v - u₂)) →
        ‖u₁ - u₂‖ ≤ 1 / α * ‖ℓ₁ - ℓ₂‖ := by
  have hcoer : SesqForm.IsCoerciveWith (a.toCLM hM) α :=
    (a.isEllipticWith_iff_isCoerciveWith hM).1 ha
  have hmono : IsStronglyMonotoneWith ℝ (BilinForm.toOperator a hM : V → V) α :=
    LinearMap.IsCoerciveWith.isStronglyMonotoneWith
      ((SesqForm.isCoerciveWith_iff_toOperator (a.toCLM hM) α).mp hcoer)
  have hriesz : ∀ ℓ₁ ℓ₂ : StrongDual ℝ V,
      SesqForm.rieszRep ℓ₁ - SesqForm.rieszRep ℓ₂ = SesqForm.rieszRep (V := V) (ℓ₁ - ℓ₂) := by
    intro ℓ₁ ℓ₂
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_sub_left, SesqForm.inner_rieszRep, SesqForm.inner_rieszRep, SesqForm.inner_rieszRep]
    simp
  constructor
  · intro ℓ
    exact (existsUnique_congr fun u => isVariationalInequalitySolution_toOperator_iff hM j ℓ K u).mp
      (existsUnique_isVariationalInequalitySolution_of_isCoercive hα hcoer hKne hKcl hKcv hj
        hjlsc ℓ)
  · intro ℓ₁ ℓ₂ u₁ u₂ h₁ h₂
    have h := IsVariationalInequalitySolution.norm_sub_le hα hmono
      ((isVariationalInequalitySolution_toOperator_iff hM j ℓ₁ K u₁).2 h₁)
      ((isVariationalInequalitySolution_toOperator_iff hM j ℓ₂ K u₂).2 h₂)
    rw [hriesz ℓ₁ ℓ₂, SesqForm.norm_rieszRep] at h
    rwa [one_div, inv_mul_eq_div]

/-- **Section 11.3** of [han2009theoretical], the remark after Example 11.3.11. Let $V$ be a real
Hilbert space and let $K \subseteq V$ be convex. Let $a$ be a bilinear form on $V$ that is
bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$, and let
$\ell \in V'$. Let $w \in V$ solve the variational equation $a(w, v) = \ell(v)$ for all
$v \in V$, and let $u$ solve (11.3.13), that is $u \in K$ and $a(u, v - u) \ge \ell(v - u)$ for
all $v \in K$. Then $u$ is a best approximation of $w$ in $K$ in the energy norm
$\|v\|_a = \sqrt{a(v, v)}$:
$$\|w - u\|_a \le \|w - v\|_a \quad \text{for all } v \in K.$$

So the inequality can be solved by solving the equation and then projecting onto $K$ in the
energy inner product. The energy norm is `AtkinsonHan.BilinForm.energyNorm`. -/
theorem isBestApprox_energy_of_theorem_11_3_9 (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hKcv : Convex ℝ K) {w u : V} (hw : ∀ v, a w v = ℓ v)
    (hu : u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u)) :
    ∀ v ∈ K, a.energyNorm (w - u) ≤ a.energyNorm (w - v) := by
  have hsc : (BilinForm.toOperator a hM : V →ₗ[ℝ] V).IsSymmetricCoercive :=
    BilinForm.isSymmetricCoercive_toOperator hM hα ha hs
  have hwr : BilinForm.toOperator a hM w = SesqForm.rieszRep ℓ :=
    (BilinForm.toOperator_eq_rieszRep_iff hM ℓ w).2 hw
  have hsol : _root_.IsVariationalInequalitySolution
      (BilinForm.toOperator a hM : V → V) 0 (SesqForm.rieszRep ℓ) K u := by
    refine (isVariationalInequalitySolution_toOperator_iff hM 0 ℓ K u).2 ⟨hu.1, fun v hv => ?_⟩
    simpa using hu.2 v hv
  have hbest := IsVariationalInequalitySolution.isBestApprox_energy hsc hKcv hwr hsol
  intro v hv
  have h := hbest.2 (WithEnergy.equiv _ hsc v) ⟨v, hv, rfl⟩
  rw [← map_sub, ← map_sub, WithEnergy.norm_equiv, WithEnergy.norm_equiv] at h
  rwa [a.energyNorm_eq_energyNorm_toOperator hM, a.energyNorm_eq_energyNorm_toOperator hM]

/-- **Exercise 11.3.2** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $a$ be a
bilinear form on $V$ that is bounded with constant $M$ and $V$-elliptic with constant
$\alpha > 0$, and let $\ell \in V'$. Then there is exactly one $u \in V$ with
$$a(u, v) = \ell(v) \quad \text{for all } v \in V.$$

The exercise shows that Theorem 11.3.6 generalizes the Lax–Milgram lemma, Theorem 8.3.4: with
$K = V$ and $A$ the operator of $a$, the inequality of the first kind becomes the variational
equation, by `AtkinsonHan.Chapter11.isVariationalInequalitySolution_univ_zero_iff`. -/
theorem exercise_11_3_2 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v := by
  have hmono : Chapter05.StronglyMonotoneWith (BilinForm.toOperator a hM : V → V) α :=
    Chapter08.stronglyMonotone_toOperator hM ha
  have hlip : ∀ v₁ v₂ : V, ‖BilinForm.toOperator a hM v₁ - BilinForm.toOperator a hM v₂‖
      ≤ ‖BilinForm.toOperator a hM‖ * ‖v₁ - v₂‖ := by
    intro v₁ v₂
    rw [← map_sub]
    exact (BilinForm.toOperator a hM).le_opNorm _
  obtain ⟨hex, -⟩ := theorem_11_3_6 (K := (univ : Set V)) univ_nonempty isClosed_univ convex_univ
    hα (norm_nonneg (BilinForm.toOperator a hM)) hmono hlip
  obtain ⟨u, hu, huniq⟩ := hex (SesqForm.rieszRep ℓ)
  rw [isVariationalInequalitySolution_univ_zero_iff] at hu
  refine ⟨u, (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).1 hu, fun y hy => ?_⟩
  exact huniq y ((isVariationalInequalitySolution_univ_zero_iff _ _ y).2
    ((BilinForm.toOperator_eq_rieszRep_iff hM ℓ y).2 hy))

/-- **Exercise 11.3.3** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $a$ be a
bilinear form on $V$ that is bounded with constant $M$, and let $\ell \in V'$. Let
$K \subseteq V$ be a convex cone: $K$ is convex and $t x \in K$ for all $t \ge 0$ and $x \in K$.
Then for $u \in K$, the inequality of the first kind (11.3.13), $a(u, v - u) \ge \ell(v - u)$
for all $v \in K$, holds if and only if
$$a(u, v) \ge \ell(v) \quad \text{for all } v \in K \qquad \text{and} \qquad a(u, u) =
  \ell(u).$$

The proof tests at $2u$ and at $0$ for the equality, and at $u + v$ for the inequality.
Conversely, subtracting the equality from the inequality at $v$ gives the variational
inequality. -/
theorem exercise_11_3_3 (hM : a.IsBoundedWith M) {K : Set V} (hKcv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K) (ℓ : StrongDual ℝ V) {u : V} (hu : u ∈ K) :
    (u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u)) ↔
      ((∀ v ∈ K, a u v ≥ ℓ v) ∧ a u u = ℓ u) := by
  have hiff := IsVariationalInequalitySolution.iff_of_isCone
    (A := (BilinForm.toOperator a hM : V → V)) (f := SesqForm.rieszRep ℓ) hKcv hKcone hu
  have hz : IsVariationalInequalitySolution (BilinForm.toOperator a hM) 0
      (SesqForm.rieszRep ℓ) K u ↔ (u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u)) := by
    rw [isVariationalInequalitySolution_toOperator_iff hM 0 ℓ K u]
    simp
  refine hz.symm.trans (hiff.trans ?_)
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep, ge_iff_le]

/-- **Exercise 11.3.10** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $a$ be a
bilinear form on $V$ that is bounded with constant $M$, and let $\ell \in V'$. Let
$j \colon V \to \mathbb{R}$ be convex and positively homogeneous: $j(t v) = t j(v)$ for all
$t > 0$ and $v \in V$. Then $u \in V$ solves the inequality of the second kind (11.3.14),
$a(u, v - u) + j(v) - j(u) \ge \ell(v - u)$ for all $v \in V$, if and only if
$$a(u, v) + j(v) \ge \ell(v) \quad \text{for all } v \in V \qquad \text{and} \qquad a(u, u) +
  j(u) = \ell(u).$$

Convexity and positive homogeneity make $j$ subadditive, and this turns the test at $u + v$ into
the inequality at $v$. -/
theorem exercise_11_3_10 (hM : a.IsBoundedWith M) {j : V → ℝ} (hj : ConvexOn ℝ univ j)
    (hhom : ∀ t : ℝ, 0 < t → ∀ v : V, j (t • v) = t * j v) (ℓ : StrongDual ℝ V) {u : V} :
    (∀ v, a u (v - u) + j v - j u ≥ ℓ (v - u)) ↔
      ((∀ v, a u v + j v ≥ ℓ v) ∧ a u u + j u = ℓ u) := by
  have hiff := IsVariationalInequalitySolution.iff_of_isPositiveHomogeneous
    (A := (BilinForm.toOperator a hM : V → V)) (f := SesqForm.rieszRep ℓ) hj hhom (u := u)
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep] at hiff
  rw [← hiff, ← isVariationalInequalitySolution_iff,
    isVariationalInequalitySolution_univ_iff]
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep]

end BilinearForm

/-! ### Example 11.3.10: the obstacle problem -/

section Obstacle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {a : BilinForm V} {M α : ℝ}

/-- **Theorem 11.3.9** of [han2009theoretical] with $j = 0$, existence and uniqueness. Let $V$ be a
real Hilbert space and let $K \subseteq V$ be nonempty, closed and convex. Let $a$ be a bilinear
form on $V$, bounded with constant $M$ and $V$-elliptic with constant $\alpha > 0$, and let
$\ell \in V'$. Then the inequality of the first kind (11.3.13),
$$u \in K, \qquad a(u, v - u) \ge \ell(v - u) \quad \text{for all } v \in K,$$
has exactly one solution.

It is stated for an abstract space so that Example 11.3.10 is a single application of it. -/
theorem theorem_11_3_9_zero_existsUnique (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) (ℓ : StrongDual ℝ V) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u) := by
  have h := (theorem_11_3_9 hM hα ha hKne hKcl hKcv (j := fun _ ↦ (0 : ℝ))
    (convexOn_const _ hKcv) (lowerSemicontinuous_const.lowerSemicontinuousOn _)).1 ℓ
  simp only [add_zero, sub_zero] at h
  exact h

/-- **Theorem 11.3.9** of [han2009theoretical] with $j = 0$, Lipschitz dependence. Let $V$ be a real
Hilbert space and let $K \subseteq V$ be nonempty, closed and convex. Let $a$ be a bilinear form
on $V$, bounded with constant $M$ and $V$-elliptic with constant $\alpha > 0$. If $u_1$ solves
the inequality of the first kind (11.3.13) with $\ell_1 \in V'$ and $u_2$ solves it with
$\ell_2 \in V'$, then
$$\|u_1 - u_2\| \le \frac{1}{\alpha} \|\ell_1 - \ell_2\|.$$

It is stated for an abstract space so that Example 11.3.10 is a single application of it. -/
theorem theorem_11_3_9_zero_lipschitz (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) (ℓ₁ ℓ₂ : StrongDual ℝ V) {u₁ u₂ : V}
    (h₁ : u₁ ∈ K ∧ ∀ v ∈ K, a u₁ (v - u₁) ≥ ℓ₁ (v - u₁))
    (h₂ : u₂ ∈ K ∧ ∀ v ∈ K, a u₂ (v - u₂) ≥ ℓ₂ (v - u₂)) :
    ‖u₁ - u₂‖ ≤ 1 / α * ‖ℓ₁ - ℓ₂‖ := by
  have h := (theorem_11_3_9 hM hα ha hKne hKcl hKcv (j := fun _ ↦ (0 : ℝ))
    (convexOn_const _ hKcv) (lowerSemicontinuous_const.lowerSemicontinuousOn _)).2 ℓ₁ ℓ₂ u₁ u₂
  simp only [add_zero, sub_zero] at h
  exact h h₁ h₂

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Example 11.3.10** of [han2009theoretical] (the obstacle problem). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open with $\Omega \subseteq B(0, R)$ for some $R \ge 0$.
Let $\psi \in H^1(\Omega)$ be an obstacle such that $\max\{\psi, 0\}$ is almost everywhere equal
to the function of an element of $H^1_0(\Omega)$. Let $K = \{v \in H^1_0(\Omega) : v \ge \psi
\text{ a.e.}\}$, $a(u, v) = \int_\Omega \nabla u \cdot \nabla v \, dx$, and
$\ell_f(v) = \int_\Omega f v \, dx$ for $f \in L^2(\Omega)$. Then the obstacle problem (11.1.7)
is the inequality of the first kind (11.3.13) on $V = H^1_0(\Omega)$:
$$u \in K, \qquad a(u, v - u) \ge \ell_f(v - u) \quad \text{for all } v \in K.$$
For every $f \in L^2(\Omega)$ it has exactly one solution. If $u_1$ solves it with $f_1$ and
$u_2$ with $f_2$, then
$$\|u_1 - u_2\|_{H^1(\Omega)} \le \bigl(1 + (2R)^2\bigr) \|f_1 - f_2\|_{L^2(\Omega)}.$$

**Reading.** The source asks that $\psi \le 0$ on $\Gamma$. Without a trace, this is read as the
condition that $\max\{\psi, 0\}$ is the function of an element of $H^1_0(\Omega)$, as in Example
11.1.1.

The hypotheses of Theorem 11.3.9 are those of Example 11.2.3. The set $K$ is
`AtkinsonHan.Chapter11.obstacleSet`; it contains $\max\{\psi, 0\}$ and is closed and convex. The
form $a$ is `AtkinsonHan.Chapter11.dirichletBilinForm`; it is bounded with $M = 1$ and
$V$-elliptic with $\alpha = (1 + (2R)^2)^{-1}$ by the Poincaré inequality, and $1/\alpha$ is the
Lipschitz constant. The load is `AtkinsonHan.Chapter11.loadZero`, with $\|\ell_{f_1} -
\ell_{f_2}\| \le \|f_1 - f_2\|_{L^2}$. The proof applies
`AtkinsonHan.Chapter11.theorem_11_3_9_zero_existsUnique` and
`AtkinsonHan.Chapter11.theorem_11_3_9_zero_lipschitz`. -/
theorem example_11_3_10 {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ Metric.ball 0 R)
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    (hψ : ∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, SobolevMultiIndex.fn w
      =ᵐ[MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ max (SobolevMultiIndex.fn ψ x) 0) :
    (∀ f : MeasureTheory.Lp ℝ 2
        (MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ∃! u, u ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
        dirichletBilinForm Ω u (v - u) ≥ loadZero Ω f (v - u)) ∧
    ∀ (f₁ f₂ : MeasureTheory.Lp ℝ 2
        (MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
      (u₁ u₂ : SobolevEuclideanZero (d + 1) 1 2 Ω),
      (u₁ ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
        dirichletBilinForm Ω u₁ (v - u₁) ≥ loadZero Ω f₁ (v - u₁)) →
      (u₂ ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
        dirichletBilinForm Ω u₂ (v - u₂) ≥ loadZero Ω f₂ (v - u₂)) →
      ‖u₁ - u₂‖ ≤ (1 + (2 * R) ^ 2) * ‖f₁ - f₂‖ := by
  have hM := dirichletBilinForm_isBoundedWith Ω
  have hα := dirichletBilinForm_isEllipticWith Ω hR hΩ
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  refine ⟨fun f ↦ theorem_11_3_9_zero_existsUnique hM hpos hα (obstacleSet_nonempty Ω hψ)
    (isClosed_obstacleSet Ω ψ) (convex_obstacleSet Ω ψ) (loadZero Ω f),
    fun f₁ f₂ u₁ u₂ hh₁ hh₂ ↦ ?_⟩
  have hk := theorem_11_3_9_zero_lipschitz hM hpos hα (obstacleSet_nonempty Ω hψ)
    (isClosed_obstacleSet Ω ψ) (convex_obstacleSet Ω ψ) (loadZero Ω f₁) (loadZero Ω f₂) hh₁ hh₂
  have hc : ∀ y : ℝ, 1 / (1 + (2 * R) ^ 2)⁻¹ * y = (1 + (2 * R) ^ 2) * y := fun y ↦ by
    rw [one_div, inv_inv]
  exact (hk.trans_eq (hc _)).trans
    (mul_le_mul_of_nonneg_left (norm_loadZero_sub_le Ω f₁ f₂) (by positivity))

end Obstacle

/-! ### Theorem 11.3.12 for $p = 2$: $H^2$ regularity for the obstacle problem -/

section Regularity

open MeasureTheory SobolevMultiIndex Metric

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, $\psi \in H^1(\Omega)$ and $f \in L^2(\Omega)$.
If $u \in H^1_0(\Omega)$ solves the obstacle problem of Example 11.3.10, then $u$, viewed in
$H^1(\Omega)$, is a solution in the sense of `Elliptic.IsObstacleSolution`:
$u \in H^1_0(\Omega)$, $u \ge \psi$ a.e., and $\int_\Omega \nabla u \cdot \nabla (v - u) \ge
\int_\Omega f (v - u)$ for every $v \in H^1_0(\Omega)$ with $v \ge \psi$ a.e.

This connects Example 11.3.10 to the backbone regularity theory used for Theorem 11.3.12. -/
theorem isObstacleSolution_of_example_11_3_10 {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hu : u ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
      dirichletBilinForm Ω u (v - u) ≥ loadZero Ω f (v - u)) :
    Elliptic.IsObstacleSolution Ω ψ f (u : SobolevEuclidean (d + 1) 1 2 Ω) where
  mem_zero := u.2
  ae_le := (mem_obstacleSet_iff Ω).1 hu.1
  ineq v hv hψv := by
    have h := hu.2 ⟨v, hv⟩ ((mem_obstacleSet_iff Ω).2 hψv)
    rw [ge_iff_le, dirichletBilinForm_apply] at h
    exact h

/-- The a priori $H^1$ bound for the obstacle problem. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
open with $\Omega \subseteq B(0, R)$ for some $R \ge 0$, let $\psi \in H^1(\Omega)$ and
$f \in L^2(\Omega)$, and let $w \in K = \{v \in H^1_0(\Omega) : v \ge \psi \text{ a.e.}\}$. If
$u$ solves the obstacle problem of Example 11.3.10, then
$$\|u\|_{H^1(\Omega)} \le 2 \bigl(1 + (2R)^2\bigr) \bigl(\|w\|_{H^1(\Omega)} +
  \|f\|_{L^2(\Omega)}\bigr).$$

This bound is used in the proof of Theorem 11.3.12. It is `Elliptic.IsObstacleSolution.norm_le`.
Testing with $v = w$ gives $a(u, u) \le a(u, w) - \ell(w) + \ell(u)$, and
$a(u, u) \ge (1 + (2R)^2)^{-1} \|u\|^2$ by the Poincaré inequality. -/
theorem norm_le_of_obstacle_solution {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {w : SobolevEuclideanZero (d + 1) 1 2 Ω} (hwK : w ∈ obstacleSet Ω ψ)
    {u : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hu : u ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
      dirichletBilinForm Ω u (v - u) ≥ loadZero Ω f (v - u)) :
    ‖u‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖w‖ + ‖f‖) :=
  (isObstacleSolution_of_example_11_3_10 Ω hu).norm_le hR hΩ w.2 ((mem_obstacleSet_iff Ω).1 hwK)

/-- The obstacle $\psi \in H^2(\Omega)$ of Theorem 11.3.12 of [han2009theoretical], viewed as an
element of $H^1(\Omega)$ through the inclusion $H^2(\Omega) \subseteq H^1(\Omega)$.

The inclusion is `SobolevMultiIndex.toLowerOrder`. -/
noncomputable abbrev obstacleOfH2 (Ψ : SobolevEuclidean (d + 1) 2 2 Ω) :
    SobolevEuclidean (d + 1) 1 2 Ω :=
  toLowerOrder ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 Ω volume (by norm_num) Ψ

/-- **Theorem 11.3.12** of [han2009theoretical], the case $p = 2$ for the Laplacian
($a_{ij} = \delta_{ij}$) on a $C^2$ domain. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open
set of class $C^2$ with $\Omega \subseteq B(0, R)$ for some $R \ge 0$. Then there is a constant
$C \ge 0$ with the following property. Let $\psi \in H^2(\Omega)$ be an obstacle such that
$\max\{\psi, 0\}$ is almost everywhere equal to the function of an element of $H^1_0(\Omega)$,
let $f \in L^2(\Omega)$, and let $u \in K = \{v \in H^1_0(\Omega) : v \ge \psi \text{ a.e.}\}$
solve the obstacle problem (11.1.7). Then $u \in H^2(\Omega)$, and every $U \in H^2(\Omega)$
whose function equals $u$ almost everywhere satisfies
$$\|U\|_{H^2(\Omega)} \le C \bigl(\|f\|_{L^2(\Omega)} + \|\psi\|_{H^2(\Omega)}\bigr).$$

**Reading.** The source asks that $\psi \le 0$ on $\Gamma$. This is read as the condition that
$\max\{\psi, 0\}$ is the function of an element of $H^1_0(\Omega)$, as in Examples 11.1.1 and
11.3.10.

The source states the theorem for $1 < p < \infty$, uniformly elliptic coefficients
$a_{ij} \in C(\overline\Omega)$ and $C^{1,1}$ domains: for $f \in L^p(\Omega)$ and
$\psi \in W^{2,p}(\Omega)$, the solution lies in $W^{2,p}(\Omega)$ and $\|u\|_{2,p} \le C_p
(\|f\|_{0,p} + \|\psi\|_{2,p})$, with $C_p$ independent of $u$, $f$ and $\psi$. It quotes the
theorem without proof from Brezis–Stampacchia and Gilbarg–Trudinger. Only the case stated here
is formalized; the module documentation says what the general case needs. The class $C^2$ is
`IsContDiffChartDomain 2`. The constant $C$ depends only on $\Omega$, and
`AtkinsonHan.Chapter11.example_11_3_10` gives the existence and the uniqueness of $u$. The proof
specializes `Elliptic.regularity_obstacle_sobolev_two`. Its main step is the Lewy–Stampacchia
inequality $f \le -\Delta u \le \max\{f, -\Delta\psi\}$,
`Elliptic.IsObstacleSolution.exists_dirichletForm_eq_load`, which is proved with the truncation
$\min\{\varepsilon\Phi, u - \psi\}$ and the Hahn–Banach theorem, not by penalization. It gives
$-\Delta u \in L^2(\Omega)$, so the linear regularity theorem `Elliptic.regularity_dirichlet`
applies. The bound also uses the a priori estimate `Elliptic.IsObstacleSolution.norm_le` and
$\|\psi^+\|_{H^1} \le \|\psi\|_{H^1} \le \|\psi\|_{H^2}$. -/
theorem theorem_11_3_12_two {R : ℝ} (hR : 0 ≤ R)
    (hΩb : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ψ : SobolevEuclidean (d + 1) 2 2 Ω)
        (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
        (∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, fn w
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            fun x ↦ max (fn (obstacleOfH2 Ω Ψ) x) 0) →
        ∀ u : SobolevEuclideanZero (d + 1) 1 2 Ω,
          (u ∈ obstacleSet Ω (obstacleOfH2 Ω Ψ) ∧ ∀ v ∈ obstacleSet Ω (obstacleOfH2 Ω Ψ),
            dirichletBilinForm Ω u (v - u) ≥ loadZero Ω f (v - u)) →
          MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
            (fn (u : SobolevEuclidean (d + 1) 1 2 Ω)) 2 2 Ω volume ∧
          ∀ U : SobolevEuclidean (d + 1) 2 2 Ω,
            fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              fn (u : SobolevEuclidean (d + 1) 1 2 Ω) →
            ‖U‖ ≤ C * (‖f‖ + ‖Ψ‖) := by
  obtain ⟨C, hC, h⟩ := Elliptic.regularity_obstacle_sobolev_two hR hΩb hΩ
  exact ⟨C, hC, fun Ψ f hψ u hu ↦
    h Ψ (obstacleOfH2 Ω Ψ) (Filter.EventuallyEq.refl _ _) hψ f u
      (isObstacleSolution_of_example_11_3_10 Ω hu)⟩

end Regularity

/-! ### Example 11.3.11: the simplified friction problem -/

section Friction

open MeasureTheory
open scoped ENNReal

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω) (𝒯 : B.TraceFamily)

/-- The Euclidean space $\mathbb{R}^N$, as local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Example 11.3.11** of [han2009theoretical] (the simplified friction problem as an inequality of
the second kind). Let $\Omega \subseteq \mathbb{R}^N$ be open, with boundary data $B$ (a surface
measure $ds$ on $\Gamma = \partial\Omega$) and a boundary trace $\gamma$ given by
`𝒯 : B.TraceFamily`, and let $g > 0$. Let
$$a(u, v) = \int_\Omega (\nabla u \cdot \nabla v + u v) \, dx, \qquad \ell_f(v) = \int_\Omega f
  v \, dx, \qquad j(v) = g \int_\Gamma |\gamma v| \, ds.$$
Then for every $f \in L^2(\Omega)$ the variational inequality (11.1.13),
$$u \in V = H^1(\Omega), \qquad a(u, v - u) + j(v) - j(u) \ge \ell_f(v - u) \quad \text{for all
  } v \in V,$$
has exactly one solution. If $u_1$ solves it with $f_1$ and $u_2$ with $f_2$, then
$$\|u_1 - u_2\|_{H^1(\Omega)} \le \|f_1 - f_2\|_{L^2(\Omega)}.$$

**Reading.** The source poses the problem on a Lipschitz domain. Here the domain is any open set
with a boundary trace in the sense of `BoundaryData.TraceFamily`, for example a bounded $C^1$
domain or a polygon without slits.

The existence clause writes the inequality out with integrals; the Lipschitz clause writes it
with `Elliptic.laplaceForm`, `Elliptic.load` and `AtkinsonHan.Chapter11.frictionFunctional`. The
proof applies Theorem 11.3.9 on $V$ with $K = V$. The form is
`AtkinsonHan.Chapter11.frictionBilinForm`, bounded and $V$-elliptic with constant $1$, and $j$
is convex and continuous by `AtkinsonHan.Chapter11.convexOn_frictionFunctional` and
`AtkinsonHan.Chapter11.continuous_frictionFunctional`. The bound $\|\ell_{f_1} - \ell_{f_2}\|
\le \|f_1 - f_2\|_{L^2}$ is `Elliptic.norm_load_le`. Example 11.2.4 reaches the existence and
uniqueness by the other route, through minimization. -/
theorem example_11_3_11 {g : ℝ} (hg : 0 < g) :
    (∀ f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)), ∃! u : SobolevEuclidean N 1 2 Ω,
      ∀ v : SobolevEuclidean N 1 2 Ω,
        ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
          ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
              * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
              + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
            + g * ∫ x, (|(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
              - |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|) ∂B.σ) ∧
    ∀ (f₁ f₂ : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u₁ u₂ : SobolevEuclidean N 1 2 Ω),
      (∀ v, Elliptic.load Ω f₁ (v - u₁) ≤ Elliptic.laplaceForm Ω u₁ (v - u₁)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u₁) →
      (∀ v, Elliptic.load Ω f₂ (v - u₂) ≤ Elliptic.laplaceForm Ω u₂ (v - u₂)
        + frictionFunctional B 𝒯 g v - frictionFunctional B 𝒯 g u₂) →
      ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ := by
  have key := theorem_11_3_9 frictionBilinForm_isBoundedWith one_pos
    frictionBilinForm_isEllipticWith univ_nonempty isClosed_univ convex_univ
    (j := frictionFunctional B 𝒯 g) (convexOn_frictionFunctional B 𝒯 hg.le)
    ((continuous_frictionFunctional B 𝒯 g).lowerSemicontinuous.lowerSemicontinuousOn univ)
  refine ⟨fun f ↦ ?_, fun f₁ f₂ u₁ u₂ h₁ h₂ ↦ ?_⟩
  · obtain ⟨u, ⟨-, hu⟩, huniq⟩ := key.1 (Elliptic.load Ω f)
    refine ⟨u, fun v ↦ (friction_ineq_iff B 𝒯 g f u v).2 (hu v (mem_univ _)), fun y hy ↦
      huniq y ⟨mem_univ _, fun v _ ↦ (friction_ineq_iff B 𝒯 g f y v).1 (hy v)⟩⟩
  · have h := key.2 (Elliptic.load Ω f₁) (Elliptic.load Ω f₂) u₁ u₂
      ⟨mem_univ _, fun v _ ↦ h₁ v⟩ ⟨mem_univ _, fun v _ ↦ h₂ v⟩
    have e : Elliptic.load Ω f₁ - Elliptic.load Ω f₂ = Elliptic.load Ω (f₁ - f₂) :=
      ContinuousLinearMap.ext fun v ↦ (Elliptic.load_sub Ω f₁ f₂ v).symm
    rw [one_div_one, one_mul, e] at h
    exact h.trans (Elliptic.norm_load_le Ω _)

end Friction

end AtkinsonHan.Chapter11
