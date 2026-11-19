/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Normed.Module.MilmanPettis
import NumlibSurface.Brezis.Chapter03.Section06

/-!
# Brezis, Section 3.7: Uniformly convex spaces

This module formalizes Section 3.7 of [brezis2011functional] for a real Banach space $E$. The space
$E$ is uniformly convex if for every $\varepsilon > 0$ there is $\delta > 0$ such that for
$x, y \in E$,
$$\|x\| \le 1,\ \|y\| \le 1,\ \|x - y\| > \varepsilon \implies \Bigl\|\frac{x + y}{2}\Bigr\| < 1 -
  \delta.$$
On $\mathbb{R}^2$ the Euclidean norm is uniformly convex, and the norms $\|\cdot\|_1$ and
$\|\cdot\|_\infty$ are not (Example 1). Hilbert spaces are uniformly convex (Example 2). Every
uniformly convex Banach space is reflexive (Theorem 3.31, Milman–Pettis). In a uniformly convex
space, weak convergence $x_n \rightharpoonup x$ with $\limsup \|x_n\| \le \|x\|$ implies strong
convergence (Proposition 3.32).

The proofs use Mathlib's `UniformConvexSpace` and `InnerProductSpace.toUniformConvexSpace`, and the
backbone modules `Numlib.Analysis.Normed.Module.MilmanPettis` (Theorem 3.31) and
`Numlib.Analysis.Convex.Uniform` (Proposition 3.32). The invariance clause of Remark 21 is the
backbone's `NormedSpace.isReflexive_congr`.

## Main definitions

* Section 3.7, definition of a uniformly convex space, `Brezis.Chapter03.IsUniformlyConvex`: the
  condition displayed above.

## Main results

* Section 3.7, `Brezis.Chapter03.uniformlyConvex_iff`: the definition agrees with Mathlib's
  `UniformConvexSpace E`.
* Example 1, `Brezis.Chapter03.example_3_7_1_euclidean`: the Euclidean norm on $\mathbb{R}^2$ is
  uniformly convex.
* Example 1, `Brezis.Chapter03.example_3_7_1_l1`: the norm $\|\cdot\|_1$ on $\mathbb{R}^2$ is not
  uniformly convex.
* Example 1, `Brezis.Chapter03.example_3_7_1_linf`: the norm $\|\cdot\|_\infty$ on $\mathbb{R}^2$ is
  not uniformly convex.
* Example 2, `Brezis.Chapter03.example_3_7_2`: Hilbert spaces are uniformly convex.
* Theorem 3.31 (Milman–Pettis), `Brezis.Chapter03.theorem_3_31`: every uniformly convex Banach space
  is reflexive.
* Remark 21, `Brezis.Chapter03.remark_3_21`: reflexivity is invariant under isomorphism, and uniform
  convexity is not.
* Proposition 3.32, `Brezis.Chapter03.proposition_3_32`: in a uniformly convex space,
  $x_n \rightharpoonup x$ and $\limsup \|x_n\| \le \|x\|$ imply $x_n \to x$ strongly.

## Conventions

* Theorem 3.31 and Proposition 3.32 assume `Brezis.Chapter03.IsUniformlyConvex E`. Examples 1 and 2
  and Remark 21 state Mathlib's class `UniformConvexSpace`. The two notions agree by
  `Brezis.Chapter03.uniformlyConvex_iff`.
* `EuclideanSpace ℝ (Fin 2)` is $\mathbb{R}^2$ with the Euclidean norm.
* `WithLp 1 (ℝ × ℝ)` is $\mathbb{R}^2$ with the norm $\|\cdot\|_1$.
* `ℝ × ℝ` is $\mathbb{R}^2$ with the norm $\|\cdot\|_\infty$, which is Mathlib's norm on a product.

## Deviations from the source

* **Definition of uniform convexity and Example 2** (generalization). The definition applies to
  incomplete normed spaces, and the Hilbert-space example applies to incomplete inner product
  spaces. See `Brezis.Chapter03.IsUniformlyConvex` and `Brezis.Chapter03.example_3_7_2`.

## Not formalized

* **Example 2, the spaces $L^p$ with $1 < p < \infty$.** This claim is Theorem 4.10 of Chapter 4.
-/

open Filter Metric Set Topology

namespace Brezis.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Section 3.7** of [brezis2011functional], definition of a uniformly convex space. A real normed
space $E$ is **uniformly convex** if for every $\varepsilon > 0$ there is $\delta > 0$ such that
for all $x, y \in E$,
$$\|x\| \le 1,\ \|y\| \le 1,\ \|x - y\| > \varepsilon \implies \Bigl\|\frac{x + y}{2}\Bigr\| <
  1 - \delta.$$

**Generalization.** The source makes the definition for a Banach space. The predicate applies to
real normed spaces. -/
def IsUniformlyConvex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ε < ‖x - y‖ →
    ‖(1 / 2 : ℝ) • (x + y)‖ < 1 - δ

/-- **Section 3.7** of [brezis2011functional]. A real normed space $E$ is uniformly convex in the
sense of `Brezis.Chapter03.IsUniformlyConvex` if and only if it is a `UniformConvexSpace`.
Mathlib's condition uses the unit sphere and non-strict inequalities: for every
$\varepsilon > 0$ there is $\delta > 0$ such that $\|x\| = \|y\| = 1$ and
$\|x - y\| \ge \varepsilon$ imply $\|x + y\| \le 2 - \delta$. -/
theorem uniformlyConvex_iff : IsUniformlyConvex E ↔ UniformConvexSpace E := by
  have hhalf : ∀ v : E, ‖(1 / 2 : ℝ) • v‖ = ‖v‖ / 2 := fun v => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  constructor
  · intro h
    refine ⟨fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := h (ε / 2) (by positivity)
    refine ⟨2 * δ, by positivity, fun x hx y hy hxy => ?_⟩
    have := hδ' x y hx.le hy.le (by linarith)
    rw [hhalf] at this
    linarith
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := exists_forall_closed_ball_dist_add_le_two_sub E hε
    refine ⟨δ / 4, by positivity, fun x y hx hy hxy => ?_⟩
    have := hδ' hx hy hxy.le
    rw [hhalf]
    linarith

/-- **Example 1** of [brezis2011functional], Section 3.7, the Euclidean norm. The Euclidean norm
$\|x\|_2 = (|x_1|^2 + |x_2|^2)^{1/2}$ on $\mathbb{R}^2$ is uniformly convex. -/
theorem example_3_7_1_euclidean : UniformConvexSpace (EuclideanSpace ℝ (Fin 2)) :=
  inferInstance

/-- **Example 1** of [brezis2011functional], Section 3.7, the norm $\|\cdot\|_1$. The norm
$\|x\|_1 = |x_1| + |x_2|$ on $\mathbb{R}^2$ is not uniformly convex.

The points $x = (1, 0)$ and $y = (0, 1)$ have $\|x\|_1 = \|y\|_1 = 1$ and
$\|x - y\|_1 = \|x + y\|_1 = 2$. The space is `WithLp 1 (ℝ × ℝ)`. -/
theorem example_3_7_1_l1 : ¬ UniformConvexSpace (WithLp 1 (ℝ × ℝ)) := by
  intro h
  obtain ⟨δ, hδ, hs⟩ :=
    exists_forall_sphere_dist_add_le_two_sub (WithLp 1 (ℝ × ℝ)) (ε := 2) two_pos
  have hx : ‖WithLp.toLp 1 ((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
  have hy : ‖WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))‖ = 1 := by simp
  have hsub : ‖WithLp.toLp 1 ((1 : ℝ), (0 : ℝ)) - WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))‖ = 2 := by
    rw [← WithLp.toLp_sub]
    simp [WithLp.prod_norm_eq_of_L1]
    norm_num
  have hadd : ‖WithLp.toLp 1 ((1 : ℝ), (0 : ℝ)) + WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))‖ = 2 := by
    rw [← WithLp.toLp_add]
    simp [WithLp.prod_norm_eq_of_L1]
    norm_num
  have := hs hx hy hsub.ge
  linarith

/-- **Example 1** of [brezis2011functional], Section 3.7, the norm $\|\cdot\|_\infty$. The norm
$\|x\|_\infty = \max(|x_1|, |x_2|)$ on $\mathbb{R}^2$ is not uniformly convex.

The points $x = (1, 1)$ and $y = (1, -1)$ have $\|x\|_\infty = \|y\|_\infty = 1$ and
$\|x - y\|_\infty = \|x + y\|_\infty = 2$. The space is `ℝ × ℝ`, whose Mathlib norm is the
maximum norm. -/
theorem example_3_7_1_linf : ¬ UniformConvexSpace (ℝ × ℝ) := by
  intro h
  obtain ⟨δ, hδ, hs⟩ := exists_forall_sphere_dist_add_le_two_sub (ℝ × ℝ) (ε := 2) two_pos
  have hx : ‖((1 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hy : ‖((1 : ℝ), (-1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hsub : ‖((1 : ℝ), (1 : ℝ)) - ((1 : ℝ), (-1 : ℝ))‖ = 2 := by
    simp [Prod.norm_def]
    norm_num
  have hadd : ‖((1 : ℝ), (1 : ℝ)) + ((1 : ℝ), (-1 : ℝ))‖ = 2 := by
    simp [Prod.norm_def]
    norm_num
  have := hs hx hy hsub.ge
  linarith

/-- **Example 2** of [brezis2011functional], Section 3.7, Hilbert spaces. Every real inner product
space $H$ is uniformly convex.

**Generalization.** The Hilbert-space clause applies to incomplete real inner product spaces.
The proof is Mathlib's `InnerProductSpace.toUniformConvexSpace`, which uses the parallelogram law.
The clause on $L^p$, $1 < p < \infty$, is Theorem 4.10. -/
theorem example_3_7_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    UniformConvexSpace H :=
  inferInstance

/-- **Theorem 3.31** of [brezis2011functional] (Milman–Pettis). Every uniformly convex real Banach
space is reflexive. -/
theorem theorem_3_31 [CompleteSpace E] (h : IsUniformlyConvex E) : IsReflexive E := by
  have := uniformlyConvex_iff.1 h
  exact isReflexive_iff.2 NormedSpace.isReflexive_of_uniformConvexSpace

/-- **Remark 21** in Chapter 3 of [brezis2011functional]. Reflexivity is a topological property, and
uniform convexity is a geometric property of the norm. Precisely:

1. if $E$ and $F$ are real Banach spaces and $E \cong F$ by a continuous linear isomorphism,
   then $E$ is reflexive if and only if $F$ is reflexive;
2. $\mathbb{R}^2$ with the Euclidean norm is uniformly convex, $\mathbb{R}^2$ with the norm
   $\|\cdot\|_1$ is not uniformly convex, and the two spaces are isomorphic.

In particular a reflexive space stays reflexive for an equivalent norm. The isomorphism in (1)
is `e : E ≃L[ℝ] F`. -/
theorem remark_3_21 [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (e : E ≃L[ℝ] F) :
    (IsReflexive E ↔ IsReflexive F) ∧
      (UniformConvexSpace (EuclideanSpace ℝ (Fin 2)) ∧ ¬ UniformConvexSpace (WithLp 1 (ℝ × ℝ)) ∧
        Nonempty (EuclideanSpace ℝ (Fin 2) ≃L[ℝ] WithLp 1 (ℝ × ℝ))) := by
  refine ⟨?_, example_3_7_1_euclidean, example_3_7_1_l1, ⟨?_⟩⟩
  · rw [isReflexive_iff, isReflexive_iff]
    exact NormedSpace.isReflexive_congr e
  · refine (ContinuousLinearEquiv.ofFinrankEq ?_).trans
      (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ ℝ).symm
    simp [Module.finrank_prod]

/-- **Proposition 3.32** of [brezis2011functional]. Let $E$ be a uniformly convex real Banach space,
and let $(x_n)$ be a sequence in $E$ with $x_n \rightharpoonup x$ weakly and
$$\limsup_{n \to \infty} \|x_n\| \le \|x\|.$$
Then $x_n \to x$ strongly. -/
theorem proposition_3_32 [CompleteSpace E] (h : IsUniformlyConvex E) {x : ℕ → E} {u : E}
    (hx : x ⇀ u) (hlim : limsup (fun n => ‖x n‖) atTop ≤ ‖u‖) : Tendsto x atTop (𝓝 u) := by
  have := uniformlyConvex_iff.1 h
  exact tendsto_of_forall_dual_tendsto_of_limsup_norm_le ((proposition_3_5 _ _).1 hx) hlim

end Brezis.Chapter03
