/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Numlib.Variational.WeakMinimization
import NumlibSurface.Brezis.Chapter03.Section07

/-!
# Brezis, Section 5.1: Definitions and elementary properties. Projection onto a closed convex set

This module formalizes Section 5.1 of [brezis2011functional] for a real Hilbert space $H$ with
scalar product $(u, v)$ and norm $|u| = (u, u)^{1/2}$. It recalls the definitions of a scalar
product and of a Hilbert space, the Cauchy–Schwarz inequality, the parallelogram law
$$\Bigl|\frac{a + b}{2}\Bigr|^2 + \Bigl|\frac{a - b}{2}\Bigr|^2 = \frac12 \bigl(|a|^2 + |b|^2\bigr),
  \qquad (1)$$
and the examples $L^2$ and $\ell^2$. A Hilbert space is uniformly convex, and so reflexive
(Proposition 5.1). For a nonempty closed convex set $K \subseteq H$ and $f \in H$ there is a unique
$u \in K$ with $|f - u| = \min_{v \in K} |f - v|$, characterized by
$$u \in K, \qquad (f - u, v - u) \le 0 \quad \text{for all } v \in K \qquad (3)$$
(Theorem 5.2). This $u$ is the projection $P_K f$. The map $P_K$ does not increase distances
(Proposition 5.3), and on a closed subspace it is the orthogonal projection (Corollary 5.4). The
module also contains Theorem 5.12 of the Comments on Chapter 5, the converse of the parallelogram
law.

The projection theorem is Mathlib's, written with the backbone's `IsBestApprox` from
`Numlib.Analysis.Normed.Module.BestApprox`, and $P_K$ is the backbone's `bestApprox K` from
`Numlib.Analysis.InnerProductSpace.ConvexProjection`. Uniform convexity and reflexivity are the
definitions of Chapter 3, `Brezis.Chapter03.IsUniformlyConvex` and `Brezis.Chapter03.IsReflexive`,
so that Proposition 5.1 and Remark 2 use Theorem 3.31 (Milman–Pettis), as the source does.

## Main definitions

* Section 5.1, definition of a scalar product, `Brezis.Chapter05.scalarProduct`: the scalar product
  of $H$ is bilinear, symmetric, positive and definite.
* Section 5.1, definition of a Hilbert space, `Brezis.Chapter05.hilbertSpace`: $|u| = (u, u)^{1/2}$
  is a norm, and completeness means that every Cauchy sequence converges.

## Main results

* Section 5.1, `Brezis.Chapter05.cauchySchwarz`: the Cauchy–Schwarz inequality
  $|(u, v)| \le |u| |v|$.
* Section 5.1, `Brezis.Chapter05.cauchySchwarz_of_nonneg`: the Cauchy–Schwarz inequality for a
  symmetric positive bilinear form that need not be definite.
* Section 5.1, `Brezis.Chapter05.parallelogram_law`: the parallelogram law (1).
* Section 5.1, `Brezis.Chapter05.basicExample_L2` and `Brezis.Chapter05.basicExample_l2`:
  $L^2(\Omega)$ and $\ell^2$ are Hilbert spaces.
* Proposition 5.1, `Brezis.Chapter05.proposition_5_1` and
  `Brezis.Chapter05.proposition_5_1_reflexive`: $H$ is uniformly convex, and so reflexive.
* Theorem 5.2, `Brezis.Chapter05.theorem_5_2`: for a nonempty closed convex $K$, every $f$ has a
  unique best approximation in $K$.
* Theorem 5.2, `Brezis.Chapter05.theorem_5_2_infDist`: the minimum $|f - u|$ is the distance from
  $f$ to $K$.
* Theorem 5.2, `Brezis.Chapter05.theorem_5_2_iff`: the characterization (3).
* Theorem 5.2, `Brezis.Chapter05.theorem_5_2_bestApprox`: the projection $P_K f$ is the element of
  Theorem 5.2.
* Remark 1, `Brezis.Chapter05.remark_5_1`: the first-order condition for a minimum of a
  differentiable function on $[0, 1]$.
* Remark 2, `Brezis.Chapter05.remark_5_2`: the projection theorem in a uniformly convex Banach
  space.
* Proposition 5.3, `Brezis.Chapter05.proposition_5_3`: $|P_K f_1 - P_K f_2| \le |f_1 - f_2|$.
* Corollary 5.4, `Brezis.Chapter05.corollary_5_4`: on a closed subspace $M$, $u = P_M f$ if and only
  if $u \in M$ and $(f - u, v) = 0$ for all $v \in M$.
* Corollary 5.4, `Brezis.Chapter05.corollary_5_4_linear`: $P_M$ is a linear operator, the orthogonal
  projection.
* Theorem 5.12 (Fréchet–von Neumann–Jordan), `Brezis.Chapter05.theorem_5_12`: a norm that satisfies
  the parallelogram law comes from a scalar product.

## Conventions

* A real Hilbert space $H$ is a type with `[NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]`. The results about definitions do not assume completeness.
* The scalar product $(u, v)$ is Mathlib's `⟪u, v⟫_ℝ`. It is symmetric over `ℝ`, so the order of the
  arguments does not matter.
* "$u$ is a best approximation of $f$ from $K$" is `IsBestApprox K f u`: $u \in K$ and
  $|f - u| \le |f - v|$ for all $v \in K$.

## Implementation notes

* The two definitions of the source, of a scalar product and of a Hilbert space, are stated as
  theorems about Mathlib's `InnerProductSpace ℝ H` and `CompleteSpace H`. Mathlib has no bundled
  class of Hilbert spaces.
* Theorem 5.12 belongs to the Comments on Chapter 5. It is in this module because it is the converse
  of the parallelogram law.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

open Brezis.Chapter03 (IsUniformlyConvex IsReflexive uniformlyConvex_iff isReflexive_iff
  theorem_3_31)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Definitions and elementary properties -/

/-- **Section 5.1** of [brezis2011functional], definition of a scalar product. The scalar product
$(u, v)$ of a real inner product space $H$ is a bilinear form on $H \times H$ (linear in each
variable), symmetric, $(u, v) = (v, u)$, positive, $(u, u) \ge 0$, and definite, $(u, u) \neq 0$
for $u \neq 0$.

The converse, that a real vector space with a scalar product is an inner product space with the
norm $|u| = (u, u)^{1/2}$, is Mathlib's `InnerProductSpace.ofCore`. -/
theorem scalarProduct :
    ((∀ u v w : H, ⟪u + v, w⟫_ℝ = ⟪u, w⟫_ℝ + ⟪v, w⟫_ℝ) ∧
        (∀ (a : ℝ) (u w : H), ⟪a • u, w⟫_ℝ = a * ⟪u, w⟫_ℝ) ∧
        (∀ u v w : H, ⟪u, v + w⟫_ℝ = ⟪u, v⟫_ℝ + ⟪u, w⟫_ℝ) ∧
        (∀ (a : ℝ) (u w : H), ⟪u, a • w⟫_ℝ = a * ⟪u, w⟫_ℝ)) ∧
      (∀ u v : H, ⟪u, v⟫_ℝ = ⟪v, u⟫_ℝ) ∧
      (∀ u : H, 0 ≤ ⟪u, u⟫_ℝ) ∧
      (∀ u : H, u ≠ 0 → ⟪u, u⟫_ℝ ≠ 0) :=
  ⟨⟨inner_add_left, fun a u w => real_inner_smul_left u w a, inner_add_right,
      fun a u w => real_inner_smul_right u w a⟩,
    fun u v => real_inner_comm v u, fun _ => real_inner_self_nonneg,
    fun _ hu => mt inner_self_eq_zero.1 hu⟩

/-- **Section 5.1** of [brezis2011functional], the Cauchy–Schwarz inequality. For all $u, v \in H$,
$$|(u, v)| \le (u, u)^{1/2} (v, v)^{1/2}.$$
-/
theorem cauchySchwarz (u v : H) : |⟪u, v⟫_ℝ| ≤ √⟪u, u⟫_ℝ * √⟪v, v⟫_ℝ := by
  rw [← norm_eq_sqrt_real_inner, ← norm_eq_sqrt_real_inner]
  exact abs_real_inner_le_norm u v

/-- **Section 5.1** of [brezis2011functional], the remark after the Cauchy–Schwarz inequality: the
proof does not use the definiteness of the scalar product. Let $V$ be a real vector space and
let $b$ be a bilinear form on $V$ that is symmetric and positive, $b(v, v) \ge 0$ for all $v$.
Then for all $u, v \in V$,
$$b(u, v)^2 \le b(u, u) \, b(v, v).$$

The proof is Mathlib's Cauchy–Schwarz inequality for a `PreInnerProductSpace.Core`, which is a
scalar product without the definiteness condition. -/
theorem cauchySchwarz_of_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ u v, b u v = b v u) (hpos : ∀ v, 0 ≤ b v v) (u v : V) :
    b u v ^ 2 ≤ b u u * b v v := by
  let _ : PreInnerProductSpace.Core ℝ V :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by simp [hsymm x y]
      re_inner_nonneg := fun x => by simpa using hpos x
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ) (F := V) u v
  simp only [RCLike.re_to_real, Real.norm_eq_abs] at h
  change |b u v| * |b v u| ≤ b u u * b v v at h
  rw [hsymm v u, ← sq, sq_abs] at h
  exact h

/-- **Section 5.1** of [brezis2011functional], definition of a Hilbert space. Let $H$ be a real
inner product space. Then:

1. the norm of $H$ is $|u| = (u, u)^{1/2}$;
2. it satisfies the triangle inequality $|u + v| \le |u| + |v|$, which the source derives from
   the Cauchy–Schwarz inequality;
3. $H$ is complete, that is, a Hilbert space, if and only if every Cauchy sequence in $H$
   converges.

Mathlib has no bundled class of Hilbert spaces; a Hilbert space is a type with
`[InnerProductSpace ℝ H] [CompleteSpace H]`. -/
theorem hilbertSpace :
    (∀ u : H, ‖u‖ = √⟪u, u⟫_ℝ) ∧ (∀ u v : H, ‖u + v‖ ≤ ‖u‖ + ‖v‖) ∧
      (CompleteSpace H ↔ ∀ u : ℕ → H, CauchySeq u → ∃ v, Tendsto u atTop (𝓝 v)) :=
  ⟨norm_eq_sqrt_real_inner, norm_add_le,
    ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu,
      fun h => Metric.complete_of_cauchySeq_tendsto h⟩⟩

/-- **Section 5.1** of [brezis2011functional], the parallelogram law (1). For all $a, b \in H$,
$$\Bigl|\frac{a + b}{2}\Bigr|^2 + \Bigl|\frac{a - b}{2}\Bigr|^2 = \frac12 \bigl(|a|^2 +
  |b|^2\bigr).$$
-/
theorem parallelogram_law (a b : H) :
    ‖(1 / 2 : ℝ) • (a + b)‖ ^ 2 + ‖(1 / 2 : ℝ) • (a - b)‖ ^ 2 = (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  have h := parallelogram_law_with_norm ℝ a b
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [h]

/-- **Section 5.1** of [brezis2011functional], the basic example $L^2$. Let $(\Omega, \mu)$ be a
measure space. The space $L^2(\Omega)$ with the scalar product
$$(u, v) = \int_\Omega u(x) v(x) \, d\mu$$
is a Hilbert space.

The space is Mathlib's `MeasureTheory.Lp ℝ 2 μ`. -/
theorem basicExample_L2 {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) :
    (∀ u v : MeasureTheory.Lp ℝ 2 μ, ⟪u, v⟫_ℝ = ∫ x, u x * v x ∂μ) ∧
      CompleteSpace (MeasureTheory.Lp ℝ 2 μ) :=
  ⟨fun u v => by
    rw [MeasureTheory.L2.inner_def]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by
      simp [RCLike.inner_apply, mul_comm]), inferInstance⟩

/-- **Section 5.1** of [brezis2011functional], the basic example $\ell^2$. The space $\ell^2$ with
the scalar product $(u, v) = \sum_n u_n v_n$ is a Hilbert space.

The space is `lp (fun _ : ℕ => ℝ) 2`, with coordinates indexed from $0$. -/
theorem basicExample_l2 :
    (∀ u v : lp (fun _ : ℕ => ℝ) 2, ⟪u, v⟫_ℝ = ∑' n, u n * v n) ∧
      CompleteSpace (lp (fun _ : ℕ => ℝ) 2) :=
  ⟨fun u v => by
    rw [lp.inner_eq_tsum]
    exact tsum_congr fun n => by simp [RCLike.inner_apply, mul_comm], inferInstance⟩

/-- **Proposition 5.1** of [brezis2011functional], first statement. Every real inner product space
$H$ is uniformly convex in the sense of Section 3.7.

Uniform convexity is `Brezis.Chapter03.IsUniformlyConvex`. Mathlib's instance
`InnerProductSpace.toUniformConvexSpace` follows the proof of the source, the parallelogram law
with $\delta = 1 - (1 - \varepsilon^2/4)^{1/2}$. Completeness is not needed. -/
theorem proposition_5_1 : IsUniformlyConvex H :=
  uniformlyConvex_iff.2 inferInstance

/-- **Proposition 5.1** of [brezis2011functional], second statement. Every real Hilbert space $H$ is
reflexive.

The proof applies the Milman–Pettis theorem (Theorem 3.31) to
`Brezis.Chapter05.proposition_5_1`. -/
theorem proposition_5_1_reflexive [CompleteSpace H] : IsReflexive H :=
  theorem_3_31 proposition_5_1

/-! ### Projection onto a closed convex set -/

section Projection

variable [CompleteSpace H]

/-- **Theorem 5.2** of [brezis2011functional] (projection onto a closed convex set), existence and
uniqueness. Let $K \subseteq H$ be a nonempty closed convex set. Then for every $f \in H$ there
is a unique $u \in K$ such that
$$|f - u| = \min_{v \in K} |f - v|.$$

The condition on $u$ is `IsBestApprox K f u`: $u \in K$ and $|f - u| \le |f - v|$ for all
$v \in K$. The proof is the backbone's `existsUnique_isBestApprox`, which is the second, direct
proof of the source: a minimizing sequence is a Cauchy sequence by the parallelogram law. -/
theorem theorem_5_2 {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K)
    (f : H) : ∃! u, IsBestApprox K f u :=
  existsUnique_isBestApprox hne hcl hK f

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- **Theorem 5.2** of [brezis2011functional], the identity (2). Let $K$ be a subset of a normed
space and let $u \in K$. Then $u$ is a best approximation of $f$ from $K$ if and only if
$$|f - u| = \operatorname{dist}(f, K) = \inf_{v \in K} |f - v|.$$

No scalar product and no completeness are needed. The distance is Mathlib's
`Metric.infDist f K`. -/
theorem theorem_5_2_infDist {K : Set H} {f u : H} (hu : u ∈ K) :
    IsBestApprox K f u ↔ ‖f - u‖ = Metric.infDist f K :=
  isBestApprox_iff_norm_sub_eq_infDist hu

omit [CompleteSpace H] in
/-- **Theorem 5.2** of [brezis2011functional], the characterization (3). Let $K \subseteq H$ be
convex, let $f \in H$ and let $u \in K$. Then $u$ is the best approximation of $f$ from $K$ if
and only if
$$(f - u, v - u) \le 0 \quad \text{for all } v \in K.$$

This part needs neither the closedness of $K$ nor the completeness of $H$. -/
theorem theorem_5_2_iff {K : Set H} (hK : Convex ℝ K) {f u : H} (hu : u ∈ K) :
    IsBestApprox K f u ↔ ∀ v ∈ K, ⟪f - u, v - u⟫_ℝ ≤ 0 :=
  isBestApprox_iff_inner_le_zero hK hu

/-- **Theorem 5.2** of [brezis2011functional], the notation $P_K$. Let $K \subseteq H$ be a nonempty
closed convex set and $f \in H$. The element $u$ of Theorem 5.2 is called the **projection** of
$f$ onto $K$ and is written $u = P_K f$. Here $P_K f$ is the best approximation of $f$ from $K$,
and for every $w \in H$,
$$P_K f = w \iff w \in K \text{ and } (f - w, v - w) \le 0 \text{ for all } v \in K.$$

The projection $P_K f$ is the backbone's `bestApprox K f`. -/
theorem theorem_5_2_bestApprox {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (f : H) :
    IsBestApprox K f (bestApprox K f) ∧
      ∀ w, bestApprox K f = w ↔ w ∈ K ∧ ∀ v ∈ K, ⟪f - w, v - w⟫_ℝ ≤ 0 :=
  ⟨isBestApprox_bestApprox_of_isClosed hne hcl hK f, fun _ => bestApprox_eq_iff hne hcl hK⟩

omit [CompleteSpace H] in
/-- **Remark 1** in Chapter 5 of [brezis2011functional]. A minimization problem is connected with a
system of inequalities. Let $F : \mathbb{R} \to \mathbb{R}$ be differentiable, and let
$u \in [0, 1]$ be a point where $F$ attains its minimum on $[0, 1]$. Then one of the following
holds:

1. $u \in (0, 1)$ and $F'(u) = 0$;
2. $u = 0$ and $F'(u) \ge 0$;
3. $u = 1$ and $F'(u) \le 0$.

The three cases are summarized by $F'(u)(v - u) \ge 0$ for all $v \in [0, 1]$, which is also
stated. -/
theorem remark_5_1 {F : ℝ → ℝ} (hF : Differentiable ℝ F) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hmin : IsMinOn F (Set.Icc 0 1) u) :
    ((u ∈ Set.Ioo 0 1 ∧ deriv F u = 0) ∨ (u = 0 ∧ 0 ≤ deriv F u) ∨ (u = 1 ∧ deriv F u ≤ 0)) ∧
      ∀ v ∈ Set.Icc 0 1, 0 ≤ deriv F u * (v - u) := by
  have key : ∀ v ∈ Set.Icc (0 : ℝ) 1, 0 ≤ deriv F u * (v - u) := fun v hv => by
    have hseg : segment ℝ u (u + (v - u)) ⊆ Set.Icc 0 1 := by
      rw [add_sub_cancel]
      exact (convex_Icc 0 1).segment_subset hu hv
    have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
      (hF u).hasDerivAt.hasFDerivAt.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using h
  refine ⟨?_, key⟩
  obtain ⟨hu0, hu1⟩ := hu
  have ha := key 0 ⟨le_rfl, zero_le_one⟩
  have hb := key 1 ⟨zero_le_one, le_rfl⟩
  rcases hu0.lt_or_eq with h0 | h0
  · rcases hu1.lt_or_eq with h1 | h1
    · exact Or.inl ⟨⟨h0, h1⟩, by nlinarith⟩
    · subst h1
      exact Or.inr (Or.inr ⟨rfl, by linarith⟩)
  · subst h0
    exact Or.inr (Or.inl ⟨rfl, by linarith⟩)

/-- **Remark 2** in Chapter 5 of [brezis2011functional]. Let $E$ be a uniformly convex real Banach
space and let $K \subseteq E$ be a nonempty closed convex set. Then for every $f \in E$ there is
a unique $u \in K$ with
$$\|f - u\| = \min_{v \in K} \|f - v\|.$$

The source refers to Exercise 3.32, a direct argument with a minimizing sequence. Here existence
follows from reflexivity (Theorem 3.31, Milman–Pettis) and the direct method of the calculus of
variations (`exists_isBestApprox_of_convex`), and uniqueness follows from strict convexity. -/
theorem remark_5_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hE : IsUniformlyConvex E) {K : Set E} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (f : E) : ∃! u, IsBestApprox K f u := by
  have := uniformlyConvex_iff.1 hE
  have := isReflexive_iff.1 (theorem_3_31 hE)
  obtain ⟨u, hu⟩ := exists_isBestApprox_of_convex hne hcl hK f
  exact ⟨u, hu, fun w hw => hw.unique hK hu⟩

/-- **Proposition 5.3** of [brezis2011functional]. Let $K \subseteq H$ be a nonempty closed convex
set. Then $P_K$ does not increase distances:
$$|P_K f_1 - P_K f_2| \le |f_1 - f_2| \quad \text{for all } f_1, f_2 \in H.$$
-/
theorem proposition_5_3 {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K)
    (f₁ f₂ : H) : ‖bestApprox K f₁ - bestApprox K f₂‖ ≤ ‖f₁ - f₂‖ :=
  norm_bestApprox_sub_bestApprox_le hne hcl hK f₁ f₂

/-- **Corollary 5.4** of [brezis2011functional], the characterization (8). Let $M \subseteq H$ be a
closed linear subspace and let $f, u \in H$. Then $u = P_M f$ if and only if
$$u \in M \quad \text{and} \quad (f - u, v) = 0 \text{ for all } v \in M.$$
-/
theorem corollary_5_4 {M : Submodule ℝ H} (hM : IsClosed (M : Set H)) (f u : H) :
    bestApprox (M : Set H) f = u ↔ u ∈ M ∧ ∀ v ∈ M, ⟪f - u, v⟫_ℝ = 0 := by
  have := hM.completeSpace_coe
  rw [bestApprox_eq_starProjection]
  constructor
  · rintro rfl
    exact ⟨M.starProjection_apply_mem f, fun v hv => M.starProjection_inner_eq_zero f v hv⟩
  · rintro ⟨hu, h⟩
    exact M.eq_starProjection_of_mem_of_inner_eq_zero hu h

/-- **Corollary 5.4** of [brezis2011functional], linearity. Let $M \subseteq H$ be a closed linear
subspace. Then $P_M$ is a linear operator, called the **orthogonal projection** onto $M$.
Precisely, $P_M$ is the bounded linear operator `Submodule.starProjection M`, and its norm is at
most $1$. -/
theorem corollary_5_4_linear {M : Submodule ℝ H} (hM : IsClosed (M : Set H)) :
    haveI := hM.completeSpace_coe
    bestApprox (M : Set H) = ⇑M.starProjection ∧ ‖M.starProjection‖ ≤ 1 := by
  have := hM.completeSpace_coe
  exact ⟨funext (bestApprox_eq_starProjection M), M.starProjection_norm_le⟩

end Projection

/-- **Theorem 5.12** of [brezis2011functional] (Fréchet–von Neumann–Jordan). Let $E$ be a real
normed space whose norm satisfies the parallelogram law
$$\|x + y\|^2 + \|x - y\|^2 = 2 \bigl(\|x\|^2 + \|y\|^2\bigr) \quad \text{for all } x, y \in
  E.$$
Then the norm is a Hilbert norm: there is a scalar product on $E$ with $\|u\| = (u, u)^{1/2}$
for all $u \in E$.

The source states this theorem in the Comments on Chapter 5. The scalar product is an instance
of `InnerProductSpace ℝ E`, whose definition includes the identity $\|u\|^2 = (u, u)$. Mathlib's
`InnerProductSpace.ofNorm` is the polarization construction of Exercise 5.1 of the source. -/
theorem theorem_5_12 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ∀ x y : E, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    Nonempty (InnerProductSpace ℝ E) :=
  ⟨InnerProductSpace.ofNorm ℝ fun x y => by simpa only [← pow_two] using h x y⟩

end Brezis.Chapter05

end
