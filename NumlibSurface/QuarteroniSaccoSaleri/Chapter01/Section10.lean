/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalities
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Module.NormEquivalence

/-!
# Quarteroni, Sacco and Saleri, Section 1.10: Scalar product and norms in vector spaces

This module formalizes §1.10 of [quarteroni2000numerical]. A scalar product $(\cdot, \cdot)$ on a
vector space is linear in its first argument, Hermitian and positive definite (Definition 1.16); on
$\mathbb{C}^n$ the Euclidean scalar product is $(x, y) = y^H x$, and it satisfies
$(Ax, y) = (x, A^H y)$ (1.12) and is preserved by unitary matrices (Property 1.8). A norm is a
nonnegative, definite, absolutely homogeneous and subadditive function (Definition 1.17). On
$\mathbb{R}^n$ the $p$-norms are $\|x\|_p = (\sum_i |x_i|^p)^{1/p}$ for $1 \le p < \infty$ and
$\|x\|_\infty = \max_i |x_i|$ (1.13), and $\|x\|_\infty$ is the limit of $\|x\|_p$ as
$p \to \infty$. The module proves the Cauchy–Schwarz inequality (Property 1.9) and Hölder's
inequality, the continuity of a norm (Property 1.10), the norm $x \mapsto \|Ax\|$ (Property 1.11),
the equivalence of all norms in finite dimension (Definition 1.18) with the constants of Table 1.1,
and the characterizations of the convergence of a sequence of vectors by its components (1.15) and
by a norm (Property 1.12).

Definition 1.16 is Mathlib's `InnerProductSpace 𝕜 V`, and Definition 1.17 is Mathlib's
`NormedAddCommGroup` and `NormedSpace` (norm and normed space), `Seminorm` (seminorm) and
$\|v\| = 1$ (unit vector); these two definitions carry statements that check the axioms. The proofs
use Mathlib and the backbone modules `Numlib.Analysis.Normed.Lp.PiLp` (the comparison of the
$p$-norms), `Numlib.Analysis.Normed.Module.NormEquivalence` (the equivalence of norms in finite
dimension) and `Numlib.Analysis.Matrix.ToEuclideanLin`.

## Main definitions

* Definition 1.16, `QuarteroniSaccoSaleri.Chapter01.definition_1_16`: the axioms of a scalar
  product, for Mathlib's inner product.
* Definition 1.17, `QuarteroniSaccoSaleri.Chapter01.definition_1_17`: the axioms of a norm and of a
  seminorm, for Mathlib's seminorms and norms.
* Definition 1.18, `QuarteroniSaccoSaleri.Chapter01.definition_1_18`: equivalent norms; all norms on
  a finite-dimensional space are equivalent.

## Main results

* §1.10, `QuarteroniSaccoSaleri.Chapter01.inner_eq_star_dotProduct`: the Euclidean scalar product is
  $(x, y) = y^H x = \sum_i x_i \bar y_i$.
* Equation (1.12), `QuarteroniSaccoSaleri.Chapter01.equation_1_12`: $(Ax, y) = (x, A^H y)$.
* Property 1.8, `QuarteroniSaccoSaleri.Chapter01.property_1_8`: unitary matrices preserve the
  Euclidean scalar product.
* Equation (1.13), `QuarteroniSaccoSaleri.Chapter01.equation_1_13`: the formulas for the $p$-norms,
  the maximum norm and the Euclidean norm.
* §1.10, `QuarteroniSaccoSaleri.Chapter01.tendsto_norm_lp_atTop`: $\|x\|_p \to \|x\|_\infty$ as
  $p \to \infty$.
* Property 1.9, `QuarteroniSaccoSaleri.Chapter01.property_1_9` (Cauchy–Schwarz inequality):
  $|(x, y)| \le \|x\|_2 \|y\|_2$, with equality if and only if $x$ and $y$ are linearly dependent.
* §1.10, `QuarteroniSaccoSaleri.Chapter01.holder_inequality` (Hölder's inequality):
  $|(x, y)| \le \|x\|_p \|y\|_q$ for conjugate exponents.
* Property 1.10, `QuarteroniSaccoSaleri.Chapter01.property_1_10`: every norm on a finite-dimensional
  space is Lipschitz with respect to a fixed norm, and continuous.
* Property 1.11, `QuarteroniSaccoSaleri.Chapter01.property_1_11`: $x \mapsto \|Ax\|$ is a norm when
  the columns of $A$ are linearly independent.
* Table 1.1, `QuarteroniSaccoSaleri.Chapter01.table_1_1`: the equivalence constants of the norms
  $\|\cdot\|_1$, $\|\cdot\|_2$ and $\|\cdot\|_\infty$ on $\mathbb{R}^n$.
* Equation (1.15), `QuarteroniSaccoSaleri.Chapter01.equation_1_15`: a sequence of vectors converges
  if and only if its components converge.
* Property 1.12, `QuarteroniSaccoSaleri.Chapter01.property_1_12`: convergence is convergence in any
  norm, and any two norms have the same null sequences.

## Conventions

* The book's scalar product $(x, y)$ is linear in its first argument (Definition 1.16). Mathlib's
  `inner 𝕜 x y` is conjugate-linear in its first argument, so the book's $(x, y)$ is `inner 𝕜 y x`
  in every statement. On $\mathbb{C}^n$ this is $(x, y) = y^H x = \sum_i x_i \bar y_i$.
* A vector norm on $V$ is a definite seminorm: `p : Seminorm 𝕜 V` with `∀ v, p v = 0 → v = 0`. All
  statements about "an arbitrary norm" in §1.10 and §1.11 use this form.
* The $p$-norm of $x \in \mathbb{R}^n$ is the norm of `WithLp.toLp p x` in `PiLp p (fun _ ↦ ℝ)`, for
  an exponent `p : ℝ≥0∞`.

## Deviations from the source

* **Property 1.9** (correction). The book states equality in the Cauchy–Schwarz inequality if and
  only if $y = \alpha x$ for some $\alpha$, which fails for $x = 0 \neq y$; the condition here is
  $x = 0$ or $y = \alpha x$. See `QuarteroniSaccoSaleri.Chapter01.property_1_9`.
* **Property 1.10** (reading). As printed, with the same norm on both sides, the statement is the
  reverse triangle inequality with $C = 1$; following the proof of Exercise 14, the bound is against
  a fixed reference norm. See `QuarteroniSaccoSaleri.Chapter01.property_1_10`.
* **Property 1.11** (generalization). The book states the square case $m = n$; the statement here
  allows $A \in \mathbb{R}^{m \times n}$, as in Exercise 15. See
  `QuarteroniSaccoSaleri.Chapter01.property_1_11`.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter01

/-! ### Definition 1.16: the scalar product -/

section Inner

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Definition 1.16** of [quarteroni2000numerical]. Let $V$ be a vector space over
$K = \mathbb{R}$ or $\mathbb{C}$. A **scalar product** on $V$ is a map
$(\cdot, \cdot) : V \times V \to K$ that is (1) linear in its first argument, $(\gamma x +
\delta z, y) = \gamma (x, y) + \delta (z, y)$; (2) Hermitian, $(y, x) = \overline{(x, y)}$; and
(3) positive definite, $(x, x) > 0$ for $x \neq 0$. The statement checks these axioms for the
inner product of an inner product space: for all $x, y, z \in V$ and $\gamma, \delta \in K$, (1)
and (2) hold; if $x \neq 0$, then $(x, x)$ is real and positive; and $(x, x) = 0$ if and only if
$x = 0$.

Mathlib's `inner 𝕜` is conjugate-linear in its first argument and linear in its second, so the
book's $(x, y)$ is `inner 𝕜 y x`. -/
theorem definition_1_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (x y z : V) (γ δ : 𝕜) :
    inner 𝕜 y (γ • x + δ • z) = γ * inner 𝕜 y x + δ * inner 𝕜 y z ∧
      inner 𝕜 x y = star (inner 𝕜 y x) ∧
      (x ≠ 0 → 0 < RCLike.re (inner 𝕜 x x) ∧ RCLike.im (inner 𝕜 x x) = 0) ∧
      (inner 𝕜 x x = 0 ↔ x = 0) := by
  refine ⟨by rw [inner_add_right, inner_smul_right, inner_smul_right], ?_,
    fun hx => ⟨re_inner_self_pos.2 hx, inner_self_im x⟩, inner_self_eq_zero⟩
  rw [← inner_conj_symm x y, starRingEnd_apply]

/-- **Section 1.10** of [quarteroni2000numerical], the Euclidean scalar product. For
$x, y \in \mathbb{K}^n$, with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
$$(x, y) = y^H x = \sum_{i=1}^n x_i \bar y_i.$$

The vectors live in `EuclideanSpace 𝕜 (Fin n)`, and $(x, y)$ is `inner 𝕜 y x`. This fixes the
order of the arguments in the whole library. The proof uses
`EuclideanSpace.inner_eq_star_dotProduct`. -/
theorem inner_eq_star_dotProduct {n : ℕ} (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 y x = ofLp x ⬝ᵥ star (ofLp y) ∧ inner 𝕜 y x = ∑ i, x i * star (y i) :=
  ⟨EuclideanSpace.inner_eq_star_dotProduct y x, rfl⟩

/-- **Equation (1.12)** of [quarteroni2000numerical]. Let $A, Q \in \mathbb{K}^{n \times n}$, with
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and $x, y \in \mathbb{K}^n$. For the Euclidean scalar
product,
$$(Ax, y) = (x, A^H y).$$
In particular $(Qx, Qy) = (x, Q^H Q y)$.

The proof uses Mathlib's `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`: $A^H$ acts as the
adjoint of $A$. -/
theorem equation_1_12 {n : ℕ} (A Q : Matrix (Fin n) (Fin n) 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 y (toEuclideanLin A x) = inner 𝕜 (toEuclideanLin Aᴴ y) x ∧
      inner 𝕜 (toEuclideanLin Q y) (toEuclideanLin Q x) =
        inner 𝕜 (toEuclideanLin (Qᴴ * Q) y) x := by
  refine ⟨(toEuclideanLin_conjTranspose_inner_left A x y).symm, ?_⟩
  rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]

/-- **Property 1.8** of [quarteroni2000numerical]. Unitary matrices preserve the Euclidean scalar
product: if $Q \in \mathbb{K}^{n \times n}$ is unitary, with $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, then $(Qx, Qy) = (x, y)$ for all $x, y \in \mathbb{K}^n$.

The proof uses the backbone theorem `Matrix.inner_toLp_mulVec_of_mem_unitaryGroup`. -/
theorem property_1_8 {n : ℕ} {Q : Matrix (Fin n) (Fin n) 𝕜} (hQ : Q ∈ unitaryGroup (Fin n) 𝕜)
    (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (toEuclideanLin Q y) (toEuclideanLin Q x) = inner 𝕜 y x :=
  inner_toLp_mulVec_of_mem_unitaryGroup hQ _ _

end Inner

/-! ### Definition 1.17: norms and the $p$-norms -/

section Norms

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Definition 1.17** of [quarteroni2000numerical]. Let $V$ be a vector space over
$K = \mathbb{R}$ or $\mathbb{C}$. A **norm** on $V$ is a map $\|\cdot\| : V \to \mathbb{R}$ such
that (1) $\|v\| \ge 0$, and $\|v\| = 0$ if and only if $v = 0$; (2)
$\|\alpha v\| = |\alpha| \|v\|$ for $\alpha \in K$; (3) $\|v + w\| \le \|v\| + \|w\|$. A map
that satisfies (1) without the condition $\|v\| = 0 \Rightarrow v = 0$, together with (2) and
(3), is a **seminorm**. The statement checks the axioms: a seminorm $p$ on $V$ with
$p(v) = 0 \Rightarrow v = 0$ satisfies (1), (2) and (3); and the norm of a normed space $E$ is a
seminorm with this property.

A seminorm is Mathlib's `Seminorm 𝕜 V`, and a norm is a seminorm `p` with
`∀ v, p v = 0 → v = 0`. The norm of $E$, as a seminorm, is `normSeminorm 𝕜 E`. -/
theorem definition_1_17 {V : Type*} [AddCommGroup V] [Module 𝕜 V] (p : Seminorm 𝕜 V)
    (hp : ∀ v, p v = 0 → v = 0) (α : 𝕜) (v w : V)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (e : E) :
    (0 ≤ p v ∧ (p v = 0 ↔ v = 0)) ∧ p (α • v) = ‖α‖ * p v ∧ p (v + w) ≤ p v + p w ∧
      normSeminorm 𝕜 E e = ‖e‖ ∧ (∀ e : E, normSeminorm 𝕜 E e = 0 → e = 0) :=
  ⟨⟨apply_nonneg p v, ⟨hp v, fun h => by rw [h, map_zero]⟩⟩, map_smul_eq_mul p α v,
    map_add_le_add p v w, rfl, fun e he => norm_eq_zero.1 he⟩

/-- **Equation (1.13)** of [quarteroni2000numerical], the $p$-norms on $\mathbb{R}^n$. Let
$x \in \mathbb{R}^n$. For $1 \le p < \infty$,
$$\|x\|_p = \Big(\sum_{i=1}^n |x_i|^p\Big)^{1/p}.$$
The **maximum norm** is $\|x\|_\infty = \max_i |x_i|$, and the Euclidean norm is $\|x\|_2 = (x,
x)^{1/2} = (\sum_i |x_i|^2)^{1/2}$.

The vector $x$ is read in `PiLp p (fun _ ↦ ℝ)` through `WithLp.toLp p`. The maximum is a
supremum, which is $0$ for $n = 0$. -/
theorem equation_1_13 {n : ℕ} (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp₂ : p ≠ ⊤) (x : Fin n → ℝ) :
    ‖toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) ∧
      ‖toLp ⊤ x‖ = ⨆ i, |x i| ∧
      ‖toLp 2 x‖ = √(inner ℝ (toLp 2 x) (toLp 2 x)) ∧ ‖toLp 2 x‖ = √(∑ i, |x i| ^ 2) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp₁).ne' hp₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [PiLp.norm_eq_sum hp]
    simp only [Real.norm_eq_abs]
  · rw [PiLp.norm_eq_ciSup]
    simp only [Real.norm_eq_abs]
  · rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  · rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs]

/-- **Section 1.10** of [quarteroni2000numerical], the limit of the $p$-norms. For
$x \in \mathbb{R}^n$, the limit of $\|x\|_p$ as $p \to \infty$ exists, is finite, and equals the
maximum modulus of the components of $x$:
$$\lim_{p \to \infty} \|x\|_p = \max_i |x_i| = \|x\|_\infty.$$

Here $p$ runs over the reals, and $\|x\|_p$ is the norm of `toLp (ENNReal.ofReal p) x`. The
proof uses the backbone theorem `PiLp.tendsto_norm_toLp_atTop`. -/
theorem tendsto_norm_lp_atTop {n : ℕ} (x : Fin n → ℝ) :
    Tendsto (fun p : ℝ => ‖toLp (ENNReal.ofReal p) x‖) atTop (𝓝 (⨆ i, |x i|)) := by
  have h := PiLp.tendsto_norm_toLp_atTop x
  rwa [PiLp.norm_eq_ciSup] at h

/-- **Property 1.9** of [quarteroni2000numerical] (Cauchy–Schwarz inequality), with (1.14). For
$x, y \in \mathbb{R}^n$, the Euclidean scalar product is $(x, y) = x^T y = \sum_i x_i y_i$, and
$$|(x, y)| \le \|x\|_2 \|y\|_2,$$
with equality if and only if $x = 0$ or $y = \alpha x$ for some $\alpha \in \mathbb{R}$, that
is, if and only if $x$ and $y$ are linearly dependent.

**Correction.** The book states that equality holds if and only if $y = \alpha x$ for some
$\alpha \in \mathbb{R}$. This fails for $x = 0$ and $y \neq 0$, where equality holds but $y$ is
not a multiple of $x$. The condition here adds the case $x = 0$. -/
theorem property_1_9 {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y x = ∑ i, x i * y i ∧ |inner ℝ y x| ≤ ‖x‖ * ‖y‖ ∧
      (|inner ℝ y x| = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ α : ℝ, y = α • x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct]
  · rw [real_inner_comm]
    exact abs_real_inner_le_norm x y
  · rw [real_inner_comm, ← Real.norm_eq_abs]
    exact (norm_inner_eq_norm_tfae ℝ x y).out 1 3

/-- **Section 1.10** of [quarteroni2000numerical] (Hölder's inequality). Let
$x, y \in \mathbb{R}^n$, and let $p, q > 0$ with $1/p + 1/q = 1$. Then
$$|(x, y)| \le \|x\|_p \|y\|_q.$$
Moreover, at the endpoint $p = 1$, $q = \infty$, $|(x, y)| \le \|x\|_1 \|y\|_\infty$.

The scalar product is written as the sum $\sum_i x_i y_i$. The proof uses Mathlib's
`Real.inner_le_Lp_mul_Lq`. -/
theorem holder_inequality {n : ℕ} (x y : Fin n → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    |∑ i, x i * y i| ≤ ‖toLp (ENNReal.ofReal p) x‖ * ‖toLp (ENNReal.ofReal q) y‖ ∧
      |∑ i, x i * y i| ≤ ‖toLp 1 x‖ * ‖toLp ⊤ y‖ := by
  have habs : |∑ i, x i * y i| ≤ ∑ i, |x i| * |y i| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => abs_mul _ _))
  constructor
  · have h := Real.inner_le_Lp_mul_Lq univ (fun i => |x i|) (fun i => |y i|) hpq
    simp only [abs_abs] at h
    rw [PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hpq.nonneg]; exact hpq.pos),
      PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hpq.symm.nonneg]; exact hpq.symm.pos),
      ENNReal.toReal_ofReal hpq.nonneg, ENNReal.toReal_ofReal hpq.symm.nonneg]
    simp only [Real.norm_eq_abs]
    exact habs.trans h
  · refine habs.trans ?_
    rw [PiLp.norm_eq_sum (by norm_num), ENNReal.toReal_one]
    simp only [div_one, Real.rpow_one, Real.norm_eq_abs]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (toLp ⊤ y) i

end Norms

/-! ### Properties 1.10 and 1.11 -/

section Continuity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Property 1.10** of [quarteroni2000numerical]. Let $V$ be a finite-dimensional real normed
space, and let $\|\cdot\|$ be a seminorm on $V$, in particular any vector norm. Then there is a
constant $C > 0$ such that
$$\big| \|x\| - \|\hat x\| \big| \le C \|x - \hat x\|_V \quad \text{for all } x, \hat x \in V,$$
where $\|\cdot\|_V$ is the norm of the normed space $V$. So $\|x - \hat x\|_V \le \varepsilon$
implies $|\|x\| - \|\hat x\|| \le C \varepsilon$, and $\|\cdot\|$ is a continuous function of
its argument.

**Reading.** As printed, with the same norm on both sides, the inequality is the reverse
triangle inequality with $C = 1$ (Mathlib's `abs_sub_map_le_sub`). The proof of Exercise 14
shows that the intended statement bounds $|\|x\| - \|\hat x\||$ by a multiple of a fixed
reference norm, and this is the statement here, with the continuity of the norm as a
consequence.

The reference norm is the given norm of $V$; on $V = \mathbb{R}^n$ with `Fin n → ℝ` it is the
maximum norm of the components. The proof uses the backbone theorems
`Seminorm.exists_le_mul_norm` and `Seminorm.continuous_of_finiteDimensional`. -/
theorem property_1_10 (p : Seminorm ℝ V) :
    (∃ C : ℝ, 0 < C ∧ ∀ x y : V, |p x - p y| ≤ C * ‖x - y‖) ∧ Continuous p := by
  obtain ⟨C, hC, h⟩ := p.exists_le_mul_norm
  exact ⟨⟨C, hC, fun x y => (abs_sub_map_le_sub p x y).trans (h (x - y))⟩,
    p.continuous_of_finiteDimensional⟩

/-- **Property 1.11** of [quarteroni2000numerical]. Let $\|\cdot\|$ be a norm on $\mathbb{R}^m$, and
let $A \in \mathbb{R}^{m \times n}$ have $n$ linearly independent columns. Then
$\|x\|_A = \|Ax\|$ is a norm on $\mathbb{R}^n$: it is a seminorm, and $\|x\|_A = 0$ implies
$x = 0$.

**Generalization.** The book states the property for a square matrix, $m = n$. The statement
here allows a rectangular $A$, as in Exercise 15.

The norm $\|\cdot\|_A$ is the seminorm `p.comp A.mulVecLin`. -/
theorem property_1_11 {m n : ℕ} (p : Seminorm ℝ (Fin m → ℝ)) (hp : ∀ v, p v = 0 → v = 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ A.col) :
    (∀ x, p.comp A.mulVecLin x = p (A *ᵥ x)) ∧
      ∀ x, p.comp A.mulVecLin x = 0 → x = 0 := by
  refine ⟨fun x => rfl, fun x hx => ?_⟩
  have h : A *ᵥ x = 0 := hp _ hx
  exact mulVec_injective_iff.2 hA (by rw [h, mulVec_zero])

/-! ### Definition 1.18 and Table 1.1 -/

/-- **Definition 1.18** of [quarteroni2000numerical], and the equivalence of all norms in finite
dimension. Two norms $\|\cdot\|_p$ and $\|\cdot\|_q$ on $V$ are **equivalent** if there are
constants $c_{pq}, C_{pq} > 0$ such that
$$c_{pq} \|x\|_q \le \|x\|_p \le C_{pq} \|x\|_q \quad \text{for all } x \in V.$$
Let $V$ be a finite-dimensional real normed space, and let $\|\cdot\|_p$ and $\|\cdot\|_q$ be
norms on $V$. Then $\|\cdot\|_p$ is equivalent to the norm of $V$, and $\|\cdot\|_p$ and
$\|\cdot\|_q$ are equivalent.

The two norms are definite seminorms. The proof uses the backbone theorem
`Seminorm.exists_bounds`. -/
theorem definition_1_18 (p q : Seminorm ℝ V) (hp : ∀ x, p x = 0 → x = 0)
    (hq : ∀ x, q x = 0 → x = 0) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ p x ∧ p x ≤ C * ‖x‖) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * q x ≤ p x ∧ p x ≤ C * q x := by
  refine ⟨p.exists_bounds hp, ?_⟩
  obtain ⟨c₁, C₁, hc₁, hC₁, h₁⟩ := p.exists_bounds hp
  obtain ⟨c₂, C₂, hc₂, hC₂, h₂⟩ := q.exists_bounds hq
  refine ⟨c₁ / C₂, C₁ / c₂, by positivity, by positivity, fun x => ⟨?_, ?_⟩⟩
  · calc c₁ / C₂ * q x ≤ c₁ / C₂ * (C₂ * ‖x‖) := by gcongr; exact (h₂ x).2
      _ = c₁ * ‖x‖ := by field_simp
      _ ≤ p x := (h₁ x).1
  · calc p x ≤ C₁ * ‖x‖ := (h₁ x).2
      _ = C₁ / c₂ * (c₂ * ‖x‖) := by field_simp
      _ ≤ C₁ / c₂ * q x := by gcongr; exact (h₂ x).1

/-- **Table 1.1** of [quarteroni2000numerical]. For $x \in \mathbb{R}^n$, the norms $\|\cdot\|_1$,
$\|\cdot\|_2$ and $\|\cdot\|_\infty$ satisfy
$$\|x\|_2 \le \|x\|_1 \le \sqrt n \|x\|_2, \qquad \|x\|_\infty \le \|x\|_2 \le \sqrt n
  \|x\|_\infty, \qquad \|x\|_\infty \le \|x\|_1 \le n \|x\|_\infty.$$
These are the constants $1$, $n^{1/2}$ and $n$ of the table. The entries $n^{-1/2}$ and $n^{-1}$
of the table are the same inequalities read in the other direction.

The proof uses the backbone theorems `PiLp.norm_le_norm_of_le` and
`PiLp.norm_le_card_rpow_mul_norm`. -/
theorem table_1_1 {n : ℕ} (x : Fin n → ℝ) :
    (‖toLp 2 x‖ ≤ ‖toLp 1 x‖ ∧ ‖toLp 1 x‖ ≤ √n * ‖toLp 2 x‖) ∧
      (‖toLp ⊤ x‖ ≤ ‖toLp 2 x‖ ∧ ‖toLp 2 x‖ ≤ √n * ‖toLp ⊤ x‖) ∧
      (‖toLp ⊤ x‖ ≤ ‖toLp 1 x‖ ∧ ‖toLp 1 x‖ ≤ n * ‖toLp ⊤ x‖) := by
  refine ⟨⟨PiLp.norm_toLp_two_le_norm_toLp_one x, ?_⟩,
    ⟨PiLp.norm_toLp_top_le_norm_toLp_two x, ?_⟩,
    ⟨PiLp.norm_toLp_top_le_norm_toLp_one x, ?_⟩⟩
  · simpa using PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two x
  · simpa using PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top x
  · simpa using PiLp.norm_toLp_one_le_card_mul_norm_toLp_top x

/-! ### Convergence of vectors: (1.15) and Property 1.12 -/

/-- **Equation (1.15)** of [quarteroni2000numerical]. Let $V$ be a real vector space of finite
dimension $n$ with a basis $b$. A sequence $x^{(k)}$ in $V$ converges to $x$ if and only if its
components with respect to $b$ converge,
$$\lim_{k \to \infty} x_i^{(k)} = x_i, \qquad i = 1, \dots, n.$$
For $V = \mathbb{R}^n$, the components are the entries, so a sequence $u^{(k)}$ in
$\mathbb{R}^n$ converges to $v$ if and only if $u_i^{(k)} \to v_i$ for every $i$. The limit is
unique.

Here $V$ is a finite-dimensional real normed space, and convergence is convergence in its
topology. The components are `b.repr (x k) i`. The coordinate map `b.repr` is a homeomorphism in
finite dimension. The case $V = \mathbb{R}^n$ uses `tendsto_pi_nhds`, and the uniqueness uses
`tendsto_nhds_unique`. -/
theorem equation_1_15 {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (x : ℕ → V) (y : V)
    (u : ℕ → (Fin n → ℝ)) (v w : Fin n → ℝ) :
    (Tendsto x atTop (𝓝 y) ↔
        ∀ i, Tendsto (fun k => b.repr (x k) i) atTop (𝓝 (b.repr y i))) ∧
      (Tendsto u atTop (𝓝 v) ↔ ∀ i, Tendsto (fun k => u k i) atTop (𝓝 (v i))) ∧
      (Tendsto u atTop (𝓝 v) → Tendsto u atTop (𝓝 w) → v = w) := by
  refine ⟨?_, tendsto_pi_nhds, fun hv hw => tendsto_nhds_unique hv hw⟩
  rw [b.equivFun.toContinuousLinearEquiv.toHomeomorph.isInducing.tendsto_nhds_iff,
    tendsto_pi_nhds]
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_apply]

/-- **Property 1.12** of [quarteroni2000numerical], and the topological equivalence of norms before
it. Let $V$ be a finite-dimensional real normed space, and let $\|\cdot\|$ and $|||\cdot|||$ be
norms on $V$. For a sequence $x^{(k)}$ in $V$ and $x \in V$,
$$\lim_{k \to \infty} x^{(k)} = x \iff \lim_{k \to \infty} \|x - x^{(k)}\| = 0.$$
Moreover, $|||x^{(k)}||| \to 0$ if and only if $\|x^{(k)}\| \to 0$.

The norms are definite seminorms. The topological equivalence of norms is the backbone theorem
`Seminorm.tendsto_apply_iff_tendsto_norm`: a sequence tends to $0$ in a norm if and only if it
tends to $0$ in the norm of $V$. -/
theorem property_1_12 (p q : Seminorm ℝ V) (hp : ∀ x, p x = 0 → x = 0)
    (hq : ∀ x, q x = 0 → x = 0) (x : ℕ → V) (y : V) :
    (Tendsto x atTop (𝓝 y) ↔ Tendsto (fun k => p (y - x k)) atTop (𝓝 0)) ∧
      (Tendsto (fun k => p (x k)) atTop (𝓝 0) ↔ Tendsto (fun k => q (x k)) atTop (𝓝 0)) := by
  refine ⟨?_, (Seminorm.tendsto_apply_iff_tendsto_norm p hp x).trans
    (Seminorm.tendsto_apply_iff_tendsto_norm q hq x).symm⟩
  rw [tendsto_iff_norm_sub_tendsto_zero, Seminorm.tendsto_apply_iff_tendsto_norm p hp]
  simp only [norm_sub_rev]

end Continuity

end QuarteroniSaccoSaleri.Chapter01
