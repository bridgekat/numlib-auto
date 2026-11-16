/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Numlib.IntegralEquations.Basic
import NumlibSurface.AtkinsonHan.Chapter01.Section01
import NumlibSurface.AtkinsonHan.Chapter02.Section01

/-!
# Atkinson and Han, Section 2.2: Continuous linear operators

This module formalizes Section 2.2 of [han2009theoretical]. A linear operator $L$ between normed
spaces $V$ and $W$ is continuous if and only if it is bounded, that is, if and only if
$\|Lv\| \le \gamma \|v\|$ for a constant $\gamma$ and all $v \in V$. The smallest such $\gamma$ is
the operator norm
$$\|L\| = \sup_{v \neq 0} \frac{\|Lv\|}{\|v\|},$$
which is submultiplicative, $\|L_2 L_1\| \le \|L_2\| \|L_1\|$. The space $\mathcal{L}(V, W)$ of
bounded linear operators is a normed space, and it is a Banach space when $W$ is one. The section
also computes the operator norms of a matrix for the vector norms $\|\cdot\|_\infty$, $\|\cdot\|_1$
and $\|\cdot\|_2$, and the norm of an integral operator with continuous kernel on $C[a, b]$.

The book's $\mathcal{L}(V, W)$ is Mathlib's `V →L[𝕜] W`, so Theorems 2.2.5 and 2.2.10 restate facts
that Mathlib already has. The norm of an integral operator is the backbone result
`IntegralOperator.norm_fredholm` of `Numlib.IntegralEquations.Basic`.

## Main definitions

* Definition 2.2.1, `AtkinsonHan.Chapter02.definition_2_2_1`: a linear operator, in the form
  $L(\alpha_1 v_1 + \alpha_2 v_2) = \alpha_1 L v_1 + \alpha_2 L v_2$.

## Main results

* Definition 2.2.1, `AtkinsonHan.Chapter02.definition_2_2_1_iff` and
  `AtkinsonHan.Chapter02.definition_2_2_1_iff_linearMap`: the definition is equivalent to additivity
  and homogeneity (Definition 1.1.13), and to being a Mathlib `LinearMap`.
* Proposition 2.2.2, `AtkinsonHan.Chapter02.proposition_2_2_2`: a linear operator is continuous if
  and only if it maps null sequences to null sequences.
* Proposition 2.2.3, `AtkinsonHan.Chapter02.proposition_2_2_3`: a linear operator is bounded in the
  sense of Definition 2.1.6 if and only if it satisfies (2.2.2), $\|Lv\| \le \gamma \|v\|$.
* Theorem 2.2.4, `AtkinsonHan.Chapter02.theorem_2_2_4`: a linear operator is continuous if and only
  if it is bounded.
* Equation (2.2.3), `AtkinsonHan.Chapter02.equation_2_2_3`:
  $\|L v_1 - L v_2\| \le \|L\| \|v_1 - v_2\|$.
* Theorem 2.2.5, `AtkinsonHan.Chapter02.theorem_2_2_5`: four descriptions of the operator norm,
  among them (2.2.4) and the description of Exercise 2.2.4 as the least admissible $\gamma$.
* Theorem 2.2.6, `AtkinsonHan.Chapter02.theorem_2_2_6`: (2.2.5) $\|Lv\| \le \|L\| \|v\|$, (2.2.6)
  $\|L_2 L_1\| \le \|L_2\| \|L_1\|$, and $\|L^n\| \le \|L\|^n$.
* Example 2.2.7, `AtkinsonHan.Chapter02.example_2_2_7`: the identity operator is bounded and has
  norm $1$.
* Example 2.2.8, `AtkinsonHan.Chapter02.example_2_2_8_linfty`,
  `AtkinsonHan.Chapter02.example_2_2_8_l1` and `AtkinsonHan.Chapter02.example_2_2_8_l2`: the matrix
  norm induced by $\|\cdot\|_\infty$ is the maximum absolute row sum, the one induced by
  $\|\cdot\|_1$ is the maximum absolute column sum, and the one induced by $\|\cdot\|_2$ is
  $\sqrt{\rho(A^* A)}$.
* Example 2.2.9, `AtkinsonHan.Chapter02.equation_2_2_8`: the integral operator with continuous
  kernel $k$ on $C[a, b]$ has norm (2.2.8), $\max_x \int_a^b |k(x, y)| \, dy$.
* Theorem 2.2.10, `AtkinsonHan.Chapter02.theorem_2_2_10`: $\mathcal{L}(V, W)$ is a Banach space when
  $W$ is one.

## Conventions

* Definition 2.2.1 is a `def … : Prop` in the words of the book, with companion theorems `…_iff`, as
  in Chapter 1. The definition asks only that $V$ and $W$ be linear spaces. It is therefore stated
  over a `DivisionRing` of scalars, as Definition 1.1.13 is, and not over the normed spaces of the
  rest of the section.

## Implementation notes

* The formula (2.2.4) is also stated on its own as `AtkinsonHan.Chapter02.opNorm_eq_sSup_ratio`,
  because later sections use it directly.
* Example 2.2.8 has three declarations, because Mathlib keeps the three matrix norms apart with
  scoped instances. Mathlib has no operator norm on matrices for $\|\cdot\|_1$. Therefore
  `AtkinsonHan.Chapter02.example_2_2_8_l1` states that the maximum absolute column sum is the least
  $\gamma \ge 0$ with $\|Ax\|_1 \le \gamma \|x\|_1$ for all $x$. By Exercise 2.2.4 this is what the
  equation $\|A\|_1 = \max_j \sum_i |a_{ij}|$ says.
* Exercises 2.2.3, 2.2.4 and 2.2.5 are not separate declarations. Exercise 2.2.3 is Theorem 2.2.5,
  Exercise 2.2.4 is the fourth clause of `AtkinsonHan.Chapter02.theorem_2_2_5`, and Exercise 2.2.5
  is `AtkinsonHan.Chapter02.equation_2_2_8`.

## Deviations from the source

* **Example 2.2.7** (reading). The book does not exclude the zero space, on which every operator
  norm is $0$. The statement assumes $V \neq \{0\}$. See `AtkinsonHan.Chapter02.example_2_2_7`.

## Not formalized

* **Exercises 2.2.1, 2.2.2, 2.2.7 and 2.2.8.** They are one-line consequences of linearity and of
  `LinearMap.ker_eq_bot`.
* **Exercise 2.2.6** (multiplication by $m \in C(\bar\Omega)$ has norm $\|m\|_\infty$ on
  $L^p(\Omega)$). It is not used later.
-/

open Bornology Filter Metric Topology

namespace AtkinsonHan.Chapter02

/-! ### Definition 2.2.1: linear operators -/

section Linear

variable {𝕜 V W : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W]
  [Module 𝕜 W]

/-- **Definition 2.2.1** of [han2009theoretical]. Let $V$ and $W$ be linear spaces over a division
ring of scalars $\mathbb{K}$. An operator $L : V \to W$ is **linear** if
$$L(\alpha_1 v_1 + \alpha_2 v_2) = \alpha_1 L v_1 + \alpha_2 L v_2$$
for all $v_1, v_2 \in V$ and all $\alpha_1, \alpha_2 \in \mathbb{K}$.

The book adds that, equivalently, $L$ is additive and homogeneous as in Definition 1.1.13. This
equivalence is `AtkinsonHan.Chapter02.definition_2_2_1_iff`, and
`AtkinsonHan.Chapter02.definition_2_2_1_iff_linearMap` identifies the definition with Mathlib's
`LinearMap`. The book's space $\mathcal{L}(V, W)$ of bounded linear operators is Mathlib's
`V →L[𝕜] W`, which the rest of the section uses. -/
def definition_2_2_1 (𝕜 : Type*) {V W : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (L : V → W) : Prop :=
  ∀ (v₁ v₂ : V) (α₁ α₂ : 𝕜), L (α₁ • v₁ + α₂ • v₂) = α₁ • L v₁ + α₂ • L v₂

/-- **Definition 2.2.1** of [han2009theoretical], the equivalent form. Let $V$ and $W$ be linear
spaces over a division ring $\mathbb{K}$. A map $L : V \to W$ is linear in the sense of
Definition 2.2.1 if and only if it is additive and homogeneous in the sense of Definition
1.1.13: $L(u + v) = Lu + Lv$ and $L(\alpha v) = \alpha L v$ for all $u, v \in V$ and
$\alpha \in \mathbb{K}$. -/
theorem definition_2_2_1_iff (L : V → W) :
    definition_2_2_1 𝕜 L ↔ Chapter01.definition_1_1_13 𝕜 L := by
  constructor
  · intro h
    refine ⟨fun u v => ?_, fun α v => ?_⟩
    · simpa using h u v 1 1
    · simpa using h v v α 0
  · rintro ⟨hadd, hsmul⟩ v₁ v₂ α₁ α₂
    rw [hadd, hsmul, hsmul]

/-- **Definition 2.2.1** of [han2009theoretical], the identification with Mathlib. A map
$L : V \to W$ between linear spaces over a division ring is linear in the sense of Definition
2.2.1 if and only if it is the underlying function of a Mathlib `LinearMap`.

The proof goes through Definition 1.1.13 and `AtkinsonHan.Chapter01.definition_1_1_13_iff`. -/
theorem definition_2_2_1_iff_linearMap (L : V → W) :
    definition_2_2_1 𝕜 L ↔ ∃ T : V →ₗ[𝕜] W, ⇑T = L :=
  (definition_2_2_1_iff L).trans (Chapter01.definition_1_1_13_iff L)

end Linear

section Continuity

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Proposition 2.2.2** of [han2009theoretical]. Let $V$ and $W$ be normed spaces over
$\mathbb{K}$ and let $L : V \to W$ be linear. Then $L$ is continuous if and only if
$L u_n \to 0$ for every sequence $u_n \to 0$ in $V$.

The book states that continuity at the origin gives continuity everywhere, and argues with
sequences: if $u_n \to u$, then $u_n - u \to 0$. The converse is immediate, so the statement is
an equivalence. -/
theorem proposition_2_2_2 (L : V →ₗ[𝕜] W) :
    (∀ u : ℕ → V, Tendsto u atTop (𝓝 0) → Tendsto (fun n => L (u n)) atTop (𝓝 0)) ↔
      Continuous L := by
  constructor
  · intro h
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero]
    exact Filter.tendsto_iff_seq_tendsto.2 h
  · intro h u hu
    have := (h.tendsto (0 : V)).comp hu
    rwa [map_zero] at this

/-- **Proposition 2.2.3** of [han2009theoretical]. Let $V$ and $W$ be normed spaces over
$\mathbb{K}$ and let $L : V \to W$ be linear. Then $L$ is bounded in the sense of Definition
2.1.6, that is, it maps bounded sets to bounded sets, if and only if there is a constant
$\gamma \ge 0$ with
$$\|Lv\| \le \gamma \|v\| \quad \text{for all } v \in V. \qquad (2.2.2)$$

With this result the rest of the book works with the constant $\gamma$ instead of with images of
bounded sets. Boundedness is `AtkinsonHan.Chapter02.IsBoundedOperator`. -/
theorem proposition_2_2_3 (L : V →ₗ[𝕜] W) :
    IsBoundedOperator L ↔ ∃ γ : ℝ, 0 ≤ γ ∧ ∀ v, ‖L v‖ ≤ γ * ‖v‖ := by
  constructor
  · intro hL
    obtain ⟨R, hR⟩ := hL 1 one_pos
    obtain ⟨C, hC⟩ := L.bound_of_ball_bound one_pos R fun z hz =>
      hR z (mem_ball_zero_iff.mp hz).le
    refine ⟨max C 0, le_max_right _ _, fun v => (hC v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)
  · rintro ⟨γ, hγ, h⟩ r _
    exact ⟨γ * r, fun v hv => (h v).trans (mul_le_mul_of_nonneg_left hv hγ)⟩

/-- **Theorem 2.2.4** of [han2009theoretical]. Let $V$ and $W$ be normed spaces over $\mathbb{K}$
and let $L : V \to W$ be linear. Then $L$ is continuous if and only if $L$ is bounded in the
sense of Definition 2.1.6.

Together with Proposition 2.2.3, the theorem lets the book replace continuity of a linear
operator by an estimate $\|Lv\| \le \gamma \|v\|$. Boundedness is
`AtkinsonHan.Chapter02.IsBoundedOperator`. -/
theorem theorem_2_2_4 (L : V →ₗ[𝕜] W) : Continuous L ↔ IsBoundedOperator L := by
  rw [proposition_2_2_3]
  constructor
  · intro h
    obtain ⟨C, hC0, hC⟩ := ContinuousLinearMap.bound (⟨L, h⟩ : V →L[𝕜] W)
    exact ⟨C, hC0.le, hC⟩
  · rintro ⟨γ, _, h⟩
    exact AddMonoidHomClass.continuous_of_bound L γ h

/-- **Equation (2.2.3)** of [han2009theoretical]. Let $V$ and $W$ be normed spaces over $\mathbb{K}$
and let $L \in \mathcal{L}(V, W)$. Then for all $v_1, v_2 \in V$,
$$\|L v_1 - L v_2\| \le \|L\| \, \|v_1 - v_2\|.$$

Thus a continuous linear operator is Lipschitz continuous with the constant $\|L\|$, which is
what the book means when it says that continuity of a linear operator is uniform. -/
theorem equation_2_2_3 (L : V →L[𝕜] W) (v₁ v₂ : V) : ‖L v₁ - L v₂‖ ≤ ‖L‖ * ‖v₁ - v₂‖ := by
  rw [← map_sub]
  exact L.le_opNorm _

end Continuity

section OperatorNorm

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Equation (2.2.4)** of [han2009theoretical]. Let $V$ and $W$ be normed spaces over $\mathbb{K}$
and let $L \in \mathcal{L}(V, W)$. Then
$$\|L\| = \sup \Big\{ \frac{\|Lv\|}{\|v\|} : v \in V, \ v \neq 0 \Big\}.$$
If $V = \{0\}$, the set is empty and both sides are $0$, because `sSup ∅ = 0`. Otherwise the set
is bounded above by $\|L\|$, so the supremum is a real supremum. -/
theorem opNorm_eq_sSup_ratio (L : V →L[𝕜] W) :
    ‖L‖ = sSup ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hL : L = 0 := by
      ext v
      rw [Subsingleton.elim v 0, map_zero]
      simp
    have hempty : {v : V | v ≠ 0} = ∅ := by
      ext v
      simp [Subsingleton.elim v 0]
    rw [hL, hempty, Set.image_empty, Real.sSup_empty, norm_zero]
  · obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have hbdd : BddAbove ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) :=
      ⟨‖L‖, by rintro _ ⟨v, -, rfl⟩; exact L.ratio_le_opNorm v⟩
    have hne : ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}).Nonempty := ⟨_, ⟨w, hw, rfl⟩⟩
    refine le_antisymm ?_ (csSup_le hne (by rintro _ ⟨v, -, rfl⟩; exact L.ratio_le_opNorm v))
    have hS0 : 0 ≤ sSup ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) :=
      le_trans (by positivity) (le_csSup hbdd ⟨w, hw, rfl⟩)
    refine L.opNorm_le_bound hS0 ?_
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [← div_le_iff₀ (norm_pos_iff.mpr hv)]
      exact le_csSup hbdd ⟨v, hv, rfl⟩

/-- **Theorem 2.2.5** of [han2009theoretical], with (2.2.4) and Exercise 2.2.4. Let $V$ and $W$ be
normed spaces over $\mathbb{K}$ and let $L \in \mathcal{L}(V, W)$. Then
$$\|L\| = \sup_{v \neq 0} \frac{\|Lv\|}{\|v\|} = \sup_{\|v\| \le 1} \|Lv\| = \sup_{\|v\| = 1}
  \|Lv\|,$$
and $\|L\|$ is the least $\gamma \ge 0$ such that $\|Lv\| \le \gamma \|v\|$ for all $v \in V$.

The book also states that $\mathcal{L}(V, W)$ with this norm is a normed linear space. In Lean
this is the normed space `V →L[𝕜] W` of Mathlib, so the theorem states only the four
descriptions of the norm. The suprema are `sSup` of the images; on the zero space every supremum
here is $0$, the value of `sSup` at the empty set and at $\{0\}$. -/
theorem theorem_2_2_5 (L : V →L[𝕜] W) :
    ‖L‖ = sSup ((fun v => ‖L v‖ / ‖v‖) '' {v : V | v ≠ 0}) ∧
      ‖L‖ = sSup ((fun v => ‖L v‖) '' closedBall 0 1) ∧
        ‖L‖ = sSup ((fun v => ‖L v‖) '' sphere 0 1) ∧
          IsLeast {γ : ℝ | 0 ≤ γ ∧ ∀ v, ‖L v‖ ≤ γ * ‖v‖} ‖L‖ :=
  ⟨opNorm_eq_sSup_ratio L, (L.sSup_unitClosedBall_eq_norm).symm, (L.sSup_sphere_eq_norm).symm,
    L.isLeast_opNorm⟩

/-- **Theorem 2.2.6** of [han2009theoretical], with (2.2.5) and (2.2.6). Let $U$, $V$ and $W$ be
normed spaces over $\mathbb{K}$, and let $L_1 \in \mathcal{L}(U, V)$,
$L_2 \in \mathcal{L}(V, W)$ and $L \in \mathcal{L}(U)$. Then
$$\|L_1 u\| \le \|L_1\| \, \|u\| \ \text{ for all } u \in U, \qquad
  \|L_2 L_1\| \le \|L_2\| \, \|L_1\|, \qquad
  \|L^n\| \le \|L\|^n \ \text{ for all } n \ge 0.$$

The last inequality iterates the second one, and every Neumann series estimate of Section 2.3
uses it. In Lean the spaces $U$, $V$, $W$ are `V`, `W`, `X`. -/
theorem theorem_2_2_6 {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (L₁ : V →L[𝕜] W)
    (L₂ : W →L[𝕜] X) (L : V →L[𝕜] V) :
    (∀ v, ‖L₁ v‖ ≤ ‖L₁‖ * ‖v‖) ∧ ‖L₂.comp L₁‖ ≤ ‖L₂‖ * ‖L₁‖ ∧ ∀ n : ℕ, ‖L ^ n‖ ≤ ‖L‖ ^ n :=
  ⟨L₁.le_opNorm, L₂.opNorm_comp_le L₁, fun n => by
    cases n with
    | zero =>
      simpa [ContinuousLinearMap.one_def] using
        ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := V)
    | succ n => exact norm_pow_le' L n.succ_pos⟩

/-- **Theorem 2.2.10** of [han2009theoretical]. Let $V$ and $W$ be normed spaces over $\mathbb{K}$.
If $W$ is a Banach space, then $\mathcal{L}(V, W)$ is a Banach space.

This is the Mathlib instance `ContinuousLinearMap.completeSpace`. The statement gives the
numbered result a name. -/
theorem theorem_2_2_10 [CompleteSpace W] : CompleteSpace (V →L[𝕜] W) := inferInstance

/-- **Example 2.2.7** of [han2009theoretical]. Let $V \neq \{0\}$ be a normed space over
$\mathbb{K}$. The identity operator $I : V \to V$ belongs to $\mathcal{L}(V)$, and $\|I\| = 1$.

**Reading.** The book does not exclude the zero space. On $V = \{0\}$ every operator norm is
$0$, so the statement assumes $V \neq \{0\}$, which is `[Nontrivial V]`.

The bounded operator $I$ is `ContinuousLinearMap.id`, and the first clause says that its
underlying function is the identity. -/
theorem example_2_2_7 (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [Nontrivial V] :
    ⇑(ContinuousLinearMap.id 𝕜 V) = (id : V → V) ∧ ‖ContinuousLinearMap.id 𝕜 V‖ = 1 :=
  ⟨rfl, ContinuousLinearMap.norm_id⟩

end OperatorNorm

/-!
### Example 2.2.8: the operator norms of a matrix

Each of the three vector norms of the book gives a different norm on matrices. Mathlib keeps them
apart with scoped instances, so each clause below opens its own scope.
-/

section MatrixLinfty

open scoped Matrix.Norms.Operator

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Example 2.2.8** of [han2009theoretical], the $\infty$-norm. Let
$A \in \mathbb{K}^{m \times n}$. For the vector norm $\|x\|_\infty = \max_i |x_i|$, the induced
matrix norm is the maximum absolute row sum,
$$\|A\|_\infty = \max_{1 \le i \le m} \sum_{j=1}^n |a_{ij}|,$$
and it is the operator norm of the map $x \mapsto Ax$ from $\mathbb{K}^n$ to $\mathbb{K}^m$,
both with the norm $\|\cdot\|_\infty$.

The matrix norm is Mathlib's operator norm of the scope `Matrix.Norms.Operator`. The maximum
over an empty set of rows is $0$. -/
theorem example_2_2_8_linfty (A : Matrix m n 𝕜) :
    ‖A‖ = ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ℝ) ∧
      ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)
        (Matrix.mulVecLin A).continuous_of_finiteDimensional‖ :=
  ⟨Matrix.linfty_opNorm_def A, Matrix.linfty_opNorm_eq_opNorm A⟩

end MatrixLinfty

section MatrixL1

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Example 2.2.8** of [han2009theoretical], the $1$-norm. Let $A \in \mathbb{K}^{m \times n}$.
For the vector norm $\|x\|_1 = \sum_i |x_i|$, the induced matrix norm is the maximum absolute
column sum: the number
$$\max_{1 \le j \le n} \sum_{i=1}^m |a_{ij}|$$
is the least $\gamma \ge 0$ such that $\|Ax\|_1 \le \gamma \|x\|_1$ for all
$x \in \mathbb{K}^n$.

Mathlib has no operator norm on matrices for $\|\cdot\|_1$. The statement is therefore the
characterization of the induced norm as a least constant, which is the description of the
operator norm in Exercise 2.2.4 and in the fourth clause of
`AtkinsonHan.Chapter02.theorem_2_2_5`. It says what the book's
$\|A\|_1 = \max_j \sum_i |a_{ij}|$ says. The least constant is attained at the unit vector $e_j$
of a column $j$ with the largest sum. -/
theorem example_2_2_8_l1 (A : Matrix m n 𝕜) :
    IsLeast {γ : ℝ | 0 ≤ γ ∧ ∀ x : n → 𝕜, ∑ i, ‖(A *ᵥ x) i‖ ≤ γ * ∑ j, ‖x j‖}
      ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) := by
  classical
  have hcol : ∀ j, ∑ i, ‖A i j‖ ≤ ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) := by
    intro j
    have h : (∑ i, ‖A i j‖₊) ≤ (Finset.univ.sup fun j => ∑ i, ‖A i j‖₊) :=
      Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (Finset.mem_univ j)
    simpa using NNReal.coe_le_coe.2 h
  refine ⟨⟨NNReal.coe_nonneg _, fun x => ?_⟩, ?_⟩
  · have hstep : ∀ i, ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      intro i
      rw [Matrix.mulVec_apply_eq_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      exact le_of_eq (norm_mul _ _)
    calc ∑ i, ‖(A *ᵥ x) i‖ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x j‖ := Finset.sum_le_sum fun i _ => hstep i
      _ = ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ := by rw [Finset.sum_comm]; simp [Finset.sum_mul]
      _ ≤ ∑ j, ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (norm_nonneg _)
      _ = ((Finset.univ.sup fun j => ∑ i, ‖A i j‖₊ : NNReal) : ℝ) * ∑ j, ‖x j‖ := by
          rw [Finset.mul_sum]
  · rintro γ ⟨hγ0, hγ⟩
    lift γ to NNReal using hγ0 with γ'
    rw [NNReal.coe_le_coe]
    refine Finset.sup_le fun j _ => ?_
    have hx : ∑ k, ‖(Pi.single j 1 : n → 𝕜) k‖ = 1 := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
    have hAx : ∀ i, (A *ᵥ (Pi.single j 1 : n → 𝕜)) i = A i j := by
      intro i
      rw [Matrix.mulVec_apply_eq_sum,
        Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
      simp
    have h := hγ (Pi.single j 1)
    simp only [hAx, hx, mul_one] at h
    rw [← NNReal.coe_le_coe]
    push_cast
    exact h

end MatrixL1

section MatrixL2

open scoped Matrix Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Example 2.2.8** of [han2009theoretical], the $2$-norm. Let $A \in \mathbb{C}^{m \times n}$.
For the Euclidean vector norm, the induced matrix norm is
$$\|A\|_2 = \sqrt{\rho(A^* A)},$$
where $\rho$ is the spectral radius. Moreover $\|A^* A\|_2 = \|A\|_2^2$, and $\|A\|_2$ is the
operator norm of the map $x \mapsto Ax$ from $\mathbb{C}^n$ to $\mathbb{C}^m$, both with the
Euclidean norm.

The second clause is the $C^*$-identity from which the formula follows: $A^* A$ is self-adjoint,
so its spectral radius is its norm. The statement is over $\mathbb{C}$, as the book states
Example 2.2.8, because Mathlib has the spectral radius formula for self-adjoint elements of a
$C^*$-algebra over $\mathbb{C}$. The matrix norm is Mathlib's operator norm of the scope
`Matrix.Norms.L2Operator`. -/
theorem example_2_2_8_l2 (A : Matrix m n ℂ) :
    ‖A‖ = Real.sqrt (spectralRadius ℂ (Aᴴ * A)).toReal ∧
      ‖Aᴴ * A‖ = ‖A‖ ^ 2 ∧
        ‖A‖ = ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A‖ := by
  have hsa : IsSelfAdjoint (Aᴴ * A) := by
    simp [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  have hmul : ‖Aᴴ * A‖ = ‖A‖ ^ 2 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  refine ⟨?_, hmul, Matrix.l2_opNorm_def A⟩
  rw [IsSelfAdjoint.spectralRadius_eq_nnnorm hsa, ENNReal.coe_toReal, coe_nnnorm, hmul,
    Real.sqrt_sq (norm_nonneg A)]

end MatrixL2

section IntegralOperator

/-- **Example 2.2.9** of [han2009theoretical], formula (2.2.8). Let $a \le b$ and let $k$ be a
real continuous function on $[a, b] \times [a, b]$. The integral operator
$$Kv(x) = \int_a^b k(x, y) v(y) \, dy$$
on $C[a, b]$ is bounded, and
$$\|K\| = \max_{a \le x \le b} \int_a^b |k(x, y)| \, dy.$$

The same formula is (3.7.9) and (3.7.17) in Chapter 3. The operator is
`IntegralOperator.fredholm`, and the formula is the backbone theorem
`IntegralOperator.norm_fredholm` of `Numlib.IntegralEquations.Basic`. In Lean the maximum is a
supremum over $x$, and the kernel is extended to $y \in \mathbb{R}$ by `Set.projIcc`. -/
theorem equation_2_2_8 {a b : ℝ} (hab : a ≤ b) (k : C(Set.Icc a b × Set.Icc a b, ℝ)) :
    ‖IntegralOperator.fredholm hab k‖ = ⨆ x, ∫ y in a..b, |k (x, Set.projIcc a b hab y)| :=
  IntegralOperator.norm_fredholm hab k

end IntegralOperator

end AtkinsonHan.Chapter02
