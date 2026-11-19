/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Projection.Basic
import Numlib.Projection.Optimality
import NumlibSurface.SaadSparse.Chapter01.Section11
import NumlibSurface.SaadSparse.Chapter01.Section12

/-!
# Saad, Sections 5.1–5.2: Projection methods

This module formalizes §5.1–5.2 of [saad2003iterative], the general projection method for $Ax = b$
with $A \in \mathbb{R}^{n \times n}$. Given subspaces $K$ and $L$ of $\mathbb{R}^n$ of the same
dimension $m$ and an initial guess $x_0$, the method finds $\tilde x$ with
$$\tilde x \in x_0 + K, \qquad b - A\tilde x \perp L \qquad (5.5)\text{–}(5.6).$$
With bases $V$ of $K$ and $W$ of $L$ this is $\tilde x = x_0 + V(W^TAV)^{-1}W^Tr_0$ (5.7), where
$r_0 = b - Ax_0$. The case $L = K$ is an orthogonal projection method, and the other cases are
oblique projection methods.

The module proves when $W^TAV$ is nonsingular (Example 5.2 and Proposition 5.1), the optimality of
the approximation in the energy norm for $L = K$ and in the residual norm for $L = AK$ (Propositions
5.2–5.5), the operators $P_K$, $Q_K^L$ and $A_m = Q_K^L A P_K$ of §5.2.3, the exactness of the
approximation for an invariant subspace (Proposition 5.6), and the error identity of Theorem 5.7.
The proofs specialize `Numlib.Projection.Basic` and `Numlib.Projection.Optimality`, through the
identification of (5.5)–(5.6) with the Petrov–Galerkin condition `IsPetrovGalerkin` of
`Matrix.toEuclideanLin A`.

## Main definitions

* Equations (5.5)–(5.6), `SaadSparse.Chapter05.IsProjectionApprox`: $\tilde x - x_0 \in K$ and
  $b - A\tilde x \perp L$.
* Equation (5.7) and Algorithm 5.1, `SaadSparse.Chapter05.projStep`: the step
  $x \mapsto x + V(W^TAV)^{-1}W^T(b - Ax)$.
* §5.2.1, `SaadSparse.Chapter05.E_A` and `SaadSparse.Chapter05.R_A`: the error functional
  $E(x) = (A(x^* - x), x^* - x)^{1/2}$ and the residual functional $R(x) = \|b - Ax\|_2$.
* §5.2.3, `SaadSparse.Chapter05.A_m`: the operator $A_m = Q_K^L A P_K$.

## Main results

* §5.1.2, `SaadSparse.Chapter05.isUnit_transpose_mul_mul_iff`: $W^TAV$ is nonsingular if and only if
  no nonzero $u \in K$ has $Au \perp L$.
* Example 5.2, `SaadSparse.Chapter05.example_5_2`: $W^TAV$ can be singular for a nonsingular $A$.
* Proposition 5.1, `SaadSparse.Chapter05.proposition_5_1_i` and
  `SaadSparse.Chapter05.proposition_5_1_ii`: the approximation exists and is unique if $A$ is
  positive definite and $L = K$, or if $A$ is nonsingular and $L = AK$.
* Proposition 5.2, `SaadSparse.Chapter05.proposition_5_2`: for symmetric positive definite $A$ and
  $L = K$, the approximation minimizes $E$ over $x_0 + K$.
* Proposition 5.3, `SaadSparse.Chapter05.proposition_5_3`: for $L = AK$, the approximation minimizes
  $R$ over $x_0 + K$.
* Proposition 5.4, `SaadSparse.Chapter05.proposition_5_4`: for $L = AK$, the residual is
  $(I - P)r_0$ with $P$ the orthogonal projector onto $AK$.
* Proposition 5.5, `SaadSparse.Chapter05.proposition_5_5_char`: for $L = K$, the error
  $x^* - \tilde x$ is $A$-orthogonal to $K$.
* Proposition 5.6, `SaadSparse.Chapter05.proposition_5_6`: if $K$ is invariant under $A$ and
  $r_0 \in K$, the approximation is exact.
* Theorem 5.7, `SaadSparse.Chapter05.theorem_5_7`: the identity
  $b - A_m x^* = Q_K^L A (I - P_K) x^*$.
* Theorem 5.7, `SaadSparse.Chapter05.theorem_5_7_matrix`: for $L = K$ and an orthonormal basis $V$
  of $K$, $\|V^Tb - (V^TAV)V^Tx^*\|_2 \le \gamma \|(I - P_K)x^*\|_2$ with
  $\gamma = \|P_K A (I - P_K)\|_2$.

## Notation

* `E n`: `EuclideanSpace ℝ (Fin n)`, the space $\mathbb{R}^n$.

## Implementation notes

* "$A$ is positive definite" in Proposition 5.1 is the definition of the book,
  `Matrix.IsPositiveReal`: $(Au, u) > 0$ for every $u \neq 0$, with no symmetry. "Symmetric positive
  definite" is Mathlib's `Matrix.PosDef`.
* A basis $V$ of $K$ is a matrix whose columns form a basis of $K$, `Matrix.IsBasisOf`. The operator
  $Q_K^L$ is `SaadSparse.obliqueProjection K L`, which needs $\dim K = \dim L$ and
  $K \cap L^\perp = \{0\}$.
* Theorem 5.7 is stated as the identity from which (5.11) follows by the definition of the operator
  norm. The bound itself is stated in the matrix form for $L = K$,
  `SaadSparse.Chapter05.theorem_5_7_matrix`, where the isometry $\|Vy\|_2 = \|y\|_2$ turns it into a
  statement about the projected system in the coordinates of $V$.

## Deviations from the source

* **Generalization.** The Petrov–Galerkin predicate allows trial and test subspaces of unequal
  dimension. See `SaadSparse.Chapter05.IsProjectionApprox`,
  `SaadSparse.Chapter05.isProjectionApprox_iff`.
* **Reading.** The projection prototype is a single update with a totalized inverse. See
  `SaadSparse.Chapter05.projStep`.
* **Reading.** Proposition 5.1 is stated as basis-free existence and uniqueness. See
  `SaadSparse.Chapter05.proposition_5_1_i`, `SaadSparse.Chapter05.proposition_5_1_ii`.
* **Generalization.** The error functional is defined for all matrices, with the norm interpretation
  in the SPD case. See `SaadSparse.Chapter05.E_A`.
* **Reading.** Proposition 5.5 is represented by its algebraic characterization and a separate norm
  bound. See `SaadSparse.Chapter05.proposition_5_5_char`.
* **Reading.** The reduced operator and projector reformulations make the oblique projector’s
  hypotheses explicit. See `SaadSparse.Chapter05.A_m`,
  `SaadSparse.Chapter05.isProjectionApprox_zero_iff_Q`,
  `SaadSparse.Chapter05.isProjectionApprox_zero_iff_A_m`.
* **Reading.** The general statement of Theorem 5.7 gives the residual identity from its proof. See
  `SaadSparse.Chapter05.theorem_5_7`.
* **Reading.** The matrix forms expose the automatic trivial-intersection hypothesis when $L=K$. See
  `SaadSparse.Chapter05.theorem_5_7_matrix_eq`, `SaadSparse.Chapter05.theorem_5_7_matrix`.
* **§5.1.2** (reading). The book states that $W^TAV$ is nonsingular if and only if no vector of $AK$
  is orthogonal to $L$; read literally, this fails for $A = 0$. The statement here is that $u \in K$
  and $u \neq 0$ imply $Au \notin L^\perp$. See `SaadSparse.Chapter05.isUnit_transpose_mul_mul_iff`.
* **Proposition 5.6** (reading). The statement presupposes that $Q_K^L$ exists, that is
  $K \cap L^\perp = \{0\}$; without it the statement fails, so the hypothesis is added. See
  `SaadSparse.Chapter05.proposition_5_6`.
-/

open Matrix Module Submodule Finset
open scoped SaadSparse

namespace SaadSparse.Chapter05

variable {n m : ℕ}

/-- The notation `E n` stands for `EuclideanSpace ℝ (Fin n)`, the space $\mathbb{R}^n$ of
Chapter 5. -/
local notation "E" n => EuclideanSpace ℝ (Fin n)

/-! ### The projection step (5.1)–(5.7) -/

/-- **Equations (5.5)–(5.6)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$,
$b, x_0 \in \mathbb{R}^n$, and let $K$, $L$ be subspaces of $\mathbb{R}^n$. A vector $\tilde x$
is a **projection approximation** onto $K$ orthogonally to $L$, starting from $x_0$, if
$$\tilde x - x_0 \in K \qquad \text{and} \qquad (w, b - A\tilde x) = 0 \text{ for every } w \in
  L.$$

**Generalization.** The defining conditions make sense for unequal-dimensional subspaces, which Lean
allows. The setup of §5.1 starts with equal dimensions.
-/
def IsProjectionApprox (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n)
    (K L : Submodule ℝ (E n)) (x : E n) : Prop :=
  x - x₀ ∈ K ∧ ∀ w ∈ L, inner ℝ w (b - (A ⬝ x)) = 0

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ x : E n} {K L : Submodule ℝ (E n)}

/-- Equations (5.5)–(5.6) of [saad2003iterative] are the Petrov–Galerkin condition
`IsPetrovGalerkin` of the backbone for the operator `Matrix.toEuclideanLin A`.

**Generalization.** The defining conditions make sense for unequal-dimensional subspaces, which Lean
allows. The setup of §5.1 starts with equal dimensions.
-/
theorem isProjectionApprox_iff :
    IsProjectionApprox A b x₀ K L x ↔ IsPetrovGalerkin (toEuclideanLin A) b x₀ K L x :=
  ⟨fun h => ⟨h.1, (Submodule.mem_orthogonal _ _).2 h.2⟩,
    fun h => ⟨h.mem, (Submodule.mem_orthogonal _ _).1 h.orth⟩⟩

/-- **Equation (5.7)** of [saad2003iterative] and Algorithm 5.1. For $A \in \mathbb{R}^{n \times n}$
and $V, W \in \mathbb{R}^{n \times m}$, the **projection step** from $x$ is
$$x \mapsto x + V (W^TAV)^{-1} W^T (b - Ax).$$

If $W^TAV$ is singular, its inverse is $0$ in Lean, and the step returns $x$.

**Reading.** Lean defines one update with the supplied matrices and uses the zero inverse at a
singular projected matrix, returning $x$. The source requires a nonsingular projected matrix and
iteratively selects bases until convergence.
-/
noncomputable def projStep (A : Matrix (Fin n) (Fin n) ℝ) (b : E n)
    (V W : Matrix (Fin n) (Fin m) ℝ) (x : E n) : E n :=
  x + ((V * (Wᵀ * A * V)⁻¹ * Wᵀ) ⬝ (b - (A ⬝ x)))

section Bases

variable {V W : Matrix (Fin n) (Fin m) ℝ}

/-- For a real matrix $V$, the conjugate transpose $V^H$ is the transpose $V^T$. -/
theorem conjTranspose_eq_transpose (V : Matrix (Fin n) (Fin m) ℝ) : Vᴴ = Vᵀ :=
  conjTranspose_eq_transpose_of_trivial V

/-- For $V, W \in \mathbb{R}^{n \times m}$ with columns $v_j$ and $w_i$, the matrix with entries
$(w_i, Av_j)$ is $W^TAV$. -/
theorem crossGram_matrix (A : Matrix (Fin n) (Fin n) ℝ) (V W : Matrix (Fin n) (Fin m) ℝ) :
    (Matrix.of fun i j => inner ℝ (W.cols i) (A ⬝ V.cols j)) = Wᵀ * A * V := by
  ext i j
  rw [Matrix.of_apply, SaadSparse.real_inner_toEuclideanLin', Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, ofLp_cols_apply, mul_comm]
  rfl

/-- For $V \in \mathbb{R}^{n \times m}$ with columns $v_j$ and $y \in \mathbb{R}^m$, the vector
$x_0 + Vy$ is $x_0 + \sum_j y_j v_j$. -/
theorem add_toEuclideanLin_eq (V : Matrix (Fin n) (Fin m) ℝ) (x₀ : E n) (y : Fin m → ℝ) :
    x₀ + (V ⬝ (WithLp.toLp 2 y : E m)) = x₀ + ∑ j, y j • V.cols j := by
  rw [toEuclideanLin_apply_eq_sum]
  rfl

/-- Equation (5.7) of [saad2003iterative]: let $V$ be a basis of $K$ and $W$ a basis of $L$. For
$y \in \mathbb{R}^m$, the vector $x_0 + Vy$ is a projection approximation onto $K$ orthogonally
to $L$ if and only if
$$(W^TAV) y = W^T r_0, \qquad r_0 = b - Ax_0.$$
-/
theorem isProjectionApprox_add_iff (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) (y : Fin m → ℝ) :
    IsProjectionApprox A b x₀ K L (x₀ + (V ⬝ (WithLp.toLp 2 y : E m))) ↔
      (Wᵀ * A * V) *ᵥ y = Wᵀ *ᵥ WithLp.ofLp (b - (A ⬝ x₀)) := by
  have hbasis := isPetrovGalerkin_iff_mulVec (A := toEuclideanLin A) (b := b) (x₀ := x₀)
    hV.toBasis hW.toBasis y
  simp only [IsBasisOf.coe_toBasis_apply] at hbasis
  rw [isProjectionApprox_iff, add_toEuclideanLin_eq, hbasis, crossGram_matrix]
  constructor
  · intro h
    rw [h, ← conjTranspose_eq_transpose, conjTranspose_mulVec_eq_inner]
  · intro h
    rw [h, ← conjTranspose_eq_transpose, conjTranspose_mulVec_eq_inner]

/-- §5.1.2 of [saad2003iterative]: let $V$ be a basis of $K$ and $W$ a basis of $L$. Then $W^TAV$ is
nonsingular if and only if every $u \in K$ with $Au \in L^\perp$ is $0$.

**Reading.** The book states that $W^TAV$ is nonsingular if and only if no vector of the
subspace $AK$ is orthogonal to $L$. Read literally, this fails for $A = 0$. The statement here
reads it as the nondegeneracy hypothesis of the backbone: $u \in K$ and $u \neq 0$ imply
$Au \notin L^\perp$. -/
theorem isUnit_transpose_mul_mul_iff (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) :
    IsUnit (Wᵀ * A * V) ↔ ∀ u ∈ K, (A ⬝ u) ∈ Lᗮ → u = 0 := by
  have hzero : ∀ y : Fin m → ℝ, (Wᵀ * A * V) *ᵥ y = 0 ↔
      (A ⬝ (V ⬝ (WithLp.toLp 2 y : E m))) ∈ Lᗮ := by
    intro y
    rw [← Chapter01.conjTranspose_mulVec_eq_zero_iff hW]
    have h1 : WithLp.ofLp (A ⬝ (V ⬝ (WithLp.toLp 2 y : E m))) = A *ᵥ (V *ᵥ y) := rfl
    rw [h1, mulVec_mulVec, mulVec_mulVec, conjTranspose_eq_transpose]
  have hmemK : ∀ y : Fin m → ℝ, (V ⬝ (WithLp.toLp 2 y : E m)) ∈ K :=
    fun y => hV.span_eq ▸ Chapter01.toEuclideanLin_mem_span V _
  constructor
  · intro h u huK huL
    rw [← hV.span_eq] at huK
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 huK
    have hVc : (V ⬝ (WithLp.toLp 2 c : E m)) = ∑ k, c k • V.cols k :=
      toEuclideanLin_apply_eq_sum V c
    have h0 : (Wᵀ * A * V) *ᵥ c = 0 := (hzero c).mpr (by rw [hVc]; exact huL)
    have hc : c = 0 := by
      have hinj := mulVec_injective_iff_isUnit.mpr h
      exact hinj (a₁ := c) (a₂ := 0) (by rw [h0, mulVec_zero])
    rw [hc]
    simp
  · intro hcond
    refine mulVec_injective_iff_isUnit.mp fun u v huv => ?_
    have hsub : (Wᵀ * A * V) *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
    have hzeroV := hcond _ (hmemK (u - v)) ((hzero (u - v)).mp hsub)
    rw [toEuclideanLin_apply_eq_sum] at hzeroV
    have hli := Fintype.linearIndependent_iff.mp hV.linearIndependent (u - v) hzeroV
    funext i
    have hi := hli i
    rwa [Pi.sub_apply, sub_eq_zero] at hi

end Bases

/-! ### Example 5.2 -/

/-- **Example 5.2** of [saad2003iterative] (§5.1.2). The nonsingularity of $W^TAV$ that (5.7) needs
does not follow from the nonsingularity of $A$. Let $m \ge 1$, let
$$A = \begin{bmatrix} O & I \\ I & I \end{bmatrix} \in \mathbb{R}^{2m \times 2m}, \qquad V = W =
  \begin{bmatrix} I \\ O \end{bmatrix} = [e_1, \dots, e_m].$$
Then $A$ is nonsingular and $V^TV = I$, so $V$ is an orthonormal basis of
$K = L = \operatorname{span}\{e_1, \dots, e_m\}$, but $V^TAV = O$ is singular.

In the terms of `SaadSparse.Chapter05.isUnit_transpose_mul_mul_iff`,
$AV = [e_{m+1}, \dots, e_{2m}]$ is orthogonal to $L$. The index type of $\mathbb{R}^{2m}$ is
`Fin m ⊕ Fin m`. -/
theorem example_5_2 (hm : 0 < m)
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ} (hA : A = fromBlocks 0 1 1 1)
    {V : Matrix (Fin m ⊕ Fin m) (Fin m) ℝ} (hV : V = fromRows 1 0) :
    IsUnit A ∧ Vᵀ * V = 1 ∧ Vᵀ * A * V = 0 ∧ ¬IsUnit (Vᵀ * A * V) := by
  have hVt : Vᵀ = fromCols 1 0 := by
    rw [hV, transpose_fromRows, transpose_one, transpose_zero]
  have hAV : A * V = fromRows 0 1 := by
    rw [hA, hV, fromBlocks_mul_fromRows]; simp
  have hzero : Vᵀ * A * V = 0 := by
    rw [Matrix.mul_assoc, hAV, hVt, fromCols_mul_fromRows]; simp
  refine ⟨?_, ?_, hzero, ?_⟩
  · have hinv : A * fromBlocks (-1) 1 1 0 = 1 := by
      rw [hA, fromBlocks_multiply]; simp
    have hinv' : (fromBlocks (-1) 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) * A = 1 := by
      rw [hA, fromBlocks_multiply]; simp
    exact ⟨⟨A, fromBlocks (-1) 1 1 0, hinv, hinv'⟩, rfl⟩
  · rw [hVt, hV, fromCols_mul_fromRows]; simp
  · have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    rw [hzero, Matrix.isUnit_iff_isUnit_det, det_zero]
    exact not_isUnit_zero

/-! ### Proposition 5.1 -/

/-- **Proposition 5.1(i)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, that is $(Au, u) > 0$ for every $u \neq 0$, and let $L = K$. Then for every $b$ and
$x_0$ there is exactly one projection approximation onto $K$ orthogonally to $K$.

The book states that $W^TAV$ is nonsingular for any bases $V$ and $W$ of $K$ and $L$. By
`SaadSparse.Chapter05.isProjectionApprox_add_iff` this is equivalent to the unique existence of
the approximation, which is the form stated here. Positive definiteness is
`Matrix.IsPositiveReal`.

**Reading.** The source asserts nonsingularity of the reduced matrix for any bases. Lean states its
basis-free consequence, existence and uniqueness of the projection approximation.
-/
theorem proposition_5_1_i (hA : A.IsPositiveReal) (K : Submodule ℝ (E n)) (b x₀ : E n) :
    ∃! x, IsProjectionApprox A b x₀ K K x := by
  have hc : (toEuclideanLin A).IsCoercive := (Matrix.isPositiveReal_iff_isCoercive A).mp hA
  obtain ⟨x, hx, huniq⟩ := existsUnique_isGalerkin_of_isCoercive (A := toEuclideanLin A) b x₀ K hc
  exact ⟨x, isProjectionApprox_iff.mpr hx, fun y hy => huniq y (isProjectionApprox_iff.mp hy)⟩

/-- If $A$ is nonsingular, the operator $x \mapsto Ax$ on $\mathbb{R}^n$ is injective. -/
theorem injective_toEuclideanLin (hA : IsUnit A) : Function.Injective (toEuclideanLin A) := by
  intro u v huv
  have h1 : A *ᵥ WithLp.ofLp u = A *ᵥ WithLp.ofLp v := congrArg WithLp.ofLp huv
  simpa using congrArg (WithLp.toLp 2) (mulVec_injective_iff_isUnit.mpr hA h1)

/-- **Proposition 5.1(ii)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular and let $L = AK$. Then for every $b$ and $x_0$ there is exactly one projection
approximation onto $K$ orthogonally to $AK$.

As in part (i), the unique existence of the approximation is the nonsingularity of $W^TAV$.

**Reading.** The source asserts nonsingularity of the reduced matrix for any bases. Lean states its
basis-free consequence, existence and uniqueness of the projection approximation.
-/
theorem proposition_5_1_ii (hA : IsUnit A) (K : Submodule ℝ (E n)) (b x₀ : E n) :
    ∃! x, IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x := by
  have hinj : Set.InjOn (toEuclideanLin A) K :=
    fun u _ v _ huv => injective_toEuclideanLin hA huv
  obtain ⟨x, hx, huniq⟩ := existsUnique_isMinResidual_of_injOn (A := toEuclideanLin A) b x₀ K hinj
  refine ⟨x, isProjectionApprox_iff.mpr hx.isPetrovGalerkin, fun y hy => ?_⟩
  exact huniq y (IsMinResidual.iff_isPetrovGalerkin.mpr (isProjectionApprox_iff.mp hy))

/-- §5.1 of [saad2003iterative]: if $A$ is symmetric, the projected matrix $V^TAV$ is symmetric. -/
theorem isSymm_transpose_mul_mul (hA : A.IsSymm) (V : Matrix (Fin n) (Fin m) ℝ) :
    (Vᵀ * A * V).IsSymm := by
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, hA, Matrix.mul_assoc]

/-- §5.1 of [saad2003iterative]: if $A$ is symmetric positive definite and
$V \in \mathbb{R}^{n \times m}$ has linearly independent columns, the projected matrix $V^TAV$
is symmetric positive definite. -/
theorem posDef_transpose_mul_mul {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {V : Matrix (Fin n) (Fin m) ℝ} (hV : Function.Injective V.mulVec) :
    (Vᵀ * A * V).PosDef := by
  have h := hA.conjTranspose_mul_mul_same hV
  rwa [conjTranspose_eq_transpose] at h

/-! ### Propositions 5.2–5.5 -/

/-- **Section 5.2.1** of [saad2003iterative], the error functional. For
$A \in \mathbb{R}^{n \times n}$ and the exact solution $x^*$, the **error functional** is
$$E(x) = \big( A(x^* - x), x^* - x \big)^{1/2},$$
the quantity that Proposition 5.2 minimizes.

The square root is `Real.sqrt`, which is $0$ at a negative argument.

**Generalization.** Lean defines the square-root expression for all $A$. Its intended interpretation
as an error norm requires symmetric positive definiteness as in Proposition 5.2.
-/
noncomputable def E_A (A : Matrix (Fin n) (Fin n) ℝ) (xstar x : E n) : ℝ :=
  Real.sqrt (inner ℝ (A ⬝ (xstar - x)) (xstar - x))

/-- **Section 5.2.1** of [saad2003iterative], the residual functional. For
$A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, the **residual functional** is
$R(x) = \|b - Ax\|_2$, the quantity that Proposition 5.3 minimizes. -/
noncomputable def R_A (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : ℝ := ‖b - (A ⬝ x)‖

/-- The error functional $E(x)$ is the energy norm `energyNorm` of the error $x^* - x$ for the
operator of $A$. -/
theorem E_A_eq_energyNorm (A : Matrix (Fin n) (Fin n) ℝ) (xstar x : E n) :
    E_A A xstar x = energyNorm (toEuclideanLin A) (xstar - x) := rfl

/-- **Proposition 5.2** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $Ax^* = b$, and let $L = K$. Then $\tilde x$ is a projection
approximation onto $K$ orthogonally to $K$ if and only if $\tilde x \in x_0 + K$ and
$$E(\tilde x) \le E(y) \qquad \text{for every } y \in x_0 + K.$$
-/
theorem proposition_5_2 (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) :
    IsProjectionApprox A b x₀ K K x ↔
      (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → E_A A xstar x ≤ E_A A xstar y) := by
  have hsc : (toEuclideanLin A).IsSymmetricCoercive :=
    (Matrix.posDef_iff_isSymmetricCoercive A).mp hA
  rw [isProjectionApprox_iff]
  simpa only [E_A_eq_energyNorm] using
    IsGalerkin.iff_energyNorm_min (A := toEuclideanLin A) (b := b) (x₀ := x₀) (K := K) (x := x)
      (xstar := xstar) hsc hstar

/-- **Proposition 5.3** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be arbitrary and
let $L = AK$. Then $\tilde x$ is a projection approximation onto $K$ orthogonally to $AK$ if and
only if $\tilde x \in x_0 + K$ and
$$R(\tilde x) \le R(y) \qquad \text{for every } y \in x_0 + K.$$
-/
theorem proposition_5_3 :
    IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x ↔
      (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → R_A A b x ≤ R_A A b y) := by
  rw [isProjectionApprox_iff, ← IsMinResidual.iff_isPetrovGalerkin]
  exact ⟨fun h => ⟨h.mem, h.min⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Proposition 5.4** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and $L = AK$. If
$\tilde x$ is a projection approximation onto $K$ orthogonally to $AK$, then its residual is
$$b - A\tilde x = (I - P) r_0, \qquad r_0 = b - Ax_0,$$
where $P$ is the orthogonal projector onto $AK$.

The projector $P$ is `Submodule.starProjection` of $AK$. -/
theorem proposition_5_4 (hx : IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x) :
    b - (A ⬝ x) =
      (b - (A ⬝ x₀)) - (K.map (toEuclideanLin A)).starProjection (b - (A ⬝ x₀)) :=
  (IsMinResidual.iff_isPetrovGalerkin.mpr (isProjectionApprox_iff.mp hx)).residual_eq

/-- §5.2.2 of [saad2003iterative]: for $L = AK$, the residual norm of a projection approximation is
at most the residual norm of $x_0$. -/
theorem norm_residual_le (hx : IsProjectionApprox A b x₀ K (K.map (toEuclideanLin A)) x) :
    ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ x₀)‖ :=
  IsMinResidual.norm_residual_le_norm_residual_zero
    (IsMinResidual.iff_isPetrovGalerkin.mpr (isProjectionApprox_iff.mp hx))

/-- **Proposition 5.5** of [saad2003iterative], the characterization. Let $Ax^* = b$ and $L = K$. If
$\tilde x$ is a projection approximation onto $K$ orthogonally to $K$, then
$\tilde x - x_0 \in K$ and the error $x^* - \tilde x$ is $A$-orthogonal to $K$:
$$\big( A(x^* - \tilde x), w \big) = 0 \qquad \text{for every } w \in K.$$

The $A$-inner product is `Matrix.energyInner`.

**Reading.** Lean gives the algebraic orthogonality characterization used by the source. It holds
without symmetric positive definiteness. The printed proposition gives the projector identity in the
inner product induced by an SPD matrix.
-/
theorem proposition_5_5_char {xstar : E n} (hstar : (A ⬝ xstar) = b)
    (hx : IsProjectionApprox A b x₀ K K x) :
    x - x₀ ∈ K ∧ ∀ w ∈ K, A.energyInner (xstar - x) w = 0 := by
  refine ⟨hx.1, fun w hw => ?_⟩
  have h : A.energyInner (xstar - x) w = inner ℝ w (A ⬝ (xstar - x)) := rfl
  rw [h, map_sub, hstar]
  simpa using hx.2 w hw

/-- Proposition 5.5 of [saad2003iterative]: for symmetric positive definite $A$, $Ax^* = b$ and
$L = K$, a projection approximation $\tilde x$ satisfies $E(\tilde x) \le E(x_0)$. -/
theorem energyNorm_error_le (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b)
    (hx : IsProjectionApprox A b x₀ K K x) : E_A A xstar x ≤ E_A A xstar x₀ :=
  IsGalerkin.energyNorm_le ((Matrix.posDef_iff_isSymmetricCoercive A).mp hA)
    (isProjectionApprox_iff.mp hx) hstar (by simp)

/-! ### §5.2.3: The operators $P_K$, $Q_K^L$ and $A_m$ -/

/-- **Section 5.2.3** of [saad2003iterative], the operator $A_m$. Let $\dim K = \dim L$ and
$K \cap L^\perp = \{0\}$. The **projected operator** is
$$A_m = Q_K^L A P_K,$$
where $P_K$ is the orthogonal projector onto $K$ and $Q_K^L$ is the projector onto $K$
orthogonally to $L$.

$Q_K^L$ is `SaadSparse.obliqueProjection K L` and $P_K$ is `Submodule.starProjection` of $K$.

**Reading.** Lean requires $\dim K=\dim L$ and $K\cap L^\perp=\{0\}$ so the oblique projector
$Q_K^L$ in these formulations exists. The section relies implicitly on the projector from §1.12.
-/
noncomputable def A_m (A : Matrix (Fin n) (Fin n) ℝ) (K L : Submodule ℝ (E n))
    (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) : (E n) →ₗ[ℝ] (E n) :=
  (SaadSparse.obliqueProjection K L hd h).comp
    ((toEuclideanLin A).comp (K.starProjection : (E n) →L[ℝ] (E n)).toLinearMap)

/-- §5.2.3 of [saad2003iterative]: let $\dim K = \dim L$ and $K \cap L^\perp = \{0\}$. With
$x_0 = 0$, a vector $x$ is a projection approximation onto $K$ orthogonally to $L$ if and only
if $x \in K$ and $Q_K^L(b - Ax) = 0$.

**Reading.** Lean requires $\dim K=\dim L$ and $K\cap L^\perp=\{0\}$ so the oblique projector
$Q_K^L$ in these formulations exists. The section relies implicitly on the projector from §1.12.
-/
theorem isProjectionApprox_zero_iff_Q (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) :
    IsProjectionApprox A b 0 K L x ↔
      x ∈ K ∧ SaadSparse.obliqueProjection K L hd h (b - (A ⬝ x)) = 0 := by
  rw [IsProjectionApprox,
    SaadSparse.obliqueProjection_eq_zero_iff hd h (b - (A ⬝ x)),
    ← Submodule.mem_orthogonal L (b - (A ⬝ x))]
  simp

/-- §5.2.3 of [saad2003iterative]: let $\dim K = \dim L$ and $K \cap L^\perp = \{0\}$. With
$x_0 = 0$, a vector $x$ is a projection approximation onto $K$ orthogonally to $L$ if and only
if $x \in K$ and $A_m x = Q_K^L b$.

**Reading.** Lean requires $\dim K=\dim L$ and $K\cap L^\perp=\{0\}$ so the oblique projector
$Q_K^L$ in these formulations exists. The section relies implicitly on the projector from §1.12.
-/
theorem isProjectionApprox_zero_iff_A_m (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) :
    IsProjectionApprox A b 0 K L x ↔
      x ∈ K ∧ A_m A K L hd h x = SaadSparse.obliqueProjection K L hd h b := by
  rw [isProjectionApprox_zero_iff_Q hd h]
  refine and_congr_right fun hx => ?_
  have hP : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hAm : A_m A K L hd h x = SaadSparse.obliqueProjection K L hd h (A ⬝ x) := by
    rw [A_m]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hP]
  rw [hAm, map_sub, sub_eq_zero, eq_comm]

/-! ### Proposition 5.6 -/

/-- **Proposition 5.6** of [saad2003iterative]. Let $K$ be invariant under $A$, let
$K \cap L^\perp = \{0\}$, and let the initial residual satisfy $b - Ax_0 \in K$. If $\tilde x$
is a projection approximation onto $K$ orthogonally to $L$, then $A\tilde x = b$.

**Reading.** The book states the result with the projector $Q_K^L$, and so presupposes that it
exists, that is $K \cap L^\perp = \{0\}$. Without this condition the statement fails, so the
hypothesis is added. -/
theorem proposition_5_6 (hK : K ∈ Module.End.invtSubmodule (toEuclideanLin A))
    (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) (hr : b - (A ⬝ x₀) ∈ K)
    (hx : IsProjectionApprox A b x₀ K L x) : (A ⬝ x) = b :=
  (isProjectionApprox_iff.mp hx).eq_of_invt hK hr hKL

/-! ### Theorem 5.7 -/

/-- §5.2.3 of [saad2003iterative]: for every $x \in K$, the distance from $x^*$ to $x$ is at least
the distance from $x^*$ to $K$: $\|x^* - P_K x^*\|_2 \le \|x^* - x\|_2$. -/
theorem norm_sub_ge_of_mem {xstar : E n} (hx : x ∈ K) :
    ‖xstar - K.starProjection xstar‖ ≤ ‖xstar - x‖ :=
  Submodule.norm_sub_le_of_forall_inner_eq_zero (K.starProjection_apply_mem xstar)
    (fun w hw => K.starProjection_inner_eq_zero xstar w hw) hx

/-- **Theorem 5.7** of [saad2003iterative], the identity. Let $\dim K = \dim L$,
$K \cap L^\perp = \{0\}$, $b \in K$ and $Ax^* = b$. Then
$$b - A_m x^* = Q_K^L A (I - P_K) x^*.$$

With $x_0 = 0$, the bound $\|b - A_m x^*\|_2 \le \|Q_K^L A (I - P_K)\|_2 \|(I - P_K) x^*\|_2$ of
(5.11) follows from this identity by the definition of the operator norm. The bound is stated in
the matrix form for $L = K$, `SaadSparse.Chapter05.theorem_5_7_matrix`.

**Reading.** Lean gives the residual identity from the proof, with the conditions for $Q_K^L$
explicit. The source's statement is the norm bound for general $K,L$. The bound is stated separately
in Lean for the orthogonal matrix case $L=K$.
-/
theorem theorem_5_7 (hd : finrank ℝ K = finrank ℝ L) (h : K ⊓ Lᗮ = ⊥) (hb : b ∈ K)
    {xstar : E n} (hstar : (A ⬝ xstar) = b) :
    b - A_m A K L hd h xstar =
      SaadSparse.obliqueProjection K L hd h (A ⬝ (xstar - K.starProjection xstar)) := by
  have hQb : SaadSparse.obliqueProjection K L hd h b = b :=
    ((SaadSparse.isProjOnto_iff_eq_obliqueProjection hd h b b).mp ⟨hb, by simp⟩)
  have hAm : A_m A K L hd h xstar
      = SaadSparse.obliqueProjection K L hd h (A ⬝ K.starProjection xstar) := rfl
  rw [hAm, ← hQb, ← map_sub]
  congr 1
  rw [map_sub, hstar]

/-! ### Theorem 5.7 in matrix form (§5.2.3) -/

/-- §1.12.2 of [saad2003iterative]: if $K \cap K^\perp = \{0\}$, the projector onto $K$ orthogonally
to $K$ is the orthogonal projector $P_K$. -/
theorem obliqueProjection_self (h : K ⊓ Kᗮ = ⊥) (z : E n) :
    SaadSparse.obliqueProjection K K rfl h z = K.starProjection z :=
  (SaadSparse.isProjOnto_iff_eq_obliqueProjection rfl h z _).mp
    ((SaadSparse.isProjOnto_self_iff_eq_starProjection z _).mpr rfl)

section MatrixForm

variable {V : Matrix (Fin n) (Fin m) ℝ}

/-- If $V \in \mathbb{R}^{n \times m}$ has orthonormal columns, $V^TV = I$, then
$\|Vy\|_2 = \|y\|_2$ for every $y$. This isometry is what makes the coordinate form of Theorem
5.7 equivalent to the vector form. -/
theorem norm_toEuclideanLin_of_orthonormal (hV : Vᵀ * V = 1) (y : E m) : ‖(V ⬝ y)‖ = ‖y‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [real_norm_sq_eq_dotProduct, real_norm_sq_eq_dotProduct, Matrix.ofLp_toEuclideanLin,
    dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hV, one_mulVec]

/-- Theorem 5.7 of [saad2003iterative] in matrix form, the identity behind it: let $L = K$, let $V$
be a basis of $K$ with $V^TV = I$, let $K \cap K^\perp = \{0\}$ and $b \in K$. Then for every
$x$,
$$\|V^Tb - (V^TAV)V^Tx\|_2 = \|b - A_m x\|_2.$$
The reason is that $VV^T = P_K$ and $b = VV^Tb$, so $V(V^Tb - (V^TAV)V^Tx) = b - A_m x$.

**Reading.** The explicit hypothesis $K\cap K^\perp=\{0\}$ comes from the oblique-projector
representation. For $L=K$ it holds for all subspaces.
-/
theorem theorem_5_7_matrix_eq (hV : Vᵀ * V = 1) (hVK : V.IsBasisOf K) (h : K ⊓ Kᗮ = ⊥)
    (hb : b ∈ K) : ‖(Vᵀ ⬝ b) - ((Vᵀ * A * V) ⬝ (Vᵀ ⬝ x))‖ = ‖b - A_m A K K rfl h x‖ := by
  have hVVt : toEuclideanLin (V * Vᵀ) = (K.starProjection : (E n) →ₗ[ℝ] (E n)) :=
    Chapter01.toEuclideanLin_mul_conjTranspose (by rwa [conjTranspose_eq_transpose]) hVK
  have hP : ∀ z : E n, ((V * Vᵀ) ⬝ z) = K.starProjection z := fun z =>
    LinearMap.congr_fun hVVt z
  have h1 : (V ⬝ (Vᵀ ⬝ b)) = b := by
    rw [← Matrix.toEuclideanLin_mul_apply, hP]
    exact Submodule.starProjection_eq_self_iff.mpr hb
  have h2 : (V ⬝ ((Vᵀ * A * V) ⬝ (Vᵀ ⬝ x))) = K.starProjection (A ⬝ K.starProjection x) := by
    have e1 : (V ⬝ ((Vᵀ * A * V) ⬝ (Vᵀ ⬝ x))) = ((V * (Vᵀ * A * V) * Vᵀ) ⬝ x) := by
      rw [← Matrix.toEuclideanLin_mul_apply, ← Matrix.toEuclideanLin_mul_apply]
    have e2 : V * (Vᵀ * A * V) * Vᵀ = (V * Vᵀ) * A * (V * Vᵀ) := by
      simp only [Matrix.mul_assoc]
    have e3 : (((V * Vᵀ) * A * (V * Vᵀ)) ⬝ x) = ((V * Vᵀ) ⬝ (A ⬝ ((V * Vᵀ) ⬝ x))) := by
      rw [← Matrix.toEuclideanLin_mul_apply, ← Matrix.toEuclideanLin_mul_apply]
    rw [e1, e2, e3, hP, hP]
  have hAm : A_m A K K rfl h x
      = SaadSparse.obliqueProjection K K rfl h (A ⬝ K.starProjection x) := rfl
  have hkey : (V ⬝ ((Vᵀ ⬝ b) - ((Vᵀ * A * V) ⬝ (Vᵀ ⬝ x)))) = b - A_m A K K rfl h x := by
    rw [map_sub, h1, h2, hAm, obliqueProjection_self]
  rw [← hkey, norm_toEuclideanLin_of_orthonormal hV]

/-- **Theorem 5.7** of [saad2003iterative], matrix form (§5.2.3). Let $L = K$, let $V$ be a basis of
$K$ with orthonormal columns, $V^TV = I$, let $K \cap K^\perp = \{0\}$, $b \in K$ and
$Ax^* = b$. Then
$$\|V^Tb - (V^TAV)V^Tx^*\|_2 \le \gamma \, \|(I - P_K) x^*\|_2, \qquad \gamma = \|P_K A (I -
  P_K)\|_2.$$
This is (5.11) in the coordinates of $V$: the residual of the projected system is controlled by
the part of the exact solution that $K$ does not contain.

The hypothesis $K \cap K^\perp = \{0\}$ always holds; it is the hypothesis of
`SaadSparse.obliqueProjection` for $L = K$.

**Reading.** The explicit hypothesis $K\cap K^\perp=\{0\}$ comes from the oblique-projector
representation. For $L=K$ it holds for all subspaces.
-/
theorem theorem_5_7_matrix (hV : Vᵀ * V = 1) (hVK : V.IsBasisOf K) (h : K ⊓ Kᗮ = ⊥) (hb : b ∈ K)
    {xstar : E n} (hstar : (A ⬝ xstar) = b) :
    ‖(Vᵀ ⬝ b) - ((Vᵀ * A * V) ⬝ (Vᵀ ⬝ xstar))‖ ≤
      ‖(K.starProjection ∘L LinearMap.toContinuousLinearMap (toEuclideanLin A) ∘L
          (ContinuousLinearMap.id ℝ (E n) - K.starProjection) : (E n) →L[ℝ] (E n))‖ *
        ‖xstar - K.starProjection xstar‖ := by
  have hPP : K.starProjection (K.starProjection xstar) = K.starProjection xstar :=
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem xstar)
  have hPz : K.starProjection (xstar - K.starProjection xstar) = 0 := by
    rw [map_sub, hPP, sub_self]
  have hTz : (K.starProjection ∘L LinearMap.toContinuousLinearMap (toEuclideanLin A) ∘L
        (ContinuousLinearMap.id ℝ (E n) - K.starProjection) : (E n) →L[ℝ] (E n))
        (xstar - K.starProjection xstar)
      = K.starProjection (A ⬝ (xstar - K.starProjection xstar)) := by
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.sub_apply,
      ContinuousLinearMap.coe_id', id_eq, hPz, sub_zero]
    rfl
  rw [theorem_5_7_matrix_eq hV hVK h hb, theorem_5_7 rfl h hb hstar, obliqueProjection_self,
    ← hTz]
  exact ContinuousLinearMap.le_opNorm _ _

end MatrixForm

end SaadSparse.Chapter05
