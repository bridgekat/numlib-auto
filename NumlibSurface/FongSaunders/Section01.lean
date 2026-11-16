/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Subspace
import Numlib.Krylov.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.PosDef

/-!
# Fong and Saunders, Section 1: The setting, Krylov subspaces and the Lanczos process

This module formalizes the setting of Section 1 of [fong2012cg]. The paper studies a real symmetric
positive definite system $Ax = b$ of order $n$, solved by Krylov subspace methods from the starting
point $x_0 = 0$, with $\|\cdot\|$ the 2-norm on vectors. The module defines the space
$\mathbb{R}^n$, the matrix–vector product, the Krylov subspaces $\mathcal{K}_k(A, b) =
\operatorname{span}\{b, Ab, \dots, A^{k-1} b\}$, the Lanczos vectors $v_1, v_2, \dots$, the
tridiagonal Lanczos matrices $T_k$ and $\underline{T}_k$, and the exact solution $x^* = A^{-1} b$.

It proves the unnumbered facts of Section 1 and Section 1.1: the Lanczos relation
$A V_k = V_{k+1} \underline{T}_k$, where $V_k = [v_1, \dots, v_k]$; the termination of the Lanczos
process at a step $\ell \le n$, where $A V_\ell = V_\ell T_\ell$; the description $x = V_k y$ of the
elements of $\mathcal{K}_k(A, b)$; and the existence and uniqueness of $x^*$. It also proves the
lemmas that connect this vocabulary to the backbone. The proofs specialize `Numlib.Krylov.Subspace`,
`Numlib.Krylov.Arnoldi` and `Numlib.Krylov.Lanczos`.

## Main definitions

* Section 1, `FongSaunders.Vec`: the space $\mathbb{R}^n$ with the 2-norm and the inner product
  $x^T y$.
* Section 1, `FongSaunders.mulVecE`: the matrix–vector product $Ax$ as a map from $\mathbb{R}^n$ to
  $\mathbb{R}^n$.
* Section 1, `FongSaunders.krylov`: the Krylov subspace $\mathcal{K}_k(A, b)$.
* Section 1, `FongSaunders.xstar`: the exact solution $x^* = A^{-1} b$.

## Main results

* Section 1, `FongSaunders.lanczos_relation`: for symmetric $A$, the Lanczos relation
  $A V_k = V_{k+1} \underline{T}_k$ holds for every $k$.
* Section 1, `FongSaunders.lanczos_relation_term`: for symmetric $A$, at the termination step $\ell$
  the relation closes up to $A V_\ell = V_\ell T_\ell$.
* Section 1, `FongSaunders.lanczosVec_orthonormal`: the Lanczos vectors $v_1, \dots, v_\ell$ are
  orthonormal.
* Section 1, `FongSaunders.span_lanczosVec`: the vectors $v_1, \dots, v_k$ span
  $\mathcal{K}_k(A, b)$.
* Section 1, `FongSaunders.mem_krylov_iff_exists_lanczos`: the elements of $\mathcal{K}_k(A, b)$ are
  exactly the vectors $V_k y$ with $y \in \mathbb{R}^k$.
* Section 1, `FongSaunders.lanczosTerm_le`: the Lanczos process terminates at a step $\ell \le n$.
* Section 1, `FongSaunders.existsUnique_solution`: if $A$ is positive definite, then $Ax = b$ has
  exactly one solution.

## Notation

Both notations are scoped to the namespace `FongSaunders`, and Sections 2–5 use them.

* `⟪x, y⟫_ℝ`: the inner product $x^T y$, which is `inner ℝ x y`.
* `A ⬝ x`: the product $Ax$, which is `FongSaunders.mulVecE A x`, that is
  `Matrix.toEuclideanLin A x`. The notation binds tighter than the arithmetic operators, so
  `r - α • A ⬝ p` is $r - \alpha A p$.

## Conventions

* The Lanczos vectors are indexed from $0$: `FongSaunders.lanczosVec A b j` is the vector $v_{j+1}$
  of the paper.
* The termination step $\ell$ of the Lanczos process is `FongSaunders.lanczosTerm A b`, the grade of
  $b$ with respect to $A$.

## Implementation notes

* The Lanczos vectors are not defined again here. They are the backbone Arnoldi vectors
  `Arnoldi.vec` of `Matrix.toEuclideanLin A` and $b$, which satisfy the three-term Lanczos
  recurrence when $A$ is symmetric. After the termination step the Arnoldi vectors are $0$.
-/

namespace FongSaunders

open Krylov Matrix

/-- The inner product $x^T y$ of two vectors $x, y \in \mathbb{R}^n$, written `⟪x, y⟫_ℝ`. -/
scoped notation "⟪" x ", " y "⟫_ℝ" => inner ℝ x y

/-- **Section 1** of [fong2012cg], the vector space. The space $\mathbb{R}^n$ of real vectors with
$n$ components, with the inner product $x^T y$ and the 2-norm $\|x\| = (x^T x)^{1/2}$.

The space is `EuclideanSpace ℝ (Fin n)`, so the components are indexed by `Fin n`, and the norm
and the inner product are those of a Euclidean space. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- **Section 1** of [fong2012cg], the matrix–vector product. For $A \in \mathbb{R}^{n \times n}$
and $x \in \mathbb{R}^n$, the product $Ax \in \mathbb{R}^n$.

The product is `Matrix.toEuclideanLin A x`. The scoped notation `A ⬝ x` stands for it. -/
noncomputable abbrev mulVecE (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Vec n :=
  Matrix.toEuclideanLin A x

@[inherit_doc] scoped infixr:73 " ⬝ " => mulVecE

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n)

/-! ### The matrix–vector product -/

section Glue

variable {A} {x y : Vec n} {c : ℝ}

/-- The product is additive in the vector: $A(x + y) = Ax + Ay$. -/
theorem mulVecE_add : A ⬝ (x + y) = A ⬝ x + A ⬝ y := map_add _ _ _

/-- The product is homogeneous in the vector: $A(cx) = c\,Ax$ for $c \in \mathbb{R}$. -/
theorem mulVecE_smul : A ⬝ (c • x) = c • (A ⬝ x) := map_smul _ _ _

/-- The product distributes over a difference of vectors: $A(x - y) = Ax - Ay$. -/
theorem mulVecE_sub : A ⬝ (x - y) = A ⬝ x - A ⬝ y := map_sub _ _ _

/-- A matrix maps the zero vector to zero: $A0 = 0$. -/
@[simp] theorem mulVecE_zero : A ⬝ (0 : Vec n) = 0 := map_zero _

/-- The zero matrix maps every vector to zero: $0x = 0$. -/
@[simp] theorem zero_mulVecE (x : Vec n) : (0 : Matrix (Fin n) (Fin n) ℝ) ⬝ x = 0 := by
  change Matrix.toEuclideanLin 0 x = 0
  rw [map_zero, LinearMap.zero_apply]

/-- The product $Ax$ is `Matrix.toEuclideanLin A x`, the backbone linear map of $A$ applied to $x$.

The statement holds by definition, since `FongSaunders.mulVecE` is reducible. It lets `rw` and
`simp only` rewrite towards the backbone; after that, `Matrix.ofLp_toEuclideanLin` gives the
coordinate form `A *ᵥ x`. -/
theorem mulVecE_eq (A : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    A ⬝ x = Matrix.toEuclideanLin A x := rfl

/-- In coordinates, $x^T (Ay)$ is the dot product of the coordinate vector of $x$ with $A$ times the
coordinate vector of $y$. -/
theorem inner_mulVecE (A : Matrix (Fin n) (Fin n) ℝ) (x y : Vec n) :
    ⟪x, A ⬝ y⟫_ℝ = WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp y) := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- If $A$ is symmetric, then the linear map `Matrix.toEuclideanLin A` is a symmetric operator on
$\mathbb{R}^n$. -/
theorem isSymmetric_toEuclideanLin (hA : A.IsSymm) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  hA.isSymmetric_toEuclideanLin

/-- If $A$ is symmetric, then $x^T (Ay) = (Ax)^T y$ for all $x, y \in \mathbb{R}^n$. -/
theorem inner_mulVecE_comm (hA : A.IsSymm) (x y : Vec n) : ⟪x, A ⬝ y⟫_ℝ = ⟪A ⬝ x, y⟫_ℝ :=
  ((isSymmetric_toEuclideanLin hA) x y).symm

/-- For every $i \in \mathbb{N}$, the matrix power $A^i$ acts on $x$ as the $i$-th power of the
linear map `Matrix.toEuclideanLin A`. -/
theorem mulVecE_pow (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) (x : Vec n) :
    (A ^ i) ⬝ x = (Matrix.toEuclideanLin A ^ i) x :=
  DFunLike.congr_fun (Matrix.toEuclideanLin_pow A i) x

/-- If $A$ is positive definite ($A \succ 0$ in the notation of the paper), then the linear map
`Matrix.toEuclideanLin A` is symmetric and coercive in the sense of
`LinearMap.IsSymmetricCoercive`.

Over $\mathbb{R}$, `Matrix.PosDef` means that $A$ is symmetric and $x^T A x > 0$ for every
$x \neq 0$. Through this lemma, the backbone theorems for symmetric coercive operators apply to
$A$. -/
theorem isSymmetricCoercive_of_posDef (hA : A.PosDef) :
    (Matrix.toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

/-- Let $A$ be symmetric. For $u, p \in \mathbb{R}^n$ and $c \in \mathbb{R}$, the quadratic form of
$A$ along the line $u + cp$ is $$(u + cp)^T A (u + cp) = u^T A u + 2c\,(Au)^T p + c^2\,p^T A
p.$$
-/
theorem inner_mulVecE_add_smul (hA : A.IsSymm) (u p : Vec n) (c : ℝ) :
    ⟪u + c • p, A ⬝ (u + c • p)⟫_ℝ
      = ⟪u, A ⬝ u⟫_ℝ + 2 * c * ⟪A ⬝ u, p⟫_ℝ + c ^ 2 * ⟪p, A ⬝ p⟫_ℝ := by
  simp only [mulVecE_add, mulVecE_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_mulVecE_comm hA u p, real_inner_comm (A ⬝ u) p]
  ring

/-- If $A$ is positive definite and $x \neq 0$, then $x^T A x > 0$. -/
theorem inner_mulVecE_self_pos (hA : A.PosDef) {x : Vec n} (hx : x ≠ 0) : 0 < ⟪x, A ⬝ x⟫_ℝ := by
  have h := (isSymmetricCoercive_of_posDef hA).isCoercive.inner_self_pos hx
  rw [RCLike.re_to_real] at h
  rwa [real_inner_comm]

/-- If $A$ is positive definite, then $x^T A x \ge 0$ for every $x \in \mathbb{R}^n$. -/
theorem inner_mulVecE_self_nonneg (hA : A.PosDef) (x : Vec n) : 0 ≤ ⟪x, A ⬝ x⟫_ℝ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (inner_mulVecE_self_pos hA hx).le

/-- If $A$ is positive definite and $x^T A x = 0$, then $x = 0$. -/
theorem eq_zero_of_inner_mulVecE_self_eq_zero (hA : A.PosDef) {x : Vec n}
    (hx : ⟪x, A ⬝ x⟫_ℝ = 0) : x = 0 := by
  by_contra h
  exact absurd hx (inner_mulVecE_self_pos hA h).ne'

/-- If $A$ is positive definite and $\mathbb{R}^n$ contains a nonzero vector, then $A \neq 0$.

In Section 3 this gives $\|A\| \neq 0$, which the ratios $\|E\| / \|A\|$ of the paper need. -/
theorem ne_zero_of_posDef (hA : A.PosDef) {x : Vec n} (hx : x ≠ 0) : A ≠ 0 := by
  rintro rfl
  exact absurd (by rw [zero_mulVecE, inner_zero_right]) (inner_mulVecE_self_pos hA hx).ne'

end Glue

/-! ### Krylov subspaces and the Lanczos objects -/

/-- **Section 1** of [fong2012cg], Krylov subspaces. For $A \in \mathbb{R}^{n \times n}$,
$b \in \mathbb{R}^n$ and $k \in \mathbb{N}$, the **Krylov subspace** is $$\mathcal{K}_k(A, b) =
\operatorname{span}\{b, Ab, \dots, A^{k-1} b\} \subseteq \mathbb{R}^n.$$ For $k = 0$ it is
$\{0\}$.

`FongSaunders.krylov_eq` identifies it with the backbone subspace `Krylov.subspace` of
`Matrix.toEuclideanLin A` and $b$. -/
noncomputable def krylov (k : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range fun i : Fin k => (A ^ (i : ℕ)) ⬝ b)

/-- The **Lanczos vector** $v_{j+1}$ of [fong2012cg] for $A$ and $b$: the index starts at $0$, so
`FongSaunders.lanczosVec A b 0` is $v_1 = b / \|b\|$.

The Lanczos vectors are the backbone Arnoldi vectors `Arnoldi.vec`, the Gram–Schmidt
orthonormalization of $b, Ab, A^2 b, \dots$, which is $0$ after the termination step. For
symmetric $A$ they satisfy the three-term Lanczos recurrence. -/
noncomputable abbrev lanczosVec (j : ℕ) : Vec n := Arnoldi.vec (Matrix.toEuclideanLin A) b j

/-- The $(k+1) \times k$ tridiagonal Lanczos matrix $\underline{T}_k$ of [fong2012cg], which is
`Lanczos.tridiagExt` of `Matrix.toEuclideanLin A` and $b$. -/
noncomputable abbrev lanczosT (k : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  Lanczos.tridiagExt (Matrix.toEuclideanLin A) b k

/-- The $k \times k$ tridiagonal Lanczos matrix $T_k$ of [fong2012cg], which is `Lanczos.tridiag` of
`Matrix.toEuclideanLin A` and $b$. -/
noncomputable abbrev lanczosTsq (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Lanczos.tridiag (Matrix.toEuclideanLin A) b k

/-- The termination step $\ell$ of the Lanczos process of [fong2012cg]: the grade of $b$ with
respect to $A$, that is, the dimension of the sum of all the Krylov subspaces
$\mathcal{K}_k(A, b)$. -/
noncomputable abbrev lanczosTerm : ℕ := Krylov.grade (Matrix.toEuclideanLin A) b

/-- The surface Krylov subspace $\mathcal{K}_k(A, b)$ is the backbone subspace `Krylov.subspace` of
`Matrix.toEuclideanLin A` and $b$. -/
theorem krylov_eq (k : ℕ) : krylov A b k = Krylov.subspace (Matrix.toEuclideanLin A) b k :=
  (Matrix.krylov_subspace_toEuclideanLin A b k).symm

/-- The Krylov subspaces are nested: if $k \le l$, then $\mathcal{K}_k(A, b) \subseteq
\mathcal{K}_l(A, b)$. -/
theorem krylov_mono {k l : ℕ} (h : k ≤ l) : krylov A b k ≤ krylov A b l := by
  rw [krylov_eq, krylov_eq]
  exact Krylov.subspace_mono _ _ h

/-- The Krylov subspace $\mathcal{K}_0(A, b)$ is $\{0\}$. This corresponds to the starting point
$x_0 = 0$ of the paper. -/
@[simp] theorem krylov_zero : krylov A b 0 = ⊥ := by rw [krylov_eq, Krylov.subspace_zero]

/-- **Section 1** of [fong2012cg], Krylov coordinates. For every $k$, a vector $x \in \mathbb{R}^n$
lies in $\mathcal{K}_k(A, b)$ if and only if $x = V_k y = \sum_{j=1}^{k} y_j v_j$ for some
$y \in \mathbb{R}^k$. -/
theorem mem_krylov_iff_exists_lanczos (k : ℕ) (x : Vec n) :
    x ∈ krylov A b k ↔ ∃ y : Fin k → ℝ, x = ∑ j, y j • lanczosVec A b j := by
  have hspan : krylov A b k =
      Submodule.span ℝ (Set.range fun j : Fin k => lanczosVec A b (j : ℕ)) := by
    rw [krylov_eq, ← Arnoldi.span_vec (Matrix.toEuclideanLin A) b k]
    congr 1
    ext v
    simp [lanczosVec, Set.mem_range, Fin.exists_iff]
  rw [hspan, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

section ZeroStart

variable {A b}

/-- The residual of the starting point $x_0 = 0$ is $b - A0 = b$. -/
theorem sub_mulVecE_zero : b - Matrix.toEuclideanLin A 0 = b := by rw [map_zero, sub_zero]

/-- For $x_0 = 0$, the backbone condition $x - x_0 \in \mathcal{K}_k(A, b - A x_0)$ is the condition
$x \in \mathcal{K}_k(A, b)$. -/
theorem sub_zero_mem_subspace_iff {k : ℕ} {x : Vec n} :
    x - 0 ∈ Krylov.subspace (Matrix.toEuclideanLin A) (b - Matrix.toEuclideanLin A 0) k
      ↔ x ∈ krylov A b k := by
  rw [sub_zero, sub_mulVecE_zero, krylov_eq]

end ZeroStart

/-! ### The Lanczos relation and termination -/

/-- **Section 1** of [fong2012cg], the Lanczos relation. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric and $b \in \mathbb{R}^n$. For every $k \in \mathbb{N}$, $$A V_k = V_{k+1}
\underline{T}_k,$$ that is, $A (V_k y) = V_{k+1} (\underline{T}_k y)$ for every
$y \in \mathbb{R}^k$.

The relation is stated for every $k$, also beyond the termination step $\ell$: there the extra
Lanczos vectors are $0$, and both sides still agree. The matrix $V_k$ appears through the sum
$\sum_j y_j v_j$, and $\underline{T}_k$ is `FongSaunders.lanczosT`. -/
theorem lanczos_relation (hA : A.IsSymm) (k : ℕ) (y : Fin k → ℝ) :
    A ⬝ (∑ j, y j • lanczosVec A b j) =
      ∑ i : Fin (k + 1), (lanczosT A b k).mulVec y i • lanczosVec A b i := by
  have h := Arnoldi.apply_sum (Matrix.toEuclideanLin A) b k y
  rw [Lanczos.hessenberg_eq_map_tridiagExt b (isSymmetric_toEuclideanLin hA) k] at h
  simpa [lanczosVec, lanczosT, Matrix.map_apply, Matrix.mulVec, dotProduct] using h

/-- **Section 1** of [fong2012cg], termination of the Lanczos relation. Let $A$ be symmetric, and
let $\ell$ be the termination step of the Lanczos process. Then the Lanczos relation closes up:
$$A V_\ell = V_\ell T_\ell,$$ that is, $A (V_\ell y) = V_\ell (T_\ell y)$ for every
$y \in \mathbb{R}^\ell$.

The matrix $T_\ell$ is `FongSaunders.lanczosTsq` at the step `FongSaunders.lanczosTerm A b`. -/
theorem lanczos_relation_term (hA : A.IsSymm) (y : Fin (lanczosTerm A b) → ℝ) :
    A ⬝ (∑ j, y j • lanczosVec A b j) =
      ∑ i, (lanczosTsq A b (lanczosTerm A b)).mulVec y i • lanczosVec A b i := by
  have h := Lanczos.apply_sum_grade b (isSymmetric_toEuclideanLin hA) y
  simpa [lanczosVec, lanczosTsq, lanczosTerm, Matrix.map_apply, Matrix.mulVec, dotProduct]
    using h

/-- **Section 1** of [fong2012cg], orthonormality. For every $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, the Lanczos vectors $v_1, \dots, v_\ell$ up to the termination step $\ell$
are orthonormal.

No symmetry of $A$ is needed, since the vectors come from the Gram–Schmidt process. -/
theorem lanczosVec_orthonormal :
    Orthonormal ℝ fun j : Fin (lanczosTerm A b) => lanczosVec A b (j : ℕ) :=
  Arnoldi.orthonormal (Matrix.toEuclideanLin A) b

/-- **Section 1** of [fong2012cg], the Lanczos basis. For every $k \in \mathbb{N}$,
$$\operatorname{span}\{v_1, \dots, v_k\} = \mathcal{K}_k(A, b).$$

The vectors are `FongSaunders.lanczosVec A b j` for $j < k$. -/
theorem span_lanczosVec (k : ℕ) :
    Submodule.span ℝ (lanczosVec A b '' Set.Iio k) = krylov A b k := by
  rw [krylov_eq]
  exact Arnoldi.span_vec (Matrix.toEuclideanLin A) b k

/-- **Section 1** of [fong2012cg], termination. The Lanczos process for
$A \in \mathbb{R}^{n \times n}$ and $b$ terminates at a step $\ell \le n$. -/
theorem lanczosTerm_le : lanczosTerm A b ≤ n := by
  have h := Krylov.grade_le_finrank (Matrix.toEuclideanLin A) b
  rwa [finrank_euclideanSpace_fin] at h

/-! ### The exact solution $x^*$ -/

/-- **Section 1** of [fong2012cg], the exact solution. If $A \in \mathbb{R}^{n \times n}$ is
positive definite, then for every $b \in \mathbb{R}^n$ the system $Ax = b$ has exactly one
solution $x \in \mathbb{R}^n$. -/
theorem existsUnique_solution {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b : Vec n) :
    ∃! x : Vec n, A ⬝ x = b := by
  have hinj : Function.Injective (Matrix.toEuclideanLin A) :=
    (isSymmetricCoercive_of_posDef hA).isCoercive.injective
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.1 hinj b
  exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩

/-- **Section 1** of [fong2012cg], the exact solution. The vector $x^* = A^{-1} b$.

The inverse is Mathlib's `Matrix.inv`, which is $0$ for a singular matrix. For positive definite
$A$, `FongSaunders.mulVecE_xstar` shows $Ax^* = b$, and `FongSaunders.xstar_unique` shows that
$x^*$ is the only solution. -/
noncomputable def xstar : Vec n := A⁻¹ ⬝ b

variable {A b}

/-- If $A$ is positive definite, then $A x^* = b$. -/
@[simp] theorem mulVecE_xstar (hA : A.PosDef) : A ⬝ xstar A b = b := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have h : A ⬝ xstar A b = (A * A⁻¹) ⬝ b := by
    change Matrix.toEuclideanLin A (Matrix.toEuclideanLin A⁻¹ b)
      = Matrix.toEuclideanLin (A * A⁻¹) b
    rw [Matrix.toEuclideanLin_mul]; rfl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ⬝ b = b := by
    change Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) b = b
    rw [Matrix.toEuclideanLin_one]; rfl
  rw [h, Matrix.mul_nonsing_inv A hdet, h1]

/-- If $A$ is positive definite and $Ax = b$, then $x = x^*$. -/
theorem xstar_unique (hA : A.PosDef) {x : Vec n} (h : A ⬝ x = b) : x = xstar A b :=
  (isSymmetricCoercive_of_posDef hA).isCoercive.injective (h.trans (mulVecE_xstar hA).symm)

end FongSaunders
