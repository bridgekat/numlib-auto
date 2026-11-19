/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Block
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Section02

/-!
# Saad, Section 6.12: Block Krylov methods

This module formalizes Section 6.12 of [saad2003iterative], on Krylov methods that start from a
block $V_1 = [v_1, \dots, v_p]$ of $p$ vectors instead of one vector. The block Krylov subspace is
$\mathcal{K}_m(A, V_1) = \mathcal{K}_m(A, v_1) + \dots + \mathcal{K}_m(A, v_p)$. The block Arnoldi
processes (Algorithms 6.22 and 6.23) orthogonalize one block of $p$ vectors at a time. Ruhe's
variant (Algorithm 6.24) orthonormalizes the block Krylov sequence $v_1, \dots, v_p, Av_1, \dots,
Av_p, A^2 v_1, \dots$ one vector at a time, and its coefficients satisfy the band relation
$AV_m = V_{m+p} \bar H_m$ of (6.130), with a band Hessenberg matrix $\bar H_m$ of size
$(m + p) \times m$. Block FOM and block GMRES apply the Galerkin and the minimal-residual conditions
to each right-hand side over the space that these vectors span, and (6.135)–(6.136) reduce them to
small banded systems. The proofs specialize `Numlib.Krylov.Block`.

## Main definitions

* Section 6.12, `SaadSparse.Chapter06.blockKrylov`: the block Krylov subspace
  $\mathcal{K}_m(A, V_1)$.
* Algorithm 6.24, `SaadSparse.Chapter06.ruhe`, `SaadSparse.Chapter06.ruheCoeff`: the vectors and the
  coefficients of Ruhe's variant of the block Arnoldi process.
* Equation (6.130), `SaadSparse.Chapter06.HbarBlock`, `SaadSparse.Chapter06.HBlock`: the band
  Hessenberg matrices $\bar H_m$ and $H_m$ of Ruhe's variant.
* Algorithms 6.22 and 6.23, `SaadSparse.Chapter06.IsBlockArnoldi`: the specification of a block
  Arnoldi process, an orthonormal sequence that spans the same flag as the block Krylov sequence.
* Section 6.12, `SaadSparse.Chapter06.IsBlockGMRES`, `SaadSparse.Chapter06.IsBlockFOM`: the block
  GMRES and block FOM approximations to one right-hand side.

## Main results

* Equation (6.129), `SaadSparse.Chapter06.equation_6_129`: the vectors of Algorithms 6.22–6.23 are
  orthonormal and satisfy the band Hessenberg relation.
* Section 6.12, `SaadSparse.Chapter06.ruhe_eq_blockArnoldiMGS`: Algorithms 6.23 and 6.24 are
  mathematically equivalent; their vectors agree up to unimodular scalars, and they span the same
  block Krylov subspaces at the multiples of $p$.
* Equation (6.130), `SaadSparse.Chapter06.equation_6_130`: $Av_k = \sum_{i \le k+p} h_{ik} v_i$ for
  Ruhe's variant, that is, $AV_m = V_{m+p} \bar H_m$.
* Equations (6.135)–(6.136), `SaadSparse.Chapter06.equation_6_136`: the residual of $X_0 + V_m Y$ is
  $V_{m+p}(E_1 R - \bar H_m Y)$, and its norm is that of the small vector.
* Section 6.12, `SaadSparse.Chapter06.blockFOM_iff`, `SaadSparse.Chapter06.blockGMRES_iff`: block
  FOM is the square band system $H_m y = \bar g^{(i)}$, and block GMRES is the least-squares problem
  $\min_y \|\bar g^{(i)} - \bar H_m y\|_2$.

## Conventions

* A block of the book, an $n \times p$ matrix such as $V_1$, the right-hand sides $B$ or the initial
  guesses $X_0$, is given by the family of its columns, of type `Fin p → EuclideanSpace 𝕜 (Fin n)`.
  `SaadSparse.Chapter06.blockCols` turns a matrix into this family.
* Indices are $0$-based, as elsewhere in Chapter 6: `SaadSparse.Chapter06.ruhe A v j` is the book's
  $v_{j+1}$, and `SaadSparse.Chapter06.ruheCoeff A v i j` is its $h_{i+1,j+1}$.

## Implementation notes

* Algorithms 6.22 and 6.23 are given by their specification, not by an implementation, because the
  book leaves the QR factorization of a block unspecified. The specification
  `SaadSparse.Chapter06.IsBlockArnoldi` asks for an orthonormal sequence indexed by all of
  $\mathbb{N}$. No such sequence exists in $\mathbb{K}^n$, so `SaadSparse.Chapter06.equation_6_129`
  and `SaadSparse.Chapter06.ruhe_eq_blockArnoldiMGS`, which assume it, are vacuous as stated. The
  results on Ruhe's variant and on block FOM and block GMRES do not assume it.
* The book's "mathematical equivalence" of Algorithms 6.23 and 6.24 "when $m$ is a multiple of $p$"
  is read as follows: a sequence with this property is Ruhe's sequence under the Gram–Schmidt sign
  convention, agrees with it up to unimodular scalars in general, and spans the block Krylov
  subspace at every multiple of $p$.
* The band relation (6.129)–(6.130) is the backbone's `Krylov.BandRelation`, of bandwidth $p$, not
  `Krylov.HessenbergRelation`, whose bandwidth is $1$.
* Block FOM and block GMRES are `IsGalerkin` and `IsMinResidual` over $x_0^{(i)} +
  \operatorname{span}\{v_1, \dots, v_m\}$, one right-hand side at a time.

## Deviations from the source

* **Reading.** Ruhe's definition uses raw block powers and can continue through dependent columns.
  See `SaadSparse.Chapter06.ruhe`.
* **Generalization.** The Ruhe band relation includes zero columns produced by raw-sequence
  dependence. See `SaadSparse.Chapter06.ruheCoeff`, `SaadSparse.Chapter06.HbarBlock`,
  `SaadSparse.Chapter06.HBlock`, `SaadSparse.Chapter06.equation_6_130`.
* **Scope.** The block Arnoldi comparison assumes an infinite orthonormal sequence and is vacuous in
  finite dimension. See `SaadSparse.Chapter06.IsBlockArnoldi`,
  `SaadSparse.Chapter06.equation_6_129`, `SaadSparse.Chapter06.ruhe_eq_blockArnoldiMGS`.
* **Generalization.** Ruhe's block Krylov span identity persists through dependent columns. See
  `SaadSparse.Chapter06.span_ruhe_eq_blockKrylov`.
* **Scope.** The initial residual coefficient theorem uses span membership and a single right-hand
  side. See `SaadSparse.Chapter06.exists_initial_residual_coeffs`.
* **Reading.** The residual and FOM formulas use one right-hand side and general initial block
  coefficients. See `SaadSparse.Chapter06.equation_6_136`, `SaadSparse.Chapter06.blockFOM_iff`.
* **Scope.** The block GMRES definitions and coordinate theorem state minimality without a
  uniqueness claim. See `SaadSparse.Chapter06.IsBlockGMRES`, `SaadSparse.Chapter06.blockGMRES_iff`.

## Not formalized

* **The Givens elimination of block GMRES**, with $p$ rotations per column. The book states no
  result about it.
-/

open scoped ComplexOrder

namespace SaadSparse.Chapter06

section Block

variable {n p : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The block data -/

/-- The columns of an $n \times p$ block $B$ of the book, as a family of $p$ vectors of
$\mathbb{K}^n$. The block Krylov statements below take such families, which carry the same data
as the matrix. -/
noncomputable abbrev blockCols (B : Matrix (Fin n) (Fin p) 𝕜) (i : Fin p) : 𝔼 :=
  WithLp.toLp 2 fun j => B j i

/-- **Section 6.12** of [saad2003iterative], the **block Krylov subspace**. For an $n \times n$
matrix $A$ and vectors $v_1, \dots, v_p$,
$$\mathcal{K}_m(A, V_1) = \mathcal{K}_m(A, v_1) + \dots + \mathcal{K}_m(A, v_p),$$
the span of the vectors $A^j v_i$ with $j < m$.

This is the backbone's `Krylov.blockSubspace`. -/
noncomputable abbrev blockKrylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Submodule 𝕜 𝔼 :=
  Krylov.blockSubspace (op A) v m

/-! ### Algorithm 6.24: Ruhe's variant -/

/-- **Algorithm 6.24** of [saad2003iterative] (Ruhe's variant of the block Arnoldi process). For an
$n \times n$ matrix $A$ and vectors $v_1, \dots, v_p$, the sequence of vectors obtained by
orthonormalizing the block Krylov sequence
$$v_1, \dots, v_p, Av_1, \dots, Av_p, A^2 v_1, \dots$$
one vector at a time by the Gram–Schmidt process. The book forms each vector after the first $p$
from $A$ applied to the vector $p$ places earlier, orthogonalized against all vectors computed
so far and normalized. Without breakdown this gives the same vectors.

`SaadSparse.Chapter06.ruhe A v j` is the book's $v_{j+1}$ before breakdown. This is the
backbone's `BlockArnoldi.vec`.

**Reading.** Lean applies normalized Gram–Schmidt to the raw block Krylov sequence, including the
supplied initial block. The source starts with an orthonormal block and applies $A$ to the computed
vector $p$ places earlier. The construction agrees prior to dependence. The printed line 9 divides
by the norm without a zero test. Lean gives zero at a dependent raw column and can give nonzero
vectors at later independent columns.
-/
noncomputable abbrev ruhe (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) : ℕ → 𝔼 :=
  BlockArnoldi.vec (op A) v

/-- **Algorithm 6.24** of [saad2003iterative], lines 5 and 9. The coefficients
$h_{ik} = (Av_k, v_i)$ of Ruhe's variant.

This is the backbone's `BlockArnoldi.coeff`, with $0$-based indices.

**Generalization.** The coefficients are inner products with the normalized raw-sequence vectors.
Their band identities hold at every index, including dependent columns represented by zero. The
source derives them for the orthonormal vectors actually computed by the displayed loop.
-/
noncomputable abbrev ruheCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (i k : ℕ) : 𝕜 :=
  BlockArnoldi.coeff (op A) v i k

/-- **Equation (6.130)** of [saad2003iterative]. The $(m + p) \times m$ band Hessenberg matrix
$\bar H_m = (h_{ik})$ of the coefficients of Ruhe's variant.

**Generalization.** The coefficients are inner products with the normalized raw-sequence vectors.
Their band identities hold at every index, including dependent columns represented by zero. The
source derives them for the orthonormal vectors actually computed by the displayed loop.
-/
noncomputable abbrev HbarBlock (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Matrix (Fin (m + p)) (Fin m) 𝕜 :=
  BlockArnoldi.hessenberg (op A) v m

/-- **Section 6.12** of [saad2003iterative]. The square $m \times m$ band Hessenberg matrix $H_m$ of
Ruhe's variant, the first $m$ rows of $\bar H_m$.

**Generalization.** The coefficients are inner products with the normalized raw-sequence vectors.
Their band identities hold at every index, including dependent columns represented by zero. The
source derives them for the orthonormal vectors actually computed by the displayed loop.
-/
noncomputable abbrev HBlock (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  BlockArnoldi.hessenbergSq (op A) v m

/-- **Algorithms 6.22 and 6.23** of [saad2003iterative], by their specification. A sequence
$u_0, u_1, \dots$ of vectors of $\mathbb{K}^n$ **is a block Arnoldi basis** for $A$ and
$v_1, \dots, v_p$ if it is orthonormal and, for every $k$, its first $k + 1$ vectors span the
same space as the first $k + 1$ vectors of the block Krylov sequence $v_1, \dots, v_p, Av_1,
\dots, Av_p, A^2 v_1, \dots$.

The block algorithms of the book orthogonalize a block of $p$ vectors at a time and then factor
the result as $W_j = V_{j+1} H_{j+1,j}$. The QR factorization is left unspecified, and the
specification is meant to cover every choice of it. The condition is imposed for every
$k \in \mathbb{N}$, so it describes a process that never breaks down. Since an orthonormal
family in $\mathbb{K}^n$ has at most $n$ members, no sequence indexed by all of $\mathbb{N}$
satisfies it, and the results that assume it, `SaadSparse.Chapter06.equation_6_129` and
`SaadSparse.Chapter06.ruhe_eq_blockArnoldiMGS`, are vacuous as stated. The definition is the
backbone's `IsBlockArnoldiBasis`.

**Reading.** The specification requires orthonormality and equality of the prefix spans for an
infinite sequence in a finite-dimensional space. No such sequence exists. Consequently the two
theorems taking this predicate as a hypothesis do not establish the source claims for a finite block
Arnoldi run. The Hessenberg formula also selects the Gram–Schmidt phase convention.
-/
def IsBlockArnoldi (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (u : ℕ → 𝔼) : Prop :=
  IsBlockArnoldiBasis (op A) v u

/-- **Equation (6.129)** of [saad2003iterative]. Let $u$ be a block Arnoldi basis for $A$ and
$v_1, \dots, v_p$ (Algorithms 6.22–6.23), and assume that $(u_k, s_k) > 0$ for every $k$, where
$s_k$ is the $k$-th vector of the block Krylov sequence. Then:

1. the vectors $u_k$ are orthonormal, so each block $V_i$ is orthonormal and the blocks are
   mutually orthogonal;
2. $Au_k = \sum_{i \le k+p} h_{ik} u_i$ for every $k$, with the coefficients $h_{ik}$ of Ruhe's
   variant;
3. $h_{ik} = 0$ for $i > k + p$;
4. $AU_m y = U_{m+p} \bar H_m y$ for every $m$ and every $y \in \mathbb{K}^m$.

Vector by vector, this is the band Hessenberg relation
$AU_m = U_m H_m + V_{m+1} H_{m+1,m} E_m^T$ of the book. The hypothesis $(u_k, s_k) > 0$ is the
Gram–Schmidt sign convention on the block QR factorization, which Algorithm 6.23 (modified
Gram–Schmidt) satisfies. Without it, the same conclusion holds after the unimodular rescaling of
`SaadSparse.Chapter06.ruhe_eq_blockArnoldiMGS`.

**Reading.** The specification requires orthonormality and equality of the prefix spans for an
infinite sequence in a finite-dimensional space. No such sequence exists. Consequently the two
theorems taking this predicate as a hypothesis do not establish the source claims for a finite block
Arnoldi run. The Hessenberg formula also selects the Gram–Schmidt phase convention.
-/
theorem equation_6_129 {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin p → 𝔼} {u : ℕ → 𝔼}
    (hu : IsBlockArnoldi A v u)
    (hpos : ∀ k, 0 < inner 𝕜 (u k) (Krylov.blockSeq (op A) v k)) :
    Orthonormal 𝕜 u ∧
      (∀ k, op A (u k) = ∑ i ∈ Finset.range (k + p + 1), ruheCoeff A v i k • u i) ∧
      (∀ i k, k + p < i → ruheCoeff A v i k = 0) ∧
      ∀ (m : ℕ) (y : Fin m → 𝕜),
        op A (∑ j, y j • u (j : ℕ)) =
          ∑ i : Fin (m + p), (HbarBlock A v m).mulVec y i • u (i : ℕ) := by
  have hue : u = ruhe A v := funext fun k => BlockArnoldi.blockVec_eq_vec hu (hpos k)
  subst hue
  exact ⟨hu.orthonormal, BlockArnoldi.apply_vec (op A) v,
    fun _ _ h => BlockArnoldi.coeff_eq_zero_of_lt (op A) v h,
    fun m y => (BlockArnoldi.hessenbergRelation (op A) v).apply_sum m y⟩

/-- **Section 6.12** of [saad2003iterative], the mathematical equivalence of Algorithms 6.23 and
6.24. Let $u$ be a block Arnoldi basis for $A$ and $v_1, \dots, v_p$, for any choice of the QR
factorization. Then:

1. if $(u_k, s_k) > 0$, where $s_k$ is the $k$-th vector of the block Krylov sequence, then
   $u_k$ is the $k$-th vector of Ruhe's variant;
2. for every $k$, $u_k = \varepsilon v_k$ for a scalar $\varepsilon$ with $|\varepsilon| = 1$,
   where $v_k$ is the $k$-th vector of Ruhe's variant;
3. for every $m$, the first $mp$ vectors $u_k$ span the block Krylov subspace
   $\mathcal{K}_m(A, V_1)$.

So, when the number of vectors is a multiple of $p$, the two algorithms build the same space.

**Reading.** The specification requires orthonormality and equality of the prefix spans for an
infinite sequence in a finite-dimensional space. No such sequence exists. Consequently the two
theorems taking this predicate as a hypothesis do not establish the source claims for a finite block
Arnoldi run. The Hessenberg formula also selects the Gram–Schmidt phase convention.
-/
theorem ruhe_eq_blockArnoldiMGS {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin p → 𝔼} {u : ℕ → 𝔼}
    (hu : IsBlockArnoldi A v u) :
    (∀ k, 0 < inner 𝕜 (u k) (Krylov.blockSeq (op A) v k) → u k = ruhe A v k) ∧
      (∀ k, ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u k = ε • ruhe A v k) ∧
      ∀ m : ℕ, Submodule.span 𝕜 (u '' Set.Iio (m * p)) = blockKrylov A v m :=
  ⟨fun _ hpos => BlockArnoldi.blockVec_eq_vec hu hpos,
    hu.exists_norm_eq_one_smul_vec, hu.span_eq_blockSubspace⟩

/-- **Equation (6.130)** of [saad2003iterative]. For Ruhe's variant of the block Arnoldi process,
$$Av_k = \sum_{i=1}^{k+p} h_{ik} v_i \quad\text{and}\quad h_{ik} = 0 \text{ for } i > k + p,$$
that is, $AV_m = V_{m+p} \bar H_m$: for every $m$ and $y \in \mathbb{K}^m$,
$A V_m y = V_{m+p} \bar H_m y$.

The indices in the Lean statement are $0$-based.

**Generalization.** The coefficients are inner products with the normalized raw-sequence vectors.
Their band identities hold at every index, including dependent columns represented by zero. The
source derives them for the orthonormal vectors actually computed by the displayed loop.
-/
theorem equation_6_130 (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) :
    (∀ k, op A (ruhe A v k) =
        ∑ i ∈ Finset.range (k + p + 1), ruheCoeff A v i k • ruhe A v i) ∧
      (∀ i k, k + p < i → ruheCoeff A v i k = 0) ∧
      ∀ (m : ℕ) (y : Fin m → 𝕜),
        op A (∑ j, y j • ruhe A v (j : ℕ)) =
          ∑ i : Fin (m + p), (HbarBlock A v m).mulVec y i • ruhe A v (i : ℕ) :=
  ⟨BlockArnoldi.apply_vec (op A) v, fun _ _ h => BlockArnoldi.coeff_eq_zero_of_lt (op A) v h,
    fun m y => (BlockArnoldi.hessenbergRelation (op A) v).apply_sum m y⟩

/-- **Section 6.12** of [saad2003iterative]. For every $m$, the first $mp$ vectors of Ruhe's variant
span the block Krylov subspace $\mathcal{K}_m(A, V_1)$. So Algorithm 6.24 reaches the spaces of
Algorithm 6.22 exactly at the multiples of $p$.

**Generalization.** The span relation holds for the raw-sequence definition even when some vectors
are zero because the orthogonalization has found a dependent column.
-/
theorem span_ruhe_eq_blockKrylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin p → 𝔼) (m : ℕ) :
    Submodule.span 𝕜 (ruhe A v '' Set.Iio (m * p)) = blockKrylov A v m :=
  BlockArnoldi.span_vec_eq_blockSubspace (op A) v m

/-! ### Block FOM and block GMRES -/

/-- **Section 6.12** of [saad2003iterative], block GMRES. For the $i$-th right-hand side $b^{(i)}$
and initial guess $x_0^{(i)}$, a vector $x$ is a **block GMRES approximation** after $m$ steps
if it minimizes the residual norm $\|b^{(i)} - Ax\|_2$ over $x_0^{(i)} +
\operatorname{span}\{v_1, \dots, v_m\}$, where $v_1, \dots, v_m$ are the vectors of Ruhe's
variant.

For $m = kp$, the search space is $x_0^{(i)} + \mathcal{K}_k(A, V_1)$
(`SaadSparse.Chapter06.span_ruhe_eq_blockKrylov`).

**Reading.** Lean specifies minimization of the individual residual and its coordinate
characterization. The source calls the minimizing vector unique, which requires injectivity of the
matrix on the trial space. Lean does not assume this or assert a uniqueness conclusion.
-/
def IsBlockGMRES (A : Matrix (Fin n) (Fin n) 𝕜) (B X₀ v : Fin p → 𝔼) (m : ℕ) (i : Fin p)
    (x : 𝔼) : Prop :=
  IsMinResidual (op A) (B i) (X₀ i) (Submodule.span 𝕜 (ruhe A v '' Set.Iio m)) x

/-- **Section 6.12** of [saad2003iterative], block FOM. For the $i$-th right-hand side $b^{(i)}$ and
initial guess $x_0^{(i)}$, a vector $x$ is a **block FOM approximation** after $m$ steps if it
satisfies the Galerkin condition over $x_0^{(i)} + \operatorname{span}\{v_1, \dots, v_m\}$: $x$
lies in this affine space and $b^{(i)} - Ax$ is orthogonal to
$\operatorname{span}\{v_1, \dots, v_m\}$, where $v_1, \dots, v_m$ are the vectors of Ruhe's
variant. -/
def IsBlockFOM (A : Matrix (Fin n) (Fin n) 𝕜) (B X₀ v : Fin p → 𝔼) (m : ℕ) (i : Fin p)
    (x : 𝔼) : Prop :=
  IsGalerkin (op A) (B i) (X₀ i) (Submodule.span 𝕜 (ruhe A v '' Set.Iio m)) x

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B X₀ v : Fin p → EuclideanSpace 𝕜 (Fin n)}
  {g : ℕ → 𝕜} {m : ℕ} {i : Fin p}

/-- **Section 6.12** of [saad2003iterative], the block QR factorization $R_0 = V_p R$ of the initial
residual block. If the $i$-th initial residual $b^{(i)} - Ax_0^{(i)}$ lies in
$\mathcal{K}_1(A, V_1)$, then it is a linear combination $\sum_{k < p} g_k v_k$ of the first $p$
vectors of Ruhe's variant.

This is the form of the hypothesis on the initial residual in (6.135)–(6.136).

**Reading.** The result extracts a coefficient vector for a single residual that lies in the first
block span. The source factors the whole residual block with orthonormal columns and an upper
triangular factor. This theorem proves coefficient existence without that triangular structure.
-/
theorem exists_initial_residual_coeffs (hr : B i - op A (X₀ i) ∈ blockKrylov A v 1) :
    ∃ g : ℕ → 𝕜, B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k :=
  BlockArnoldi.exists_coeffs_of_mem_blockSubspace_one (op A) v hr

/-- **Equations (6.135)–(6.136)** of [saad2003iterative]. Assume that the first $m + p$ vectors
$v_k$ of Ruhe's variant are orthonormal, that is, the process has not broken down, and that the
$i$-th initial residual is $b^{(i)} - Ax_0^{(i)} = \sum_{k < p} g_k v_k$. Let
$\bar g^{(i)} \in \mathbb{K}^{m+p}$ have the entries $g_0, \dots, g_{p-1}$ followed by zeros.
Then for every $y \in \mathbb{K}^m$ the residual of $x = x_0^{(i)} + V_m y$ is
$$b^{(i)} - Ax = V_{m+p} \left(\bar g^{(i)} - \bar H_m y\right),$$
and therefore $\|b^{(i)} - Ax\|_2 = \|\bar g^{(i)} - \bar H_m y\|_2$.

In the book, $\bar g^{(i)} = E_1 R e_i$ and the residual block is
$B - AX = V_{m+p}(E_1 R - \bar H_m Y)$. Here $\bar g^{(i)}$ is
`Krylov.firstBlockVec g p (m + p)`.

**Reading.** The reduction is stated for one right-hand side, with an explicit orthonormality
hypothesis on the finite prefix. Its coefficient vector can have nonzeros anywhere in the first $p$
entries, unlike the column-dependent triangular pattern of the source's QR factor.
-/
theorem equation_6_136 (hon : Orthonormal 𝕜 fun k : Fin (m + p) => ruhe A v (k : ℕ))
    (hr : B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k) (y : Fin m → 𝕜) :
    (B i - op A (X₀ i + ∑ j, y j • ruhe A v (j : ℕ)) =
        ∑ k : Fin (m + p),
          ((Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec y :
            Fin (m + p) → 𝕜)) k • ruhe A v (k : ℕ)) ∧
      ‖B i - op A (X₀ i + ∑ j, y j • ruhe A v (j : ℕ))‖ =
        ‖(WithLp.toLp 2 (Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec y) :
          EuclideanSpace 𝕜 (Fin (m + p)))‖ :=
  ⟨BlockArnoldi.residual_eq (op A) v hr y, BlockArnoldi.norm_residual_eq (op A) v hon hr y⟩

/-- **Section 6.12** of [saad2003iterative], block FOM in coordinates. Assume that the first $m + p$
vectors of Ruhe's variant are orthonormal and that the $i$-th initial residual is
$\sum_{k < p} g_k v_k$. Then for $y \in \mathbb{K}^m$, the vector $x_0^{(i)} + V_m y$ is a block
FOM approximation if and only if $y$ solves the square band system
$$H_m y = \bar g^{(i)},$$
where $\bar g^{(i)} \in \mathbb{K}^m$ has the entries $g_k$ for $k < \min(p, m)$, followed by
zeros.

**Reading.** The reduction is stated for one right-hand side, with an explicit orthonormality
hypothesis on the finite prefix. Its coefficient vector can have nonzeros anywhere in the first $p$
entries, unlike the column-dependent triangular pattern of the source's QR factor.
-/
theorem blockFOM_iff (hon : Orthonormal 𝕜 fun k : Fin (m + p) => ruhe A v (k : ℕ))
    (hr : B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k) (y : Fin m → 𝕜) :
    IsBlockFOM A B X₀ v m i (X₀ i + ∑ j, y j • ruhe A v (j : ℕ)) ↔
      (HBlock A v m).mulVec y = Krylov.firstBlockVec g p m :=
  BlockArnoldi.isGalerkin_iff_mulVec_eq (op A) v hon hr y

/-- **Equation (6.136)** of [saad2003iterative], block GMRES in coordinates. Assume that the first
$m + p$ vectors of Ruhe's variant are orthonormal and that the $i$-th initial residual is
$\sum_{k < p} g_k v_k$. Then for $y \in \mathbb{K}^m$, the vector $x_0^{(i)} + V_m y$ is a block
GMRES approximation if and only if $y$ solves the banded least-squares problem
$$\min_{z \in \mathbb{K}^m} \left\|\bar g^{(i)} - \bar H_m z\right\|_2,$$
where $\bar g^{(i)} \in \mathbb{K}^{m+p}$ has the entries $g_0, \dots, g_{p-1}$ followed by
zeros.

**Reading.** Lean specifies minimization of the individual residual and its coordinate
characterization. The source calls the minimizing vector unique, which requires injectivity of the
matrix on the trial space. Lean does not assume this or assert a uniqueness conclusion.
-/
theorem blockGMRES_iff (hon : Orthonormal 𝕜 fun k : Fin (m + p) => ruhe A v (k : ℕ))
    (hr : B i - op A (X₀ i) = ∑ k ∈ Finset.range p, g k • ruhe A v k) (y : Fin m → 𝕜) :
    IsBlockGMRES A B X₀ v m i (X₀ i + ∑ j, y j • ruhe A v (j : ℕ)) ↔
      ∀ z : Fin m → 𝕜,
        ‖(WithLp.toLp 2 (Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec y) :
          EuclideanSpace 𝕜 (Fin (m + p)))‖ ≤
          ‖(WithLp.toLp 2 (Krylov.firstBlockVec g p (m + p) - (HbarBlock A v m).mulVec z) :
            EuclideanSpace 𝕜 (Fin (m + p)))‖ :=
  BlockArnoldi.isMinResidual_iff (op A) v hon hr y

end Block

end SaadSparse.Chapter06
