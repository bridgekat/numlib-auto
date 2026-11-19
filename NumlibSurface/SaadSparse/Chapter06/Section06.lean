/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Lanczos
import Numlib.Krylov.OrthogonalPolynomials
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.Hessenberg
import NumlibSurface.SaadSparse.Chapter06.Section03

/-!
# Saad, Section 6.6: The symmetric Lanczos algorithm

This module formalizes Section 6.6 of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric and let $v_1$ be a vector with $\|v_1\|_2 = 1$. The symmetric Lanczos algorithm (Algorithm
6.15) starts from $\beta_1 = 0$ and $v_0 = 0$, and at step $j = 1, 2, \dots$ computes
$w_j := A v_j - \beta_j v_{j-1}$, $\alpha_j := (w_j, v_j)$, $w_j := w_j - \alpha_j v_j$,
$\beta_{j+1} := \|w_j\|_2$ and $v_{j+1} := w_j / \beta_{j+1}$. Theorem 6.19 states that Arnoldi's
method applied to $A$ gives coefficients with $h_{ij} = 0$ for $i < j - 1$ and
$h_{j,j+1} = h_{j+1,j}$, so that $H_m$ is tridiagonal and symmetric. For this reason Algorithm 6.15
is Arnoldi's method for a symmetric matrix: it computes the same vectors, with $\alpha_j = h_{jj}$
and $\beta_{j+1} = h_{j+1,j}$, and the tridiagonal matrix $T_m = \operatorname{tridiag}(\beta_i,
\alpha_i, \beta_{i+1})$ of (6.84) is $H_m$.

Section 6.6.2 relates the algorithm to orthogonal polynomials. The form $\langle p, q
\rangle_{v_1} = (p(A) v_1, q(A) v_1)$ of (6.85) is an inner product on $\mathbb{P}_{m-1}$, the
polynomials of degree less than $m$, when $m \le \mu$, the grade of $v_1$. The map
$q \mapsto q(A) v_1$ is an isomorphism from $\mathbb{P}_{m-1}$ onto $\mathcal{K}_m$, and
$v_{i+1} = q_i(A) v_1$ for polynomials $q_i$ of degree $i$ that are orthogonal for (6.85). The
characteristic polynomial $p_{T_m}$ of $T_m$ minimizes $\|p(A) v_1\|_2$ among the monic polynomials
$p$ of degree $m$, and $p_{T_m}(A) v_1 = \beta_2 \beta_3 \cdots \beta_{m+1} v_{m+1}$. The proofs
specialize the backbone modules `Numlib.Krylov.Arnoldi`, `Numlib.Krylov.Lanczos`,
`Numlib.Krylov.OrthogonalPolynomials` and `Numlib.Eigen.RayleighRitz`, and the Arnoldi theory of
`NumlibSurface.SaadSparse.Chapter06.Section03`.

## Main definitions

* Algorithm 6.15, `SaadSparse.Chapter06.lanczosState`: the state of the symmetric Lanczos algorithm
  after $j$ steps. Its vectors $v_{j+1}$ and coefficients $\alpha_{j+1}$, $\beta_{j+1}$ are
  `SaadSparse.Chapter06.lanczosV`, `SaadSparse.Chapter06.lanczosAlpha` and
  `SaadSparse.Chapter06.lanczosBeta`.
* Equation (6.84), `SaadSparse.Chapter06.T`: the symmetric tridiagonal matrix $T_m =
  \operatorname{tridiag}(\beta_i, \alpha_i, \beta_{i+1})$.
* `SaadSparse.Chapter06.Tbar`: the $(m+1) \times m$ matrix $\bar T_m$, which is $T_{m+1}$ without
  its last column.
* Equation (6.85), `SaadSparse.Chapter06.polyInner`: the form $\langle p, q \rangle_{v_1} = (p(A)
  v_1, q(A) v_1)$ on polynomials.
* Section 6.6.2, `SaadSparse.Chapter06.lanczosPoly`: the Lanczos polynomials $q_i$ with
  $v_{i+1} = q_i(A) v_1$.

## Main results

* Theorem 6.19, `SaadSparse.Chapter06.theorem_6_19`: for a real symmetric matrix the Arnoldi
  coefficients satisfy (6.82) and (6.83), and every $H_m$ is tridiagonal and symmetric.
* Section 6.6.1, `SaadSparse.Chapter06.algorithm_6_15_eq_alg_6_2`: Algorithm 6.15 computes the
  vectors of Algorithm 6.2, with $\alpha_j = h_{jj}$ and $\beta_{j+1} = h_{j+1,j}$.
* Section 6.6.1, `SaadSparse.Chapter06.lanczosV_eq`: Algorithm 6.15 computes the vectors of
  Algorithm 6.1.
* Equation (6.84), `SaadSparse.Chapter06.T_eq_H`: $T_m = H_m$.
* Section 6.6.2, `SaadSparse.Chapter06.equation_6_85_isomorphism`: for $m \le \mu$, the map
  $q \mapsto q(A) v_1$ is a bijection from $\mathbb{P}_{m-1}$ onto $\mathcal{K}_m$.
* Section 6.6.2, `SaadSparse.Chapter06.equation_6_85_nondegenerate`: for $m \le \mu$, the form
  (6.85) is nondegenerate on $\mathbb{P}_{m-1}$.
* Section 6.6.2, `SaadSparse.Chapter06.equation_6_85_orthogonal_polynomials`: for $i < \mu$, $q_i$
  has degree $i$, $v_{i+1} = q_i(A) v_1$, and the $q_i$ are orthogonal for (6.85).
* Section 6.6.2, `SaadSparse.Chapter06.equation_6_85_charpoly_isMinOn`: $p_{T_m}$ minimizes
  $\|p(A) v_1\|_2$ among the monic polynomials of degree $m$.
* Section 6.6.2, `SaadSparse.Chapter06.equation_6_85_lanczos_charpoly`: $p_{T_m}(A) v_1 = \beta_2
  \beta_3 \cdots \beta_{m+1} v_{m+1}$.

## Conventions

* Indices of the Lanczos data start at $0$, as for the Arnoldi data of
  `NumlibSurface.SaadSparse.Chapter06.Section03`.
* The Lanczos vector `lanczosV A v₁ j` is $v_{j+1}$.
* The diagonal coefficient `lanczosAlpha A v₁ j` is $\alpha_{j+1}$.
* The off-diagonal coefficient `lanczosBeta A v₁ j` is $\beta_{j+1}$. Its value at $j = 0$ is
  $\beta_1 = 0$.
* The matrix $A$ acts on vectors as the operator `SaadSparse.Chapter06.op A`. The Krylov subspace
  $\mathcal{K}_m$ is `SaadSparse.Chapter06.krylov A v₁ m`, and the grade $\mu$ of $v_1$ is
  `SaadSparse.Chapter06.grade A v₁`.
* The vector $p(A) v$ is `Polynomial.aeval (op A) p v`, and $\mathbb{P}_{m-1}$ is
  `Polynomial.degreeLT 𝕜 m`.

## Implementation notes

* The definitions are polymorphic in the scalar field $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$
  (`RCLike 𝕜`). The general lemmas assume that the operator of $A$ is symmetric, that is, $A$ is
  Hermitian, and that $\|v_1\| = 1$. The numbered results are stated over $\mathbb{R}$ with $A$
  symmetric (`Matrix.IsSymm`), the generality of the source.
* The recurrence uses totalized division. After a breakdown all further vectors are $0$.
  The breakdown happens exactly at the grade of $v_1$
  (`SaadSparse.Chapter06.lanczosBeta_succ_eq_zero_iff`).
* `SaadSparse.Chapter06.lanczosAlpha` is the real part of the computed coefficient. For a Hermitian
  $A$ the coefficient is real (`SaadSparse.Chapter06.lanczosAlpha_eq_inner`).

## Deviations from the source

* **Reading.** The Lanczos state, vector and off-diagonal coefficient continue with zeros after
  breakdown. See `SaadSparse.Chapter06.lanczosStep`, `SaadSparse.Chapter06.lanczosStep_eq`,
  `SaadSparse.Chapter06.lanczosState`, `SaadSparse.Chapter06.lanczosState_succ`,
  `SaadSparse.Chapter06.lanczosV`, `SaadSparse.Chapter06.lanczosBeta`.
* **Generalization.** The Lanczos residual and coefficient formulas extend to the complex inner
  product. See `SaadSparse.Chapter06.lanczosStepAlpha`, `SaadSparse.Chapter06.lanczosStepAlpha_eq`,
  `SaadSparse.Chapter06.lanczosStepW`, `SaadSparse.Chapter06.lanczosStepW_eq`.
* **Reading.** The Lanczos diagonal accessor extracts a real coefficient. See
  `SaadSparse.Chapter06.lanczosAlpha`.
* **Generalization.** The Lanczos and Arnoldi comparisons extend to Hermitian matrices and the
  totalized sequences. See `SaadSparse.Chapter06.lanczosV_eq`,
  `SaadSparse.Chapter06.lanczosV_eq_arnoldiMGS`,
  `SaadSparse.Chapter06.lanczosAlpha_eq_arnoldiCoeff`,
  `SaadSparse.Chapter06.lanczosBeta_succ_eq_arnoldiCoeff`.
* **Reading.** The zero-norm test characterizes breakdown and subsequent indices. See
  `SaadSparse.Chapter06.lanczosBeta_succ_eq_zero_iff`.
* **Reading.** The tridiagonal and equivalence theorems quantify over the totalized coefficients.
  See `SaadSparse.Chapter06.theorem_6_19`, `SaadSparse.Chapter06.algorithm_6_15_eq_alg_6_2`.
* **Generalization.** The tridiagonal and Hessenberg arrays agree after mapping real coefficients
  into the field. See `SaadSparse.Chapter06.map_T_eq_H`, `SaadSparse.Chapter06.map_Tbar_eq_Hbar`.
* **Generalization.** The polynomial pairing is defined on all polynomials over the real or complex
  field. See `SaadSparse.Chapter06.polyInner`.
* **Generalization.** Polynomial evaluation is surjective even when the degree bound exceeds the
  grade. See `SaadSparse.Chapter06.polyToKrylov`, `SaadSparse.Chapter06.polyToKrylov_surjective`.
* **Reading.** A Lanczos polynomial is chosen at every index and has the prescribed degree below the
  grade. See `SaadSparse.Chapter06.lanczosPoly`, `SaadSparse.Chapter06.aeval_lanczosPoly`.
* **Scope.** The polynomial pairing theorem states nondegeneracy directly. See
  `SaadSparse.Chapter06.equation_6_85_nondegenerate`.
* **Reading.** The Lanczos polynomial orthogonality includes the totalized post-breakdown vectors.
  See `SaadSparse.Chapter06.equation_6_85_orthogonal_polynomials`.
* **Reading.** Characteristic-polynomial minimization is among monic polynomials of the same degree.
  See `SaadSparse.Chapter06.equation_6_85_charpoly_isMinOn`.
* **Reading.** The characteristic-polynomial vectors equal the Lanczos vectors multiplied by the
  subdiagonal product. See `SaadSparse.Chapter06.equation_6_85_lanczos_charpoly`.
-/

open Polynomial

namespace SaadSparse.Chapter06

/-- A state of Algorithm 6.15 at step $j$ (in the numbering of the book): the vectors $v_{j-1}$ and
$v_j$, the coefficient $\beta_j$, and the coefficient $\alpha_{j-1}$ of the previous step. After
$k$ passes from the start, the state is at step $k + 1$. -/
structure LanczosState (n : ℕ) (𝕜 : Type*) [RCLike 𝕜] where
  /-- The previous Lanczos vector $v_{j-1}$; it is $0$ at the start, the book's $v_0 = 0$. -/
  vPrev : EuclideanSpace 𝕜 (Fin n)
  /-- The current Lanczos vector $v_j$. -/
  v : EuclideanSpace 𝕜 (Fin n)
  /-- The coefficient $\beta_j$, the norm of the vector $w_{j-1}$ of the previous step; it is $0$ at
  the start, the book's $\beta_1 = 0$. -/
  beta : ℝ
  /-- The coefficient $\alpha_{j-1}$ computed on line 4 of the previous step; it is $0$ at the
  start. -/
  alpha : 𝕜

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.15 -/

/-- The coefficient $\alpha_j = (w_j, v_j)$ of line 4 of Algorithm 6.15, computed from a state at
step $j$, where $w_j = A v_j - \beta_j v_{j-1}$ is the vector of line 3.

**Generalization.** These expressions permit arbitrary complex states and use the inner product
linear in the candidate residual $w_j$, corresponding to $(w_j,v_j)$ with the book's convention. The
source works in real arithmetic.
-/
noncomputable def lanczosStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) : 𝕜 :=
  inner 𝕜 s.v (op A s.v - (s.beta : 𝕜) • s.vPrev)

/-- The vector $w_j = A v_j - \beta_j v_{j-1} - \alpha_j v_j$ after lines 3 and 5 of Algorithm 6.15,
computed from a state at step $j$.

**Generalization.** These expressions permit arbitrary complex states and use the inner product
linear in the candidate residual $w_j$, corresponding to $(w_j,v_j)$ with the book's convention. The
source works in real arithmetic.
-/
noncomputable def lanczosStepW (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    EuclideanSpace 𝕜 (Fin n) :=
  op A s.v - (s.beta : 𝕜) • s.vPrev - lanczosStepAlpha A s • s.v

/-- One pass through lines 3–7 of Algorithm 6.15, from the state at step $j$ to the state at step
$j + 1$: $w_j := A v_j - \beta_j v_{j-1}$, $\alpha_j := (w_j, v_j)$,
$w_j := w_j - \alpha_j v_j$, $\beta_{j+1} := \|w_j\|_2$ and $v_{j+1} := w_j / \beta_{j+1}$.

At a zero norm the new vector is $0$ by totalized division.

**Reading.** The source stops on a zero norm. The Lean step totalizes the reciprocal and returns a
zero new vector; the sequence is defined at all subsequent indices. The state and step are also
defined for complex matrices and without a unit-vector check.
-/
noncomputable def lanczosStep (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    LanczosState n 𝕜 :=
  { vPrev := s.v, v := ((‖lanczosStepW A s‖ : 𝕜))⁻¹ • lanczosStepW A s,
    beta := ‖lanczosStepW A s‖, alpha := lanczosStepAlpha A s }

/-- The coefficient `SaadSparse.Chapter06.lanczosStepAlpha` is $(A v_j - \beta_j v_{j-1}, v_j)$.

**Generalization.** These expressions permit arbitrary complex states and use the inner product
linear in the candidate residual $w_j$, corresponding to $(w_j,v_j)$ with the book's convention. The
source works in real arithmetic.
-/
theorem lanczosStepAlpha_eq (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    lanczosStepAlpha A s = inner 𝕜 s.v (op A s.v - (s.beta : 𝕜) • s.vPrev) := rfl

/-- The vector `SaadSparse.Chapter06.lanczosStepW` is $A v_j - \beta_j v_{j-1} - \alpha_j v_j$.

**Generalization.** These expressions permit arbitrary complex states and use the inner product
linear in the candidate residual $w_j$, corresponding to $(w_j,v_j)$ with the book's convention. The
source works in real arithmetic.
-/
theorem lanczosStepW_eq (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    lanczosStepW A s =
      op A s.v - (s.beta : 𝕜) • s.vPrev - lanczosStepAlpha A s • s.v := rfl

/-- One pass of Algorithm 6.15 gives the state with previous vector $v_j$, current vector
$w_j / \|w_j\|$, coefficient $\beta_{j+1} = \|w_j\|$ and coefficient $\alpha_j$.

**Reading.** The source stops on a zero norm. The Lean step totalizes the reciprocal and returns a
zero new vector; the sequence is defined at all subsequent indices. The state and step are also
defined for complex matrices and without a unit-vector check.
-/
theorem lanczosStep_eq (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    lanczosStep A s =
      { vPrev := s.v, v := ((‖lanczosStepW A s‖ : 𝕜))⁻¹ • lanczosStepW A s,
        beta := ‖lanczosStepW A s‖, alpha := lanczosStepAlpha A s } := rfl

/-- **Algorithm 6.15** of [saad2003iterative] (symmetric Lanczos). The state after $j$ passes of the
algorithm from the starting vector $v_1$, with $v_0 = 0$ and $\beta_1 = 0$; this is the state at
step $j + 1$.

**Reading.** The source stops on a zero norm. The Lean step totalizes the reciprocal and returns a
zero new vector; the sequence is defined at all subsequent indices. The state and step are also
defined for complex matrices and without a unit-vector check.
-/
noncomputable def lanczosState (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (j : ℕ) :
    LanczosState n 𝕜 :=
  (lanczosStep A)^[j] { vPrev := 0, v := v₁, beta := 0, alpha := 0 }

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n))

/-- **Algorithm 6.15** of [saad2003iterative], the Lanczos vectors. For a square matrix $A$ over
$\mathbb{K}$, a starting vector $v_1$ and $j \ge 0$, this is the vector $v_{j+1}$ computed by
$j$ passes of Algorithm 6.15.

Indices start at $0$: `lanczosV A v₁ 0 = v₁`. The book takes $\|v_1\|_2 = 1$. The definition
does not need it, and the results that compare the algorithm with Arnoldi's method assume it.

**Reading.** The source stops on a zero norm. The Lean step totalizes the reciprocal and returns a
zero new vector; the sequence is defined at all subsequent indices. The state and step are also
defined for complex matrices and without a unit-vector check.
-/
noncomputable def lanczosV (j : ℕ) : 𝔼 := (lanczosState A v₁ j).v

/-- The diagonal coefficient $\alpha_{j+1}$ of Algorithm 6.15, line 4: the real part of the
coefficient that the pass at step $j + 1$ computes. For a Hermitian $A$ this coefficient is real
(`SaadSparse.Chapter06.lanczosAlpha_eq_inner`).

**Reading.** The accessor extracts the real part of the stored inner product. In the source's real
setting this leaves the result unchanged; for an arbitrary complex state the underlying step
coefficient can be nonreal.
-/
noncomputable def lanczosAlpha (j : ℕ) : ℝ := RCLike.re (lanczosState A v₁ (j + 1)).alpha

/-- The off-diagonal coefficient $\beta_{j+1}$ of Algorithm 6.15: $\beta_1 = 0$ (line 1), and for
$j \ge 1$, $\beta_{j+1} = \|w_j\|_2$ is computed on line 6 of the pass at step $j$.

**Reading.** The source stops on a zero norm. The Lean step totalizes the reciprocal and returns a
zero new vector; the sequence is defined at all subsequent indices. The state and step are also
defined for complex matrices and without a unit-vector check.
-/
noncomputable def lanczosBeta (j : ℕ) : ℝ := (lanczosState A v₁ j).beta

/-- The first Lanczos vector is the starting vector $v_1$. -/
@[simp] theorem lanczosV_zero : lanczosV A v₁ 0 = v₁ := rfl

/-- The coefficient $\beta_1$ is $0$. -/
@[simp] theorem lanczosBeta_zero : lanczosBeta A v₁ 0 = 0 := rfl

/-- The state after $j + 1$ passes is one pass applied to the state after $j$ passes.

**Reading.** The source stops on a zero norm. The Lean step totalizes the reciprocal and returns a
zero new vector; the sequence is defined at all subsequent indices. The state and step are also
defined for complex matrices and without a unit-vector check.
-/
theorem lanczosState_succ (j : ℕ) :
    lanczosState A v₁ (j + 1) = lanczosStep A (lanczosState A v₁ j) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Identification with Arnoldi's method (Theorem 6.19 and Section 6.6.1) -/

/-- If the current vector of a state is the backbone Arnoldi vector of index $j$, and the computed
$\alpha$ and $w$ are the backbone ones, then one pass gives the state described by the backbone
data at index $j + 1$. -/
private theorem lanczosStep_of {s : LanczosState n 𝕜} {j : ℕ}
    (hvj : s.v = Arnoldi.vec (op A) v₁ j)
    (halpha : lanczosStepAlpha A s = Arnoldi.coeff (op A) v₁ j j)
    (hw : lanczosStepW A s = Arnoldi.w (op A) v₁ j) :
    lanczosStep A s =
      { vPrev := Arnoldi.vec (op A) v₁ j, v := Arnoldi.vec (op A) v₁ (j + 1),
        beta := Lanczos.beta (op A) v₁ j, alpha := Arnoldi.coeff (op A) v₁ j j } := by
  rw [lanczosStep_eq, hvj, halpha, hw, Arnoldi.vec_succ_eq]
  rfl

/-- For a Hermitian $A$ and $\|v_1\| = 1$, the state after $j + 1$ passes of Algorithm 6.15, in
terms of the backbone Arnoldi and Lanczos data. -/
private theorem lanczosState_succ_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosState A v₁ (j + 1) =
      { vPrev := Arnoldi.vec (op A) v₁ j, v := Arnoldi.vec (op A) v₁ (j + 1),
        beta := Lanczos.beta (op A) v₁ j, alpha := Arnoldi.coeff (op A) v₁ j j } := by
  have hvec0 : Arnoldi.vec (op A) v₁ 0 = v₁ :=
    (arnoldiCGS_eq_vec A v₁ hv 0).symm.trans (arnoldiCGS_zero A v₁)
  induction j with
  | zero =>
    have halpha : lanczosStepAlpha A (lanczosState A v₁ 0) = Arnoldi.coeff (op A) v₁ 0 0 := by
      rw [lanczosStepAlpha_eq, Arnoldi.coeff]
      change (inner 𝕜 v₁ (op A v₁ - ((0 : ℝ) : 𝕜) • (0 : 𝔼)) : 𝕜) = _
      rw [hvec0]
      simp
    rw [lanczosState_succ]
    refine lanczosStep_of A v₁ hvec0.symm halpha ?_
    rw [lanczosStepW_eq, halpha, Arnoldi.w, Finset.sum_range_one, hvec0]
    change op A v₁ - ((0 : ℝ) : 𝕜) • (0 : 𝔼) - Arnoldi.coeff (op A) v₁ 0 0 • v₁ = _
    simp
  | succ j ih =>
    have halpha : lanczosStepAlpha A (lanczosState A v₁ (j + 1))
        = Arnoldi.coeff (op A) v₁ (j + 1) (j + 1) := by
      rw [lanczosStepAlpha_eq, ih]
      change (inner 𝕜 (Arnoldi.vec (op A) v₁ (j + 1)) (op A (Arnoldi.vec (op A) v₁ (j + 1)) -
        ((Lanczos.beta (op A) v₁ j : ℝ) : 𝕜) • Arnoldi.vec (op A) v₁ j) : 𝕜) = _
      rw [inner_sub_right, inner_smul_right,
        Arnoldi.inner_vec_eq_zero (op A) v₁ (Nat.succ_ne_self j), mul_zero, sub_zero]
      rfl
    rw [lanczosState_succ]
    refine lanczosStep_of A v₁ (by rw [ih]) halpha ?_
    rw [lanczosStepW_eq, halpha, ih]
    change op A (Arnoldi.vec (op A) v₁ (j + 1)) -
      ((Lanczos.beta (op A) v₁ j : ℝ) : 𝕜) • Arnoldi.vec (op A) v₁ j -
      Arnoldi.coeff (op A) v₁ (j + 1) (j + 1) • Arnoldi.vec (op A) v₁ (j + 1) = _
    rw [Lanczos.w_succ_eq v₁ hA j, ← Lanczos.coe_alpha v₁ hA (j + 1)]
    abel

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and let $\|v_1\| = 1$. Then the vectors of
Algorithm 6.15 are the backbone Arnoldi vectors `Arnoldi.vec (op A) v₁`.

This is the remark of Section 6.6.1 that "this leads to the following form of the modified
Gram–Schmidt variant of Arnoldi's method": for a symmetric $A$ the inner loop of Algorithm 6.2
subtracts only the two terms $\alpha_j v_j$ and $\beta_j v_{j-1}$. -/
theorem lanczosV_eq_vec (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = Arnoldi.vec (op A) v₁ j := by
  cases j with
  | zero => exact ((arnoldiCGS_eq_vec A v₁ hv 0).symm.trans (arnoldiCGS_zero A v₁)).symm
  | succ j => rw [lanczosV, lanczosState_succ_eq A v₁ hA hv j]

/-- **Section 6.6.1** of [saad2003iterative], Algorithm 6.15 against Algorithm 6.1. Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian and let $\|v_1\|_2 = 1$. Then for every $j \ge 1$
the vector $v_j$ of Algorithm 6.15 is the vector $v_j$ of Algorithm 6.1 (Arnoldi's method with
classical Gram–Schmidt).

The vectors of Algorithm 6.1 are `SaadSparse.Chapter06.arnoldiCGS`. The proof identifies both
families with `Arnoldi.vec`.

**Generalization.** The exact comparison extends from real symmetric matrices to Hermitian matrices
and quantifies over the totalized sequences. The source compares generated vectors and coefficients
before either process stops.
-/
theorem lanczosV_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = arnoldiCGS A v₁ j := by
  rw [lanczosV_eq_vec A v₁ hA hv, arnoldiCGS_eq_vec A v₁ hv]

/-- Section 6.6.1: for a Hermitian $A$ and $\|v_1\| = 1$, Algorithm 6.15 computes the vectors of
Algorithm 6.2 (Arnoldi's method with modified Gram–Schmidt).

**Generalization.** The exact comparison extends from real symmetric matrices to Hermitian matrices
and quantifies over the totalized sequences. The source compares generated vectors and coefficients
before either process stops.
-/
theorem lanczosV_eq_arnoldiMGS (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = arnoldiMGS A v₁ j := by
  rw [lanczosV_eq A v₁ hA hv, arnoldiMGS_eq_arnoldiCGS A v₁ hv]

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, the coefficient $\alpha_j$ of Algorithm 6.15
is the diagonal Arnoldi coefficient $h_{jj}$.

**Generalization.** The exact comparison extends from real symmetric matrices to Hermitian matrices
and quantifies over the totalized sequences. The source compares generated vectors and coefficients
before either process stops.
-/
theorem lanczosAlpha_eq_arnoldiCoeff (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosAlpha A v₁ j : ℝ) : 𝕜) = arnoldiCoeff A v₁ j j := by
  rw [lanczosAlpha, lanczosState_succ_eq A v₁ hA hv, arnoldiCoeff_eq A v₁ hv]
  exact (Arnoldi.coeff_diag_re_of_isSymmetric hA v₁ j).symm

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, the coefficient $\alpha_j$ is the backbone
Lanczos coefficient `Lanczos.alpha`, the real part of $(A v_j, v_j)$. -/
theorem lanczosAlpha_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosAlpha A v₁ j = Lanczos.alpha (op A) v₁ j := by
  rw [lanczosAlpha, lanczosState_succ_eq A v₁ hA hv]
  rfl

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, the coefficient $\beta_{j+1}$ is the backbone
off-diagonal Lanczos coefficient `Lanczos.beta`, which is $h_{j+1,j} = \|w_j\|_2$. -/
theorem lanczosBeta_succ_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosBeta A v₁ (j + 1) = Lanczos.beta (op A) v₁ j := by
  rw [lanczosBeta, lanczosState_succ_eq A v₁ hA hv]

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, $\beta_{j+1} = h_{j+1,j}$.

**Generalization.** The exact comparison extends from real symmetric matrices to Hermitian matrices
and quantifies over the totalized sequences. The source compares generated vectors and coefficients
before either process stops.
-/
theorem lanczosBeta_succ_eq_arnoldiCoeff (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosBeta A v₁ (j + 1) : ℝ) : 𝕜) = arnoldiCoeff A v₁ (j + 1) j := by
  rw [lanczosBeta_succ_eq A v₁ hA hv, arnoldiCoeff_eq A v₁ hv, Lanczos.coe_beta]

/-- The coefficients $\beta_j$ of Algorithm 6.15 are nonnegative. -/
theorem lanczosBeta_nonneg (j : ℕ) : 0 ≤ lanczosBeta A v₁ j := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [lanczosBeta, lanczosState_succ, lanczosStep_eq]
    exact norm_nonneg _

/-- Breakdown. Let $A$ be Hermitian, $\|v_1\| = 1$ and $j \ge 1$. Then $\beta_{j+1} = 0$ if and only
if the grade $\mu$ of $v_1$ satisfies $\mu \le j$.

**Reading.** The source tests for the first zero norm and stops. Lean identifies all zero norms in
the totalized sequence as those at or after the grade.
-/
theorem lanczosBeta_succ_eq_zero_iff (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosBeta A v₁ (j + 1) = 0 ↔ grade A v₁ ≤ j + 1 := by
  rw [lanczosBeta_succ_eq A v₁ hA hv, Lanczos.beta_eq_zero_iff v₁, grade_eq]

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, the coefficient of line 4 of Algorithm 6.15 is
the Rayleigh quotient $\alpha_j = (A v_j, v_j)$. In particular $(A v_j, v_j)$ is real. -/
theorem lanczosAlpha_eq_inner (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosAlpha A v₁ j : ℝ) : 𝕜) = inner 𝕜 (lanczosV A v₁ j) (op A (lanczosV A v₁ j)) := by
  rw [lanczosAlpha_eq_arnoldiCoeff A v₁ hA hv, arnoldiCoeff, lanczosV_eq A v₁ hA hv]

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, $\beta_{j+1} = (A v_j, v_{j+1})$. -/
theorem lanczosBeta_succ_eq_inner (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosBeta A v₁ (j + 1) : ℝ) : 𝕜)
      = inner 𝕜 (lanczosV A v₁ (j + 1)) (op A (lanczosV A v₁ j)) := by
  rw [lanczosBeta_succ_eq_arnoldiCoeff A v₁ hA hv, arnoldiCoeff, lanczosV_eq A v₁ hA hv,
    lanczosV_eq A v₁ hA hv]

/-- The three-term recurrence of Algorithm 6.15 at the first step: for a Hermitian $A$ and
$\|v_1\| = 1$, $A v_1 = \alpha_1 v_1 + \beta_2 v_2$ (lines 3–7 with $\beta_1 = 0$ and
$v_0 = 0$). -/
theorem apply_lanczosV_zero (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) :
    op A (lanczosV A v₁ 0) = (lanczosAlpha A v₁ 0 : 𝕜) • lanczosV A v₁ 0 +
      (lanczosBeta A v₁ 1 : 𝕜) • lanczosV A v₁ 1 := by
  rw [lanczosV_eq_vec A v₁ hA hv, lanczosV_eq_vec A v₁ hA hv, lanczosAlpha_eq A v₁ hA hv,
    lanczosBeta_succ_eq A v₁ hA hv]
  exact Lanczos.apply_vec_zero v₁ hA

/-- The three-term recurrence of Algorithm 6.15, lines 3–7: for a Hermitian $A$, $\|v_1\| = 1$ and
$j \ge 1$,
$$A v_{j+1} = \beta_{j+1} v_j + \alpha_{j+1} v_{j+1} + \beta_{j+2} v_{j+2}.$$
-/
theorem apply_lanczosV (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (lanczosV A v₁ (j + 1)) = (lanczosBeta A v₁ (j + 1) : 𝕜) • lanczosV A v₁ j +
      (lanczosAlpha A v₁ (j + 1) : 𝕜) • lanczosV A v₁ (j + 1) +
      (lanczosBeta A v₁ (j + 2) : 𝕜) • lanczosV A v₁ (j + 2) := by
  have hb2 : lanczosBeta A v₁ (j + 2) = Lanczos.beta (op A) v₁ (j + 1) :=
    lanczosBeta_succ_eq A v₁ hA hv (j + 1)
  rw [lanczosV_eq_vec A v₁ hA hv, lanczosV_eq_vec A v₁ hA hv, lanczosV_eq_vec A v₁ hA hv,
    lanczosAlpha_eq A v₁ hA hv, lanczosBeta_succ_eq A v₁ hA hv j, hb2]
  exact Lanczos.apply_vec v₁ hA j

/-- For a Hermitian $A$ and $\|v_1\| = 1$, the Lanczos vectors are orthogonal: $(v_i, v_j) = 0$ for
$i \ne j$. -/
theorem inner_lanczosV_eq_zero (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (lanczosV A v₁ i) (lanczosV A v₁ j) = 0 := by
  rw [lanczosV_eq A v₁ hA hv, lanczosV_eq A v₁ hA hv]
  exact inner_arnoldiCGS_eq_zero A v₁ hv h

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 1$, the Lanczos vector $v_j$ lies in
$\mathcal{K}_j$. -/
theorem lanczosV_mem_krylov (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j ∈ krylov A v₁ (j + 1) := by
  rw [lanczosV_eq_vec A v₁ hA hv, krylov_eq]
  exact Arnoldi.vec_mem_subspace (op A) v₁ j

/-- For a Hermitian $A$, $\|v_1\| = 1$ and $j \ge 0$, the Lanczos vector $v_{j+1}$ is orthogonal to
$\mathcal{K}_j$. -/
theorem lanczosV_mem_orthogonal (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j ∈ (krylov A v₁ j)ᗮ := by
  rw [lanczosV_eq_vec A v₁ hA hv, krylov_eq]
  exact Arnoldi.vec_mem_orthogonal (op A) v₁ j

/-! ### The tridiagonal matrices $T_m$ of (6.84) and $\bar T_m$ -/

/-- **Equation (6.84)** of [saad2003iterative]. For $m \ge 0$, the **Lanczos matrix**
$T_m \in \mathbb{R}^{m \times m}$ is the symmetric tridiagonal matrix built from the
coefficients of Algorithm 6.15,
$$T_m = \operatorname{tridiag}(\beta_i, \alpha_i, \beta_{i+1}) = \begin{bmatrix} \alpha_1 &
  \beta_2 & & \\ \beta_2 & \alpha_2 & \ddots & \\ & \ddots & \ddots & \beta_m \\ & & \beta_m &
  \alpha_m \end{bmatrix}.$$

Rows and columns are indexed by `Fin m` from $0$: the entry $(i, i)$ is `lanczosAlpha A v₁ i`,
that is $\alpha_{i+1}$, and the entries $(i, i + 1)$ and $(i + 1, i)$ are
`lanczosBeta A v₁ (i + 1)`, that is $\beta_{i+2}$. -/
noncomputable def T (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then lanczosAlpha A v₁ i
    else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
    else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
    else 0

/-- The **extended Lanczos matrix** $\bar T_m \in \mathbb{R}^{(m+1) \times m}$: the matrix $T_{m+1}$
with its last column deleted, that is, $T_m$ with the extra last row
$(0, \dots, 0, \beta_{m+1})$. It plays for Algorithm 6.15 the role that the Hessenberg matrix
$\bar H_m$ plays for Arnoldi's method.

The entries have the same formula as those of `SaadSparse.Chapter06.T`, on the index types
`Fin (m + 1)` and `Fin m`. For a Hermitian $A$ and $\|v_1\| = 1$, $\bar T_m = \bar H_m$
(`SaadSparse.Chapter06.map_Tbar_eq_Hbar`). -/
noncomputable def Tbar (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then lanczosAlpha A v₁ i
    else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
    else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
    else 0

/-- The entries of $T_m$, with indices from $0$: the entry $(i, j)$ is $\alpha_{i+1}$ if $i = j$,
$\beta_{j+1}$ if $j = i + 1$, $\beta_{i+1}$ if $i = j + 1$, and $0$ otherwise. -/
@[simp] theorem T_apply {m : ℕ} (i j : Fin m) :
    T A v₁ m i j =
      if (i : ℕ) = j then lanczosAlpha A v₁ i
      else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
      else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
      else 0 := rfl

/-- The entries of $\bar T_m$, with indices from $0$: the entry $(i, j)$ is $\alpha_{i+1}$ if
$i = j$, $\beta_{j+1}$ if $j = i + 1$, $\beta_{i+1}$ if $i = j + 1$, and $0$ otherwise. -/
@[simp] theorem Tbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Tbar A v₁ m i j =
      if (i : ℕ) = j then lanczosAlpha A v₁ i
      else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
      else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
      else 0 := rfl

/-- For a Hermitian $A$ and $\|v_1\| = 1$, $T_m$ is the backbone tridiagonal Lanczos matrix
`Lanczos.tridiag (op A) v₁ m`. -/
theorem T_eq_tridiag (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    T A v₁ m = Lanczos.tridiag (op A) v₁ m := by
  ext i j
  rw [T_apply]
  simp only [Lanczos.tridiag, Matrix.of_apply]
  split_ifs with h₁ h₂ h₃
  · rw [lanczosAlpha_eq A v₁ hA hv]
  · rw [← h₂, lanczosBeta_succ_eq A v₁ hA hv]
  · rw [← h₃, lanczosBeta_succ_eq A v₁ hA hv]
  · rfl

/-- For a Hermitian $A$ and $\|v_1\| = 1$, $\bar T_m$ is the backbone extended tridiagonal Lanczos
matrix `Lanczos.tridiagExt (op A) v₁ m`. -/
theorem Tbar_eq_tridiagExt (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    Tbar A v₁ m = Lanczos.tridiagExt (op A) v₁ m := by
  ext i j
  rw [Tbar_apply]
  simp only [Lanczos.tridiagExt, Matrix.of_apply]
  split_ifs with h₁ h₂ h₃
  · rw [lanczosAlpha_eq A v₁ hA hv]
  · rw [← h₂, lanczosBeta_succ_eq A v₁ hA hv]
  · rw [← h₃, lanczosBeta_succ_eq A v₁ hA hv]
  · rfl

/-- Equation (6.84): for a Hermitian $A$ and $\|v_1\| = 1$, the matrix $T_m$, with its real entries
viewed in $\mathbb{K}$, is the Arnoldi matrix $H_m$.

**Generalization.** The real tridiagonal arrays are mapped into the scalar field, so that the
identity also holds for Hermitian matrices in complex arithmetic.
-/
theorem map_T_eq_H (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (T A v₁ m).map (algebraMap ℝ 𝕜) = H A v₁ m := by
  rw [T_eq_tridiag A v₁ hA hv, H_eq A v₁ hv, Lanczos.hessenbergSq_eq_map_tridiag v₁ hA m]

/-- For a Hermitian $A$ and $\|v_1\| = 1$, the matrix $\bar T_m$, with its real entries viewed in
$\mathbb{K}$, is the Arnoldi matrix $\bar H_m$.

**Generalization.** The real tridiagonal arrays are mapped into the scalar field, so that the
identity also holds for Hermitian matrices in complex arithmetic.
-/
theorem map_Tbar_eq_Hbar (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (Tbar A v₁ m).map (algebraMap ℝ 𝕜) = Hbar A v₁ m := by
  rw [Tbar_eq_tridiagExt A v₁ hA hv, Hbar_eq A v₁ hv,
    Lanczos.hessenberg_eq_map_tridiagExt v₁ hA m]

/-- For a Hermitian $A$ and $\|v_1\| = 1$, the matrix $T_m$ is tridiagonal. -/
theorem T_isTridiagonal (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (T A v₁ m).IsTridiagonal := by
  rw [T_eq_tridiag A v₁ hA hv]
  exact Lanczos.tridiag_isTridiagonal (op A) v₁ m

/-- For a Hermitian $A$ and $\|v_1\| = 1$, the matrix $T_m$ is symmetric. -/
theorem T_isSymm (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) : (T A v₁ m).IsSymm := by
  rw [T_eq_tridiag A v₁ hA hv]
  exact Lanczos.tridiag_isSymm (op A) v₁ m

/-! ### Section 6.6.2: the inner product (6.85) and the Lanczos polynomials -/

/-- **Equation (6.85)** of [saad2003iterative]. For a square matrix $A$ over $\mathbb{K}$ and a
vector $v_1$, the form on polynomials
$$\langle p, q \rangle_{v_1} = (p(A) v_1, q(A) v_1).$$

In Lean the form is `inner 𝕜 (q(A) v₁) (p(A) v₁)`: Mathlib's inner product is conjugate-linear
in its first argument, and the book's in its second. So the form is linear in $p$ and
conjugate-linear in $q$, as in the book.

**Generalization.** The expression is defined on all polynomials, with the inner-product arguments
ordered to match the convention linear in the first polynomial. The source uses a real bilinear form
on the degree-restricted space, where the grade makes it nondegenerate.
-/
noncomputable def polyInner (p q : 𝕜[X]) : 𝕜 :=
  inner 𝕜 (aeval (op A) q v₁) (aeval (op A) p v₁)

/-- $\langle p, p \rangle_{v_1} = \|p(A) v_1\|^2$. -/
theorem polyInner_self_eq (p : 𝕜[X]) :
    polyInner A v₁ p p = ((‖aeval (op A) p v₁‖ ^ 2 : ℝ) : 𝕜) := by
  rw [polyInner, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

/-- $\langle p, p \rangle_{v_1} = 0$ if and only if $p(A) v_1 = 0$. -/
theorem polyInner_self_eq_zero_iff (p : 𝕜[X]) :
    polyInner A v₁ p p = 0 ↔ aeval (op A) p v₁ = 0 := by
  rw [polyInner, inner_self_eq_zero]

/-- The linear map $q \mapsto q(A) v_1$ of Section 6.6.2, from $\mathbb{P}_{m-1}$, the polynomials
of degree less than $m$, into $\mathcal{K}_m$.

**Generalization.** The evaluation map is defined and surjective at every degree bound. The source
invokes the bound by the grade to obtain the isomorphism. Lean imposes that bound separately for
injectivity.
-/
noncomputable def polyToKrylov (m : ℕ) : degreeLT 𝕜 m →ₗ[𝕜] krylov A v₁ m :=
  ((Krylov.polyEval (op A) v₁).domRestrict (degreeLT 𝕜 m)).codRestrict (krylov A v₁ m) fun p => by
    rw [krylov_eq_map_degreeLT]
    exact Submodule.mem_map_of_mem p.2

/-- The map `SaadSparse.Chapter06.polyToKrylov` sends $p$ to $p(A) v_1$. -/
@[simp] theorem coe_polyToKrylov {m : ℕ} (p : degreeLT 𝕜 m) :
    (polyToKrylov A v₁ m p : 𝔼) = aeval (op A) (p : 𝕜[X]) v₁ := rfl

/-- For every $m$, the map $q \mapsto q(A) v_1$ from $\mathbb{P}_{m-1}$ to $\mathcal{K}_m$ is
surjective.

**Generalization.** The evaluation map is defined and surjective at every degree bound. The source
invokes the bound by the grade to obtain the isomorphism. Lean imposes that bound separately for
injectivity.
-/
theorem polyToKrylov_surjective (m : ℕ) : Function.Surjective (polyToKrylov A v₁ m) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, hp, hpx⟩ := (mem_krylov_iff_exists_aeval A v₁).1 hx
  exact ⟨⟨p, Polynomial.mem_degreeLT.2 hp⟩, Subtype.ext hpx⟩

/-- Section 6.6.2, first property: if $m \le \mu$, the grade of $v_1$, then the map
$q \mapsto q(A) v_1$ is a bijection from $\mathbb{P}_{m-1}$ onto $\mathcal{K}_m$. -/
theorem polyToKrylov_bijective {m : ℕ} (hm : m ≤ grade A v₁) :
    Function.Bijective (polyToKrylov A v₁ m) := by
  have : FiniteDimensional 𝕜 (degreeLT 𝕜 m) :=
    (Polynomial.degreeLTEquiv 𝕜 m).symm.finiteDimensional
  have hdim : Module.finrank 𝕜 (degreeLT 𝕜 m) = Module.finrank 𝕜 (krylov A v₁ m) := by
    rw [(Polynomial.degreeLTEquiv 𝕜 m).finrank_eq, Module.finrank_fin_fun 𝕜,
      finrank_krylov A v₁ m, min_eq_left hm]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    (polyToKrylov_surjective A v₁ m), polyToKrylov_surjective A v₁ m⟩

/-- Let $m \le \mu$, the grade of $v_1$. If $p$ has degree less than $m$ and $p(A) v_1 = 0$, then
$p = 0$. -/
theorem eq_zero_of_aeval_eq_zero {m : ℕ} (hm : m ≤ grade A v₁) {p : 𝕜[X]} (hp : p.degree < m)
    (h : aeval (op A) p v₁ = 0) : p = 0 := by
  have hinj := (polyToKrylov_bijective A v₁ hm).1
  have h0 : polyToKrylov A v₁ m ⟨p, Polynomial.mem_degreeLT.2 hp⟩ = polyToKrylov A v₁ m 0 := by
    refine Subtype.ext ?_
    rw [coe_polyToKrylov, h]
    simp
  exact congrArg Subtype.val (hinj h0)

/-- **Section 6.6.2** of [saad2003iterative], nondegeneracy of (6.85). Let $A$ be a square matrix
over $\mathbb{K}$, let $v_1$ be a vector of grade $\mu$, and let $m \le \mu$. If
$p \in \mathbb{P}_{m-1}$ satisfies $\langle p, q \rangle_{v_1} = 0$ for every
$q \in \mathbb{P}_{m-1}$, then $p = 0$.

This form of the statement is over $\mathbb{K}$ and needs neither the symmetry of $A$ nor
$\|v_1\| = 1$. The real form is `SaadSparse.Chapter06.equation_6_85_nondegenerate`. -/
theorem polyInner_nondegenerate {m : ℕ} (hm : m ≤ grade A v₁) {p : 𝕜[X]} (hp : p.degree < m)
    (h : ∀ q : 𝕜[X], q.degree < m → polyInner A v₁ p q = 0) : p = 0 :=
  eq_zero_of_aeval_eq_zero A v₁ hm hp
    ((polyInner_self_eq_zero_iff A v₁ p).1 (h p hp))

private theorem exists_aeval_eq_vec (i : ℕ) :
    ∃ p : 𝕜[X], p.degree < ((i + 1 : ℕ) : ℕ) ∧ aeval (op A) p v₁ = Arnoldi.vec (op A) v₁ i := by
  refine (mem_krylov_iff_exists_aeval A v₁).1 ?_
  rw [krylov_eq]
  exact Arnoldi.vec_mem_subspace (op A) v₁ i

/-- **Section 6.6.2** of [saad2003iterative], the Lanczos polynomials. For $i \ge 0$, $q_i$ is a
polynomial of degree at most $i$ such that $q_i(A) v_1$ is the backbone Arnoldi vector
`Arnoldi.vec (op A) v₁ i`. For a Hermitian $A$ and $\|v_1\| = 1$ this vector is the Lanczos
vector, so $v_{i+1} = q_i(A) v_1$ (`SaadSparse.Chapter06.aeval_lanczosPoly`).

The polynomial is chosen with `Classical.choose`. For $i < \mu$ it is unique
(`SaadSparse.Chapter06.eq_zero_of_aeval_eq_zero`).

**Reading.** Lean chooses some polynomial of degree at most the index whose evaluation is the
corresponding vector. Past breakdown the vector is zero and the chosen polynomial can be nonunique.
Below the grade the polynomial is uniquely determined and has the stated exact degree.
-/
noncomputable def lanczosPoly (i : ℕ) : 𝕜[X] := (exists_aeval_eq_vec A v₁ i).choose

/-- The polynomial $q_i$ has degree less than $i + 1$. -/
theorem degree_lanczosPoly_lt (i : ℕ) : (lanczosPoly A v₁ i).degree < ((i + 1 : ℕ) : ℕ) :=
  (exists_aeval_eq_vec A v₁ i).choose_spec.1

/-- $q_i(A) v_1$ is the backbone Arnoldi vector `Arnoldi.vec (op A) v₁ i`. -/
theorem aeval_lanczosPoly_eq_vec (i : ℕ) :
    aeval (op A) (lanczosPoly A v₁ i) v₁ = Arnoldi.vec (op A) v₁ i :=
  (exists_aeval_eq_vec A v₁ i).choose_spec.2

/-- Section 6.6.2, third property: for a Hermitian $A$ and $\|v_1\| = 1$, $v_{i+1} = q_i(A) v_1$.

**Reading.** Lean chooses some polynomial of degree at most the index whose evaluation is the
corresponding vector. Past breakdown the vector is zero and the chosen polynomial can be nonunique.
Below the grade the polynomial is uniquely determined and has the stated exact degree.
-/
theorem aeval_lanczosPoly (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (i : ℕ) :
    aeval (op A) (lanczosPoly A v₁ i) v₁ = lanczosV A v₁ i := by
  rw [aeval_lanczosPoly_eq_vec, lanczosV_eq_vec A v₁ hA hv]

/-- Section 6.6.2, third property: if $i < \mu$, the grade of $v_1$, then $q_i$ has degree exactly
$i$. -/
theorem degree_lanczosPoly {i : ℕ} (hi : i < grade A v₁) :
    (lanczosPoly A v₁ i).degree = (i : ℕ) := by
  refine le_antisymm (Order.le_of_lt_succ (degree_lanczosPoly_lt A v₁ i)) (not_lt.1 fun hlt => ?_)
  have hmem : Arnoldi.vec (op A) v₁ i ∈ Krylov.subspace (op A) v₁ i := by
    rw [← krylov_eq, ← aeval_lanczosPoly_eq_vec A v₁ i]
    exact aeval_mem_krylov A v₁ hlt
  have hperp := (Submodule.mem_orthogonal _ _).1 (Arnoldi.vec_mem_orthogonal (op A) v₁ i) _ hmem
  have hzero : Arnoldi.vec (op A) v₁ i = 0 := inner_self_eq_zero.1 hperp
  have hone : ‖Arnoldi.vec (op A) v₁ i‖ = 1 :=
    Arnoldi.norm_vec_eq_one_of_lt_grade (op A) v₁ (by rwa [← grade_eq])
  rw [hzero, norm_zero] at hone
  exact zero_ne_one hone

/-- Section 6.6.2, third property: the Lanczos polynomials are orthogonal for (6.85),
$\langle q_i, q_j \rangle_{v_1} = 0$ for $i \ne j$. -/
theorem polyInner_lanczosPoly {i j : ℕ} (h : i ≠ j) :
    polyInner A v₁ (lanczosPoly A v₁ i) (lanczosPoly A v₁ j) = 0 := by
  rw [polyInner, aeval_lanczosPoly_eq_vec, aeval_lanczosPoly_eq_vec]
  exact Arnoldi.inner_vec_eq_zero (op A) v₁ (Ne.symm h)

end General

/-! ### The numbered results of Section 6.6, over the real numbers -/

section BookResults

variable {n : ℕ}

/-- A real symmetric matrix $A$ defines a symmetric operator $x \mapsto Ax$ on $\mathbb{R}^n$. -/
theorem isSymmetric_op_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (op A).IsSymmetric :=
  hA.isSymmetric_toEuclideanLin

variable (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : EuclideanSpace ℝ (Fin n))

/-- **Theorem 6.19** of [saad2003iterative]. Assume that Arnoldi's method is applied to a real
symmetric matrix $A$, with a starting vector $v_1$ of norm $1$. Then the coefficients $h_{ij}$
generated by the algorithm satisfy
$$h_{ij} = 0 \ \text{ for } 1 \le i < j - 1 \quad (6.82), \qquad
  h_{j,j+1} = h_{j+1,j} \ \text{ for } j \ge 1 \quad (6.83).$$
In other words, for every $m$ the matrix $H_m$ obtained from the Arnoldi process is tridiagonal
and symmetric.

The coefficients are `SaadSparse.Chapter06.arnoldiCoeff` of Algorithm 6.1, indexed from $0$:
`arnoldiCoeff A v₁ i j` is $h_{i+1,j+1}$. So (6.82) is stated for $i + 1 < j$, and (6.83) for
all $j \ge 0$.

**Reading.** The coefficients and vectors are defined at every natural index. The source states the
identities for the data generated by the finite Arnoldi or Lanczos process. In particular, the
equality involving the entry above the last subdiagonal uses coefficients from the enlarged matrix.
-/
theorem theorem_6_19 (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (∀ i j : ℕ, i + 1 < j → arnoldiCoeff A v₁ i j = 0) ∧
      (∀ j : ℕ, arnoldiCoeff A v₁ j (j + 1) = arnoldiCoeff A v₁ (j + 1) j) ∧
      (H A v₁ m).IsTridiagonal ∧ (H A v₁ m).IsSymm := by
  have hA' := isSymmetric_op_of_isSymm hA
  have hH : H A v₁ m = T A v₁ m := by
    rw [← map_T_eq_H A v₁ hA' hv]
    exact (Matrix.ext fun _ => congrFun rfl).symm
  refine ⟨fun i j hij => ?_, fun j => ?_, ?_, ?_⟩
  · rw [arnoldiCoeff_eq A v₁ hv]
    exact Arnoldi.coeff_eq_zero_of_isSymmetric hA' v₁ hij
  · rw [arnoldiCoeff_eq A v₁ hv, arnoldiCoeff_eq A v₁ hv,
      Arnoldi.coeff_conj_of_isSymmetric hA' v₁ j (j + 1)]
    rfl
  · rw [hH]; exact T_isTridiagonal A v₁ hA' hv m
  · rw [hH]; exact T_isSymm A v₁ hA' hv m

/-- **Equation (6.84)** of [saad2003iterative]. For a real symmetric $A$ and $\|v_1\|_2 = 1$, the
Lanczos matrix is the Arnoldi matrix: $T_m = H_m$ for every $m$. -/
theorem T_eq_H (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (m : ℕ) : T A v₁ m = H A v₁ m := by
  rw [← map_T_eq_H A v₁ (isSymmetric_op_of_isSymm hA) hv]
  exact Matrix.ext fun _ => congrFun rfl

/-- **Section 6.6.1** of [saad2003iterative], Algorithm 6.15 as a form of Algorithm 6.2. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and let $\|v_1\|_2 = 1$. Then for every $j \ge 1$
the vector $v_j$ of Algorithm 6.15 is the vector $v_j$ of Algorithm 6.2 (Arnoldi's method with
modified Gram–Schmidt), and
$$\alpha_j = h_{jj}, \qquad \beta_{j+1} = h_{j+1,j}.$$

In Lean the index starts at $0$: the three equations are for `lanczosV A v₁ j`,
`lanczosAlpha A v₁ j` and `lanczosBeta A v₁ (j + 1)`, against `arnoldiMGS A v₁ j`,
`arnoldiCoeff A v₁ j j` and `arnoldiCoeff A v₁ (j + 1) j`. The coefficients
`SaadSparse.Chapter06.arnoldiCoeff` are defined from the vectors of Algorithm 6.1.

**Reading.** The coefficients and vectors are defined at every natural index. The source states the
identities for the data generated by the finite Arnoldi or Lanczos process. In particular, the
equality involving the entry above the last subdiagonal uses coefficients from the enlarged matrix.
-/
theorem algorithm_6_15_eq_alg_6_2 (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = arnoldiMGS A v₁ j ∧ lanczosAlpha A v₁ j = arnoldiCoeff A v₁ j j ∧
      lanczosBeta A v₁ (j + 1) = arnoldiCoeff A v₁ (j + 1) j :=
  ⟨lanczosV_eq_arnoldiMGS A v₁ (isSymmetric_op_of_isSymm hA) hv j,
    lanczosAlpha_eq_arnoldiCoeff A v₁ (isSymmetric_op_of_isSymm hA) hv j,
    lanczosBeta_succ_eq_arnoldiCoeff A v₁ (isSymmetric_op_of_isSymm hA) hv j⟩

/-!
### The real forms used by Section 6.7

Over $\mathbb{R}$ the coefficients of Algorithm 6.15 are scalars of the space itself, so the
coercions `RCLike.ofReal` of the general statements above disappear.
-/

/-- For a real symmetric $A$ and $\|v_1\|_2 = 1$: $A v_1 = \alpha_1 v_1 + \beta_2 v_2$ (Algorithm
6.15, lines 3–7, at the first step). -/
theorem apply_lanczosV_zero_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) :
    op A (lanczosV A v₁ 0) =
      lanczosAlpha A v₁ 0 • lanczosV A v₁ 0 + lanczosBeta A v₁ 1 • lanczosV A v₁ 1 := by
  simpa using apply_lanczosV_zero A v₁ (isSymmetric_op_of_isSymm hA) hv

/-- For a real symmetric $A$, $\|v_1\|_2 = 1$ and $j \ge 1$: $A v_{j+1} = \beta_{j+1} v_j +
\alpha_{j+1} v_{j+1} + \beta_{j+2} v_{j+2}$ (Algorithm 6.15, lines 3–7). -/
theorem apply_lanczosV_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (lanczosV A v₁ (j + 1)) = lanczosBeta A v₁ (j + 1) • lanczosV A v₁ j +
      lanczosAlpha A v₁ (j + 1) • lanczosV A v₁ (j + 1) +
      lanczosBeta A v₁ (j + 2) • lanczosV A v₁ (j + 2) := by
  simpa using apply_lanczosV A v₁ (isSymmetric_op_of_isSymm hA) hv j

/-- For a real symmetric $A$, $\|v_1\|_2 = 1$ and $j \ge 1$: $\alpha_j = (A v_j, v_j)$. -/
theorem lanczosAlpha_eq_inner_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosAlpha A v₁ j = inner ℝ (lanczosV A v₁ j) (op A (lanczosV A v₁ j)) := by
  simpa using lanczosAlpha_eq_inner A v₁ (isSymmetric_op_of_isSymm hA) hv j

/-- For a real symmetric $A$, $\|v_1\|_2 = 1$ and $j \ge 1$: $\beta_{j+1} = (A v_j, v_{j+1})$. -/
theorem lanczosBeta_succ_eq_inner_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosBeta A v₁ (j + 1) = inner ℝ (lanczosV A v₁ (j + 1)) (op A (lanczosV A v₁ j)) := by
  simpa using lanczosBeta_succ_eq_inner A v₁ (isSymmetric_op_of_isSymm hA) hv j

/-- **Section 6.6.2** of [saad2003iterative], the isomorphism $q \mapsto q(A) v_1$. Let
$A \in \mathbb{R}^{n \times n}$, let $v_1 \in \mathbb{R}^n$ have grade $\mu$, and let
$m \le \mu$. Then the map $q \mapsto q(A) v_1$ is a bijection from $\mathbb{P}_{m-1}$ onto
$\mathcal{K}_m$.

The map is the linear map `SaadSparse.Chapter06.polyToKrylov`, so the statement makes it a
linear isomorphism. $\mathbb{P}_{m-1}$ is `Polynomial.degreeLT ℝ m`. The statement needs neither
the symmetry of $A$ nor $\|v_1\| = 1$. -/
theorem equation_6_85_isomorphism {m : ℕ} (hm : m ≤ grade A v₁) :
    Function.Bijective (polyToKrylov A v₁ m) :=
  polyToKrylov_bijective A v₁ hm

/-- **Section 6.6.2** of [saad2003iterative], nondegeneracy of (6.85). Let
$A \in \mathbb{R}^{n \times n}$, let $v_1 \in \mathbb{R}^n$ have grade $\mu$, and let
$m \le \mu$. If $p \in \mathbb{P}_{m-1}$ satisfies $\langle p, q \rangle_{v_1} = 0$ for every
$q \in \mathbb{P}_{m-1}$, then $p = 0$. So (6.85) is a nondegenerate bilinear form on
$\mathbb{P}_{m-1}$.

The statement needs neither the symmetry of $A$ nor $\|v_1\| = 1$. The polynomials of degree
less than $m$ are those `p : ℝ[X]` with `p.degree < m`.

**Reading.** The statement gives nondegeneracy as an implication for a polynomial paired with every
member of the degree-restricted space. The source also refers to the pairing there as an inner
product.
-/
theorem equation_6_85_nondegenerate {m : ℕ} (hm : m ≤ grade A v₁) {p : ℝ[X]} (hp : p.degree < m)
    (h : ∀ q : ℝ[X], q.degree < m → polyInner A v₁ p q = 0) : p = 0 :=
  polyInner_nondegenerate A v₁ hm hp h

/-- **Section 6.6.2** of [saad2003iterative], the Lanczos polynomials. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $\|v_1\|_2 = 1$, and let $\mu$ be the grade of
$v_1$. For every $i < \mu$, the Lanczos polynomial $q_i$ has degree $i$, satisfies
$v_{i+1} = q_i(A) v_1$, and is orthogonal to every other Lanczos polynomial:
$\langle q_i, q_j \rangle_{v_1} = 0$ for every $j \ne i$.

The polynomials are `SaadSparse.Chapter06.lanczosPoly`. The Lanczos vector `lanczosV A v₁ i` is
$v_{i+1}$.

**Reading.** The polynomial indexed by $i$ is required to precede breakdown for its degree
conclusion. Its pairing with every other polynomial vanishes, including with the choices for zero
vectors after breakdown.
-/
theorem equation_6_85_orthogonal_polynomials (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {i : ℕ}
    (hi : i < grade A v₁) :
    (lanczosPoly A v₁ i).degree = (i : ℕ) ∧
      aeval (op A) (lanczosPoly A v₁ i) v₁ = lanczosV A v₁ i ∧
      ∀ j, i ≠ j → polyInner A v₁ (lanczosPoly A v₁ i) (lanczosPoly A v₁ j) = 0 :=
  ⟨degree_lanczosPoly A v₁ hi,
    aeval_lanczosPoly A v₁ (isSymmetric_op_of_isSymm hA) hv i,
    fun _ h => polyInner_lanczosPoly A v₁ h⟩

/-- For a real symmetric $A$, $\|v_1\|_2 = 1$ and $m \le \mu$, the characteristic polynomial of
$T_m$ is that of the compression of $A$ to $\mathcal{K}_m$. -/
private theorem charpoly_T_eq (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {m : ℕ} (hm : m ≤ grade A v₁) :
    (T A v₁ m).charpoly =
      LinearMap.charpoly (compression (op A) (Krylov.subspace (op A) v₁ m)) := by
  have hA' := isSymmetric_op_of_isSymm hA
  have h := Lanczos.charpoly_tridiag_map hA' v₁ (m := m) (by rwa [← grade_eq])
  rw [Algebra.algebraMap_self, Polynomial.map_id] at h
  rw [T_eq_tridiag A v₁ hA' hv, h]

/-- **Section 6.6.2** of [saad2003iterative], the minimizing property of the characteristic
polynomial. Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $\|v_1\|_2 = 1$, and let
$m \le \mu$, the grade of $v_1$. Among the monic polynomials $p$ of degree $m$, the
characteristic polynomial $p_{T_m}$ of $T_m$ minimizes $\|p\|_{v_1} = \|p(A) v_1\|_2$:
$$\|p_{T_m}(A) v_1\|_2 \le \|p(A) v_1\|_2 \quad \text{for every monic } p \text{ of degree }
  m.$$

The book states this property without proof. The proof specializes
`Arnoldi.charpoly_compression_isMinOn`: $T_m$ is the matrix of the compression of $A$ to
$\mathcal{K}_m$ (6.84), and the hypothesis $m \le \mu$ gives this compression the $m$
orthonormal basis vectors that form the book's $V_m$.

**Reading.** The source describes minimization over monic polynomials without spelling out the
degree in that sentence. The comparison is between monic polynomials of the same degree $m$, with
$m$ bounded by the grade.
-/
theorem equation_6_85_charpoly_isMinOn (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {m : ℕ}
    (hm : m ≤ grade A v₁) :
    IsMinOn (fun p : ℝ[X] => ‖aeval (op A) p v₁‖) {p : ℝ[X] | p.Monic ∧ p.natDegree = m}
      (T A v₁ m).charpoly := by
  rw [charpoly_T_eq A v₁ hA hv hm]
  exact Arnoldi.charpoly_compression_isMinOn (op A) v₁ (by rwa [← grade_eq])

/-- **Section 6.6.2** of [saad2003iterative], the Lanczos algorithm computes $p_{T_m}(A) v_1$ up to
a scalar. Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $\|v_1\|_2 = 1$, and let
$m \le \mu$, the grade of $v_1$. Then the characteristic polynomial $p_{T_m}$ of $T_m$ satisfies
$$p_{T_m}(A) v_1 = \beta_2 \beta_3 \cdots \beta_{m+1} \, v_{m+1}.$$
Since $\beta_2, \dots, \beta_m$ are nonzero for $m \le \mu$, this vector is $0$ exactly when
$\beta_{m+1} = 0$, that is, when the algorithm breaks down at step $m$.

The book states this property without proof. The product is over `Finset.range m` of
`lanczosBeta A v₁ (j + 1)`. The vector `lanczosV A v₁ m` is $v_{m+1}$. For $m = 0$ the product
is empty and the statement is $v_1 = v_1$.

**Reading.** The source says the Lanczos recurrence computes the vectors without displaying the
normalization. Lean gives the exact product of subdiagonal coefficients relating these vectors to
the normalized Lanczos sequence. At breakdown the product is zero.
-/
theorem equation_6_85_lanczos_charpoly (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {m : ℕ}
    (hm : m ≤ grade A v₁) :
    aeval (op A) (T A v₁ m).charpoly v₁ =
      (∏ j ∈ Finset.range m, lanczosBeta A v₁ (j + 1)) • lanczosV A v₁ m := by
  have hA' := isSymmetric_op_of_isSymm hA
  have h := Lanczos.aeval_charpoly_tridiag hA' v₁ (m := m) (by rwa [← grade_eq])
  rw [Algebra.algebraMap_self, Polynomial.map_id, hv, one_mul] at h
  have hprod : ∀ j ∈ Finset.range m,
      lanczosBeta A v₁ (j + 1) = Lanczos.beta (op A) v₁ j :=
    fun j _ => lanczosBeta_succ_eq A v₁ hA' hv j
  rw [T_eq_tridiag A v₁ hA' hv, h, lanczosV_eq_vec A v₁ hA' hv, Finset.prod_congr rfl hprod]
  norm_num

end BookResults

end SaadSparse.Chapter06
