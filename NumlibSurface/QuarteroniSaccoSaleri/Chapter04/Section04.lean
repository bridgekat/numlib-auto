/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CR
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Lanczos
import Numlib.Stationary.Block
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 4.4: Methods based on Krylov subspace iterations

This module formalizes §4.4 of [quarteroni2000numerical]: the Krylov subspaces $K_m(A; v) =
\operatorname{span}\{v, Av, \dots, A^{m-1} v\}$ of a matrix $A \in \mathbb{R}^{n \times n}$, the
degree of a vector with respect to $A$ (Property 4.7, Example 4.8), the Arnoldi algorithm (4.55)
with its Hessenberg relations (4.56), and the two Krylov methods for $Ax = b$ that look for
$x^{(k)} \in x^{(0)} + K_k(A; r^{(0)})$. The Arnoldi method for linear systems (FOM, (4.57)) makes
the residual orthogonal to $K_k(A; r^{(0)})$; it reduces to a Hessenberg system (4.62) and yields
the exact solution after at most $n$ steps (Theorem 4.13). The GMRES method (4.58) minimizes the
Euclidean norm of the residual; it reduces to a least-squares problem with the matrix $\hat H_k$
(4.66), and a breakdown of the Arnoldi algorithm means that its iterate is exact (Property 4.8). The
module also treats projection methods (Remark 4.4) and the symmetric case: the Lanczos method, its
relation to the conjugate gradient method (Remark 4.5), and the conjugate residual method (§4.4.3).

The proofs specialize the backbone modules `Numlib.Krylov.Subspace` (Krylov subspaces and the
grade), `Numlib.Krylov.Arnoldi` (the Arnoldi process as Gram–Schmidt on the Krylov sequence),
`Numlib.Krylov.Iterate` and `Numlib.Krylov.Hessenberg` (the Galerkin and minimal-residual
specifications, their coordinates in the Arnoldi basis, the Givens rotations),
`Numlib.Krylov.Lanczos` (the symmetric case), `Numlib.Krylov.CR` (the conjugate residual method),
`Numlib.Projection.Basic` (projection methods) and `Numlib.Stationary.Block` (the Gauss–Seidel
method as a multiplicative projection process).

## Main definitions

* Equation (4.52), `QuarteroniSaccoSaleri.Chapter04.krylovSubspace`: the Krylov subspace
  $K_m(A; v)$.
* Property 4.7, `QuarteroniSaccoSaleri.Chapter04.degree`: the degree $\deg_A(v)$ of $v$ with respect
  to $A$.
* Example 4.8, `QuarteroniSaccoSaleri.Chapter04.example_4_8_matrix`: the matrix
  $\operatorname{tridiag}_4(-1, 2, -1)$.
* Equation (4.55), `QuarteroniSaccoSaleri.Chapter04.arnoldi`,
  `QuarteroniSaccoSaleri.Chapter04.arnoldiH` and `QuarteroniSaccoSaleri.Chapter04.arnoldiW`: the
  Arnoldi vectors $v_k$, the coefficients $h_{ik}$ and the vectors $w_k$.
* Equation (4.56), `QuarteroniSaccoSaleri.Chapter04.V`, `QuarteroniSaccoSaleri.Chapter04.H` and
  `QuarteroniSaccoSaleri.Chapter04.Hhat`: the matrices $V_m$, $H_m$ and $\hat H_m$.
* Equation (4.57), `QuarteroniSaccoSaleri.Chapter04.equation_4_57`: the iterate of the Arnoldi
  method for linear systems (FOM).
* Equation (4.58), `QuarteroniSaccoSaleri.Chapter04.equation_4_58`: the iterate of the GMRES method.
* §4.4.1, `QuarteroniSaccoSaleri.Chapter04.e₁`: the first unit vector of $\mathbb{R}^m$.
* Remark 4.4, `QuarteroniSaccoSaleri.Chapter04.remark_4_4`: the approximate solution of a projection
  method.

## Main results

* Equation (4.51), `QuarteroniSaccoSaleri.Chapter04.equation_4_51`: the residual of the
  nonstationary Richardson method is $r^{(k)} = p_k(A) r^{(0)}$ with $p_k(0) = 1$.
* Equation (4.52), `QuarteroniSaccoSaleri.Chapter04.mem_krylovSubspace_iff`: $K_m(A; v)$ is the set
  of the vectors $p(A) v$ with $\deg p \le m - 1$.
* Equations (4.53)–(4.54), `QuarteroniSaccoSaleri.Chapter04.equation_4_53`: the Richardson iterate
  $x^{(k)}$ lies in $x^{(0)} + K_k(A; r^{(0)})$.
* Property 4.7, `QuarteroniSaccoSaleri.Chapter04.degree_le` and
  `QuarteroniSaccoSaleri.Chapter04.property_4_7`: $\deg_A(v) \le n$, and
  $\dim K_m(A; v) = \min(m, \deg_A(v))$.
* Example 4.8, `QuarteroniSaccoSaleri.Chapter04.example_4_8`: the degrees of two vectors with
  respect to $\operatorname{tridiag}_4(-1, 2, -1)$.
* Equation (4.55), `QuarteroniSaccoSaleri.Chapter04.arnoldi_eq_vec` and
  `QuarteroniSaccoSaleri.Chapter04.arnoldi_basis`: the Arnoldi algorithm is the Gram–Schmidt
  orthonormalization of the Krylov sequence, and its first $m$ vectors are an orthonormal basis of
  $K_m(A; v_1)$.
* Equation (4.56), `QuarteroniSaccoSaleri.Chapter04.equation_4_56`: $V_m^T A V_m = H_m$ and
  $V_{m+1}^T A V_m = \hat H_m$, with $\hat H_m$ upper Hessenberg.
* §4.4.1, `QuarteroniSaccoSaleri.Chapter04.arnoldi_breakdown_iff`: the Arnoldi algorithm breaks down
  exactly at the degree of $v_1$.
* Equations (4.57)–(4.58), `QuarteroniSaccoSaleri.Chapter04.equation_4_57_iff` and
  `QuarteroniSaccoSaleri.Chapter04.equation_4_58_iff`: the two methods are the backbone's Galerkin
  and minimal-residual specifications, and the GMRES iterate exists.
* Equation (4.59), `QuarteroniSaccoSaleri.Chapter04.V_mulVec`: $V_k z = \sum_j z_j v_j$.
* Equations (4.59)–(4.62), `QuarteroniSaccoSaleri.Chapter04.equation_4_62`: $x^{(0)} + V_k z$ is the
  FOM iterate if and only if $H_k z = \|r^{(0)}\|_2 e_1$.
* Theorem 4.13, `QuarteroniSaccoSaleri.Chapter04.theorem_4_13`: for nonsingular $A$, the Arnoldi
  method yields the exact solution after at most $n$ steps.
* Equation (4.63), `QuarteroniSaccoSaleri.Chapter04.equation_4_63`: the FOM residual is
  $-h_{k+1,k} (e_k^T z^{(k)}) v_{k+1}$.
* Equations (4.64)–(4.65), `QuarteroniSaccoSaleri.Chapter04.equation_4_65`: $r^{(k)} =
  V_{k+1}(\|r^{(0)}\|_2 e_1 - \hat H_k z^{(k)})$.
* Equation (4.66), `QuarteroniSaccoSaleri.Chapter04.equation_4_66`: the GMRES iterate solves the
  least-squares problem $\min_z \|\|r^{(0)}\|_2 e_1 - \hat H_k z\|_2$.
* Property 4.8, `QuarteroniSaccoSaleri.Chapter04.property_4_8`: for nonsingular $A$, the Arnoldi
  algorithm breaks down at step $m$ if and only if the GMRES iterate $x^{(m)}$ is exact.
* §4.4.2, `QuarteroniSaccoSaleri.Chapter04.gmres_norm_residual_eq_norm_gamma`: after the Givens
  rotations, the last component of the rotated right-hand side gives the norm of the GMRES residual.
* Remark 4.4, `QuarteroniSaccoSaleri.Chapter04.remark_4_4_iff`,
  `QuarteroniSaccoSaleri.Chapter04.remark_4_4_krylov` and
  `QuarteroniSaccoSaleri.Chapter04.remark_4_4_gaussSeidel`: FOM is an orthogonal and GMRES an
  oblique projection method, and the Gauss–Seidel method is an orthogonal projection method onto the
  coordinate lines.
* §4.4.3, `QuarteroniSaccoSaleri.Chapter04.lanczos_tridiagonal` and
  `QuarteroniSaccoSaleri.Chapter04.lanczos_residual_eq_smul`: for symmetric $A$ the matrix $H_m$ is
  symmetric tridiagonal, and the FOM residuals are multiples of the Lanczos vectors.
* Remark 4.5, `QuarteroniSaccoSaleri.Chapter04.remark_4_5`: for symmetric positive definite $A$, the
  conjugate gradient iterate is the Lanczos iterate.
* §4.4.3, `QuarteroniSaccoSaleri.Chapter04.cr_residual_conjugate`: the conjugate residual method
  computes the GMRES iterates, and its residuals are $A$-conjugate.

## Conventions

* Vectors are `EuclideanSpace ℝ (Fin n)`, on which a matrix acts as `Matrix.toEuclideanLin A`, as in
  §4.3.
* The Krylov subspace $K_m(A; v)$ is `QuarteroniSaccoSaleri.Chapter04.krylovSubspace A v m`, which
  is the backbone's `Krylov.subspace (toEuclideanLin A) v m`
  (`QuarteroniSaccoSaleri.Chapter04.krylovSubspace_eq`). The degree $\deg_A(v)$ is
  `QuarteroniSaccoSaleri.Chapter04.degree A v`, which is the backbone's `Krylov.grade`
  (`QuarteroniSaccoSaleri.Chapter04.degree_eq_grade`).
* The Arnoldi algorithm (4.55) is written as the source writes it, but with 0-based indices:
  `arnoldi A v₁ (k - 1)` is the vector $v_k$ of the source, and `arnoldiH A v₁ (i - 1) (k - 1)` is
  its coefficient $h_{ik}$. The matrices $V_m$, $H_m$ and $\hat H_m$ are `V`, `H` and `Hhat`.
* The two Krylov methods are the specifications (4.57) and (4.58),
  `QuarteroniSaccoSaleri.Chapter04.equation_4_57` and
  `QuarteroniSaccoSaleri.Chapter04.equation_4_58`. A breakdown of the Arnoldi algorithm is a
  vanishing vector $w_k$.

## Implementation notes

* The algorithm (4.55) is identified with the backbone's Gram–Schmidt vectors `Arnoldi.vec`, for a
  unit starting vector (`QuarteroniSaccoSaleri.Chapter04.arnoldi_eq_vec`) and for the start
  $v_1 = r^{(0)}/\|r^{(0)}\|_2$ of the Krylov methods
  (`QuarteroniSaccoSaleri.Chapter04.arnoldi_normalize`).
* The specifications (4.57) and (4.58) are the backbone's `Krylov.IsGalerkinIterate` and
  `Krylov.IsMinResidualIterate`.

## Deviations from the source

* **Remark 4.4** (reading). The source writes $x^{(k)} \in Y_k$; for the Krylov instances the
  condition is $x^{(k)} \in x^{(0)} + Y_k$, as in (4.59). See
  `QuarteroniSaccoSaleri.Chapter04.remark_4_4`.
* **Property 4.8** (generalization). The source states it for $m < n$; the equivalence holds for
  every $m$, and at $m = n$ both sides are true. See `QuarteroniSaccoSaleri.Chapter04.property_4_8`.
* **§4.4.3, the Lanczos residuals** (generalization). The source makes the statement for symmetric
  $A$; it holds for every $A$. See `QuarteroniSaccoSaleri.Chapter04.lanczos_residual_eq_smul`.

## Not formalized

* **Example 4.9.** It is a numerical run.
* **Programs 21–24.** They are code.
* **The methods FOM(m), IOM, GMRES(m), QGMRES, GCR and ORTHOMIN.** The source names them without any
  result.
-/

open Filter Finset Matrix Polynomial Topology WithLp

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### (4.51)–(4.54): Krylov subspaces -/

section Krylov

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **Equation (4.51)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$, let
$\alpha_0, \alpha_1, \dots$ be real parameters and $b, x^{(0)} \in \mathbb{R}^n$. For the non
preconditioned nonstationary Richardson method (4.24), $P = I$, the residual at step $k$ is
$$r^{(k)} = \prod_{j < k} (I - \alpha_j A) \, r^{(0)} = p_k(A) r^{(0)},$$
where $p_k = \prod_{j < k} (1 - \alpha_j X)$ is a polynomial of degree at most $k$ with
$p_k(0) = 1$.

The proof is the backbone's `Richardson.residual_iterate_eq_prod`. -/
theorem equation_4_51 (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    b - A *ᵥ nonstationaryRichardson A 1 α b x₀ k =
        aeval A (∏ j ∈ range k, (1 - C (α j) * X)) *ᵥ (b - A *ᵥ x₀) ∧
      (∏ j ∈ range k, (1 - C (α j) * X : ℝ[X])).degree ≤ k ∧
      (∏ j ∈ range k, (1 - C (α j) * X : ℝ[X])).eval 0 = 1 := by
  refine ⟨?_, degree_le_of_natDegree_le (Richardson.natDegree_residualPoly_le α k),
    Richardson.residualPoly_eval_zero α k⟩
  have h := Richardson.residual_iterate_eq_prod (toEuclideanLin A) α (toLp 2 b) (toLp 2 x₀) k
  have h2 := toLp_nonstationaryRichardson A 1 α b x₀ k
  rw [inv_one, toEuclideanLin_one] at h2
  rw [← h2, Richardson.residualPoly, ← toEuclideanLin_aeval, toEuclideanLin_toLp, ← toLp_sub,
    toEuclideanLin_toLp, ← toLp_sub, toEuclideanLin_toLp] at h
  exact toLp_injective 2 h

/-- **Equation (4.52)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$v \in \mathbb{R}^n$. The **Krylov subspace** of order $m$ is
$$K_m(A; v) = \operatorname{span}\{v, Av, \dots, A^{m-1} v\}.$$

It is the backbone's `Krylov.subspace (toEuclideanLin A) v m`
(`QuarteroniSaccoSaleri.Chapter04.krylovSubspace_eq`). For $m = 0$ it is the zero subspace. -/
noncomputable def krylovSubspace (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v)

/-- The Krylov subspace $K_m(A; v)$ of (4.52) is the backbone's
`Krylov.subspace (toEuclideanLin A) v m`. The proof is `Matrix.krylov_subspace_toEuclideanLin`. -/
theorem krylovSubspace_eq (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    krylovSubspace A v m = Krylov.subspace (toEuclideanLin A) v m :=
  (krylov_subspace_toEuclideanLin A v m).symm

/-- **Equation (4.52)** of [quarteroni2000numerical], the sentence after it. A vector $u$ lies in
$K_m(A; v)$ if and only if $u = p(A) v$ for a real polynomial $p$ of degree less than $m$, that
is, $p = p_{m-1}$ of degree at most $m - 1$.

The proof is the backbone's `Krylov.mem_subspace_iff_exists_aeval`. -/
theorem mem_krylovSubspace_iff (v u : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    u ∈ krylovSubspace A v m ↔ ∃ p : ℝ[X], p.degree < m ∧ aeval (toEuclideanLin A) p v = u := by
  rw [krylovSubspace_eq, Krylov.mem_subspace_iff_exists_aeval]

/-- **Equations (4.53)–(4.54)** of [quarteroni2000numerical]. Let $x^{(k)}$ be the iterates of the
non preconditioned nonstationary Richardson method (4.24) and $r^{(0)} = b - Ax^{(0)}$. Then
$x^{(k)}$ belongs to
$$W_k = \{x^{(0)} + y : y \in K_k(A; r^{(0)})\},$$
and the elements of $W_k$ are exactly the vectors $x^{(0)} + q_{k-1}(A) r^{(0)}$ with $q_{k-1}$
a real polynomial of degree at most $k - 1$. So a Krylov method looks for its iterate in this
form.

The first clause is the backbone's `Richardson.iterate_sub_mem_subspace`. The coordinate vectors
are moved to `EuclideanSpace ℝ (Fin n)` by `WithLp.toLp 2`. -/
theorem equation_4_53 (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 (nonstationaryRichardson A 1 α b x₀ k) : EuclideanSpace ℝ (Fin n)) - toLp 2 x₀ ∈
        krylovSubspace A (toLp 2 (b - A *ᵥ x₀)) k ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        x - toLp 2 x₀ ∈ krylovSubspace A (toLp 2 (b - A *ᵥ x₀)) k ↔
          ∃ q : ℝ[X], q.degree < k ∧
            x = toLp 2 x₀ + aeval (toEuclideanLin A) q (toLp 2 (b - A *ᵥ x₀)) := by
  constructor
  · rw [toLp_nonstationaryRichardson, inv_one, toEuclideanLin_one, krylovSubspace_eq, toLp_sub,
      ← toEuclideanLin_toLp]
    exact Richardson.iterate_sub_mem_subspace (toEuclideanLin A) α (toLp 2 b) (toLp 2 x₀) k
  · intro x
    rw [mem_krylovSubspace_iff]
    constructor
    · rintro ⟨q, hq, hqx⟩
      exact ⟨q, hq, by rw [hqx, add_sub_cancel]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by rw [add_sub_cancel_left]⟩

/-- **Property 4.7** of [quarteroni2000numerical], the degree of a vector. Let
$A \in \mathbb{R}^{n \times n}$ and $v \in \mathbb{R}^n$. The **degree of $v$ with respect to
$A$**, $\deg_A(v)$, is the least degree of a monic polynomial $p$ with $p(A) v = 0$.

The degree of $v = 0$ is $0$. The degree is the backbone's `Krylov.grade`
(`QuarteroniSaccoSaleri.Chapter04.degree_eq_grade`). -/
noncomputable def degree (v : EuclideanSpace ℝ (Fin n)) : ℕ :=
  sInf {d | ∃ p : ℝ[X], p.Monic ∧ p.natDegree = d ∧ aeval (toEuclideanLin A) p v = 0}

/-- The degree $\deg_A(v)$ is the grade of $v$, the dimension of the span of all vectors $A^j v$.
The proof combines the backbone's `Krylov.grade_eq_sInf` with
`Krylov.pow_apply_mem_subspace_iff_exists_monic`. -/
theorem degree_eq_grade (v : EuclideanSpace ℝ (Fin n)) :
    degree A v = Krylov.grade (toEuclideanLin A) v := by
  rw [degree, Krylov.grade_eq_sInf]
  congr 1
  ext m
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Krylov.pow_apply_mem_subspace_iff_exists_monic]

/-- **Property 4.7** of [quarteroni2000numerical], the sentence after it. For every
$A \in \mathbb{R}^{n \times n}$ and $v \in \mathbb{R}^n$, the degree of $v$ with respect to $A$
is at most $n$: $\deg_A(v) \le n$.

The source gives the Cayley–Hamilton theorem as the reason. The proof is the backbone's
`Krylov.grade_le_finrank`. -/
theorem degree_le (v : EuclideanSpace ℝ (Fin n)) : degree A v ≤ n := by
  rw [degree_eq_grade]
  have := Krylov.grade_le_finrank (toEuclideanLin A) v
  rwa [finrank_euclideanSpace_fin] at this

/-- **Property 4.7** of [quarteroni2000numerical] and the sentence after it. Let
$A \in \mathbb{R}^{n \times n}$ and $v \in \mathbb{R}^n$. The Krylov subspace $K_m(A; v)$ has
dimension $m$ if and only if $\deg_A(v) \ge m$. In general
$$\dim K_m(A; v) = \min(m, \deg_A(v)),$$
which is a nondecreasing function of $m$.

The proof is the backbone's `Krylov.finrank_subspace`. -/
theorem property_4_7 (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    (Module.finrank ℝ (krylovSubspace A v m) = m ↔ m ≤ degree A v) ∧
      Module.finrank ℝ (krylovSubspace A v m) = min m (degree A v) := by
  rw [krylovSubspace_eq, degree_eq_grade, Krylov.finrank_subspace]
  exact ⟨min_eq_left_iff, rfl⟩

end Krylov

/-! ### Example 4.8 -/

section Example

/-- **Example 4.8** of [quarteroni2000numerical], the matrix $A = \operatorname{tridiag}_4(-1, 2,
-1) \in \mathbb{R}^{4 \times 4}$, with $2$ on the diagonal and $-1$ on the two adjacent
diagonals. -/
def example_4_8_matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]

/-- The grade of $v$ with respect to $A$ is at most $m$ when $A^m v$ is a linear combination of
$v, Av, \dots, A^{m-1} v$. -/
private theorem grade_le_of_exists_fun {A : Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin n)} {m : ℕ} (c : Fin m → ℝ)
    (h : ∑ i, c i • toEuclideanLin (A ^ (i : ℕ)) v = toEuclideanLin (A ^ m) v) :
    Krylov.grade (toEuclideanLin A) v ≤ m := by
  rw [Krylov.grade_le_iff, ← toEuclideanLin_pow, krylov_subspace_toEuclideanLin,
    Submodule.mem_span_range_iff_exists_fun]
  exact ⟨c, h⟩

/-- The grade of $v$ with respect to $A$ exceeds $m$ when $A^m v$ is not a linear combination of
$v, Av, \dots, A^{m-1} v$. -/
private theorem lt_grade_of_forall_fun {A : Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin n)} {m : ℕ}
    (h : ∀ c : Fin m → ℝ, ∑ i, c i • toEuclideanLin (A ^ (i : ℕ)) v ≠ toEuclideanLin (A ^ m) v) :
    m < Krylov.grade (toEuclideanLin A) v := by
  by_contra hle
  rw [not_lt, Krylov.grade_le_iff, ← toEuclideanLin_pow, krylov_subspace_toEuclideanLin,
    Submodule.mem_span_range_iff_exists_fun] at hle
  obtain ⟨c, hc⟩ := hle
  exact h c hc

/-- **Example 4.8** of [quarteroni2000numerical]. Let $A = \operatorname{tridiag}_4(-1, 2, -1)$. The
vector $v = (1, 1, 1, 1)^T$ has degree $2$ with respect to $A$: $p_2(A) v = 0$ for
$p_2(A) = I - 3A + A^2$, while no monic polynomial of degree $1$ annihilates $v$. Hence every
Krylov subspace $K_m(A; v)$ with $m \ge 2$ has dimension $2$. The vector $w = (1, 1, -1, 1)^T$
has degree $4$.

The proof computes the Krylov vectors explicitly and uses
`QuarteroniSaccoSaleri.Chapter04.degree_eq_grade` and
`QuarteroniSaccoSaleri.Chapter04.property_4_7`. -/
theorem example_4_8 :
    degree example_4_8_matrix (toLp 2 ![1, 1, 1, 1]) = 2 ∧
      (∀ m, 2 ≤ m → Module.finrank ℝ (krylovSubspace example_4_8_matrix (toLp 2 ![1, 1, 1, 1]) m)
        = 2) ∧
      degree example_4_8_matrix (toLp 2 ![1, 1, -1, 1]) = 4 := by
  have e1 : example_4_8_matrix *ᵥ ![1, 1, 1, 1] = ![1, 0, 0, 1] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have e2 : example_4_8_matrix *ᵥ ![1, 0, 0, 1] = ![2, -1, -1, 2] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  have f1 : example_4_8_matrix *ᵥ ![1, 1, -1, 1] = ![1, 2, -4, 3] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have f2 : example_4_8_matrix *ᵥ ![1, 2, -4, 3] = ![0, 7, -13, 10] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have f3 : example_4_8_matrix *ᵥ ![0, 7, -13, 10] = ![-7, 27, -43, 33] := by
    ext i
    fin_cases i <;> simp [example_4_8_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      norm_num
  have hv : degree example_4_8_matrix (toLp 2 ![1, 1, 1, 1]) = 2 := by
    rw [degree_eq_grade]
    refine le_antisymm (grade_le_of_exists_fun ![-1, 3] ?_) (lt_grade_of_forall_fun fun c hc => ?_)
    · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, toEuclideanLin_toLp,
        ← toLp_smul, ← toLp_add, one_mulVec, pow_succ, ← mulVec_mulVec, Matrix.one_mul, e1, e2,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      congr 1
      ext i
      fin_cases i <;> simp <;> norm_num
    · simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, toEuclideanLin_toLp, ← toLp_smul,
        one_mulVec, pow_succ, Matrix.one_mul, e1] at hc
      have h := congrArg ofLp hc
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      linarith
  refine ⟨hv, fun m hm => ?_, ?_⟩
  · rw [(property_4_7 _ _ _).2, hv, min_eq_right hm]
  · rw [degree_eq_grade]
    refine le_antisymm ?_ (lt_grade_of_forall_fun fun c hc => ?_)
    · have := Krylov.grade_le_finrank (toEuclideanLin example_4_8_matrix) (toLp 2 ![1, 1, -1, 1])
      rwa [finrank_euclideanSpace_fin] at this
    · simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
        toEuclideanLin_toLp, ← toLp_smul, ← toLp_add, one_mulVec, pow_succ, ← mulVec_mulVec,
        Matrix.one_mul, f1, f2, f3] at hc
      have h := congrArg ofLp hc
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      have h3 := congrFun h 3
      simp at h0 h1 h2 h3
      linarith

end Example

/-! ### (4.55)–(4.56): the Arnoldi algorithm -/

section Arnoldi

variable (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : EuclideanSpace ℝ (Fin n))

/-- **Equation (4.55)** of [quarteroni2000numerical], the **Arnoldi algorithm**. Let
$A \in \mathbb{R}^{n \times n}$ and $v_1 \in \mathbb{R}^n$. Starting from $v_1$, the algorithm
computes for $k = 1, 2, \dots$
$$h_{ik} = v_i^T A v_k \quad (i = 1, \dots, k), \qquad w_k = A v_k - \sum_{i=1}^{k} h_{ik} v_i,
  \qquad h_{k+1,k} = \|w_k\|_2,$$
and the next vector $v_{k+1} = w_k / \|w_k\|_2$.

The Lean vectors are indexed from $0$: `arnoldi A v₁ 0` is $v_1$, and `arnoldi A v₁ (k - 1)` is
the vector $v_k$ of the source. The source stops the process when $w_k = 0$ (a breakdown). Here
Lean's convention $0^{-1} = 0$ makes all later vectors $0$. -/
noncomputable def arnoldi : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => v₁
  | k + 1 =>
    let v : Fin (k + 1) → EuclideanSpace ℝ (Fin n) := fun i => arnoldi (i : ℕ)
    let Av := toEuclideanLin A (v (Fin.last k))
    let w := Av - ∑ i : Fin (k + 1), inner ℝ (v i) Av • v i
    ((‖w‖ : ℝ)⁻¹) • w
  termination_by k => k
  decreasing_by exact i.isLt

/-- **Equation (4.55)** of [quarteroni2000numerical], the Arnoldi coefficients
$h_{ik} = v_i^T A v_k$, in the 0-based indexing of `QuarteroniSaccoSaleri.Chapter04.arnoldi`.
They are defined for all $i$ and $k$. When $v_1$ is a unit vector, they vanish for $i > k + 1$
(`QuarteroniSaccoSaleri.Chapter04.equation_4_56`).

The value `arnoldiH A v₁ (i - 1) (k - 1)` is the coefficient $h_{ik}$ of the source. -/
noncomputable def arnoldiH (i k : ℕ) : ℝ :=
  inner ℝ (arnoldi A v₁ i) (toEuclideanLin A (arnoldi A v₁ k))

/-- **Equation (4.55)** of [quarteroni2000numerical], the vector
$w_k = A v_k - \sum_{i \le k} h_{ik} v_i$, in the 0-based indexing of
`QuarteroniSaccoSaleri.Chapter04.arnoldi`. -/
noncomputable def arnoldiW (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin A (arnoldi A v₁ k) - ∑ i ∈ range (k + 1), arnoldiH A v₁ i k • arnoldi A v₁ i

/-- The Arnoldi algorithm starts at $v_1$: `arnoldi A v₁ 0 = v₁`. -/
@[simp]
theorem arnoldi_zero : arnoldi A v₁ 0 = v₁ := by rw [arnoldi]

/-- **Equation (4.55)** of [quarteroni2000numerical]. The Arnoldi vectors satisfy
$v_{k+1} = w_k / \|w_k\|_2$, with $v_{k+1} = 0$ when $w_k = 0$. -/
theorem arnoldi_succ (k : ℕ) :
    arnoldi A v₁ (k + 1) = ((‖arnoldiW A v₁ k‖ : ℝ)⁻¹) • arnoldiW A v₁ k := by
  rw [arnoldi, arnoldiW]
  simp only [arnoldiH, Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => inner ℝ (arnoldi A v₁ i) (toEuclideanLin A (arnoldi A v₁ k)) • arnoldi A v₁ i)
    (k + 1)]

/-- The vector $w_k$ of (4.55) agrees with the backbone's `Arnoldi.w` as soon as the Arnoldi vectors
up to $v_k$ agree with the backbone's. -/
private theorem arnoldiW_eq_of_forall {r : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (ih : ∀ i ≤ k, arnoldi A v₁ i = Arnoldi.vec (toEuclideanLin A) r i) :
    arnoldiW A v₁ k = Arnoldi.w (toEuclideanLin A) r k := by
  have hsum : ∑ i ∈ range (k + 1), arnoldiH A v₁ i k • arnoldi A v₁ i =
      ∑ i ∈ range (k + 1),
        Arnoldi.coeff (toEuclideanLin A) r i k • Arnoldi.vec (toEuclideanLin A) r i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [arnoldiH, ih i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ih k le_rfl]
    rfl
  rw [arnoldiW, Arnoldi.w, hsum, ih k le_rfl]

/-- Let $r \in \mathbb{R}^n$ be a vector whose normalization, the first backbone Arnoldi vector
`Arnoldi.vec (toEuclideanLin A) r 0`, is $v_1$. Then the algorithm (4.55) started at $v_1$
computes the backbone's Arnoldi vectors of $r$: `arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A)
r k` for every $k$.

The two instances are a unit vector $v_1$ (`QuarteroniSaccoSaleri.Chapter04.arnoldi_eq_vec`) and
$v_1 = r/\|r\|_2$ (`QuarteroniSaccoSaleri.Chapter04.arnoldi_normalize`). -/
theorem arnoldi_eq_vec_of_vec_zero {r : EuclideanSpace ℝ (Fin n)}
    (h0 : Arnoldi.vec (toEuclideanLin A) r 0 = v₁) (k : ℕ) :
    arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A) r k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [arnoldi_zero, h0]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [arnoldi_succ, Arnoldi.vec_succ_eq,
        arnoldiW_eq_of_forall A v₁ fun i hi => ih i (Nat.lt_succ_of_le hi)]
      rfl

/-- Let $A \in \mathbb{R}^{n \times n}$ and let $v_1$ be a unit vector. The Arnoldi algorithm (4.55)
computes the Gram–Schmidt orthonormalization `Arnoldi.vec` of the Krylov sequence
$v_1, Av_1, A^2 v_1, \dots$; its coefficients $h_{ik}$ are `Arnoldi.coeff` and its vectors $w_k$
are `Arnoldi.w`. This identifies (4.55) with the backbone. -/
theorem arnoldi_eq_vec (hv : ‖v₁‖ = 1) :
    (∀ k, arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A) v₁ k) ∧
      (∀ i k, arnoldiH A v₁ i k = Arnoldi.coeff (toEuclideanLin A) v₁ i k) ∧
      ∀ k, arnoldiW A v₁ k = Arnoldi.w (toEuclideanLin A) v₁ k := by
  have hv0 : v₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  have hvec : ∀ k, arnoldi A v₁ k = Arnoldi.vec (toEuclideanLin A) v₁ k := by
    refine arnoldi_eq_vec_of_vec_zero A v₁ ?_
    rw [Arnoldi.vec_zero (toEuclideanLin A) v₁ hv0, hv]
    simp
  refine ⟨hvec, fun i k => ?_, fun k => arnoldiW_eq_of_forall A v₁ fun i _ => hvec i⟩
  rw [arnoldiH, hvec, hvec]
  rfl

/-- Let $r \in \mathbb{R}^n$, $r \neq 0$. The Arnoldi algorithm started at $v_1 = r/\|r\|_2$, the
start of the Krylov methods for the residual $r = r^{(0)}$, computes the backbone's Arnoldi
vectors `Arnoldi.vec` and coefficients `Arnoldi.coeff` of $r$. -/
theorem arnoldi_normalize {r : EuclideanSpace ℝ (Fin n)} (hr : r ≠ 0) :
    (∀ k, arnoldi A ((‖r‖ : ℝ)⁻¹ • r) k = Arnoldi.vec (toEuclideanLin A) r k) ∧
      ∀ i k, arnoldiH A ((‖r‖ : ℝ)⁻¹ • r) i k = Arnoldi.coeff (toEuclideanLin A) r i k := by
  have hvec := arnoldi_eq_vec_of_vec_zero A ((‖r‖ : ℝ)⁻¹ • r)
    (Arnoldi.vec_zero (toEuclideanLin A) r hr)
  refine ⟨hvec, fun i k => ?_⟩
  rw [arnoldiH, hvec, hvec]
  rfl

/-- The range of a family indexed by `Fin m` is the image of the set of natural numbers below $m$.
-/
private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun i : Fin m => f (i : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-- **Section 4.4** of [quarteroni2000numerical], the sentence before (4.56). Let $v_1$ be a unit
vector and $m \le \deg_A(v_1)$, so that the method has not terminated before step $m$. Then the
Arnoldi vectors $v_1, \dots, v_m$ are orthonormal and form a basis of $K_m(A; v_1)$.

The proof uses the backbone's `Arnoldi.orthonormal` and `Arnoldi.span_vec`. -/
theorem arnoldi_basis (hv : ‖v₁‖ = 1) {m : ℕ} (hm : m ≤ degree A v₁) :
    Orthonormal ℝ (fun i : Fin m => arnoldi A v₁ i) ∧
      Submodule.span ℝ (Set.range fun i : Fin m => arnoldi A v₁ i) = krylovSubspace A v₁ m := by
  obtain ⟨hvec, -, -⟩ := arnoldi_eq_vec A v₁ hv
  rw [degree_eq_grade] at hm
  simp only [hvec]
  refine ⟨?_, ?_⟩
  · have h := Arnoldi.orthonormal (toEuclideanLin A) v₁
    exact h.comp (fun i : Fin m => Fin.castLE hm i) (Fin.castLE_injective hm)
  · rw [range_fin_eq_image_Iio, Arnoldi.span_vec, krylovSubspace_eq]

/-- **Equation (4.56)** of [quarteroni2000numerical], the matrix $V_m \in \mathbb{R}^{n \times m}$
whose columns are the Arnoldi vectors $v_1, \dots, v_m$. -/
noncomputable def V (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => arnoldi A v₁ j i

/-- **Equation (4.56)** of [quarteroni2000numerical], the matrix $H_m \in \mathbb{R}^{m \times m}$
of the Arnoldi coefficients $h_{ij}$, $1 \le i, j \le m$. It consists of the first $m$ rows of
$\hat H_m$. -/
noncomputable def H (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => arnoldiH A v₁ i j

/-- **Equation (4.56)** of [quarteroni2000numerical], the matrix
$\hat H_m \in \mathbb{R}^{(m+1) \times m}$ of the Arnoldi coefficients $h_{ij}$,
$1 \le i \le m + 1$, $1 \le j \le m$. It is upper Hessenberg
(`QuarteroniSaccoSaleri.Chapter04.equation_4_56`). -/
noncomputable def Hhat (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j => arnoldiH A v₁ i j

/-- For all $p$ and $m$, the entry $(i, j)$ of $V_p^T A V_m$ is $v_i^T A v_j = h_{ij}$. -/
private theorem transpose_V_mul_mul_V_apply (p m : ℕ) (i : Fin p) (j : Fin m) :
    ((V A v₁ p)ᵀ * A * V A v₁ m) i j = arnoldiH A v₁ i j := by
  simp only [arnoldiH, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toEuclideanLin,
    Matrix.mul_apply, Matrix.transpose_apply, V, Matrix.of_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Equation (4.56)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and let
$v_1$ be a unit vector. Then
$$V_m^T A V_m = H_m, \qquad V_{m+1}^T A V_m = \hat H_m,$$
where $\hat H_m$ is upper Hessenberg, that is $h_{ij} = 0$ for $i > j + 1$, and $H_m$ consists
of the first $m$ rows of $\hat H_m$. The matrices $H_m$ and $\hat H_m$ are the backbone's
`Arnoldi.hessenbergSq` and `Arnoldi.hessenberg`.

The two products are the definition of the coefficients. The Hessenberg structure is the
backbone's `Arnoldi.coeff_eq_zero_of_lt`, and it needs $v_1$ to be a unit vector. Upper
Hessenberg form is `Matrix.IsUpperHessenbergRect`. -/
theorem equation_4_56 (hv : ‖v₁‖ = 1) (m : ℕ) :
    (V A v₁ m)ᵀ * A * V A v₁ m = H A v₁ m ∧ (V A v₁ (m + 1))ᵀ * A * V A v₁ m = Hhat A v₁ m ∧
      (Hhat A v₁ m).IsUpperHessenbergRect ∧
      (∀ i j : Fin m, H A v₁ m i j = Hhat A v₁ m (Fin.castSucc i) j) ∧
      H A v₁ m = Arnoldi.hessenbergSq (toEuclideanLin A) v₁ m ∧
      Hhat A v₁ m = Arnoldi.hessenberg (toEuclideanLin A) v₁ m := by
  obtain ⟨-, hH, -⟩ := arnoldi_eq_vec A v₁ hv
  have hHhat : Hhat A v₁ m = Arnoldi.hessenberg (toEuclideanLin A) v₁ m := by
    ext i j
    simp only [Hhat, Arnoldi.hessenberg, Matrix.of_apply, hH]
  refine ⟨?_, ?_, ?_, fun i j => rfl, ?_, hHhat⟩
  · ext i j
    rw [transpose_V_mul_mul_V_apply]
    rfl
  · ext i j
    rw [transpose_V_mul_mul_V_apply]
    rfl
  · rw [hHhat]
    exact Arnoldi.hessenberg_isUpperHessenbergRect _ _ m
  · ext i j
    simp only [H, Arnoldi.hessenbergSq, Matrix.of_apply, hH]

/-- **Section 4.4** of [quarteroni2000numerical], the sentence after (4.56). Let $v_1$ be a unit
vector. The Arnoldi algorithm terminates exactly at the degree of $v_1$: for every $j \ge 1$,
$w_j = 0$ if and only if $h_{j+1,j} = 0$, if and only if $\deg_A(v_1) \le j$; and the computed
vector $v_j$ is $0$ if and only if $\deg_A(v_1) < j$.

The Lean statement uses 0-based indices:

* `arnoldiW A v₁ k` is $w_{k+1}$,
* `arnoldiH A v₁ (k + 1) k` is $h_{k+2,k+1}$,
* `arnoldi A v₁ k` is $v_{k+1}$.

The proof uses the backbone's `Arnoldi.coeff_succ_self_eq_zero_iff` and
`Arnoldi.vec_eq_zero_iff`. -/
theorem arnoldi_breakdown_iff (hv : ‖v₁‖ = 1) (k : ℕ) :
    (arnoldiW A v₁ k = 0 ↔ degree A v₁ ≤ k + 1) ∧
      (arnoldiH A v₁ (k + 1) k = 0 ↔ degree A v₁ ≤ k + 1) ∧
      (arnoldi A v₁ k = 0 ↔ degree A v₁ ≤ k) := by
  obtain ⟨hvec, hH, hW⟩ := arnoldi_eq_vec A v₁ hv
  rw [degree_eq_grade, hvec, hH, hW, Arnoldi.coeff_succ_self_eq_zero_iff, Arnoldi.vec_eq_zero_iff,
    ← Arnoldi.coeff_succ_self_eq_zero_iff, Arnoldi.coeff_succ_self, RCLike.ofReal_real_eq_id, id_eq,
    norm_eq_zero]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end Arnoldi

/-! ### (4.57)–(4.58): the two Krylov methods -/

section Specifications

/-- A nonsingular matrix $A \in \mathbb{R}^{n \times n}$ acts injectively on
`EuclideanSpace ℝ (Fin n)`. The proof is Mathlib's `Matrix.mulVec_injective_iff_isUnit`. -/
theorem toEuclideanLin_injective_of_isUnit {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    Function.Injective (toEuclideanLin A) := by
  intro x y hxy
  have h := congrArg ofLp hxy
  rw [ofLp_toEuclideanLin, ofLp_toEuclideanLin] at h
  exact ofLp_injective 2 (mulVec_injective_iff_isUnit.mpr hA h)

variable (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- **Equation (4.57)** of [quarteroni2000numerical], the Arnoldi method for linear systems (FOM).
Let $A \in \mathbb{R}^{n \times n}$, $b, x^{(0)} \in \mathbb{R}^n$ and $r^{(0)} = b - Ax^{(0)}$.
A vector $x$ is the **FOM iterate** at step $k$ if $x \in W_k = x^{(0)} + K_k(A; r^{(0)})$ and
the residual $b - Ax$ is orthogonal to every vector of $K_k(A; r^{(0)})$.

It is the backbone's Galerkin specification `Krylov.IsGalerkinIterate`
(`QuarteroniSaccoSaleri.Chapter04.equation_4_57_iff`). -/
def equation_4_57 (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x - x₀ ∈ krylovSubspace A (b - toEuclideanLin A x₀) k ∧
    ∀ v ∈ krylovSubspace A (b - toEuclideanLin A x₀) k, inner ℝ v (b - toEuclideanLin A x) = 0

/-- The FOM specification (4.57) is the backbone's Galerkin specification `Krylov.IsGalerkinIterate
(toEuclideanLin A) b x₀ k`. -/
theorem equation_4_57_iff (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    equation_4_57 A b x₀ k x ↔ Krylov.IsGalerkinIterate (toEuclideanLin A) b x₀ k x := by
  rw [equation_4_57, krylovSubspace_eq]
  constructor
  · rintro ⟨hmem, horth⟩
    exact ⟨hmem, (Submodule.mem_orthogonal _ _).2 horth⟩
  · rintro ⟨hmem, horth⟩
    exact ⟨hmem, (Submodule.mem_orthogonal _ _).1 horth⟩

/-- **Equation (4.58)** of [quarteroni2000numerical], the GMRES method. Let
$A \in \mathbb{R}^{n \times n}$, $b, x^{(0)} \in \mathbb{R}^n$ and $r^{(0)} = b - Ax^{(0)}$. A
vector $x$ is the **GMRES iterate** at step $k$ if $x \in W_k = x^{(0)} + K_k(A; r^{(0)})$ and
it minimizes the Euclidean norm of the residual over $W_k$:
$$\|b - Ax\|_2 = \min_{v \in W_k} \|b - Av\|_2.$$

It is the backbone's minimal-residual specification `Krylov.IsMinResidualIterate`
(`QuarteroniSaccoSaleri.Chapter04.equation_4_58_iff`). -/
def equation_4_58 (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x - x₀ ∈ krylovSubspace A (b - toEuclideanLin A x₀) k ∧
    ∀ y, y - x₀ ∈ krylovSubspace A (b - toEuclideanLin A x₀) k →
      ‖b - toEuclideanLin A x‖ ≤ ‖b - toEuclideanLin A y‖

/-- The GMRES specification (4.58) is the backbone's minimal-residual specification
`Krylov.IsMinResidualIterate (toEuclideanLin A) b x₀ k`. A GMRES iterate exists at every step,
and it is unique when $A$ is nonsingular.

Existence is the backbone's `Krylov.exists_isMinResidualIterate`, and uniqueness is
`Krylov.existsUnique_isMinResidualIterate_of_injective`. -/
theorem equation_4_58_iff (k : ℕ) :
    (∀ x, equation_4_58 A b x₀ k x ↔ Krylov.IsMinResidualIterate (toEuclideanLin A) b x₀ k x) ∧
      (∃ x, equation_4_58 A b x₀ k x) ∧ (IsUnit A → ∃! x, equation_4_58 A b x₀ k x) := by
  have hiff : ∀ x, equation_4_58 A b x₀ k x ↔
      Krylov.IsMinResidualIterate (toEuclideanLin A) b x₀ k x := by
    intro x
    rw [equation_4_58, krylovSubspace_eq]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.min⟩⟩
  refine ⟨hiff, ?_, fun hA => ?_⟩
  · simp only [hiff]
    exact Krylov.exists_isMinResidualIterate _ b x₀ k
  · simp only [hiff]
    exact Krylov.existsUnique_isMinResidualIterate_of_injective
      (toEuclideanLin_injective_of_isUnit hA) b x₀ k

/-- The first unit vector $e_1 = (1, 0, \dots, 0)$ of $\mathbb{R}^m$; for $m = 0$ it is the empty
vector. -/
def e₁ (m : ℕ) : Fin m → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

/-- For $\beta \in \mathbb{R}$, the vector $\beta e_1 \in \mathbb{R}^m$ is the backbone's
`Krylov.firstVec β m`. -/
theorem smul_e₁_eq_firstVec (β : ℝ) (m : ℕ) : β • e₁ m = Krylov.firstVec β m := by
  funext i
  simp only [e₁, Krylov.firstVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **Equation (4.59)** of [quarteroni2000numerical]. For $z \in \mathbb{R}^k$, the product $V_k z$
is $\sum_j z_j v_j$: the iterate $x^{(0)} + V_k z^{(k)}$ expanded in the Arnoldi basis. -/
theorem V_mulVec (v₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (z : Fin k → ℝ) :
    toEuclideanLin (V A v₁ k) (toLp 2 z) = ∑ j, z j • arnoldi A v₁ j := by
  rw [toEuclideanLin_apply_eq_sum]
  rfl

end Specifications

/-! ### §4.4.1 The Arnoldi method for linear systems -/

section FOM

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- The Arnoldi vectors of the start $v_1 = r^{(0)}/\|r^{(0)}\|_2$ are the backbone's Arnoldi
vectors of the residual $r^{(0)}$, and the matrices $H_k$ and $\hat H_k$ are
`Arnoldi.hessenbergSq` and `Arnoldi.hessenberg`. -/
private theorem arnoldi_residual (hr : b - toEuclideanLin A x₀ ≠ 0) :
    (∀ k, arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
        Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      (∀ k, H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
        Arnoldi.hessenbergSq (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      ∀ k, Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
        Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k := by
  obtain ⟨hvec, hH⟩ := arnoldi_normalize A hr
  refine ⟨hvec, fun k => ?_, fun k => ?_⟩
  · ext i j
    simp only [H, Arnoldi.hessenbergSq, Matrix.of_apply, hH]
  · ext i j
    simp only [Hhat, Arnoldi.hessenberg, Matrix.of_apply, hH]

/-- The degree of the residual $r^{(0)}$ with respect to $A$ is the grade `Krylov.grade` that the
backbone's statements use. -/
private theorem degree_residual :
    degree A (b - toEuclideanLin A x₀) =
      Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) :=
  degree_eq_grade A _

/-- **Equations (4.59)–(4.62)** of [quarteroni2000numerical]. Let $r^{(0)} = b - Ax^{(0)} \neq 0$,
let $k \le \deg_A(r^{(0)})$, and let the Arnoldi algorithm start from
$v_1 = r^{(0)}/\|r^{(0)}\|_2$. For $z \in \mathbb{R}^k$, the vector $x^{(0)} + V_k z$ is the FOM
iterate at step $k$ if and only if $z$ solves the Hessenberg system (4.62)
$$H_k z = \|r^{(0)}\|_2 \, e_1.$$
Moreover the FOM iterate at step $k$ exists and is unique if and only if $H_k$ is nonsingular.

The source derives (4.62) from (4.60)–(4.61), $V_k^T r^{(k)} = V_k^T r^{(0)} - V_k^T A V_k
z^{(k)} = 0$, with $V_k^T r^{(0)} = \|r^{(0)}\|_2 e_1$. The proof uses the backbone's
`Krylov.isGalerkinIterate_iff_mulVec_eq` and `Krylov.existsUnique_isGalerkinIterate_iff_isUnit`. -/
theorem equation_4_62 (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ}
    (hk : k ≤ degree A (b - toEuclideanLin A x₀)) (z : Fin k → ℝ) :
    (equation_4_57 A b x₀ k (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) ↔
      H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z =
        ‖b - toEuclideanLin A x₀‖ • e₁ k) ∧
      ((∃! x, equation_4_57 A b x₀ k x) ↔
        IsUnit (H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k)) := by
  obtain ⟨hvec, hH, -⟩ := arnoldi_residual hr
  rw [degree_residual] at hk
  simp only [equation_4_57_iff, hvec, hH, smul_e₁_eq_firstVec]
  exact ⟨Krylov.isGalerkinIterate_iff_mulVec_eq hk z,
    Krylov.existsUnique_isGalerkinIterate_iff_isUnit hk⟩

/-- **Theorem 4.13** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular and $r^{(0)} = b - Ax^{(0)}$. In exact arithmetic the Arnoldi method yields the
solution of $Ax = b$ after at most $n$ iterations: $\deg_A(r^{(0)}) \le n$, and for every
$k \ge \deg_A(r^{(0)})$ the FOM iterate at step $k$ exists, is unique, and solves $Ax = b$. The
step $k = n$ is reached because $K_n(A; r^{(0)}) = \mathbb{R}^n$, and an earlier step at a
breakdown of the Arnoldi algorithm.

The proof of the source inverts $H_m$ at the breakdown without justification. That $H_m$ is
nonsingular at the degree of $r^{(0)}$ follows from the injectivity of $A$; this is the
backbone's `Krylov.existsUnique_isGalerkinIterate_of_grade_le`, and
`Krylov.IsGalerkinIterate.apply_eq_of_grade_le` gives the exactness. -/
theorem theorem_4_13 (hA : IsUnit A) :
    degree A (b - toEuclideanLin A x₀) ≤ n ∧
      ∀ k, degree A (b - toEuclideanLin A x₀) ≤ k →
        (∃! x, equation_4_57 A b x₀ k x) ∧
          ∀ x, equation_4_57 A b x₀ k x → toEuclideanLin A x = b := by
  have hinj := toEuclideanLin_injective_of_isUnit hA
  refine ⟨degree_le A _, fun k hk => ?_⟩
  rw [degree_residual] at hk
  simp only [equation_4_57_iff]
  exact ⟨Krylov.existsUnique_isGalerkinIterate_of_grade_le hinj hk,
    fun x hx => hx.apply_eq_of_grade_le hk⟩

/-- **Equation (4.63)** of [quarteroni2000numerical], the residual formula before it. Let
$r^{(0)} = b - Ax^{(0)} \neq 0$, let $k \ge 1$, let the Arnoldi algorithm start from
$v_1 = r^{(0)}/\|r^{(0)}\|_2$, and let $z \in \mathbb{R}^k$ solve $H_k z = \|r^{(0)}\|_2 e_1$.
Then $x^{(k)} = x^{(0)} + V_k z$ has the residual
$$b - Ax^{(k)} = -h_{k+1,k} \, (e_k^T z) \, v_{k+1}.$$
If moreover $k < \deg_A(r^{(0)})$, so that $\|v_{k+1}\|_2 = 1$, then
$\|b - Ax^{(k)}\|_2 = h_{k+1,k} \, |e_k^T z|$, the quantity that the stopping test (4.63)
divides by $\|r^{(0)}\|_2$.

The proof uses the backbone's `Krylov.residual_galerkin_eq`. The Lean statement uses 0-based
indices:

* `arnoldiH … k (k - 1)` is $h_{k+1,k}$,
* `z ⟨k - 1, _⟩` is $e_k^T z$,
* `arnoldi … k` is $v_{k+1}$. -/
theorem equation_4_63 (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ} (hk : 0 < k) (z : Fin k → ℝ)
    (hz : H A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z =
      ‖b - toEuclideanLin A x₀‖ • e₁ k) :
    b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) =
        -(arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k (k - 1) *
            z ⟨k - 1, Nat.sub_lt hk one_pos⟩) •
          arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k ∧
      (k < degree A (b - toEuclideanLin A x₀) →
        ‖b - toEuclideanLin A (x₀ + ∑ j, z j •
            arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j)‖ =
          arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k (k - 1) *
            |z ⟨k - 1, Nat.sub_lt hk one_pos⟩|) := by
  obtain ⟨hvec, hH, -⟩ := arnoldi_residual hr
  obtain ⟨-, hcoeff⟩ := arnoldi_normalize A hr
  rw [hH, smul_e₁_eq_firstVec] at hz
  have hres := Krylov.residual_galerkin_eq hk z hz
  simp only [hvec, hcoeff]
  refine ⟨hres, fun hlt => ?_⟩
  rw [degree_residual] at hlt
  have hnonneg : 0 ≤ Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀) k (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Arnoldi.coeff_succ_self, RCLike.ofReal_real_eq_id, id_eq]
    exact norm_nonneg _
  rw [hres, norm_smul, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg,
    Arnoldi.norm_vec_eq_one_of_lt_grade _ _ hlt, mul_one]

end FOM

/-! ### §4.4.2 The GMRES method -/

section GMRES

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **Equations (4.64)–(4.65)** of [quarteroni2000numerical]. Let $r^{(0)} = b - Ax^{(0)} \neq 0$,
let the Arnoldi algorithm start from $v_1 = r^{(0)}/\|r^{(0)}\|_2$, and let
$z \in \mathbb{R}^k$. Then $x^{(k)} = x^{(0)} + V_k z$ has the residual
$$r^{(k)} = r^{(0)} - A V_k z = V_{k+1} \big(\|r^{(0)}\|_2 \, e_1 - \hat H_k z\big),$$
because $r^{(0)} = \|r^{(0)}\|_2 v_1$ and (4.56) holds.

The product with $V_{k+1}$ is written as the sum $\sum_{i \le k} (\cdot)_i v_{i+1}$. The proof
uses the backbone's `Krylov.HessenbergRelation₂.residual_eq` for `Arnoldi.hessenbergRelation`. -/
theorem equation_4_65 (hr : b - toEuclideanLin A x₀ ≠ 0) (k : ℕ) (z : Fin k → ℝ) :
    b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) =
      (b - toEuclideanLin A x₀) - toEuclideanLin A
        (∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) ∧
      b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) =
      ∑ i : Fin (k + 1), (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1) -
          Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z) i •
        arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) i := by
  obtain ⟨hvec, -, hHhat⟩ := arnoldi_residual hr
  refine ⟨by rw [map_add, sub_add_eq_sub_sub], ?_⟩
  simp only [hvec, hHhat, smul_e₁_eq_firstVec]
  exact (Arnoldi.hessenbergRelation (toEuclideanLin A) (b - toEuclideanLin A x₀)).residual_eq
    (Arnoldi.smul_vec_zero _ _).symm k z

/-- **Equation (4.66)** of [quarteroni2000numerical]. Let $r^{(0)} = b - Ax^{(0)} \neq 0$, let
$k \le \deg_A(r^{(0)})$, let the Arnoldi algorithm start from $v_1 = r^{(0)}/\|r^{(0)}\|_2$, and
let $z \in \mathbb{R}^k$. Then $x^{(0)} + V_k z$ is the GMRES iterate at step $k$ if and only if
$z$ minimizes
$$\big\| \|r^{(0)}\|_2 \, e_1 - \hat H_k y \big\|_2$$
over $y \in \mathbb{R}^k$. This holds because the matrix $V_{k+1}$ in (4.65) has orthonormal
columns and does not change the Euclidean norm: $\|b - A(x^{(0)} + V_k z)\|_2 = \|\|r^{(0)}\|_2
e_1 - \hat H_k z\|_2$.

The proof uses the backbone's `Krylov.isMinResidualIterate_iff_isMinOn` and
`Krylov.norm_residual_eq_norm_firstVec_sub_mulVec`. -/
theorem equation_4_66 (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ}
    (hk : k ≤ degree A (b - toEuclideanLin A x₀)) (z : Fin k → ℝ) :
    (equation_4_58 A b x₀ k (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j) ↔
      IsMinOn (fun y : Fin k → ℝ => ‖(toLp 2 (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1) -
          Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ y) :
            EuclideanSpace ℝ (Fin (k + 1)))‖) Set.univ z) ∧
      ‖b - toEuclideanLin A (x₀ +
        ∑ j, z j • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) j)‖ =
        ‖(toLp 2 (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1) -
          Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k *ᵥ z) :
            EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  obtain ⟨hvec, -, hHhat⟩ := arnoldi_residual hr
  rw [degree_residual] at hk
  simp only [hvec, hHhat, smul_e₁_eq_firstVec, (equation_4_58_iff A b x₀ k).1]
  exact ⟨Krylov.isMinResidualIterate_iff_isMinOn hk z,
    Krylov.norm_residual_eq_norm_firstVec_sub_mulVec hk z⟩

/-- **Property 4.8** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, $r^{(0)} = b - Ax^{(0)}$ and $m \ge 0$. The Arnoldi algorithm breaks down at step
$m$, that is $\deg_A(r^{(0)}) \le m$, if and only if the GMRES iterate $x^{(m)}$ is the exact
solution of $Ax = b$. The GMRES iterate at step $m$ exists and is unique.

**Generalization.** The source states the property for $m < n$. The equivalence holds for every
$m$, and at $m = n$ both sides are true.

By `QuarteroniSaccoSaleri.Chapter04.arnoldi_breakdown_iff`, $\deg_A(r^{(0)}) \le m$ is the
vanishing of $h_{m+1,m}$. The proof uses the backbone's
`Krylov.IsMinResidualIterate.apply_eq_of_grade_le` and `Krylov.grade_le_of_apply_eq`. -/
theorem property_4_8 (hA : IsUnit A) (m : ℕ) :
    (degree A (b - toEuclideanLin A x₀) ≤ m ↔
        ∀ x, equation_4_58 A b x₀ m x → toEuclideanLin A x = b) ∧
      ∃! x, equation_4_58 A b x₀ m x := by
  have hinj := toEuclideanLin_injective_of_isUnit hA
  obtain ⟨hiff, hex, hu⟩ := equation_4_58_iff A b x₀ m
  refine ⟨?_, hu hA⟩
  rw [degree_residual]
  simp only [hiff]
  constructor
  · intro hm x hx
    exact hx.apply_eq_of_grade_le hm hinj.injOn
  · intro h
    obtain ⟨x, hx⟩ := hex
    rw [hiff] at hx
    exact Krylov.grade_le_of_apply_eq hx.mem (h x hx)

/-- **Section 4.4.2** of [quarteroni2000numerical], the paragraph on Givens rotations after
Program 23. Let $r^{(0)} = b - Ax^{(0)} \neq 0$ and let the Arnoldi algorithm start from
$v_1 = r^{(0)}/\|r^{(0)}\|_2$. The product $Q_k$ of $k$ plane rotations transforms $\hat H_k$
into $Q_k \hat H_k = R_k$, upper triangular with a zero last row. The rotated right-hand side
$f_k = Q_k (\|r^{(0)}\|_2 e_1)$ has the last component $\gamma_k$; its first $k$ components and
its last component are the backbone's `Krylov.gvec` and `Krylov.gamma`. If
$k < \deg_A(r^{(0)})$, then every GMRES iterate $x$ at step $k$ satisfies
$\|b - Ax\|_2 = |\gamma_k|$, so that the norm of the residual is available without forming
$x^{(k)}$.

The matrices are the backbone's `Krylov.givensQ` and `Krylov.hessenbergOf (Krylov.rotated …) k`.
The three clauses are `Krylov.givensQ_mul_hessenbergOf`, `Krylov.givensQ_mulVec_firstVec` and
`Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma`. -/
theorem gmres_norm_residual_eq_norm_gamma (hr : b - toEuclideanLin A x₀ ≠ 0) (k : ℕ) :
    Krylov.givensQ (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀))) k *
        Hhat A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
      Krylov.hessenbergOf (Krylov.rotated
        (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀))) k) k ∧
      (Krylov.givensQ (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
          k *ᵥ (‖b - toEuclideanLin A x₀‖ • e₁ (k + 1)) =
        fun i : Fin (k + 1) => if (i : ℕ) < k then
          Krylov.gvec (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
            ‖b - toEuclideanLin A x₀‖ i
        else Krylov.gamma
          (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
            ‖b - toEuclideanLin A x₀‖ k) ∧
      (k < degree A (b - toEuclideanLin A x₀) → ∀ x, equation_4_58 A b x₀ k x →
        ‖b - toEuclideanLin A x‖ = |Krylov.gamma
          (arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)))
            ‖b - toEuclideanLin A x₀‖ k|) := by
  obtain ⟨-, hcoeff⟩ := arnoldi_normalize A hr
  have hfun : arnoldiH A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) =
      Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀) :=
    funext fun i => funext (hcoeff i)
  obtain ⟨-, -, hHhat⟩ := arnoldi_residual hr
  rw [hfun, hHhat, smul_e₁_eq_firstVec]
  refine ⟨Krylov.givensQ_mul_hessenbergOf _ k, Krylov.givensQ_mulVec_firstVec _ _ k,
    fun hk x hx => ?_⟩
  rw [degree_residual] at hk
  rw [(equation_4_58_iff A b x₀ k).1] at hx
  have h := hx.norm_residual_eq_norm_gamma hk
  rwa [Real.norm_eq_abs] at h

end GMRES

/-! ### Remark 4.4: projection methods -/

section ProjectionMethods

variable (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- **Remark 4.4** of [quarteroni2000numerical], projection methods. Let $Y$ and $L$ be subspaces of
$\mathbb{R}^n$. A **projection method** generates an approximate solution $x$ with
$x \in x^{(0)} + Y$ and with the residual $b - Ax$ orthogonal to $L$. The method is
**orthogonal** when $L = Y$, and **oblique** otherwise.

**Reading.** The source writes $x \in Y$. The Krylov instances need the affine translate
$x \in x^{(0)} + Y$, as in (4.59).

It is the backbone's Petrov–Galerkin specification `IsPetrovGalerkin`
(`QuarteroniSaccoSaleri.Chapter04.remark_4_4_iff`). -/
def remark_4_4 (Y L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x - x₀ ∈ Y ∧ b - toEuclideanLin A x ∈ Lᗮ

/-- A projection method of Remark 4.4 is the backbone's Petrov–Galerkin specification
`IsPetrovGalerkin`, and an orthogonal projection method ($L = Y$) is the Galerkin specification
`IsGalerkin`. -/
theorem remark_4_4_iff (Y L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    (remark_4_4 A b x₀ Y L x ↔ IsPetrovGalerkin (toEuclideanLin A) b x₀ Y L x) ∧
      (remark_4_4 A b x₀ Y Y x ↔ IsGalerkin (toEuclideanLin A) b x₀ Y x) :=
  ⟨⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.orth⟩⟩, ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mem, h.orth⟩⟩⟩

/-- **Remark 4.4** of [quarteroni2000numerical], the Krylov instances. Let $r^{(0)} = b - Ax^{(0)}$
and $Y_k = K_k(A; r^{(0)})$. The FOM iterate (4.57) is the orthogonal projection method with
$L_k = Y_k$, and the GMRES iterate (4.58) is the oblique projection method with $L_k = A Y_k$.

The second clause is the backbone's `IsMinResidual.iff_isPetrovGalerkin`. -/
theorem remark_4_4_krylov (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (equation_4_57 A b x₀ k x ↔ remark_4_4 A b x₀
        (krylovSubspace A (b - toEuclideanLin A x₀) k)
        (krylovSubspace A (b - toEuclideanLin A x₀) k) x) ∧
      (equation_4_58 A b x₀ k x ↔ remark_4_4 A b x₀
        (krylovSubspace A (b - toEuclideanLin A x₀) k)
        ((krylovSubspace A (b - toEuclideanLin A x₀) k).map (toEuclideanLin A)) x) := by
  constructor
  · exact and_congr Iff.rfl ⟨fun h => (Submodule.mem_orthogonal _ _).2 h,
      fun h => (Submodule.mem_orthogonal _ _).1 h⟩
  · rw [(equation_4_58_iff A b x₀ k).1, (remark_4_4_iff A b x₀ _ _ x).1, krylovSubspace_eq]
    exact IsMinResidual.iff_isPetrovGalerkin

/-- The coordinate subspace of a single index $i$ is the line spanned by the unit vector $e_i$. -/
private theorem blockSubspace_id_eq_span (i : Fin n) :
    EuclideanSpace.blockSubspace ℝ (id : Fin n → Fin n) i =
      ℝ ∙ EuclideanSpace.single i (1 : ℝ) := by
  ext v
  rw [EuclideanSpace.mem_blockSubspace, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v i, ?_⟩
    ext j
    by_cases hij : j = i
    · subst hij; simp
    · rw [hv j hij]; simp [hij]
  · rintro ⟨c, rfl⟩ j hj
    have hj' : j ≠ i := hj
    simp [hj']

/-- **Remark 4.4** of [quarteroni2000numerical], the Gauss–Seidel method. The source states: "The
Gauss–Seidel method is an orthogonal projection method where at the $k$-th step
$K = \operatorname{span}(e_k)$, the projection steps being carried out cyclically from $1$ to
$n$." Let $A \in \mathbb{R}^{n \times n}$ have nonzero diagonal entries and let
$b, x \in \mathbb{R}^n$. Then the coordinate subspaces are the lines $\operatorname{span}(e_i)$;
one Gauss–Seidel sweep from $x$ is the sweep of the multiplicative projection process over the
pairs $Y_i = L_i = \operatorname{span}(e_i)$, $i = 1, \dots, n$, in increasing order; and each
of its steps is the one-dimensional orthogonal projection step onto $\operatorname{span}(e_i)$,
which is a Galerkin step.

The Gauss–Seidel sweep is `Matrix.sorSweep A 1`, the multiplicative process is the backbone's
`Projection.multiplicativeStep`, the coordinate subspaces are `EuclideanSpace.blockSubspace` for
the trivial block labelling `id`, and the one-dimensional step is `Projection.step1`. The proof
is the backbone's `Matrix.blockGaussSeidelSplitting_step_eq_multiplicativeStep` at the labelling
`id`, together with `Projection.step1_isGalerkin`. -/
theorem remark_4_4_gaussSeidel (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, EuclideanSpace.blockSubspace ℝ (id : Fin n → Fin n) i =
        ℝ ∙ EuclideanSpace.single i (1 : ℝ)) ∧
      (toLp 2 (sorSweep A 1 b x) : EuclideanSpace ℝ (Fin n)) =
        Projection.multiplicativeStep (toEuclideanLin A) (toLp 2 b)
          (EuclideanSpace.blockSubspace ℝ id) (EuclideanSpace.blockSubspace ℝ id)
          (isNondegeneratePair_blockSubspace ((blockDiagPart_id A).symm ▸ h))
          ((Finset.univ : Finset (Fin n)).sort (· ≤ ·)) (toLp 2 x) ∧
      ∀ (i : Fin n) (y : EuclideanSpace ℝ (Fin n)),
        Projection.pairStep (toEuclideanLin A) (toLp 2 b) (EuclideanSpace.blockSubspace ℝ id i)
            (EuclideanSpace.blockSubspace ℝ id i)
            (isNondegeneratePair_blockSubspace ((blockDiagPart_id A).symm ▸ h) i) y =
          Projection.step1 (toEuclideanLin A) (toLp 2 b) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i 1) y ∧
        IsGalerkin (toEuclideanLin A) (toLp 2 b) y (ℝ ∙ EuclideanSpace.single i (1 : ℝ))
          (Projection.step1 (toEuclideanLin A) (toLp 2 b) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i 1) y) := by
  have h' : IsUnit (blockDiagPart (id : Fin n → Fin n) A) := (blockDiagPart_id A).symm ▸ h
  refine ⟨blockSubspace_id_eq_span, ?_, fun i y => ?_⟩
  · have hm : (gaussSeidelSplitting A h).m = (blockGaussSeidelSplitting id A h').m := by
      rw [(equation_4_13 h b x).2.2.1, D_sub_E]
      change _ = blockDiagPart id A + blockStrictLower id A
      rw [blockDiagPart_id, blockStrictLower_id]
    rw [blockGaussSeidelSplitting_step_eq_multiplicativeStep h', sorSweep_one_eq_mulVecStep A h,
      Stationary.Splitting.mulVecStep_eq_add_inv_mulVec, toLp_add, ← toEuclideanLin_toLp, toLp_sub,
      ← toEuclideanLin_toLp, hm]
  · have hdiag : A i i ≠ 0 := (isUnit_diagPart_iff A).1 h i
    have hinner : inner ℝ (EuclideanSpace.single i (1 : ℝ))
        (toEuclideanLin A (EuclideanSpace.single i (1 : ℝ))) ≠ 0 := by
      rw [EuclideanSpace.inner_single_left, ofLp_toEuclideanLin]
      simp [Matrix.mulVec, dotProduct, EuclideanSpace.single, hdiag]
    have hPG := Projection.step1_isPetrovGalerkin (A := toEuclideanLin A) (b := toLp 2 b)
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) y hinner
    refine ⟨?_, hPG⟩
    have hspan := blockSubspace_id_eq_span (n := n) i
    have hu := (existsUnique_isPetrovGalerkin_of_finrank_eq (A := toEuclideanLin A) (toLp 2 b) y
      (EuclideanSpace.blockSubspace ℝ id i) (EuclideanSpace.blockSubspace ℝ id i)
      (isNondegeneratePair_blockSubspace h' i).finrank_eq
      (isNondegeneratePair_blockSubspace h' i).eq_zero_of_mem_orthogonal)
    refine (hu.unique ?_ ?_).symm
    · rw [hspan]; exact hPG
    · exact Projection.pairStep_isPetrovGalerkin _ y

end ProjectionMethods

/-! ### §4.4.3 The Lanczos method for symmetric systems -/

section Lanczos

variable {A : Matrix (Fin n) (Fin n) ℝ} (v₁ : EuclideanSpace ℝ (Fin n))

/-- **Section 4.4.3** of [quarteroni2000numerical], the first paragraph. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and let $v_1$ be a unit vector. Then the Arnoldi
matrix $H_m$ is the symmetric tridiagonal matrix $T_m$ of the Lanczos method, with diagonal
entries $\alpha_i = h_{ii}$ and off-diagonal entries $\beta_i = h_{i+1,i}$. The Arnoldi
recurrence reduces to the three-term Lanczos recurrence that Program 24 computes:
$$A v_{j+1} = \beta_j v_j + \alpha_{j+1} v_{j+1} + \beta_{j+1} v_{j+2}.$$

All indices here are 0-based, as in `QuarteroniSaccoSaleri.Chapter04.arnoldi` and
`QuarteroniSaccoSaleri.Chapter04.arnoldiH`. The proof uses
`Lanczos.hessenbergSq_eq_map_tridiag`, `Lanczos.tridiag_isSymm`, `Lanczos.tridiag_isTridiagonal`
and `Lanczos.apply_vec`. The backbone's `Lanczos.tridiag`, `Lanczos.alpha` and `Lanczos.beta`
are $T_m$, $\alpha_i$ and $\beta_i$. -/
theorem lanczos_tridiagonal (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (m : ℕ) :
    H A v₁ m = Lanczos.tridiag (toEuclideanLin A) v₁ m ∧ (H A v₁ m).IsSymm ∧
      (H A v₁ m).IsTridiagonal ∧
      (∀ i, Lanczos.alpha (toEuclideanLin A) v₁ i = arnoldiH A v₁ i i) ∧
      (∀ i, Lanczos.beta (toEuclideanLin A) v₁ i = arnoldiH A v₁ (i + 1) i) ∧
      ∀ j, toEuclideanLin A (arnoldi A v₁ (j + 1)) =
        Lanczos.beta (toEuclideanLin A) v₁ j • arnoldi A v₁ j +
          Lanczos.alpha (toEuclideanLin A) v₁ (j + 1) • arnoldi A v₁ (j + 1) +
          Lanczos.beta (toEuclideanLin A) v₁ (j + 1) • arnoldi A v₁ (j + 2) := by
  have hA' := hA.isSymmetric_toEuclideanLin
  obtain ⟨hvec, hH, -⟩ := arnoldi_eq_vec A v₁ hv
  have hHm : H A v₁ m = Lanczos.tridiag (toEuclideanLin A) v₁ m := by
    have h := (equation_4_56 A v₁ hv m).2.2.2.2.1
    rw [h, Lanczos.hessenbergSq_eq_map_tridiag v₁ hA' m, Algebra.algebraMap_self, RingHom.coe_id]
    exact Matrix.map_id _
  refine ⟨hHm, hHm ▸ Lanczos.tridiag_isSymm _ _ _, hHm ▸ Lanczos.tridiag_isTridiagonal _ _ _,
    fun i => ?_, fun i => ?_, fun j => ?_⟩
  · rw [Lanczos.alpha, hH, RCLike.re_to_real]
  · rw [Lanczos.beta, hH, Arnoldi.coeff_succ_self, RCLike.ofReal_real_eq_id, id_eq]
  · simp only [hvec]
    exact Lanczos.apply_vec v₁ hA' j

variable {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **Section 4.4.3** of [quarteroni2000numerical], the Lanczos method for linear systems. Let
$A \in \mathbb{R}^{n \times n}$, let $r^{(0)} = b - Ax^{(0)} \neq 0$, and let the Arnoldi
(Lanczos) algorithm start from $v_1 = r^{(0)}/\|r^{(0)}\|_2$. If $x$ is the FOM (Lanczos)
iterate at step $k$, its residual is a multiple of the next Lanczos vector,
$b - Ax = \gamma_k v_{k+1}$ for some $\gamma_k \in \mathbb{R}$. Hence the residuals of FOM
iterates at different steps are mutually orthogonal.

**Generalization.** The source makes the statement for symmetric $A$. It holds for every $A$.

The scalar $\gamma_k$ is the one of `QuarteroniSaccoSaleri.Chapter04.equation_4_63`, and
$v_{k+1}$ is `arnoldi … k`. The proof uses the backbone's
`Krylov.IsGalerkinIterate.residual_mem_span` and
`Krylov.IsGalerkinIterate.inner_residual_eq_zero`. -/
theorem lanczos_residual_eq_smul (hr : b - toEuclideanLin A x₀ ≠ 0) {k : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : equation_4_57 A b x₀ k x) :
    (∃ γ : ℝ, b - toEuclideanLin A x =
        γ • arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k) ∧
      ∀ {k' : ℕ} {x' : EuclideanSpace ℝ (Fin n)}, equation_4_57 A b x₀ k' x' → k ≠ k' →
        inner ℝ (b - toEuclideanLin A x) (b - toEuclideanLin A x') = 0 := by
  obtain ⟨hvec, -, -⟩ := arnoldi_residual hr
  rw [equation_4_57_iff] at hx
  refine ⟨?_, fun hx' hkk' => ?_⟩
  · obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.1 hx.residual_mem_span
    exact ⟨γ, by rw [hvec, hγ]⟩
  · rw [equation_4_57_iff] at hx'
    exact hx.inner_residual_eq_zero hx' hkk'

/-- **Remark 4.5** of [quarteroni2000numerical] (the conjugate gradient method). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite and $r^{(0)} = b - Ax^{(0)}$.
Then the conjugate gradient iterate $x^{(k)}$ of §4.3.4 is the Lanczos (FOM) iterate at step
$k$. If $r^{(0)} \neq 0$ and $r^{(k)} \neq 0$, the Lanczos vector started from
$r^{(0)}/\|r^{(0)}\|_2$ is
$$v_{k+1} = (-1)^k \frac{r^{(k)}}{\|r^{(k)}\|_2}.$$
The descent directions are mutually $A$-conjugate, so that the matrix $P_k^T A P_k$ of the
source is diagonal.

The first clause is the backbone's `CG.isGalerkinIterate` through
`QuarteroniSaccoSaleri.Chapter04.cg_eq_CG`, the second is `CG.arnoldi_vec_eq`, and the third is
`QuarteroniSaccoSaleri.Chapter04.equation_4_42`. The route of the source through the LU
factorization $H_k = L_k U_k$ and $P_k = V_k U_k^{-1}$ is not restated: the content of the
remark is the identification of the two iterates. -/
theorem remark_4_5 (hA : A.PosDef) (k : ℕ) :
    equation_4_57 A b x₀ k (cgX A b x₀ k) ∧
      (b - toEuclideanLin A x₀ ≠ 0 → cgR A b x₀ k ≠ 0 →
        arnoldi A ((‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ • (b - toEuclideanLin A x₀)) k =
          ((-1) ^ k * ‖cgR A b x₀ k‖⁻¹) • cgR A b x₀ k) ∧
      ∀ i j, i ≠ j → inner ℝ (toEuclideanLin A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  refine ⟨?_, fun hr hk => ?_, (equation_4_42 hA).2⟩
  · rw [equation_4_57_iff, cgX_eq_CG hA]
    exact CG.isGalerkinIterate b x₀ hA' k
  · obtain ⟨hvec, -, -⟩ := arnoldi_residual hr
    rw [hvec, cgR_eq_CG hA] at *
    have h := CG.arnoldi_vec_eq b x₀ hA' k hk
    rwa [RCLike.ofReal_real_eq_id, id_eq] at h

/-- **Section 4.4.3** of [quarteroni2000numerical], the last paragraph: the conjugate residual
method. Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. For symmetric $A$
the GMRES method simplifies to the conjugate residual (CR) method: for every $k$ the CR iterate
is the GMRES iterate (4.58) at step $k$, and the CR residuals are mutually $A$-conjugate,
$r^{(i)T} A r^{(j)} = 0$ for $i \neq j$.

The CR recurrence is the backbone's `CR.iterate`. The proof uses `CR.isMinResidualIterate` and
`CR.inner_residual_apply_residual_eq_zero`. The source names the methods GCR and ORTHOMIN
without any result about them. -/
theorem cr_residual_conjugate (hA : A.PosDef) :
    (∀ k, equation_4_58 A b x₀ k (CR.iterate (toEuclideanLin A) b x₀ k).x) ∧
      ∀ i j, i ≠ j → inner ℝ (CR.iterate (toEuclideanLin A) b x₀ i).r
        (toEuclideanLin A (CR.iterate (toEuclideanLin A) b x₀ j).r) = 0 := by
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  refine ⟨fun k => ?_, fun i j hij => CR.inner_residual_apply_residual_eq_zero b x₀ hA' hij⟩
  rw [(equation_4_58_iff A b x₀ k).1]
  exact CR.isMinResidualIterate b x₀ hA' k

end Lanczos


end QuarteroniSaccoSaleri.Chapter04
