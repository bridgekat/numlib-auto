/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.Jacobi
import Numlib.Eigen.Sturm
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section09

/-!
# Quarteroni, Sacco and Saleri, Section 5.10: Methods for eigenvalues of symmetric matrices

This module formalizes Section 5.10 of [quarteroni2000numerical], two methods for the eigenvalues of
a real symmetric matrix. The Jacobi method (Section 5.10.1) applies plane rotations
$A^{(k)} = G_{pq}^T A^{(k-1)} G_{pq}$, each chosen to annihilate the entry $a_{pq}^{(k-1)}$; each
rotation lowers the square of the off-diagonal mass $\Psi(A) = (\sum_{i \neq j} a_{ij}^2)^{1/2}$ by
$2 a_{pq}^2$, and the classical method converges to a diagonal matrix of eigenvalues. Givens' method
(Section 5.10.2) computes the eigenvalues of a symmetric tridiagonal matrix by bisection: the number
of sign changes in the Sturm sequence $p_0(\mu), \dots, p_n(\mu)$ of the leading principal minors
counts the eigenvalues at most $\mu$. The proofs specialize `Numlib.Eigen.Jacobi`,
`Numlib.LinearAlgebra.Matrix.PlaneRotation` and `Numlib.Eigen.Sturm`.

## Main definitions

* Equation (5.61), `QuarteroniSaccoSaleri.Chapter05.jacobiTanBook`: the tangent $t$ of the rotation
  angle, the root of $t^2 + 2\eta t - 1 = 0$ of smaller modulus.
* Equations (5.61)–(5.62), `QuarteroniSaccoSaleri.Chapter05.equation_5_61`: the cosine and sine
  $c = 1/\sqrt{1 + t^2}$, $s = ct$.
* Section 5.10.1, `QuarteroniSaccoSaleri.Chapter05.jacobiRotate`: the Jacobi transformation
  $G_{pq}^T A G_{pq}$.
* Equation (5.63), `QuarteroniSaccoSaleri.Chapter05.equation_5_63`: the off-diagonal mass $\Psi(M)$.
* Section 5.10.1, `QuarteroniSaccoSaleri.Chapter05.cyclicPairs`,
  `QuarteroniSaccoSaleri.Chapter05.cyclicJacobiSweep` and
  `QuarteroniSaccoSaleri.Chapter05.cyclicJacobiIterate`: the row-cyclic Jacobi method.
* Equation (5.65), `QuarteroniSaccoSaleri.Chapter05.sturmSeq`: the Sturm sequence of a symmetric
  tridiagonal matrix.
* Section 5.10.2, `QuarteroniSaccoSaleri.Chapter05.givensBisection`: Givens' bisection from the
  Gershgorin interval.

## Main results

* Equation (5.60), `QuarteroniSaccoSaleri.Chapter05.equation_5_60`: the entries of
  $G_{pq}^T A G_{pq}$ that change, and the $2 \times 2$ block at $p, q$.
* Equation (5.61), `QuarteroniSaccoSaleri.Chapter05.jacobiTanBook_eq`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_61_eq` and
  `QuarteroniSaccoSaleri.Chapter05.equation_5_61_root`: $t$, $c$ and $s$ agree with the backbone,
  $t$ solves the quadratic equation, $|t| \le 1$ and $c^2 + s^2 = 1$.
* Section 5.10.1, `QuarteroniSaccoSaleri.Chapter05.jacobiRotate_eq_jacobiStep`: the Jacobi
  transformation is the backbone's `Matrix.jacobiStep`.
* Equation (5.59), `QuarteroniSaccoSaleri.Chapter05.equation_5_59`: the Jacobi transformation
  annihilates the entry $(p, q)$.
* Equation (5.63), `QuarteroniSaccoSaleri.Chapter05.equation_5_63_eq_sqrt` and
  `QuarteroniSaccoSaleri.Chapter05.equation_5_63_eq`: $\Psi(M)^2$ is the backbone's off-diagonal
  mass, and $\Psi(M)^2 = \|M\|_F^2 - \sum_i m_{ii}^2$.
* Equation (5.64), `QuarteroniSaccoSaleri.Chapter05.equation_5_64`: a rotation that annihilates
  $a_{pq}$ lowers $\Psi^2$ by exactly $2 a_{pq}^2$.
* Section 5.10.1, `QuarteroniSaccoSaleri.Chapter05.classicalJacobi`: the classical Jacobi method
  converges to a diagonal matrix with the eigenvalues of $A$.
* Section 5.10.1, `QuarteroniSaccoSaleri.Chapter05.foldl_jacobiRotate_spec` and
  `QuarteroniSaccoSaleri.Chapter05.cyclicJacobiSweep_spec`: the sweeps of the cyclic method keep
  symmetry and the characteristic polynomial, and do not increase $\Psi$.
* Equation (5.65), `QuarteroniSaccoSaleri.Chapter05.sturmSeq_eq` and
  `QuarteroniSaccoSaleri.Chapter05.equation_5_65`: the Sturm sequence agrees with the backbone, and
  $p_i(x) = \det(T_i - xI_i)$.
* Property 5.11, `QuarteroniSaccoSaleri.Chapter05.property_5_11_interlace`: the eigenvalues of
  $T_{i-1}$ strictly separate those of $T_i$.
* Property 5.11, `QuarteroniSaccoSaleri.Chapter05.property_5_11_count`: the number of sign changes
  $s(\mu)$ is the number of eigenvalues at most $\mu$.
* Section 5.10.2, `QuarteroniSaccoSaleri.Chapter05.givensBisection_spec`,
  `QuarteroniSaccoSaleri.Chapter05.eigenvalues_mem_Icc_givensBisection` and
  `QuarteroniSaccoSaleri.Chapter05.givensBisection_error`: the starting interval contains the
  spectrum, every bisection interval contains the eigenvalue, and the error bound.

## Conventions

* The Givens matrix $G(p, q, \theta)$ of (5.43) has $+\sin\theta$ in position $(p, q)$. The
  backbone's `Matrix.planeRotation p q c s` has $-s$ there, so the book's $G_{pq}$ with
  $c = \cos\theta$ and $s = \sin\theta$ is `planeRotation p q c (-s)`.
* The tridiagonal matrix $T = \operatorname{tridiag}(b, d, b)$ of Section 5.10.2 is
  `Matrix.symmTridiagonalOf d b n`, built from diagonals indexed by $\mathbb{N}$, so that its
  leading principal submatrix $T_i$ is the same construction at order $i$. The indices are 0-based:
  the book's $d_{i+1}$ and $b_{i+1}$ are `d i` and `b i`.
* The eigenvalues $\lambda_1(T_i) \ge \dots \ge \lambda_i(T_i)$ are
  `Sturm.eigenvalues d b i : Fin i → ℝ`, sorted decreasingly, and $s(\mu)$ with the sign convention
  of the book is `Sturm.signChanges d b n μ`.
* "Unreduced" means $b_i \neq 0$ for every $i$.

## Deviations from the source

* **Generalization.** The Jacobi two-coordinate block identity also holds before normalizing the
  rotation. See `QuarteroniSaccoSaleri.Chapter05.equation_5_60`.
* **Derivation.** The maximum-entry Jacobi result gives an explicit geometric off-diagonal rate and
  diagonal limit. See `QuarteroniSaccoSaleri.Chapter05.classicalJacobi`.
* **Scope.** The cyclic Jacobi sweep formalizes fixed-length iteration and its monotone off-diagonal
  norm. See `QuarteroniSaccoSaleri.Chapter05.cyclicPairs`,
  `QuarteroniSaccoSaleri.Chapter05.cyclicJacobiSweep`,
  `QuarteroniSaccoSaleri.Chapter05.cyclicJacobiIterate`,
  `QuarteroniSaccoSaleri.Chapter05.cyclicJacobiSweep_spec`.
* **Reading.** The Sturm determinant recurrence includes the sign needed for a monic characteristic
  polynomial. See `QuarteroniSaccoSaleri.Chapter05.sturmSeq`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_65`.
* **Scope.** Strict Sturm interlacing uses an all-index off-diagonal nonvanishing assumption. See
  `QuarteroniSaccoSaleri.Chapter05.property_5_11_interlace`.
* **Correction.** The Sturm sign count includes eigenvalues equal to the evaluation point. See
  `QuarteroniSaccoSaleri.Chapter05.property_5_11_count`.
* **Reading.** Sturm bisection returns closed enclosures with exact interval halving. See
  `QuarteroniSaccoSaleri.Chapter05.givensBisection`,
  `QuarteroniSaccoSaleri.Chapter05.givensBisection_spec`,
  `QuarteroniSaccoSaleri.Chapter05.eigenvalues_mem_Icc_givensBisection`,
  `QuarteroniSaccoSaleri.Chapter05.givensBisection_error`.
* **Property 5.11, the sign-change count** (reading). The source says that $s(\mu)$ counts the
  eigenvalues strictly less than $\mu$; under its own sign convention $s(\mu)$ counts the
  eigenvalues at most $\mu$. See `QuarteroniSaccoSaleri.Chapter05.property_5_11_count`.
* **Givens' method, the enclosure** (reading). As a consequence of the reading of Property 5.11, the
  eigenvalue is enclosed in the closed interval $[a^{(r)}, b^{(r)}]$ rather than in
  $(a^{(r)}, b^{(r)}]$; this matters when $\alpha$ is itself the smallest eigenvalue. See
  `QuarteroniSaccoSaleri.Chapter05.givensBisection_error`.

## Not formalized

* **Section 5.10.1, the quadratic convergence of the cyclic Jacobi method.** The source states
  without proof, citing Wilkinson, that if the eigenvalues of the symmetric matrix $A$ are
  separated, $|\lambda_i - \lambda_j| \ge \delta$ for $i \neq j$, then one sweep of $N = n(n-1)/2$
  row-cyclic rotations gives $\Psi(A^{(k+N)}) \le \Psi(A^{(k)})^2 / (\delta\sqrt 2)$. The inequality
  needs no smallness hypothesis, because $\Psi$ does not increase along Jacobi rotations
  (`QuarteroniSaccoSaleri.Chapter05.equation_5_64`): if $\Psi(A^{(k)}) \ge \delta\sqrt 2$, the
  right-hand side is at least $\Psi(A^{(k)})$ and the inequality holds trivially. So all the content
  is in the regime $\Psi < \delta\sqrt 2$. There the proof is an induction over the rotations of a
  sweep that carries a second-order bound on every off-diagonal entry: each rotation angle is
  $O(\Psi/\delta)$ by Gershgorin's theorem, a pair annihilated earlier in the sweep is refilled only
  to second order, and the constant $1/(\delta\sqrt 2)$ depends on the order of the sweep. The
  library has no such sweep-indexed bound.
* **Examples 5.15–5.17.** They are numerical.
-/

open Filter Finset Matrix Polynomial Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### Section 5.10.1: the Jacobi rotation -/

/-- **Equation (5.60)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, let $p \neq q$, let $c, s \in \mathbb{R}$, and let $G_{pq}$ be the Givens matrix of
(5.43) with $c$ and $s$ in place of $\cos\theta$ and $\sin\theta$. Then the entries of
$A' = G_{pq}^T A G_{pq}$ outside the rows and columns $p$ and $q$ are those of $A$, and the
entries of $A'$ at $(p, p)$, $(p, q)$ and $(q, q)$ are those of $$\begin{bmatrix} c & s \\ -s &
c \end{bmatrix}^T \begin{bmatrix} a_{pp} & a_{pq} \\ a_{pq} & a_{qq} \end{bmatrix}
\begin{bmatrix} c & s \\ -s & c \end{bmatrix}.$$

The statement holds for any $c$ and $s$, without $c^2 + s^2 = 1$. The matrix $G_{pq}$ is
`planeRotation p q c (-s)`. The proof specializes `Matrix.conj_planeRotation_apply_jj`,
`Matrix.conj_planeRotation_apply_jk`, `Matrix.conj_planeRotation_apply_kk` and
`Matrix.conj_planeRotation_apply_of_ne`.

**Generalization.** The local block calculation holds for any two scalars $c,s$, including without
the rotation normalization, and records entries away from both selected coordinates separately.
-/
theorem equation_5_60 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q)
    (c s : ℝ) :
    let G := planeRotation p q c (-s)
    let M := !![c, s; -s, c]ᵀ * !![A p p, A p q; A p q, A q q] * !![c, s; -s, c]
    (Gᵀ * A * G) p p = M 0 0 ∧ (Gᵀ * A * G) p q = M 0 1 ∧ (Gᵀ * A * G) q q = M 1 1 ∧
      ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → (Gᵀ * A * G) i j = A i j := by
  intro G M
  have hqp : A q p = A p q := hA.apply p q
  refine ⟨?_, ?_, ?_, fun i j hip hiq hjp hjq =>
    conj_planeRotation_apply_of_ne hpq A hip hiq hjp hjq⟩
  · rw [conj_planeRotation_apply_jj hpq A, hqp]
    simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [conj_planeRotation_apply_jk hpq A, hqp]
    simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [conj_planeRotation_apply_kk hpq A, hqp]
    simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- **Equation (5.61)** of [quarteroni2000numerical], the rotation angle. Let
$A \in \mathbb{R}^{n \times n}$ and $p, q$ be indices. If $a_{pq} \neq 0$, let
$\eta = (a_{qq} - a_{pp}) / (2 a_{pq})$; the tangent of the rotation angle is the root of
$t^2 + 2\eta t - 1 = 0$ that the source chooses: $$t = \begin{cases} 1 / (\eta + \sqrt{1 +
\eta^2}) & \text{if } \eta \ge 0, \\ -1 / (-\eta + \sqrt{1 + \eta^2}) & \text{if } \eta < 0.
\end{cases}$$ If $a_{pq} = 0$, the rotation is the identity and $t = 0$, as in Program 39.

This is the root of smaller modulus, the backbone's `Matrix.jacobiTanSmall`. -/
noncomputable def jacobiTanBook (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : ℝ :=
  if A p q = 0 then 0
  else
    let η := (A q q - A p p) / (2 * A p q)
    if 0 ≤ η then 1 / (η + Real.sqrt (1 + η ^ 2)) else -1 / (-η + Real.sqrt (1 + η ^ 2))

/-- **Equations (5.61)–(5.62)** of [quarteroni2000numerical], the cosine and the sine of the
rotation. Let $A \in \mathbb{R}^{n \times n}$, let $p, q$ be indices, and let $t$ be the tangent
of `QuarteroniSaccoSaleri.Chapter05.jacobiTanBook`. If $a_{pq} \neq 0$, then $$c =
\frac{1}{\sqrt{1 + t^2}}, \qquad s = ct.$$ If $a_{pq} = 0$, then $(c, s) = (1, 0)$, as in
Program 39. -/
noncomputable def equation_5_61 (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : ℝ × ℝ :=
  if A p q = 0 then (1, 0)
  else (1 / Real.sqrt (1 + jacobiTanBook A p q ^ 2),
    1 / Real.sqrt (1 + jacobiTanBook A p q ^ 2) * jacobiTanBook A p q)

/-- The tangent $t$ of (5.61) of [quarteroni2000numerical],
`QuarteroniSaccoSaleri.Chapter05.jacobiTanBook A p q`, equals the backbone's
`Matrix.jacobiTanSmall A p q`. -/
theorem jacobiTanBook_eq (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    jacobiTanBook A p q = jacobiTanSmall A p q := rfl

/-- The cosine and sine $(c, s)$ of (5.61)–(5.62) of [quarteroni2000numerical] are the backbone's
`Matrix.jacobiCosSmall A p q` and `Matrix.jacobiSinSmall A p q`. -/
theorem equation_5_61_eq (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    equation_5_61 A p q = (jacobiCosSmall A p q, jacobiSinSmall A p q) := by
  simp only [equation_5_61, jacobiSinSmall, jacobiCosSmall, jacobiTanBook_eq]
  split_ifs with h
  · simp [jacobiTanSmall, h]
  · rw [mul_comm]

/-- **Equations (5.61)–(5.62)** of [quarteroni2000numerical], the properties of the angle. Let
$A \in \mathbb{R}^{n \times n}$, let $p, q$ be indices, and let $t$, $c$, $s$ be as in
(5.61)–(5.62). If $a_{pq} \neq 0$, then $t$ solves $$t^2 + 2\eta t - 1 = 0, \qquad \eta =
\frac{a_{qq} - a_{pp}}{2 a_{pq}}.$$ In every case $|t| \le 1$, so the rotation angle is at most
$\pi/4$ in modulus, and $c^2 + s^2 = 1$.

The proof specializes `Matrix.jacobiTanSmall_sq`, `Matrix.abs_jacobiTanSmall_le_one` and
`Matrix.jacobiCosSmall_sq_add_jacobiSinSmall_sq`. -/
theorem equation_5_61_root (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (A p q ≠ 0 → jacobiTanBook A p q ^ 2 + 2 * ((A q q - A p p) / (2 * A p q)) * jacobiTanBook A p q
      - 1 = 0) ∧
      |jacobiTanBook A p q| ≤ 1 ∧
      (equation_5_61 A p q).1 ^ 2 + (equation_5_61 A p q).2 ^ 2 = 1 := by
  rw [jacobiTanBook_eq, equation_5_61_eq]
  exact ⟨jacobiTanSmall_sq A p q, abs_jacobiTanSmall_le_one A p q,
    jacobiCosSmall_sq_add_jacobiSinSmall_sq A p q⟩

/-- **Section 5.10.1** of [quarteroni2000numerical], the Jacobi transformation. For
$A \in \mathbb{R}^{n \times n}$ and indices $p, q$, it is $$A' = G_{pq}^T A G_{pq},$$ where
$G_{pq}$ is the Givens matrix built from the $(c, s)$ of (5.61)–(5.62).

The matrix $G_{pq}$ is `planeRotation p q c (-s)`. -/
noncomputable def jacobiRotate (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (planeRotation p q (equation_5_61 A p q).1 (-(equation_5_61 A p q).2))ᵀ * A *
    planeRotation p q (equation_5_61 A p q).1 (-(equation_5_61 A p q).2)

/-- The Jacobi transformation of Section 5.10.1 of [quarteroni2000numerical] is the backbone's:
`QuarteroniSaccoSaleri.Chapter05.jacobiRotate A p q` equals `Matrix.jacobiStep A p q`.

The rotation matrix built from the book's $(c, s)$ in the book's sign convention is
`Matrix.jacobiRotation`, by `Matrix.jacobiRotation_eq_planeRotation_small`. -/
theorem jacobiRotate_eq_jacobiStep (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    jacobiRotate A p q = jacobiStep A p q := by
  rw [jacobiRotate, jacobiStep, jacobiRotation_eq_planeRotation_small, equation_5_61_eq]

/-- **Equation (5.59)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric and $p \neq q$. The Jacobi transformation annihilates the chosen entry: $$a'_{pq} = 0,
\qquad A' = G_{pq}^T A G_{pq}.$$

By (5.60) the entry $a'_{pq}$ is $(c^2 - s^2) a_{pq} - cs (a_{qq} - a_{pp})$, which vanishes
exactly when $t = s/c$ solves (5.61). The proof specializes `Matrix.jacobiStep_apply_eq_zero`;
`Matrix.jacobiSmall_annihilate` is the same identity in the sign convention of the book. -/
theorem equation_5_59 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q) :
    jacobiRotate A p q p q = 0 := by
  rw [jacobiRotate_eq_jacobiStep]
  exact jacobiStep_apply_eq_zero A hA hpq

/-! ### The off-diagonal mass (5.63)–(5.64) -/

/-- **Equation (5.63)** of [quarteroni2000numerical]. For $M \in \mathbb{R}^{n \times n}$, the
**off-diagonal mass** is $$\Psi(M) = \Big(\sum_{i \neq j} m_{ij}^2\Big)^{1/2}.$$
-/
noncomputable def equation_5_63 (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j ∈ univ.erase i, M i j ^ 2)

/-- For $M \in \mathbb{R}^{n \times n}$, the off-diagonal mass $\Psi(M)$ of (5.63) of
[quarteroni2000numerical] is the square root of the backbone's `Matrix.offDiagNormSq M`. -/
theorem equation_5_63_eq_sqrt (M : Matrix (Fin n) (Fin n) ℝ) :
    equation_5_63 M = Real.sqrt (offDiagNormSq M) := by
  rw [equation_5_63, offDiagNormSq_real]

open scoped Matrix.Norms.Frobenius in
/-- **Equation (5.63)** of [quarteroni2000numerical], the two forms. For
$M \in \mathbb{R}^{n \times n}$, $\Psi(M)^2 = \sum_{i \neq j} m_{ij}^2$ is the backbone's
`Matrix.offDiagNormSq M`, $\Psi(M) \ge 0$, and $$\Psi(M) = \Big(\|M\|_F^2 - \sum_i
m_{ii}^2\Big)^{1/2}.$$

The norm $\|M\|_F$ is the Frobenius norm of `Matrix.Norms.Frobenius`. The proof uses
`Matrix.offDiagNormSq_add_sum_diag_sq_real`. -/
theorem equation_5_63_eq (M : Matrix (Fin n) (Fin n) ℝ) :
    equation_5_63 M ^ 2 = offDiagNormSq M ∧ 0 ≤ equation_5_63 M ∧
      equation_5_63 M = Real.sqrt (‖M‖ ^ 2 - ∑ i, M i i ^ 2) := by
  refine ⟨?_, Real.sqrt_nonneg _, ?_⟩
  · rw [equation_5_63_eq_sqrt, Real.sq_sqrt (offDiagNormSq_nonneg M)]
  · rw [equation_5_63_eq_sqrt, frobenius_norm_sq_eq_sum_sq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← offDiagNormSq_add_sum_diag_sq_real, add_sub_cancel_right]

/-- **Equation (5.64)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, let $p \neq q$, and let $G_{pq}$ be a Givens matrix with $c^2 + s^2 = 1$ such that
$(G_{pq}^T A G_{pq})_{pq} = 0$. Then the off-diagonal mass drops by exactly $2 a_{pq}^2$:
$$\Psi(G_{pq}^T A G_{pq})^2 = \Psi(A)^2 - 2 a_{pq}^2,$$ hence
$\Psi(G_{pq}^T A G_{pq}) \le \Psi(A)$. The same identity holds for the Jacobi transformation of
(5.59): $\Psi(A')^2 = \Psi(A)^2 - 2 a_{pq}^2$.

The matrix $G_{pq}$ is `planeRotation p q c (-s)`. The proof specializes
`Matrix.offDiagNormSq_conj_planeRotation_of_apply_eq_zero`. -/
theorem equation_5_64 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (h0 : ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q = 0) :
    equation_5_63 ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) ^ 2 =
        equation_5_63 A ^ 2 - 2 * A p q ^ 2 ∧
      equation_5_63 ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) ≤
        equation_5_63 A ∧
      equation_5_63 (jacobiRotate A p q) ^ 2 = equation_5_63 A ^ 2 - 2 * A p q ^ 2 := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by rwa [neg_sq]
  have key := offDiagNormSq_conj_planeRotation_of_apply_eq_zero A hA hpq hcs' h0
  refine ⟨?_, ?_, ?_⟩
  · rw [(equation_5_63_eq _).1, (equation_5_63_eq _).1, key]
  · rw [equation_5_63_eq_sqrt, equation_5_63_eq_sqrt, key]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (A p q)])
  · rw [(equation_5_63_eq _).1, (equation_5_63_eq _).1, jacobiRotate_eq_jacobiStep,
      offDiagNormSq_jacobiStep A hA hpq]

/-! ### The classical and the row-cyclic Jacobi method -/

/-- **Section 5.10.1** of [quarteroni2000numerical], the classical Jacobi method. In this method,
each step takes a pair $(p, q)$ with $|a_{pq}^{(k-1)}| = \max_{i \neq j} |a_{ij}^{(k-1)}|$ (the
"optimal choice" of the source). Let $A \in \mathbb{R}^{n \times n}$ be symmetric, with
$n \ge 2$. Then every iterate $A^{(\nu)}$ is symmetric and has the characteristic polynomial of
$A$, $$\Psi(A^{(\nu)})^2 \le \Big(1 - \frac{2}{n^2 - n}\Big)^\nu \Psi(A)^2,$$ and the iterates
converge to a diagonal matrix $\Lambda$ with the characteristic polynomial of $A$, so the
diagonal entries of $\Lambda$ are the eigenvalues of $A$.

The source states the convergence without a theorem. The iteration is
`Matrix.classicalJacobiIterate`, and the pair is `Matrix.maxOffDiagPair`. The proof specializes
`Matrix.isSymm_classicalJacobiIterate`, `Matrix.charpoly_classicalJacobiIterate`,
`Matrix.offDiagNormSq_classicalJacobiIterate_le` and `Matrix.tendsto_classicalJacobiIterate`.

**Reading.** Lean gives a geometric rate in squared off-diagonal norm and actual convergence to a
diagonal matrix for maximum-entry pivoting. The book introduces the pivot selector and discusses the
quadratic rate for a different cyclic variant.
-/
theorem classicalJacobi [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ n) :
    (∀ ν, (classicalJacobiIterate A ν).IsSymm) ∧
      (∀ ν, (classicalJacobiIterate A ν).charpoly = A.charpoly) ∧
      (∀ ν, equation_5_63 (classicalJacobiIterate A ν) ^ 2 ≤
        (1 - 2 / ((n : ℝ) ^ 2 - n)) ^ ν * equation_5_63 A ^ 2) ∧
      ∃ Λ : Matrix (Fin n) (Fin n) ℝ, Λ.IsDiag ∧ Λ.charpoly = A.charpoly ∧
        Tendsto (classicalJacobiIterate A) atTop (𝓝 Λ) := by
  have hn' : 2 ≤ Fintype.card (Fin n) := by rwa [Fintype.card_fin]
  refine ⟨isSymm_classicalJacobiIterate hA, charpoly_classicalJacobiIterate hn', fun ν => ?_,
    tendsto_classicalJacobiIterate hA hn'⟩
  rw [(equation_5_63_eq _).1, (equation_5_63_eq _).1]
  simpa using offDiagNormSq_classicalJacobiIterate_le hA ν

/-- **Section 5.10.1** of [quarteroni2000numerical], the row order of the cyclic Jacobi method. It
is the list of the pairs $(p, q)$ with $1 \le p < q \le n$: for each row $p = 1, \dots, n - 1$,
the columns $q = p + 1, \dots, n$.

Indices are 0-based in the Lean list.

**Reading.** The row-cyclic definitions execute a fixed number of sweeps. Their theorem states
symmetry, spectrum preservation and monotonicity, without the source's cyclic quadratic estimate or
tolerance test.
-/
def cyclicPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun p => ((List.finRange n).filter fun q => p < q).map fun q => (p, q)

/-- Every pair $(p, q)$ in the row order `QuarteroniSaccoSaleri.Chapter05.cyclicPairs n` has
$p \neq q$. -/
theorem cyclicPairs_ne {pq : Fin n × Fin n} (h : pq ∈ cyclicPairs n) : pq.1 ≠ pq.2 := by
  simp only [cyclicPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq] at h
  obtain ⟨p, q, hpq, rfl⟩ := h
  exact hpq.ne

/-- **Section 5.10.1** of [quarteroni2000numerical], one sweep of the row-cyclic Jacobi method
(Program 40). A sweep applies the Jacobi transformations (5.59)–(5.62) at the pairs $(p, q)$ of
`QuarteroniSaccoSaleri.Chapter05.cyclicPairs` in row order, $p = 1, \dots, n - 1$ and
$q = p + 1, \dots, n$. So one sweep is $N = n(n - 1)/2$ transformations.

**Reading.** The row-cyclic definitions execute a fixed number of sweeps. Their theorem states
symmetry, spectrum preservation and monotonicity, without the source's cyclic quadratic estimate or
tolerance test.
-/
noncomputable def cyclicJacobiSweep (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (cyclicPairs n).foldl (fun M pq => jacobiRotate M pq.1 pq.2) A

/-- **Section 5.10.1** of [quarteroni2000numerical], the row-cyclic Jacobi method. For
$A \in \mathbb{R}^{n \times n}$ and $k \in \mathbb{N}$, it is the result of $k$ sweeps applied
to $A$, which is the iterate $A^{(kN)}$ of the source.

**Reading.** The row-cyclic definitions execute a fixed number of sweeps. Their theorem states
symmetry, spectrum preservation and monotonicity, without the source's cyclic quadratic estimate or
tolerance test.
-/
noncomputable def cyclicJacobiIterate (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  cyclicJacobiSweep^[k] A

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, and apply Jacobi transformations to $A$ at the
pairs $(p, q)$ of a list, each with $p \neq q$. The result is symmetric, has the characteristic
polynomial of $A$, and its off-diagonal mass is at most that of $A$. -/
theorem foldl_jacobiRotate_spec (l : List (Fin n × Fin n)) (hl : ∀ pq ∈ l, pq.1 ≠ pq.2)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (l.foldl (fun M pq => jacobiRotate M pq.1 pq.2) A).IsSymm ∧
      (l.foldl (fun M pq => jacobiRotate M pq.1 pq.2) A).charpoly = A.charpoly ∧
      offDiagNormSq (l.foldl (fun M pq => jacobiRotate M pq.1 pq.2) A) ≤ offDiagNormSq A := by
  induction l generalizing A with
  | nil => exact ⟨hA, rfl, le_rfl⟩
  | cons pq l ih =>
    have hpq : pq.1 ≠ pq.2 := hl pq (List.mem_cons_self ..)
    have hl' : ∀ pq ∈ l, pq.1 ≠ pq.2 := fun pq h => hl pq (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih hl' (A := jacobiRotate A pq.1 pq.2)
      (by rw [jacobiRotate_eq_jacobiStep]; exact isSymm_jacobiStep hA _ _)
    refine ⟨h1, ?_, h3.trans ?_⟩
    · rw [h2, jacobiRotate_eq_jacobiStep, charpoly_jacobiStep A hpq]
    · rw [jacobiRotate_eq_jacobiStep, offDiagNormSq_jacobiStep A hA hpq]
      nlinarith [sq_nonneg (A pq.1 pq.2)]

/-- **Section 5.10.1** of [quarteroni2000numerical], the sweeps of the cyclic Jacobi method. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. For every $k$, the result of $k$ sweeps is
symmetric and has the characteristic polynomial of $A$, and the next sweep does not increase
$\Psi$: $$\Psi(A^{((k+1)N)}) \le \Psi(A^{(kN)}).$$

The decrease is (5.64) at every transformation of the sweep.

**Reading.** The row-cyclic definitions execute a fixed number of sweeps. Their theorem states
symmetry, spectrum preservation and monotonicity, without the source's cyclic quadratic estimate or
tolerance test.
-/
theorem cyclicJacobiSweep_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : ℕ) :
    (cyclicJacobiIterate A k).IsSymm ∧ (cyclicJacobiIterate A k).charpoly = A.charpoly ∧
      equation_5_63 (cyclicJacobiIterate A (k + 1)) ≤ equation_5_63 (cyclicJacobiIterate A k) := by
  have hstep : ∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsSymm →
      (cyclicJacobiSweep B).IsSymm ∧ (cyclicJacobiSweep B).charpoly = B.charpoly ∧
        offDiagNormSq (cyclicJacobiSweep B) ≤ offDiagNormSq B :=
    fun hB => foldl_jacobiRotate_spec (cyclicPairs n) (fun _ h => cyclicPairs_ne h) hB
  have hiter : ∀ k, (cyclicJacobiIterate A k).IsSymm ∧
      (cyclicJacobiIterate A k).charpoly = A.charpoly := by
    intro k
    induction k with
    | zero => exact ⟨hA, rfl⟩
    | succ k ih =>
      rw [cyclicJacobiIterate, Function.iterate_succ_apply']
      exact ⟨(hstep ih.1).1, (hstep ih.1).2.1.trans ih.2⟩
  refine ⟨(hiter k).1, (hiter k).2, ?_⟩
  rw [cyclicJacobiIterate, Function.iterate_succ_apply', equation_5_63_eq_sqrt,
    equation_5_63_eq_sqrt]
  exact Real.sqrt_le_sqrt (hstep (hiter k).1).2.2

/-! ### Section 5.10.2: Sturm sequences -/

/-- **Equation (5.65)** of [quarteroni2000numerical], the Sturm sequence. Let
$T = \operatorname{tridiag}(b, d, b)$ have the diagonal $d_1, \dots, d_n$ and the off-diagonal
$b_1, \dots, b_{n-1}$. The **Sturm sequence** of $T$ is the sequence of polynomials $$p_0(x) =
1, \qquad p_1(x) = d_1 - x, \qquad p_i(x) = (d_i - x)\, p_{i-1}(x) - b_{i-1}^2\, p_{i-2}(x)
\quad (i \ge 2).$$

Indices are 0-based: $d_{i+1}$ and $b_{i+1}$ are `d i` and `b i`. The sequence is defined for
every $i \in \mathbb{N}$.

**Reading.** The recurrence is defined for arbitrary infinite diagonal and off-diagonal sequences
and every prefix. The polynomial is $\det(T_i-xI)$, so in Lean's monic characteristic-polynomial
convention it equals $(-1)^i\chi_{T_i}$.
-/
noncomputable def sturmSeq (d b : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (d 0) - X
  | i + 2 => (C (d (i + 1)) - X) * sturmSeq d b (i + 1) - C (b i) ^ 2 * sturmSeq d b i

/-- The Sturm sequence (5.65) of [quarteroni2000numerical] is the backbone's:
`QuarteroniSaccoSaleri.Chapter05.sturmSeq d b i` equals `Sturm.seq d b i` for every $i$. -/
theorem sturmSeq_eq (d b : ℕ → ℝ) : ∀ i, sturmSeq d b i = Sturm.seq d b i
  | 0 => rfl
  | 1 => rfl
  | i + 2 => by
    rw [sturmSeq, Sturm.seq_add_two, sturmSeq_eq d b (i + 1), sturmSeq_eq d b i]

/-- **Equation (5.65)** of [quarteroni2000numerical], the determinant form. For every $i$,
$$p_i(x) = \det(T_i - x I_i)$$ for the leading principal submatrix $T_i$ of order $i$ of $T$,
and $p_i = (-1)^i \chi_{T_i}$, where $\chi_{T_i}(x) = \det(x I_i - T_i)$ is the characteristic
polynomial. In particular $p_n$ is the characteristic polynomial of $T$ in the convention
$\det(T - xI)$ of the book.

The matrix $T_i$ is `Matrix.symmTridiagonalOf d b i`, and $\chi_{T_i}$ is Mathlib's
`Matrix.charpoly`. The proof specializes `Sturm.seq_eq_det` and `Sturm.seq_eq_charpoly`.

**Reading.** The recurrence is defined for arbitrary infinite diagonal and off-diagonal sequences
and every prefix. The polynomial is $\det(T_i-xI)$, so in Lean's monic characteristic-polynomial
convention it equals $(-1)^i\chi_{T_i}$.
-/
theorem equation_5_65 (d b : ℕ → ℝ) (i : ℕ) :
    sturmSeq d b i = ((symmTridiagonalOf d b i).map (C : ℝ → ℝ[X]) -
        (X : ℝ[X]) • (1 : Matrix (Fin i) (Fin i) ℝ[X])).det ∧
      sturmSeq d b i = (-1) ^ i * (symmTridiagonalOf d b i).charpoly := by
  rw [sturmSeq_eq]
  exact ⟨Sturm.seq_eq_det d b i, Sturm.seq_eq_charpoly d b i⟩

/-- **Property 5.11** of [quarteroni2000numerical], strict interlacing. Let $T$ be unreduced,
$b_i \neq 0$ for all $i$. For $i \ge 2$, the eigenvalues of $T_{i-1}$ strictly separate those of
$T_i$: with the eigenvalues sorted as $\lambda_1(T_i) > \dots > \lambda_i(T_i)$,
$$\lambda_{k+1}(T_i) < \lambda_k(T_{i-1}) < \lambda_k(T_i) \quad \text{for } k = 1, \dots, i -
1.$$

Indices are 0-based: the Lean statement is for $T_i$ and $T_{i+1}$ with `k : Fin i`. The proof
specializes `Sturm.eigenvalues_succ_lt` and `Sturm.eigenvalues_lt_castSucc`, which are Cauchy
interlacing for the leading principal submatrix, made strict because consecutive $p_i$ have no
common root. Hence the eigenvalues of an unreduced $T$ are simple (`Sturm.eigenvalues_simple`).

**Reading.** Strict interlacing is stated for every consecutive prefix under nonvanishing of the
entire off-diagonal sequence. The printed application needs only the finite prefix in the matrix.
-/
theorem property_5_11_interlace (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) (i : ℕ) (k : Fin i) :
    Sturm.eigenvalues d b (i + 1) k.succ < Sturm.eigenvalues d b i k ∧
      Sturm.eigenvalues d b i k < Sturm.eigenvalues d b (i + 1) k.castSucc :=
  ⟨Sturm.eigenvalues_succ_lt d b i (fun j _ => hb j) k,
    Sturm.eigenvalues_lt_castSucc d b i (fun j _ => hb j) k⟩

/-- **Property 5.11** of [quarteroni2000numerical], the sign-change count. Let $T$ be unreduced,
$b_i \neq 0$ for all $i$, and let $\mu \in \mathbb{R}$. Then two consecutive elements of the
sequence $p_0(\mu), p_1(\mu), \dots$ do not both vanish. Let $s(\mu)$ be the number of sign
changes in $\{p_0(\mu), \dots, p_n(\mu)\}$, where a vanishing $p_i(\mu)$ takes the sign opposite
to that of $p_{i-1}(\mu)$. Then $s(\mu)$ is the number of eigenvalues of $T$ that are at most
$\mu$, counted with multiplicity.

**Reading.** The source says that $s(\mu)$ is the number of eigenvalues strictly less than
$\mu$. Under its own sign convention the count includes an eigenvalue equal to $\mu$: for
$n = 1$ and $\mu = d_1$, the sequence $1, 0$ has one sign change and no eigenvalue is less than
$\mu$. The two counts agree when $\mu$ is not an eigenvalue.

The sign and the count are `Sturm.sign` and `Sturm.signChanges`, and the number of eigenvalues
at most $\mu$ is `Polynomial.countRootsIn (Set.Iic μ)` of the characteristic polynomial. The
proof specializes `Sturm.eval_ne_zero_or_eval_ne_zero` and `Sturm.signChanges_eq_countRootsIn`.

**Correction.** The printed convention assigns a zero term the sign opposite to its predecessor.
With that convention the count includes eigenvalues equal to the evaluation point, so Lean uses the
closed half-line.
-/
theorem property_5_11_count (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) (n : ℕ) (μ : ℝ) :
    (∀ i, (sturmSeq d b i).eval μ ≠ 0 ∨ (sturmSeq d b (i + 1)).eval μ ≠ 0) ∧
      Sturm.signChanges d b n μ =
        (symmTridiagonalOf d b n).charpoly.countRootsIn (Set.Iic μ) := by
  simp only [sturmSeq_eq]
  exact ⟨fun i => Sturm.eval_ne_zero_or_eval_ne_zero d b i (fun j _ => hb j) μ,
    Sturm.signChanges_eq_countRootsIn d b n (fun j _ => hb j) μ⟩

/-! ### Givens' method -/

/-- **Section 5.10.2** of [quarteroni2000numerical], Givens' method (Programs 42–44). Let
$b_0 = b_n = 0$. By Theorem 5.2 the spectrum of $T$ lies in $J = [\alpha, \beta]$ with
$$\alpha = \min_i \big(d_i - (|b_{i-1}| + |b_i|)\big), \qquad \beta = \max_i \big(d_i +
(|b_{i-1}| + |b_i|)\big).$$ For the $i$-th eigenvalue, counted from the largest, the bisection
starts from $a^{(0)} = \alpha$ and $b^{(0)} = \beta$. At each step it sets $c = (a + b)/2$, then
$b := c$ if $s(c) > n - i$ and $a := c$ otherwise. The value at $r$ is the pair
$(a^{(r)}, b^{(r)})$.

The radii $|b_{i-1}| + |b_i|$ are `Sturm.gershgorinRadius`, and the step is
`Sturm.bisectionStep`.

**Reading.** The recurrence returns closed intervals and uses the count including equality. The
enclosure and error theorem require a valid label and nonzero off-diagonal sequence. The fixed-step
rule includes exact halving and a bound in terms of the initial width.
-/
noncomputable def givensBisection (d b : ℕ → ℝ) (n i : ℕ) (r : ℕ) : ℝ × ℝ :=
  Sturm.bisectionIterate d b n i
    (⨅ j : Fin n, (d j - Sturm.gershgorinRadius b n j),
      ⨆ j : Fin n, (d j + Sturm.gershgorinRadius b n j)) r

/-- **Section 5.10.2** of [quarteroni2000numerical], Givens' method, the enclosure and the step. The
starting interval $[\alpha, \beta]$ contains the spectrum of $T$ (Theorem 5.2), and one step is
the bisection $c = (a^{(r)} + b^{(r)})/2$, $$(a^{(r+1)}, b^{(r+1)}) = \begin{cases} (a^{(r)}, c)
& \text{if } s(c) > n - i, \\ (c, b^{(r)}) & \text{otherwise.} \end{cases}$$

The enclosure is `Sturm.spectrum_subset_Icc`.

**Reading.** The recurrence returns closed intervals and uses the count including equality. The
enclosure and error theorem require a valid label and nonzero off-diagonal sequence. The fixed-step
rule includes exact halving and a bound in terms of the initial width.
-/
theorem givensBisection_spec (d b : ℕ → ℝ) (n i : ℕ) :
    spectrum ℝ (symmTridiagonalOf d b n) ⊆
        Set.Icc (givensBisection d b n i 0).1 (givensBisection d b n i 0).2 ∧
      ∀ r, givensBisection d b n i (r + 1) =
        if n - i < Sturm.signChanges d b n
            (((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2) then
          ((givensBisection d b n i r).1,
            ((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2)
        else (((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2,
          (givensBisection d b n i r).2) :=
  ⟨Sturm.spectrum_subset_Icc d b n, fun _ => rfl⟩

/-- **Section 5.10.2** of [quarteroni2000numerical], Givens' method encloses the eigenvalue. Let $T$
be unreduced, $b_i \neq 0$ for all $i$, and let $1 \le i \le n$. Then for every $r$, the $i$-th
largest eigenvalue $\lambda_i$ of $T$ lies in the closed interval $[a^{(r)}, b^{(r)}]$.

The eigenvalue $\lambda_i$ is `Sturm.eigenvalues d b n ⟨i - 1, _⟩`. The proof specializes
`Sturm.eigenvalues_mem_Icc_bisectionIterate`: the left end $\alpha$ of the Gershgorin interval
is at most every eigenvalue (`Sturm.eigenvalues_mem_Icc`), and $s(\beta) = n$
(`Sturm.count_eq_of_le`).

**Reading.** The recurrence returns closed intervals and uses the count including equality. The
enclosure and error theorem require a valid label and nonzero off-diagonal sequence. The fixed-step
rule includes exact halving and a bound in terms of the initial width.
-/
theorem eigenvalues_mem_Icc_givensBisection (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i ≤ n) (r : ℕ) :
    Sturm.eigenvalues d b n ⟨i - 1, by omega⟩ ∈
      Set.Icc (givensBisection d b n i r).1 (givensBisection d b n i r).2 := by
  have hβ : n - i <
      Sturm.signChanges d b n (⨆ j : Fin n, (d j + Sturm.gershgorinRadius b n j)) := by
    rw [Sturm.signChanges_eq_count d b n (fun j _ => hb j), Sturm.count_eq_of_le d b le_rfl]
    omega
  exact Sturm.eigenvalues_mem_Icc_bisectionIterate d b (fun j _ => hb j) hi hin
    (ab := (⨅ j : Fin n, (d j - Sturm.gershgorinRadius b n j),
      ⨆ j : Fin n, (d j + Sturm.gershgorinRadius b n j)))
    (fun k => (Sturm.eigenvalues_mem_Icc d b n k).1) hβ r

/-- **Section 5.10.2** of [quarteroni2000numerical], Givens' method, the error bound. Let $T$ be
unreduced, $b_i \neq 0$ for all $i$, and let $1 \le i \le n$. After $r$ bisection steps from
$[\alpha, \beta]$, the interval $[a^{(r)}, b^{(r)}]$ contains $\lambda_i$ and has length
$(\beta - \alpha)/2^r$, and its midpoint $c^{(r)} = (a^{(r)} + b^{(r)})/2$ satisfies
$$|c^{(r)} - \lambda_i| \le (\beta - \alpha)\, 2^{-(r+1)} \le (|\alpha| + |\beta|)\,
2^{-(r+1)},$$ which is the bound that the source quotes from (6.9).

**Reading.** With the count of Property 5.11 as the source states it ("strictly less than
$\mu$"), the bisection would enclose $\lambda_i$ in the half-open interval $(a^{(r)}, b^{(r)}]$.
When $\alpha$ is itself the smallest eigenvalue, the bisection keeps $a^{(r)} = \alpha$ for
every $r$, so the eigenvalue lies in the closed interval $[a^{(r)}, b^{(r)}]$, which is what the
error bound needs.

The proof specializes `Sturm.bisectionIterate_length`, with
`QuarteroniSaccoSaleri.Chapter05.eigenvalues_mem_Icc_givensBisection`.

**Reading.** The recurrence returns closed intervals and uses the count including equality. The
enclosure and error theorem require a valid label and nonzero off-diagonal sequence. The fixed-step
rule includes exact halving and a bound in terms of the initial width.
-/
theorem givensBisection_error (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) {n i : ℕ} (hi : 1 ≤ i)
    (hin : i ≤ n) (r : ℕ) :
    Sturm.eigenvalues d b n ⟨i - 1, by omega⟩ ∈
        Set.Icc (givensBisection d b n i r).1 (givensBisection d b n i r).2 ∧
      (givensBisection d b n i r).2 - (givensBisection d b n i r).1 =
        ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ r ∧
      |((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2 -
          Sturm.eigenvalues d b n ⟨i - 1, by omega⟩| ≤
        ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ (r + 1) ∧
      ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ (r + 1) ≤
        (|(givensBisection d b n i 0).1| + |(givensBisection d b n i 0).2|) / 2 ^ (r + 1) := by
  have hmem := eigenvalues_mem_Icc_givensBisection d b hb hi hin r
  have hlen : (givensBisection d b n i r).2 - (givensBisection d b n i r).1 =
      ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ r :=
    Sturm.bisectionIterate_length d b n i _ r
  refine ⟨hmem, hlen, ?_, ?_⟩
  · rw [abs_le, pow_succ, ← div_div, ← hlen]
    constructor <;> linarith [hmem.1, hmem.2]
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    linarith [le_abs_self (givensBisection d b n i 0).2, neg_le_abs (givensBisection d b n i 0).1]

end QuarteroniSaccoSaleri.Chapter05
