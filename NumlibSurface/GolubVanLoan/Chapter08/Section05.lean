/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Eigen.Jacobi
import NumlibSurface.GolubVanLoan.Chapter05.Section01

/-!
# Golub and Van Loan, Section 8.5: Jacobi methods

This module formalizes §8.5 of [golub2013matrix]. For $A \in \mathbb{R}^{n \times n}$, let
$\operatorname{off}(A) = \bigl(\sum_{i \ne j} a_{ij}^2\bigr)^{1/2}$ be the Frobenius norm of the
off-diagonal part. A Jacobi rotation $J(p, q, \theta)$ is the identity matrix except for the entries
$c$ at $(p, p)$ and $(q, q)$, $s$ at $(p, q)$ and $-s$ at $(q, p)$, with $c = \cos\theta$ and
$s = \sin\theta$. If $A$ is symmetric and $B = J^T A J$ has $b_{pq} = 0$, then
$\operatorname{off}(B)^2 = \operatorname{off}(A)^2 - 2a_{pq}^2$ (8.5.2). The module states the
update formulas (8.5.1)–(8.5.3), the symmetric $2 \times 2$ Schur decomposition (Algorithm 8.5.1),
the classical and the cyclic-by-row Jacobi algorithms (Algorithms 8.5.2 and 8.5.3) with their exact
semantics, the linear convergence of the classical algorithm, the decrease of $\operatorname{off}$
in block Jacobi (§8.5.6), and the parallel ordering of §8.5.7.

The proofs specialize the backbone modules `Numlib.Eigen.Jacobi` and
`Numlib.LinearAlgebra.Matrix.PlaneRotation`.

## Main definitions

* §8.5.1, `GolubVanLoan.Chapter08.off`: $\operatorname{off}(A) = \bigl(\sum_{i \ne j}
  a_{ij}^2\bigr)^{1/2}$.
* Algorithm 8.5.1, `GolubVanLoan.Chapter08.algorithm_8_5_1`: the cosine-sine pair $(c, s)$ of the
  symmetric $2 \times 2$ Schur decomposition.
* Algorithm 8.5.2, `GolubVanLoan.Chapter08.algorithm_8_5_2`: the classical Jacobi algorithm.
* §8.5.4, `GolubVanLoan.Chapter08.cyclicPairs`: the cyclic-by-row ordering of the pairs $(p, q)$,
  $p < q$.
* Algorithm 8.5.3, `GolubVanLoan.Chapter08.algorithm_8_5_3`: the cyclic Jacobi algorithm.
* §8.5.7, `GolubVanLoan.Chapter08.parallelOrdering`: the rotation sets of the parallel ordering.

## Main results

* (8.5.1), `GolubVanLoan.Chapter08.equation_8_5_1`: $J^T A J$ changes only rows and columns $p$ and
  $q$, and its $2 \times 2$ block at $(p, q)$ is the rotated $2 \times 2$ block of $A$.
* (8.5.2), `GolubVanLoan.Chapter08.equation_8_5_2`: if $b_{pq} = 0$, then $\operatorname{off}(B)^2 =
  \operatorname{off}(A)^2 - 2a_{pq}^2$.
* (8.5.3), `GolubVanLoan.Chapter08.equation_8_5_3`: $b_{pq} = 0$ if and only if $t = s/c$ solves
  $t^2 + 2\tau t - 1 = 0$, and the smaller root has $|t| \le 1$.
* Algorithm 8.5.1, `GolubVanLoan.Chapter08.algorithm_8_5_1_spec`: in exact arithmetic, the rotation
  of Algorithm 8.5.1 makes $b_{pq} = b_{qp} = 0$.
* §8.5.2, `GolubVanLoan.Chapter08.jacobi_frobenius_dist`: the formula for $\|B - A\|_F^2$ after one
  Jacobi update.
* §8.5.3, `GolubVanLoan.Chapter08.jacobi_diag_update`: $b_{pp} = a_{pp} - t a_{pq}$ and
  $b_{qq} = a_{qq} + t a_{pq}$.
* §8.5.3, `GolubVanLoan.Chapter08.classicalJacobi_linear`: each step of the classical method
  multiplies $\operatorname{off}^2$ by at most $1 - 1/N$, $N = n(n-1)/2$.
* Algorithm 8.5.2, `GolubVanLoan.Chapter08.algorithm_8_5_2_spec`: in exact arithmetic, the output is
  an orthogonal similarity of $A$, and $\operatorname{off}$ is below the threshold or has decreased
  at the linear rate.
* §8.5.3, `GolubVanLoan.Chapter08.algorithm_8_5_2_terminates`: in exact arithmetic, enough passes
  give $\operatorname{off}(V^T A V) \le \mathrm{tol} \cdot \|A\|_F$.
* Algorithm 8.5.3, `GolubVanLoan.Chapter08.algorithm_8_5_3_spec`: in exact arithmetic, the output is
  an orthogonal similarity of $A$ with $\operatorname{off}$ not increased.
* §8.5.6, `GolubVanLoan.Chapter08.blockJacobi_off`: one block Jacobi update removes
  $2\|A_{pq}\|_F^2 + \operatorname{off}(A_{pp})^2 + \operatorname{off}(A_{qq})^2$ from
  $\operatorname{off}^2$.
* §8.5.7, `GolubVanLoan.Chapter08.parallelOrdering_spec`: the $2m - 1$ rotation sets partition the
  pairs $i < j$ of $2m$ indices into sets of $m$ disjoint pairs.

## Conventions

* The rotation $J(p, q, \theta)$ is `Matrix.planeRotation p q c (-s)`. This is the matrix
  `GolubVanLoan.Chapter05.givensRotation p q c s` of Chapter 5, since "Jacobi rotations are no
  different from Givens rotations" (§8.5.1).
* $\operatorname{off}(A)$ is `GolubVanLoan.Chapter08.off A`, the square root of
  `Matrix.offDiagNormSq A`.
* The rotation of Algorithm 8.5.1 is `(Matrix.jacobiCosSmall A p q, Matrix.jacobiSinSmall A p q)`,
  the similarity by it is `Matrix.jacobiStep A p q`, and the classical iteration is
  `Matrix.classicalJacobiIterate`.
* The Frobenius norm $\|A\|_F$ is the norm of the scoped instance `Matrix.Norms.Frobenius`.

## Implementation notes

* The algorithms are programs in a monad `M` with a rounding hook `rnd : ℝ → M ℝ`, as in the
  conventions of the library index; their exact semantics are the instances `M := Id` and
  `rnd := pure`. The tests of the algorithms are exact comparisons.
* The `while` loop of Algorithms 8.5.2 and 8.5.3 runs at most `fuel` passes and carries a flag
  `done`. The output is the triple of the final $A$, the final $V$ and the flag, which records that
  the loop exited on its test.
* The players of §8.5.7 are numbered from $0$: the book's player $i + 1$ is `i`.

## Not formalized

* **Quadratic convergence of the classical and cyclic methods** (Henrici, Schönhage, van Kempen,
  Wilkinson). The source quotes it without proof.
* **The sweep count of Brent and Luk**, $\log n$ sweeps for the parallel ordering.
* **§8.5.5**, the error analysis, including (8.5.4).
* **Operation counts.**
-/

open Matrix FloatingPoint

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.5.1 The Jacobi idea -/

/-- **Section 8.5.1** of [golub2013matrix], the off-diagonal norm. For
$A \in \mathbb{R}^{n \times n}$,
$$\operatorname{off}(A) = \Bigl(\sum_{i=1}^n \sum_{j \ne i} a_{ij}^2\Bigr)^{1/2},$$
the Frobenius norm of the off-diagonal part of $A$.

The definition is the square root of `Matrix.offDiagNormSq A`. -/
noncomputable def off (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (offDiagNormSq A)

/-- For every $A$, $\operatorname{off}(A)^2 = \sum_{i \ne j} a_{ij}^2$. -/
theorem off_sq (A : Matrix (Fin n) (Fin n) ℝ) : off A ^ 2 = offDiagNormSq A :=
  Real.sq_sqrt (offDiagNormSq_nonneg A)

/-- For every $A$, $\operatorname{off}(A) \ge 0$. -/
theorem off_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ off A :=
  Real.sqrt_nonneg _

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- For every $A$, $\operatorname{off}(A)^2 = \|A\|_F^2 - \sum_i a_{ii}^2$. -/
theorem off_sq_eq (A : Matrix (Fin n) (Fin n) ℝ) : off A ^ 2 = ‖A‖ ^ 2 - ∑ i, A i i ^ 2 := by
  rw [off_sq, frobenius_norm_sq_eq_sum_sq]
  simp only [Real.norm_eq_abs, sq_abs]
  linarith [offDiagNormSq_add_sum_diag_sq_real A]

end Frobenius

/-- For a plane rotation $J$ in the $(p, q)$-plane, $p \ne q$, the entry $(J^T M J)_{qp}$ is $c(-s
m_{pp} + c m_{qp}) + s(-s m_{pq} + c m_{qq})$. -/
private theorem conj_planeRotation_apply_kj {p q : Fin n} (hpq : p ≠ q)
    (M : Matrix (Fin n) (Fin n) ℝ) (c s : ℝ) :
    ((planeRotation p q c s)ᵀ * M * planeRotation p q c s) q p =
      c * (-s * M p p + c * M q p) + s * (-s * M p q + c * M q q) := by
  have h := conj_planeRotation_apply_jk (c := c) (s := s) hpq Mᵀ
  rw [← transpose_apply ((planeRotation p q c s)ᵀ * M * planeRotation p q c s),
    transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
  simpa using h

/-- **Equation (8.5.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, let $p \ne q$,
let $c, s \in \mathbb{R}$, and let $B = J(p, q, \theta)^T A J(p, q, \theta)$. Then
$$\begin{bmatrix} b_{pp} & b_{pq} \\ b_{qp} & b_{qq} \end{bmatrix} = \begin{bmatrix} c & s \\ -s
  & c \end{bmatrix}^T \begin{bmatrix} a_{pp} & a_{pq} \\ a_{qp} & a_{qq} \end{bmatrix}
  \begin{bmatrix} c & s \\ -s & c \end{bmatrix},$$
and, as the remark after (8.5.1) says, $b_{ij} = a_{ij}$ whenever neither $i$ nor $j$ is $p$ or
$q$.

The statement does not need $c^2 + s^2 = 1$. -/
theorem equation_8_5_1 (A : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n} (hpq : p ≠ q) (c s : ℝ) :
    !![((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p p,
        ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q;
      ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) q p,
        ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) q q] =
      !![c, s; -s, c]ᵀ * !![A p p, A p q; A q p, A q q] * !![c, s; -s, c] ∧
    ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q →
      ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) i j = A i j := by
  refine ⟨?_, fun i j hip hiq hjp hjq => conj_planeRotation_apply_of_ne hpq A hip hiq hjp hjq⟩
  rw [conj_planeRotation_apply_jj hpq, conj_planeRotation_apply_jk hpq,
    conj_planeRotation_apply_kj hpq, conj_planeRotation_apply_kk hpq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Equation (8.5.2)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let
$p \ne q$, let $c^2 + s^2 = 1$, and let $B = J(p, q, \theta)^T A J(p, q, \theta)$ satisfy
$b_{pq} = 0$. Then
$$a_{pp}^2 + a_{qq}^2 + 2a_{pq}^2 = b_{pp}^2 + b_{qq}^2, \qquad \operatorname{off}(B)^2 =
  \operatorname{off}(A)^2 - 2a_{pq}^2.$$
-/
theorem equation_8_5_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (h0 : ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q = 0) :
    A p p ^ 2 + A q q ^ 2 + 2 * A p q ^ 2 =
        ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p p ^ 2 +
          ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) q q ^ 2 ∧
      off ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) ^ 2 =
        off A ^ 2 - 2 * A p q ^ 2 := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by rw [neg_sq]; exact hcs
  refine ⟨?_, ?_⟩
  · have hqp : A q p = A p q := hA.apply p q
    rw [conj_planeRotation_apply_jk hpq, hqp] at h0
    rw [conj_planeRotation_apply_jj hpq, conj_planeRotation_apply_kk hpq, hqp]
    linear_combination (-(c ^ 2 + s ^ 2 + 1) * (A p p ^ 2 + A q q ^ 2 + 2 * A p q ^ 2)) * hcs +
      (2 * (c * (-(-s) * A p p + c * A p q) + -s * (-(-s) * A p q + c * A q q))) * h0
  · rw [off_sq, off_sq]
    exact offDiagNormSq_conj_planeRotation_of_apply_eq_zero A hA hpq hcs' h0

/-! ### §8.5.2 The 2-by-2 symmetric Schur decomposition -/

/-- **Equation (8.5.3)** of [golub2013matrix], with the derivation of §8.5.2. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $p \ne q$, and let
$B = J(p, q, \theta)^T A J(p, q, \theta)$. Then:

* for all $c, s \in \mathbb{R}$, $b_{pq} = a_{pq}(c^2 - s^2) + (a_{pp} - a_{qq}) cs$;
* if $a_{pq} \ne 0$ and $c \ne 0$, then with $\tau = (a_{qq} - a_{pp})/(2a_{pq})$ and $t = s/c$,
  $b_{pq} = 0$ if and only if $t^2 + 2\tau t - 1 = 0$;
* if $a_{pq} \ne 0$, the smaller root $t_{\min}$ solves $t^2 + 2\tau t - 1 = 0$;
* $|t_{\min}| \le 1$, so that $|\theta| \le \pi/4$;
* $c = 1/\sqrt{1 + t_{\min}^2}$ and $s = t_{\min} c$ give $b_{pq} = 0$.

The pair $(c, s)$ is `(Matrix.jacobiCosSmall A p q, Matrix.jacobiSinSmall A p q)`, and the root
is `Matrix.jacobiTanSmall A p q`. Explicitly, $t_{\min} = 1/(\tau + \sqrt{1 + \tau^2})$ for
$\tau \ge 0$, $t_{\min} = -1/(-\tau + \sqrt{1 + \tau^2})$ for $\tau < 0$, and $t_{\min} = 0$ if
$a_{pq} = 0$. -/
theorem equation_8_5_3 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    (∀ c s : ℝ, ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q =
      A p q * (c ^ 2 - s ^ 2) + (A p p - A q q) * c * s) ∧
    (∀ c s : ℝ, A p q ≠ 0 → c ≠ 0 →
      (((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q = 0 ↔
        (s / c) ^ 2 + 2 * ((A q q - A p p) / (2 * A p q)) * (s / c) - 1 = 0)) ∧
    (A p q ≠ 0 → jacobiTanSmall A p q ^ 2 +
      2 * ((A q q - A p p) / (2 * A p q)) * jacobiTanSmall A p q - 1 = 0) ∧
    |jacobiTanSmall A p q| ≤ 1 ∧
    jacobiCosSmall A p q = 1 / Real.sqrt (1 + jacobiTanSmall A p q ^ 2) ∧
    jacobiSinSmall A p q = jacobiTanSmall A p q * jacobiCosSmall A p q ∧
    ((planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q))ᵀ * A *
      planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q)) p q = 0 := by
  have hqp : A q p = A p q := hA.apply p q
  have hform : ∀ c s : ℝ, ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q =
      A p q * (c ^ 2 - s ^ 2) + (A p p - A q q) * c * s := fun c s => by
    rw [conj_planeRotation_apply_jk hpq, hqp]
    ring
  refine ⟨hform, fun c s ha hc => ?_, jacobiTanSmall_sq A p q, abs_jacobiTanSmall_le_one A p q,
    rfl, rfl, ?_⟩
  · have key : A p q * (c ^ 2 - s ^ 2) + (A p p - A q q) * c * s =
        -(c ^ 2 * A p q) * ((s / c) ^ 2 + 2 * ((A q q - A p p) / (2 * A p q)) * (s / c) - 1) := by
      field_simp
      ring
    rw [hform, key]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (neg_eq_zero.1 h) (mul_ne_zero (pow_ne_zero 2 hc) ha)
      · exact h
    · intro h
      rw [h, mul_zero]
  · rw [hform]
    linear_combination jacobiSmall_annihilate A p q

/-- **Algorithm 8.5.1** of [golub2013matrix] (`symSchur2`). Given $A \in \mathbb{R}^{n \times n}$
and indices $p$ and $q$, the algorithm computes a cosine-sine pair $(c, s)$; for symmetric $A$
and $p \ne q$ it makes $b_{pq} = b_{qp} = 0$ for $B = J(p, q, \theta)^T A J(p, q, \theta)$.
```
if a_pq ≠ 0
    τ = (a_qq - a_pp)/(2 a_pq)
    if τ ≥ 0 then t = 1/(τ + √(1 + τ²)) else t = 1/(τ - √(1 + τ²))
    c = 1/√(1 + t²),  s = t c
else
    c = 1,  s = 0
end
```

Every result of $+$, $-$, $\times$, $/$ and $\sqrt{\cdot}$ passes through `rnd`. The tests
$a_{pq} \ne 0$ and $\tau \ge 0$ are exact comparisons. The source assumes $p < q$; the program
accepts any $p$ and $q$. -/
noncomputable def algorithm_8_5_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : M (ℝ × ℝ) :=
  if A p q ≠ 0 then do
    let num ← rnd (A q q - A p p)
    let den ← rnd (2 * A p q)
    let τ ← rnd (num / den)
    let τ2 ← rnd (τ * τ)
    let r ← rnd (1 + τ2)
    let sq ← rnd (Real.sqrt r)
    let t ← if 0 ≤ τ then (do rnd (1 / (← rnd (τ + sq)))) else (do rnd (1 / (← rnd (τ - sq))))
    let t2 ← rnd (t * t)
    let u ← rnd (1 + t2)
    let v ← rnd (Real.sqrt u)
    let c ← rnd (1 / v)
    let s ← rnd (t * c)
    pure (c, s)
  else pure (1, 0)

/-- **Algorithm 8.5.1** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric and $p \ne q$. In exact arithmetic, Algorithm 8.5.1 returns the pair $(c, s)$ of
(8.5.3) with $t = t_{\min}$. The rotation $J(p, q, \theta)$ with this pair is the Jacobi
rotation `Matrix.jacobiRotation A p q`, and $B = J^T A J$ has $b_{pq} = b_{qp} = 0$.

The pair is `(Matrix.jacobiCosSmall A p q, Matrix.jacobiSinSmall A p q)`. -/
theorem algorithm_8_5_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    Id.run (algorithm_8_5_1 pure A p q) = (jacobiCosSmall A p q, jacobiSinSmall A p q) ∧
      planeRotation p q (Id.run (algorithm_8_5_1 pure A p q)).1
          (-(Id.run (algorithm_8_5_1 pure A p q)).2) = jacobiRotation A p q ∧
      ((jacobiRotation A p q)ᵀ * A * jacobiRotation A p q) p q = 0 ∧
      ((jacobiRotation A p q)ᵀ * A * jacobiRotation A p q) q p = 0 := by
  have hrun :
      Id.run (algorithm_8_5_1 pure A p q) = (jacobiCosSmall A p q, jacobiSinSmall A p q) := by
    by_cases h : A p q = 0
    · simp [algorithm_8_5_1, h, jacobiCosSmall, jacobiSinSmall, jacobiTanSmall]
    · unfold algorithm_8_5_1 jacobiSinSmall jacobiCosSmall jacobiTanSmall
      simp only [ne_eq, h, not_false_eq_true, ite_true, ite_false, pure_bind, sq]
      generalize (A q q - A p p) / (2 * A p q) = τ
      split_ifs with hτ
      · rfl
      · have : -1 / (-τ + Real.sqrt (1 + τ * τ)) = 1 / (τ - Real.sqrt (1 + τ * τ)) := by
          rw [show -τ + Real.sqrt (1 + τ * τ) = -(τ - Real.sqrt (1 + τ * τ)) by ring, div_neg,
            neg_div, neg_neg]
        rw [this]
        rfl
  have h0 := jacobiStep_apply_eq_zero A hA hpq
  refine ⟨hrun, by rw [hrun, jacobiRotation_eq_planeRotation_small], h0, ?_⟩
  have hsym := isSymm_jacobiStep hA p q
  change jacobiStep A p q q p = 0
  rw [hsym.apply p q]
  exact h0

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Section 8.5.2** of [golub2013matrix], the distance moved by a Jacobi update. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $p \ne q$, let $(c, s)$ be the rotation of
Algorithm 8.5.1, so that $c = 1/\sqrt{1 + t_{\min}^2}$ and $s = t_{\min} c$, and let
$B = J(p, q, \theta)^T A J(p, q, \theta)$. Then
$$\|B - A\|_F^2 = 4(1 - c) \sum_{i \ne p, q} (a_{ip}^2 + a_{iq}^2) + \frac{2a_{pq}^2}{c^2}.$$

The source concludes that the choice $t = t_{\min}$, which makes $c$ as large as possible,
minimizes this distance. -/
theorem jacobi_frobenius_dist {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    ‖(planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q))ᵀ * A *
        planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q) - A‖ ^ 2 =
      4 * (1 - jacobiCosSmall A p q) *
          ∑ i ∈ (Finset.univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) +
        2 * A p q ^ 2 / jacobiCosSmall A p q ^ 2 := by
  rw [← jacobiRotation_eq_planeRotation_small, jacobiCosSmall_eq]
  change ‖jacobiStep A p q - A‖ ^ 2 = _
  rw [frobenius_norm_sq_eq_sum_sq]
  simp only [Matrix.sub_apply, Real.norm_eq_abs, sq_abs]
  exact sum_sq_jacobiStep_sub A hA hpq

end Frobenius

/-! ### §8.5.3 The classical Jacobi algorithm -/

/-- **Section 8.5.3** of [golub2013matrix], the diagonal update. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, let $p \ne q$, and let $B$ be the Jacobi update of $A$ by the rotation of
Algorithm 8.5.1, with $t = t_{\min}$. Then
$$b_{pp} = a_{pp} - t a_{pq}, \qquad b_{qq} = a_{qq} + t a_{pq}.$$

The source remarks that this "precludes interchanging nearly converged diagonal entries". The
update $B$ is `Matrix.jacobiStep A p q`. -/
theorem jacobi_diag_update {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    jacobiStep A p q p p = A p p - jacobiTanSmall A p q * A p q ∧
      jacobiStep A p q q q = A q q + jacobiTanSmall A p q * A p q := by
  have h1 := jacobiStep_apply_jj_sub A hA hpq
  have h2 := jacobiStep_apply_kk_sub A hA hpq
  rw [jacobiTanSmall_eq_neg_jacobiTan]
  constructor <;> linarith

/-- **Section 8.5.3** of [golub2013matrix], the linear rate of the classical method. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $N = n(n-1)/2$, and let $p \ne q$ satisfy
$|a_{ij}| \le |a_{pq}|$ for all $i \ne j$. Then:

* $\operatorname{off}(A)^2 \le N (a_{pq}^2 + a_{qp}^2)$;
* the Jacobi update $B = J(p, q, \theta)^T A J(p, q, \theta)$ of Algorithm 8.5.1 satisfies
  $\operatorname{off}(B)^2 \le (1 - 1/N) \operatorname{off}(A)^2$;
* the iterates $A^{(k)}$ of the classical method satisfy $\operatorname{off}(A^{(k)})^2 \le (1 -
  1/N)^k \operatorname{off}(A^{(0)})^2$ for every $k$, with $A^{(0)} = A$.

The Lean statement assumes $n \ge 1$; the indices $p \ne q$ force $n \ge 2$, so $N \ge 1$. The
update is `Matrix.jacobiStep A p q`, and the iterates are `Matrix.classicalJacobiIterate A k`,
which at each step rotates at a largest off-diagonal entry. -/
theorem classicalJacobi_linear [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {p q : Fin n} (hpq : p ≠ q) (hmax : ∀ i j, i ≠ j → |A i j| ≤ |A p q|) :
    off A ^ 2 ≤ ((n : ℝ) * (n - 1) / 2) * (A p q ^ 2 + A q p ^ 2) ∧
      off (jacobiStep A p q) ^ 2 ≤ (1 - 1 / ((n : ℝ) * (n - 1) / 2)) * off A ^ 2 ∧
      ∀ k, off (classicalJacobiIterate A k) ^ 2 ≤
        (1 - 1 / ((n : ℝ) * (n - 1) / 2)) ^ k * off A ^ 2 := by
  have hqp : A q p = A p q := hA.apply p q
  have hN : (1 : ℝ) / ((n : ℝ) * (n - 1) / 2) = 2 / ((Fintype.card (Fin n) : ℝ) ^ 2 -
      Fintype.card (Fin n)) := by
    rw [Fintype.card_fin, one_div_div]
    ring
  have hbound := offDiagNormSq_le_mul_sq A (j := p) (k := q) fun x hx => hmax x.1 x.2 hx
  rw [Fintype.card_fin] at hbound
  have h1 : off A ^ 2 ≤ ((n : ℝ) * (n - 1) / 2) * (A p q ^ 2 + A q p ^ 2) := by
    rw [off_sq, hqp]
    linarith
  refine ⟨h1, ?_, fun k => ?_⟩
  · rw [off_sq, offDiagNormSq_jacobiStep A hA hpq, ← off_sq]
    have hn : (2 : ℝ) ≤ n := by
      have h1 := Fin.val_ne_of_ne hpq
      have h2 := p.isLt
      have h3 := q.isLt
      exact_mod_cast (show 2 ≤ n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) * (n - 1) / 2 := by nlinarith
    rw [hqp] at h1
    have : 2 * A p q ^ 2 ≥ off A ^ 2 / ((n : ℝ) * (n - 1) / 2) := by
      rw [ge_iff_le, div_le_iff₀ hNpos]
      linarith
    rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    linarith
  · rw [off_sq, off_sq, hN]
    exact offDiagNormSq_classicalJacobiIterate_le hA k

/-! ### §8.5.3–8.5.4 The classical and cyclic Jacobi algorithms -/

/-- The list of all index pairs $(i, j)$ of an $n \times n$ matrix, row by row. -/
def allPairs (n : ℕ) : List (Fin n × Fin n) := List.finRange n ×ˢ List.finRange n

/-- The list of the off-diagonal index pairs $(i, j)$, $i \ne j$, of an $n \times n$ matrix, row by
row. -/
def offDiagPairs (n : ℕ) : List (Fin n × Fin n) := (allPairs n).filter fun ij => ij.1 ≠ ij.2

/-- **Section 8.5.4** of [golub2013matrix], the cyclic-by-row ordering. It is the list of the pairs
$(p, q)$ with $p < q$, row by row:
$$(1, 2), (1, 3), \dots, (1, n), (2, 3), \dots, (2, n), \dots, (n-1, n).$$
-/
def cyclicPairs (n : ℕ) : List (Fin n × Fin n) := (allPairs n).filter fun pq => pq.1 < pq.2

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The computed value of $\operatorname{off}(A)$ in Algorithms 8.5.2 and 8.5.3:
$\mathrm{fl}\bigl(\sqrt{s}\bigr)$, where $s$ is the sum of the rounded squares
$\mathrm{fl}(a_{ij}^2)$ over the off-diagonal pairs, row by row, accumulated from $0$ by
Algorithm 1.1.1. -/
noncomputable def offComputed (A : Matrix (Fin n) (Fin n) ℝ) : M ℝ := do
  rnd √(← dotAccum rnd (offDiagPairs n) (fun ij => A ij.1 ij.2) (fun ij => A ij.1 ij.2) 0)

/-- The threshold $\delta = \mathrm{fl}(\mathrm{tol} \cdot \|A\|_F)$ of Algorithms 8.5.2 and 8.5.3,
where the computed Frobenius norm is $\mathrm{fl}\bigl(\sqrt{s}\bigr)$ and $s$ is the sum of the
rounded squares $\mathrm{fl}(a_{ij}^2)$ over all pairs, accumulated by Algorithm 1.1.1. -/
noncomputable def jacobiThreshold (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : M ℝ := do
  rnd (tol * (← rnd √(← dotAccum rnd (allPairs n) (fun ij => A ij.1 ij.2)
    (fun ij => A ij.1 ij.2) 0)))

/-- One Jacobi update of Algorithms 8.5.2 and 8.5.3 on the pair $(A, V)$: compute $(c, s)$ by
Algorithm 8.5.1, set $A = J(p, q, \theta)^T A J(p, q, \theta)$, and set $V = V J(p, q, \theta)$.

The rotation is `GolubVanLoan.Chapter05.givensRotation p q c s`, and the update of $A$ is
`GolubVanLoan.Chapter05.givensApplyLeft` on all columns followed by
`GolubVanLoan.Chapter05.givensApplyRight` on all rows. -/
noncomputable def jacobiUpdate (p q : Fin n) (A V : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let cs ← algorithm_8_5_1 rnd A p q
  let B ← Chapter05.givensApplyLeft rnd p q cs.1 cs.2 (List.finRange n) A
  let A' ← Chapter05.givensApplyRight rnd p q cs.1 cs.2 (List.finRange n) B
  let V' ← Chapter05.givensApplyRight rnd p q cs.1 cs.2 (List.finRange n) V
  pure (A', V')

/-- The pivot of Algorithm 8.5.2, "choose $(p, q)$ so $|a_{pq}| = \max_{i \ne j} |a_{ij}|$": the
first pair $(p, q)$ with $p < q$, row by row, at which $|a_{pq}|$ is maximal. The comparisons
are exact. For $n \le 1$ there is no pair, and the value is `none`. -/
noncomputable def classicalPivot (A : Matrix (Fin n) (Fin n) ℝ) : Option (Fin n × Fin n) :=
  (cyclicPairs n).argmax fun pq => |A pq.1 pq.2|

/-- One pass of the `while` loop of Algorithm 8.5.2 on the state $(A, V, \mathit{done})$. If the
flag is set, the state is unchanged. Otherwise the pass computes $\operatorname{off}(A)$; if it
is at most $\delta$, the loop stops and sets the flag, and if not, one Jacobi update is made at
the classical pivot. If there is no pivot ($n \le 1$), the state is unchanged. -/
noncomputable def classicalJacobiStep (δ : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2 then pure st else do
    let o ← offComputed rnd st.1
    if o ≤ δ then pure (st.1, st.2.1, true) else
      (classicalPivot st.1).elim (pure st) fun pq => do
        let AV ← jacobiUpdate rnd pq.1 pq.2 st.1 st.2.1
        pure (AV.1, AV.2, false)

/-- **Algorithm 8.5.2** of [golub2013matrix] (classical Jacobi). "Given a symmetric $A$ and a
positive tolerance $\mathrm{tol}$, this algorithm overwrites $A$ with $V^T A V$ where $V$ is
orthogonal and $\operatorname{off}(V^T A V) \le \mathrm{tol} \cdot \|A\|_F$."
```
V = I_n, δ = tol · ‖A‖_F
while off(A) > δ
    Choose (p, q) so |a_pq| = max_{i ≠ j} |a_ij|
    [c, s] = symSchur2(A, p, q)
    A = J(p, q, θ)ᵀ A J(p, q, θ)
    V = V J(p, q, θ)
end
```

The `while` loop runs at most `fuel` passes of `GolubVanLoan.Chapter08.classicalJacobiStep`,
with a flag `done`. The result is the triple of the final $A$, the final $V$ and the flag, which
records that the loop exited on its test. The program makes no assumption on `tol` or on the
symmetry of $A$; the specification theorems assume that $A$ is symmetric. -/
noncomputable def algorithm_8_5_2 (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let δ ← jacobiThreshold rnd tol A
  (List.range fuel).foldlM (fun st _ => classicalJacobiStep rnd δ st) (A, 1, false)

/-- One sweep of Algorithm 8.5.3: the Jacobi updates at all pairs $(p, q)$ with $p < q$, in the
cyclic-by-row ordering. -/
noncomputable def cyclicSweep (A V : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (cyclicPairs n).foldlM (fun AV pq => jacobiUpdate rnd pq.1 pq.2 AV.1 AV.2) (A, V)

/-- One pass of the `while` loop of Algorithm 8.5.3 on the state $(A, V, \mathit{done})$. If the
flag is set, the state is unchanged. Otherwise the pass computes $\operatorname{off}(A)$; if it
is at most $\delta$, the loop stops and sets the flag, and if not, one sweep is made. -/
noncomputable def cyclicJacobiStep (δ : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2 then pure st else do
    let o ← offComputed rnd st.1
    if o ≤ δ then pure (st.1, st.2.1, true) else do
      let AV ← cyclicSweep rnd st.1 st.2.1
      pure (AV.1, AV.2, false)

/-- **Algorithm 8.5.3** of [golub2013matrix] (cyclic Jacobi). "Given a symmetric $A$ and a positive
tolerance $\mathrm{tol}$, this algorithm overwrites $A$ with $V^T A V$ where $V$ is orthogonal
and $\operatorname{off}(V^T A V) \le \mathrm{tol} \cdot \|A\|_F$."
```
V = I_n, δ = tol · ‖A‖_F
while off(A) > δ
    for p = 1:n-1, for q = p+1:n
        [c, s] = symSchur2(A, p, q); A = J(p,q,θ)ᵀ A J(p,q,θ); V = V J(p,q,θ)
    end
end
```

The `while` loop runs at most `fuel` sweeps, with a flag `done`. The result is the triple of the
final $A$, the final $V$ and the flag, which records that the loop exited on its test. -/
noncomputable def algorithm_8_5_3 (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let δ ← jacobiThreshold rnd tol A
  (List.range fuel).foldlM (fun st _ => cyclicJacobiStep rnd δ st) (A, 1, false)

end Programs

/-! ### Exact semantics -/

/-- The sum of $g$ over a list without duplicates is the sum of $g$ over the set of its elements. -/
private theorem sum_map_eq_sum_filter {α : Type*} [Fintype α] {l : List α}
    (hl : l.Nodup) {P : α → Prop} [DecidablePred P] (hmem : ∀ x, x ∈ l ↔ P x) (g : α → ℝ) :
    (l.map g).sum = ∑ x ∈ Finset.univ.filter P, g x := by
  classical
  rw [← List.sum_toFinset g hl]
  congr 1
  ext x
  simp [hmem]

private theorem nodup_allPairs (n : ℕ) : (allPairs n).Nodup :=
  (List.nodup_finRange n).product (List.nodup_finRange n)

private theorem mem_allPairs (x : Fin n × Fin n) : x ∈ allPairs n :=
  List.mem_product.2 ⟨List.mem_finRange _, List.mem_finRange _⟩

private theorem mem_cyclicPairs {x : Fin n × Fin n} : x ∈ cyclicPairs n ↔ x.1 < x.2 := by
  simp [cyclicPairs, mem_allPairs]

/-- In exact arithmetic, the computed $\operatorname{off}(A)$ is $\operatorname{off}(A)$. -/
private theorem offComputed_id (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (offComputed pure A) = off A := by
  have h := dotAccum_id (offDiagPairs n) (fun ij : Fin n × Fin n => A ij.1 ij.2)
    (fun ij => A ij.1 ij.2) 0
  have hsum : ((offDiagPairs n).map fun ij : Fin n × Fin n => A ij.1 ij.2 * A ij.1 ij.2).sum =
      offDiagNormSq A := by
    rw [sum_map_eq_sum_filter (l := offDiagPairs n) ((nodup_allPairs n).filter _)
      (P := fun ij => ij.1 ≠ ij.2) (fun x => by simp [offDiagPairs, mem_allPairs]),
      Finset.sum_filter, Fintype.sum_prod_type,
      offDiagNormSq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.filter_ne]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs, sq]
  change Real.sqrt (Id.run (dotAccum pure (offDiagPairs n) _ _ 0)) = _
  rw [h, zero_add, hsum, off]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- In exact arithmetic, the threshold is $\mathrm{tol} \cdot \|A\|_F$. -/
private theorem jacobiThreshold_id (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (jacobiThreshold pure tol A) = tol * ‖A‖ := by
  have h := dotAccum_id (allPairs n) (fun ij : Fin n × Fin n => A ij.1 ij.2)
    (fun ij => A ij.1 ij.2) 0
  have hsum : ((allPairs n).map fun ij : Fin n × Fin n => A ij.1 ij.2 * A ij.1 ij.2).sum =
      ‖A‖ ^ 2 := by
    rw [sum_map_eq_sum_filter (nodup_allPairs n) (P := fun _ => True)
      (fun x => by simp [mem_allPairs]), Finset.filter_true_of_mem fun _ _ => trivial,
      Fintype.sum_prod_type,
      frobenius_norm_sq_eq_sum_sq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs, sq]
  change tol * Real.sqrt (Id.run (dotAccum pure (allPairs n) _ _ 0)) = _
  rw [h, zero_add, hsum, Real.sqrt_sq (norm_nonneg _)]

end Frobenius

/-- In exact arithmetic, the Jacobi update of $(A, V)$ is $(J^T A J, VJ)$ with $J$ =
`Matrix.jacobiRotation A p q`. -/
private theorem jacobiUpdate_id {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) (V : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (jacobiUpdate pure p q A V) = (jacobiStep A p q, V * jacobiRotation A p q) := by
  obtain ⟨-, hJ, -, -⟩ := algorithm_8_5_1_spec hA hpq
  have hall : ∀ i : Fin n, i ∈ List.finRange n := List.mem_finRange
  change (Id.run (Chapter05.givensApplyRight pure p q _ _ (List.finRange n)
      (Id.run (Chapter05.givensApplyLeft pure p q _ _ (List.finRange n) A))),
    Id.run (Chapter05.givensApplyRight pure p q _ _ (List.finRange n) V)) = _
  rw [Chapter05.givensApplyLeft_spec_of_forall_mem hpq _ _ (List.nodup_finRange n) hall,
    Chapter05.givensApplyRight_spec_of_forall_mem hpq _ _ (List.nodup_finRange n) hall,
    Chapter05.givensApplyRight_spec_of_forall_mem hpq _ _ (List.nodup_finRange n) hall]
  have hJ' : planeRotation p q (algorithm_8_5_1 (M := Id) pure A p q).1
      (-(algorithm_8_5_1 (M := Id) pure A p q).2) =
      jacobiRotation A p q := hJ
  simp only [Chapter05.givensRotation]
  rw [hJ']
  rfl

/-- The contraction factor $1 - 1/N$, $N = n(n-1)/2$, of the classical method is nonnegative. -/
private theorem jacobi_rate_nonneg (n : ℕ) : 0 ≤ 1 - 1 / ((n : ℝ) * (n - 1) / 2) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hN : 1 ≤ (n : ℝ) * (n - 1) / 2 := by nlinarith
    have : 1 / ((n : ℝ) * (n - 1) / 2) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hN
    linarith

/-- The classical pivot $(p, q)$ of a symmetric matrix satisfies $p \ne q$ and
$|a_{ij}| \le |a_{pq}|$ for all $i \ne j$. -/
private theorem classicalPivot_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {pq : Fin n × Fin n} (h : classicalPivot A = some pq) :
    pq.1 ≠ pq.2 ∧ ∀ i j, i ≠ j → |A i j| ≤ |A pq.1 pq.2| := by
  have hmem : pq ∈ cyclicPairs n := List.argmax_mem h
  refine ⟨(mem_cyclicPairs.1 hmem).ne, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact List.le_of_mem_argmax (f := fun pq : Fin n × Fin n => |A pq.1 pq.2|)
      (mem_cyclicPairs.2 (show (i, j).1 < (i, j).2 from hlt)) h
  · rw [hA.apply j i]
    exact List.le_of_mem_argmax (f := fun pq : Fin n × Fin n => |A pq.1 pq.2|)
      (mem_cyclicPairs.2 (show (j, i).1 < (j, i).2 from hgt)) h

/-- If there is no classical pivot ($n \le 1$), then $\operatorname{off}(B) = 0$ for every
$n \times n$ matrix $B$. -/
private theorem off_eq_zero_of_classicalPivot_eq_none {A : Matrix (Fin n) (Fin n) ℝ}
    (h : classicalPivot A = none) (B : Matrix (Fin n) (Fin n) ℝ) : off B = 0 := by
  have hnil : cyclicPairs n = [] := List.argmax_eq_none.1 h
  have hn : n ≤ 1 := by
    by_contra hn
    have hmem : ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) ∈ cyclicPairs n :=
      mem_cyclicPairs.2 (by simp [Fin.lt_def])
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  rw [off, offDiagNormSq_eq_zero_of_card_le_one (by simpa using hn), Real.sqrt_zero]

/-- For $p \ne q$, the Jacobi rotation `Matrix.jacobiRotation A p q` is orthogonal. -/
private theorem jacobiRotation_mem_orthogonalGroup (A : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n}
    (hpq : p ≠ q) : jacobiRotation A p q ∈ orthogonalGroup (Fin n) ℝ :=
  (mem_orthogonalGroup_iff' _ ℝ).2 (transpose_jacobiRotation_mul_self A p q hpq)

/-- The Jacobi step of $V^T A V$ at $(p, q)$ is the similarity of $A$ by $VJ$, where $J$ is the
Jacobi rotation of $V^T A V$. -/
private theorem jacobiStep_conj (A V : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    jacobiStep (Vᵀ * A * V) p q =
      (V * jacobiRotation (Vᵀ * A * V) p q)ᵀ * A * (V * jacobiRotation (Vᵀ * A * V) p q) := by
  rw [jacobiStep, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The loop invariant of Algorithm 8.5.2 after $k$ passes, with $\rho = 1 - 1/N$: $V$ is
orthogonal, $A_k = V^T A V$ is symmetric, $\operatorname{off}(A_k) \le \delta$ once the loop has
stopped, and $\operatorname{off}(A_k)^2 \le \rho^k \operatorname{off}(A)^2$ while it runs. -/
private def ClassicalInv (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (k : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ st.1 = st.2.1ᵀ * A * st.2.1 ∧ st.1.IsSymm ∧
    (st.2.2 = true → off st.1 ≤ δ) ∧
    (st.2.2 = false → off st.1 ^ 2 ≤ (1 - 1 / ((n : ℝ) * (n - 1) / 2)) ^ k * off A ^ 2)

private theorem classicalInv_step {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ} {k : ℕ}
    {st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool}
    (h : ClassicalInv A δ k st) :
    ClassicalInv A δ (k + 1) (Id.run (classicalJacobiStep pure δ st)) := by
  obtain ⟨Ak, V, d⟩ := st
  obtain ⟨hV, hAk, hs, hdone, hdec⟩ := h
  have hρ := jacobi_rate_nonneg n
  simp only at hV hAk hs hdone hdec
  cases d with
  | true =>
    have hrun : Id.run (classicalJacobiStep pure δ (Ak, V, true)) = (Ak, V, true) := rfl
    rw [hrun]
    exact ⟨hV, hAk, hs, hdone, fun h => absurd h (by simp)⟩
  | false =>
    have hoff := offComputed_id Ak
    by_cases ht : off Ak ≤ δ
    · have hrun : Id.run (classicalJacobiStep pure δ (Ak, V, false)) = (Ak, V, true) := by
        change (if Id.run (offComputed pure Ak) ≤ δ then _ else _) = _
        rw [hoff, ite_eq_left_of_eq_true _ _ (eq_true ht)]
        rfl
      rw [hrun]
      exact ⟨hV, hAk, hs, fun _ => ht, fun h => absurd h (by simp)⟩
    · cases hp : classicalPivot Ak with
      | none =>
        have hrun : Id.run (classicalJacobiStep pure δ (Ak, V, false)) = (Ak, V, false) := by
          change (if Id.run (offComputed pure Ak) ≤ δ then _ else _) = _
          rw [hoff, ite_eq_right_of_eq_false _ _ (eq_false ht), hp]
          rfl
        rw [hrun]
        refine ⟨hV, hAk, hs, fun h => absurd h (by simp), fun _ => ?_⟩
        rw [off_eq_zero_of_classicalPivot_eq_none hp Ak, zero_pow two_ne_zero]
        exact mul_nonneg (pow_nonneg hρ _) (sq_nonneg _)
      | some pq =>
        obtain ⟨hpq, hmax⟩ := classicalPivot_spec hs hp
        have hrun : Id.run (classicalJacobiStep pure δ (Ak, V, false)) =
            (jacobiStep Ak pq.1 pq.2, V * jacobiRotation Ak pq.1 pq.2, false) := by
          change (if Id.run (offComputed pure Ak) ≤ δ then _ else _) = _
          rw [hoff, ite_eq_right_of_eq_false _ _ (eq_false ht), hp]
          change ((Id.run (jacobiUpdate pure pq.1 pq.2 Ak V)).1,
            (Id.run (jacobiUpdate pure pq.1 pq.2 Ak V)).2, false) = _
          rw [jacobiUpdate_id hs hpq]
        rw [hrun]
        have : NeZero n := ⟨(Fin.pos pq.1).ne'⟩
        have hlin := (classicalJacobi_linear hs hpq hmax).2.1
        refine ⟨Submonoid.mul_mem _ hV (jacobiRotation_mem_orthogonalGroup Ak hpq), ?_,
          isSymm_jacobiStep hs _ _, fun h => absurd h (by simp), fun _ => ?_⟩
        · rw [hAk]
          exact jacobiStep_conj A V pq.1 pq.2
        · calc off (jacobiStep Ak pq.1 pq.2) ^ 2
              ≤ (1 - 1 / ((n : ℝ) * (n - 1) / 2)) * off Ak ^ 2 := hlin
            _ ≤ (1 - 1 / ((n : ℝ) * (n - 1) / 2)) *
                ((1 - 1 / ((n : ℝ) * (n - 1) / 2)) ^ k * off A ^ 2) :=
              mul_le_mul_of_nonneg_left (hdec rfl) hρ
            _ = (1 - 1 / ((n : ℝ) * (n - 1) / 2)) ^ (k + 1) * off A ^ 2 := by ring

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Algorithm 8.5.2** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, and let $\mathrm{tol} \in \mathbb{R}$ and the number of passes be arbitrary. In
exact arithmetic, the output $(A', V, \mathit{done})$ of Algorithm 8.5.2 satisfies: $V$ is
orthogonal, $A' = V^T A V$, and $A'$ is symmetric. If the loop exited on its test, then
$\operatorname{off}(A') \le \mathrm{tol} \cdot \|A\|_F$. Otherwise
$$\operatorname{off}(A')^2 \le (1 - 1/N)^{\mathit{fuel}} \operatorname{off}(A)^2, \qquad N =
  n(n-1)/2,$$
where $\mathit{fuel}$ is the number of passes.

The second bound is the linear rate of §8.5.3: each update is made at a largest off-diagonal
entry and multiplies $\operatorname{off}^2$ by at most $1 - 1/N$. Every largest entry gives this
bound, so the choice among several largest entries does not matter. -/
theorem algorithm_8_5_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (tol : ℝ)
    (fuel : ℕ) :
    (Id.run (algorithm_8_5_2 pure tol A fuel)).2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_8_5_2 pure tol A fuel)).1 =
        (Id.run (algorithm_8_5_2 pure tol A fuel)).2.1ᵀ * A *
          (Id.run (algorithm_8_5_2 pure tol A fuel)).2.1 ∧
      (Id.run (algorithm_8_5_2 pure tol A fuel)).1.IsSymm ∧
      ((Id.run (algorithm_8_5_2 pure tol A fuel)).2.2 = true →
        off (Id.run (algorithm_8_5_2 pure tol A fuel)).1 ≤ tol * ‖A‖) ∧
      ((Id.run (algorithm_8_5_2 pure tol A fuel)).2.2 = false →
        off (Id.run (algorithm_8_5_2 pure tol A fuel)).1 ^ 2 ≤
          (1 - 1 / ((n : ℝ) * (n - 1) / 2)) ^ fuel * off A ^ 2) := by
  have hrun : Id.run (algorithm_8_5_2 pure tol A fuel) = Id.run ((List.range fuel).foldlM
      (fun st _ => classicalJacobiStep pure (tol * ‖A‖) st) (A, 1, false)) := by
    rw [← jacobiThreshold_id]
    rfl
  have key : ∀ k, ClassicalInv A (tol * ‖A‖) k (Id.run ((List.range k).foldlM
      (fun st _ => classicalJacobiStep pure (tol * ‖A‖) st) (A, 1, false))) := by
    intro k
    induction k with
    | zero => exact ⟨one_mem _, by simp, hA, fun h => absurd h (by simp), fun _ => by simp⟩
    | succ k ih =>
      rw [List.idRun_foldlM_range_succ]
      exact classicalInv_step ih
  rw [hrun]
  exact key fuel

/-- **Section 8.5.3** of [golub2013matrix], termination of Algorithm 8.5.2 in exact arithmetic. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 2$, let $\mathrm{tol} > 0$, let
$N = n(n-1)/2$, and let the number of passes $\mathit{fuel}$ satisfy
$$\mathit{fuel} \ge \Bigl\lceil \frac{2 \log \mathrm{tol}}{\log(1 - 1/N)} \Bigr\rceil + 1.$$
Then the output of Algorithm 8.5.2 satisfies $\operatorname{off}(V^T A V) \le \mathrm{tol} \cdot
\|A\|_F$.

If the loop stopped, the bound is its test. Otherwise it follows from
$\operatorname{off}(A^{(k)})^2 \le (1 - 1/N)^k \operatorname{off}(A)^2 \le (1 - 1/N)^k
\|A\|_F^2$. The ceiling is the ceiling in $\mathbb{N}$, so a negative quotient gives $0$. For
$N = 1$ the Lean value of $\log 0$ is $0$, so the bound reads $\mathit{fuel} \ge 1$; one update
then diagonalizes $A$. -/
theorem algorithm_8_5_2_terminates {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hn : 2 ≤ n)
    {tol : ℝ} (htol : 0 < tol) {fuel : ℕ}
    (hfuel : ⌈2 * Real.log tol / Real.log (1 - 1 / ((n : ℝ) * (n - 1) / 2))⌉₊ + 1 ≤ fuel) :
    off (Id.run (algorithm_8_5_2 pure tol A fuel)).1 ≤ tol * ‖A‖ := by
  obtain ⟨-, -, -, hdone, hdec⟩ := algorithm_8_5_2_spec hA tol fuel
  cases hd : (Id.run (algorithm_8_5_2 pure tol A fuel)).2.2 with
  | true => exact hdone hd
  | false =>
    set ρ := 1 - 1 / ((n : ℝ) * (n - 1) / 2) with hρdef
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hN : 1 ≤ (n : ℝ) * (n - 1) / 2 := by nlinarith
    have hρ0 : 0 ≤ ρ := jacobi_rate_nonneg n
    have hρ1 : ρ < 1 := by
      have : 0 < 1 / ((n : ℝ) * (n - 1) / 2) := by positivity
      linarith
    have hpow : ρ ^ fuel ≤ tol ^ 2 := by
      rcases hρ0.eq_or_lt with h0 | hpos
      · rw [← h0, zero_pow (by omega)]; positivity
      · rcases le_or_gt 1 tol with ht1 | ht1
        · calc ρ ^ fuel ≤ 1 := pow_le_one₀ hρ0 hρ1.le
            _ ≤ tol ^ 2 := by nlinarith
        · have hlρ : Real.log ρ < 0 := Real.log_neg hpos hρ1
          have hc : 2 * Real.log tol / Real.log ρ ≤ fuel := by
            have := Nat.le_ceil (2 * Real.log tol / Real.log ρ)
            have h' : ((⌈2 * Real.log tol / Real.log ρ⌉₊ : ℕ) : ℝ) ≤ fuel := by
              exact_mod_cast (Nat.le_succ _).trans hfuel
            linarith
          rw [div_le_iff_of_neg hlρ] at hc
          rw [← Real.log_le_log_iff (pow_pos hpos _) (by positivity), Real.log_pow,
            Real.log_pow]
          push_cast
          linarith
    have hoffA : off A ^ 2 ≤ ‖A‖ ^ 2 := by
      rw [off_sq_eq]
      have : 0 ≤ ∑ i, A i i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith
    have hsq : off (Id.run (algorithm_8_5_2 pure tol A fuel)).1 ^ 2 ≤ (tol * ‖A‖) ^ 2 := by
      calc _ ≤ ρ ^ fuel * off A ^ 2 := hdec hd
        _ ≤ tol ^ 2 * ‖A‖ ^ 2 := mul_le_mul hpow hoffA (sq_nonneg _) (sq_nonneg _)
        _ = (tol * ‖A‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (off_nonneg _) (by positivity) two_ne_zero).1 hsq

end Frobenius

/-- The Jacobi updates of a sweep over any list of pairs $p \ne q$ keep $A_k = V^T A V$ symmetric
with $V$ orthogonal, and they do not increase $\operatorname{off}$, since each removes
$2a_{pq}^2$ from $\operatorname{off}^2$ by (8.5.2). -/
private theorem sweep_inv {A : Matrix (Fin n) (Fin n) ℝ} :
    ∀ (l : List (Fin n × Fin n)), (∀ pq ∈ l, pq.1 ≠ pq.2) →
      ∀ B V : Matrix (Fin n) (Fin n) ℝ, V ∈ orthogonalGroup (Fin n) ℝ → B = Vᵀ * A * V →
        B.IsSymm → off B ≤ off A →
        let r := Id.run (l.foldlM (fun AV pq => jacobiUpdate pure pq.1 pq.2 AV.1 AV.2) (B, V))
        r.2 ∈ orthogonalGroup (Fin n) ℝ ∧ r.1 = r.2ᵀ * A * r.2 ∧ r.1.IsSymm ∧ off r.1 ≤ off A := by
  intro l
  induction l with
  | nil => intro _ B V hV hB hs hoff; exact ⟨hV, hB, hs, hoff⟩
  | cons pq l ih =>
    intro hl B V hV hB hs hoff
    have hpq := hl pq List.mem_cons_self
    have hstep : Id.run ((pq :: l).foldlM
        (fun AV pq => jacobiUpdate pure pq.1 pq.2 AV.1 AV.2) (B, V)) =
        Id.run (l.foldlM (fun AV pq => jacobiUpdate pure pq.1 pq.2 AV.1 AV.2)
          (jacobiStep B pq.1 pq.2, V * jacobiRotation B pq.1 pq.2)) := by
      rw [← jacobiUpdate_id hs hpq]
      rfl
    simp only
    rw [hstep]
    refine ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ _
      (Submonoid.mul_mem _ hV (jacobiRotation_mem_orthogonalGroup B hpq))
      (by rw [hB]; exact jacobiStep_conj A V pq.1 pq.2) (isSymm_jacobiStep hs _ _)
      (le_trans ?_ hoff)
    refine Real.sqrt_le_sqrt ?_
    rw [offDiagNormSq_jacobiStep B hs hpq]
    nlinarith [sq_nonneg (B pq.1 pq.2)]

/-- The loop invariant of Algorithm 8.5.3: $V$ is orthogonal, $A_k = V^T A V$ is symmetric,
$\operatorname{off}(A_k) \le \operatorname{off}(A)$, and $\operatorname{off}(A_k) \le \delta$
once the loop has stopped. -/
private def CyclicInv (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ st.1 = st.2.1ᵀ * A * st.2.1 ∧ st.1.IsSymm ∧
    off st.1 ≤ off A ∧ (st.2.2 = true → off st.1 ≤ δ)

private theorem cyclicInv_step {A : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ}
    {st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool} (h : CyclicInv A δ st) :
    CyclicInv A δ (Id.run (cyclicJacobiStep pure δ st)) := by
  obtain ⟨Ak, V, d⟩ := st
  obtain ⟨hV, hAk, hs, hoff, hdone⟩ := h
  simp only at hV hAk hs hoff hdone
  cases d with
  | true =>
    have hrun : Id.run (cyclicJacobiStep pure δ (Ak, V, true)) = (Ak, V, true) := rfl
    rw [hrun]
    exact ⟨hV, hAk, hs, hoff, hdone⟩
  | false =>
    have ho := offComputed_id Ak
    by_cases ht : off Ak ≤ δ
    · have hrun : Id.run (cyclicJacobiStep pure δ (Ak, V, false)) = (Ak, V, true) := by
        change (if Id.run (offComputed pure Ak) ≤ δ then _ else _) = _
        rw [ho, ite_eq_left_of_eq_true _ _ (eq_true ht)]
        rfl
      rw [hrun]
      exact ⟨hV, hAk, hs, hoff, fun _ => ht⟩
    · have hrun : Id.run (cyclicJacobiStep pure δ (Ak, V, false)) =
          ((Id.run (cyclicSweep pure Ak V)).1, (Id.run (cyclicSweep pure Ak V)).2, false) := by
        change (if Id.run (offComputed pure Ak) ≤ δ then _ else _) = _
        rw [ho, ite_eq_right_of_eq_false _ _ (eq_false ht)]
        rfl
      rw [hrun]
      obtain ⟨h1, h2, h3, h4⟩ := sweep_inv (cyclicPairs n)
        (fun pq hpq => (mem_cyclicPairs.1 hpq).ne) Ak V hV hAk hs hoff
      exact ⟨h1, h2, h3, h4, fun h => absurd h (by simp)⟩

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Algorithm 8.5.3** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, and let $\mathrm{tol} \in \mathbb{R}$ and the number of sweeps be arbitrary. In
exact arithmetic, the output $(A', V, \mathit{done})$ of Algorithm 8.5.3 satisfies: $V$ is
orthogonal, $A' = V^T A V$, $A'$ is symmetric, and $\operatorname{off}(A') \le
\operatorname{off}(A)$. If the loop exited on its test, then $\operatorname{off}(A') \le
\mathrm{tol} \cdot \|A\|_F$.

Each rotation removes $2a_{pq}^2$ from $\operatorname{off}^2$ by (8.5.2). The source quotes the
quadratic convergence of the cyclic method; it is not claimed here. -/
theorem algorithm_8_5_3_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (tol : ℝ)
    (fuel : ℕ) :
    (Id.run (algorithm_8_5_3 pure tol A fuel)).2.1 ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_8_5_3 pure tol A fuel)).1 =
        (Id.run (algorithm_8_5_3 pure tol A fuel)).2.1ᵀ * A *
          (Id.run (algorithm_8_5_3 pure tol A fuel)).2.1 ∧
      (Id.run (algorithm_8_5_3 pure tol A fuel)).1.IsSymm ∧
      off (Id.run (algorithm_8_5_3 pure tol A fuel)).1 ≤ off A ∧
      ((Id.run (algorithm_8_5_3 pure tol A fuel)).2.2 = true →
        off (Id.run (algorithm_8_5_3 pure tol A fuel)).1 ≤ tol * ‖A‖) := by
  have hrun : Id.run (algorithm_8_5_3 pure tol A fuel) = Id.run ((List.range fuel).foldlM
      (fun st _ => cyclicJacobiStep pure (tol * ‖A‖) st) (A, 1, false)) := by
    rw [← jacobiThreshold_id]
    rfl
  have key : ∀ k, CyclicInv A (tol * ‖A‖) (Id.run ((List.range k).foldlM
      (fun st _ => cyclicJacobiStep pure (tol * ‖A‖) st) (A, 1, false))) := by
    intro k
    induction k with
    | zero => exact ⟨one_mem _, by simp, hA, le_rfl, fun h => absurd h (by simp)⟩
    | succ k ih =>
      rw [List.idRun_foldlM_range_succ]
      exact cyclicInv_step ih
  rw [hrun]
  exact key fuel

end Frobenius

/-! ### §8.5.6 Block Jacobi procedures -/

/-- **Section 8.5.6** of [golub2013matrix], block Jacobi. Let $A \in \mathbb{R}^{Nr \times Nr}$ be
symmetric and partitioned into $N \times N$ blocks $A_{ij}$ of size $r \times r$, and let
$p \ne q$ be block indices. Let
$$W = \begin{bmatrix} V_{pp} & V_{pq} \\ V_{qp} & V_{qq} \end{bmatrix} \in \mathbb{R}^{2r \times
  2r}$$
be orthogonal with
$$W^T \begin{bmatrix} A_{pp} & A_{pq} \\ A_{qp} & A_{qq} \end{bmatrix} W = \begin{bmatrix}
  D_{pp} & 0 \\ 0 & D_{qq} \end{bmatrix},$$
where $D_{pp}$ and $D_{qq}$ are diagonal. Let $V \in \mathbb{R}^{Nr \times Nr}$ have the blocks
$V_{pp}, V_{pq}, V_{qp}, V_{qq}$ in block rows and columns $p$ and $q$, and agree with the
identity in every entry whose row or column lies outside the block rows and columns $p$ and $q$.
Then
$$\operatorname{off}(V^T A V)^2 = \operatorname{off}(A)^2 - \bigl(2\|A_{pq}\|_F^2 +
  \operatorname{off}(A_{pp})^2 + \operatorname{off}(A_{qq})^2\bigr).$$

Rows and columns are indexed by pairs (block, position) in `Fin N × Fin r`. The block in block
row $p$ and block column $q$ is `A.submatrix (Prod.mk p) (Prod.mk q)`, and
`Matrix.offDiagNormSq` gives $\operatorname{off}(\cdot)^2$ of the whole matrix, over all its
off-diagonal entries. -/
theorem blockJacobi_off {N r : ℕ} {A : Matrix (Fin N × Fin r) (Fin N × Fin r) ℝ} (hA : A.IsSymm)
    {p q : Fin N} (hpq : p ≠ q) {Vpp Vpq Vqp Vqq Dpp Dqq : Matrix (Fin r) (Fin r) ℝ}
    (hW : fromBlocks Vpp Vpq Vqp Vqq ∈ orthogonalGroup (Fin r ⊕ Fin r) ℝ)
    (hD : (fromBlocks Vpp Vpq Vqp Vqq)ᵀ *
        fromBlocks (A.submatrix (Prod.mk p) (Prod.mk p)) (A.submatrix (Prod.mk p) (Prod.mk q))
          (A.submatrix (Prod.mk q) (Prod.mk p)) (A.submatrix (Prod.mk q) (Prod.mk q)) *
        fromBlocks Vpp Vpq Vqp Vqq = fromBlocks Dpp 0 0 Dqq)
    (hDpp : Dpp.IsDiag) (hDqq : Dqq.IsDiag) {V : Matrix (Fin N × Fin r) (Fin N × Fin r) ℝ}
    (hV : ∀ i j, V (p, i) (p, j) = Vpp i j ∧ V (p, i) (q, j) = Vpq i j ∧
      V (q, i) (p, j) = Vqp i j ∧ V (q, i) (q, j) = Vqq i j)
    (hV' : ∀ x y : Fin N × Fin r, (x.1 ≠ p ∧ x.1 ≠ q) ∨ (y.1 ≠ p ∧ y.1 ≠ q) →
      V x y = if x = y then 1 else 0) :
    offDiagNormSq (Vᵀ * A * V) = offDiagNormSq A -
      (2 * ∑ i, ∑ j, A (p, i) (q, j) ^ 2 + off (A.submatrix (Prod.mk p) (Prod.mk p)) ^ 2 +
        off (A.submatrix (Prod.mk q) (Prod.mk q)) ^ 2) := by
  set e : Fin r ⊕ Fin r → Fin N × Fin r := Sum.elim (Prod.mk p) (Prod.mk q) with hedef
  have he : Function.Injective e := by
    rintro (a | a) (b | b) h <;>
      simp only [hedef, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h <;> simp_all
  have hsub : A.submatrix e e = fromBlocks (A.submatrix (Prod.mk p) (Prod.mk p))
      (A.submatrix (Prod.mk p) (Prod.mk q)) (A.submatrix (Prod.mk q) (Prod.mk p))
      (A.submatrix (Prod.mk q) (Prod.mk q)) := by
    ext (a | a) (b | b) <;> rfl
  have hVe : ∀ a b, V (e a) (e b) = fromBlocks Vpp Vpq Vqp Vqq a b := by
    rintro (a | a) (b | b)
    exacts [(hV a b).1, (hV a b).2.1, (hV a b).2.2.1, (hV a b).2.2.2]
  have hrange : ∀ x : Fin N × Fin r, x ∉ Set.range e → x.1 ≠ p ∧ x.1 ≠ q := fun x hx =>
    ⟨fun h => hx ⟨Sum.inl x.2, Prod.ext h.symm rfl⟩, fun h => hx ⟨Sum.inr x.2, Prod.ext h.symm rfl⟩⟩
  have hVe' : ∀ i j, (i ∉ Set.range e ∨ j ∉ Set.range e) →
      V i j = (1 : Matrix (Fin N × Fin r) (Fin N × Fin r) ℝ) i j := fun i j h => by
    rw [hV' i j (h.imp (hrange i) (hrange j)), Matrix.one_apply]
  have hWW : (fromBlocks Vpp Vpq Vqp Vqq)ᵀ * fromBlocks Vpp Vpq Vqp Vqq = 1 :=
    (mem_orthogonalGroup_iff' _ ℝ).1 hW
  have key := offDiagNormSq_conj_block A he hWW hVe hVe'
  have hD0 : offDiagNormSq (fromBlocks Dpp 0 0 Dqq) = 0 := by
    refine offDiagNormSq_eq_zero_iff.2 ?_
    rintro (a | a) (b | b) h
    · exact hDpp fun h' => h (congrArg Sum.inl h')
    · rfl
    · rfl
    · exact hDqq fun h' => h (congrArg Sum.inr h')
  rw [key, hsub, hD, hD0, add_zero, offDiagNormSq_fromBlocks, off_sq, off_sq]
  have hsym : ∑ i, ∑ j, A.submatrix (Prod.mk q) (Prod.mk p) i j ^ 2 =
      ∑ i, ∑ j, A (p, i) (q, j) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [submatrix_apply, hA.apply (p, i) (q, j)]
  rw [hsym]
  simp only [submatrix_apply]
  ring

/-! ### §8.5.7 A note on the parallel ordering -/

/-- The seat of player $x \ge 1$ at the start of the tournament of §8.5.7 with $2m$ players,
numbered from $0$. With top row $t_1, \dots, t_m$ and bottom row $b_1, \dots, b_m$ of the $m$
tables, player $0$ stays at $t_1$, and players $1, \dots, 2m - 1$ circulate along the cycle of
seats $b_1, t_2, \dots, t_m, b_m, \dots, b_2$ of length $2m - 1$. In round $0$ player $x$ sits
at table $\lfloor x/2 \rfloor + 1$; this definition gives the number of its seat on that cycle. -/
def parallelSeat (m x : ℕ) : ℕ :=
  if x = 1 then 0 else if x % 2 = 0 then x / 2 else (4 * m - 1 - x) / 2

/-- Players $a$ and $b$, numbered from $0$, sit at the same table in round $k$, numbered from $0$,
of the tournament of §8.5.7 with $2m$ players. Seats $i$ and $j$ of the cycle of length
$M = 2m - 1$ face each other if and only if $M$ divides $i + j$, seat $0$ faces the fixed player
$0$, and in round $k$ player $x \ge 1$ sits at seat $\sigma(x) + k$ modulo $M$, where
$\sigma(x)$ is `GolubVanLoan.Chapter08.parallelSeat m x`. -/
def ParallelPaired (m k a b : ℕ) : Prop :=
  if a = 0 then 2 * m - 1 ∣ parallelSeat m b + k
  else if b = 0 then 2 * m - 1 ∣ parallelSeat m a + k
  else 2 * m - 1 ∣ parallelSeat m a + parallelSeat m b + 2 * k

/-- Whether two players sit at the same table, `GolubVanLoan.Chapter08.ParallelPaired`, is
decidable. -/
instance (m k a b : ℕ) : Decidable (ParallelPaired m k a b) := by
  unfold ParallelPaired; infer_instance

/-- **Section 8.5.7** of [golub2013matrix], the parallel ordering. For $2m$ players and a round $k$
with $0 \le k < 2m - 1$, the rotation set of round $k$ is the set of pairs $(i, j)$ with $i < j$
of players who sit at the same table in the round-robin ("chess tournament") schedule. Player
$0$ stays at the same seat, and players $1, \dots, 2m - 1$ move merry-go-round between rounds,
as in the source.

Players and rounds are numbered from $0$, so the book's player $i + 1$ is `i`. See
`GolubVanLoan.Chapter08.parallelOrdering_four` for all seven rounds when $m = 4$. Round $0$ is
the book's $\mathrm{rot.set}(1) = \{(1, 2), (3, 4), \dots, (2m - 1, 2m)\}$. -/
def parallelOrdering (m : ℕ) (k : Fin (2 * m - 1)) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter fun ij => ij.1 < ij.2 ∧ ParallelPaired m k ij.1 ij.2

/-- If $a, b < M$, $M \mid x + a$ and $M \mid x + b$, then $a = b$. -/
private lemma eq_of_dvd_add {M x a b : ℕ} (ha : a < M) (hb : b < M) (hxa : M ∣ x + a)
    (hxb : M ∣ x + b) : a = b := by
  wlog h : a ≤ b generalizing a b
  · exact (this hb ha hxb hxa (by omega)).symm
  have hd := Nat.dvd_sub hxb hxa
  rw [show x + b - (x + a) = b - a by omega] at hd
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

/-- For odd $M$, $M \mid 2y$ implies $M \mid y$. -/
private lemma dvd_of_dvd_two_mul {M y : ℕ} (hM : M % 2 = 1) (h : M ∣ 2 * y) : M ∣ y := by
  obtain ⟨e, rfl⟩ : ∃ e, M = 2 * e + 1 := ⟨M / 2, by omega⟩
  have h' : 2 * e + 1 ∣ (2 * e + 1) * y + y := by
    rw [show (2 * e + 1) * y + y = (e + 1) * (2 * y) by ring]
    exact Dvd.dvd.mul_left h _
  exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 h'

/-- For odd $M$, if $a, b < M$, $M \mid x + 2a$ and $M \mid x + 2b$, then $a = b$. -/
private lemma eq_of_dvd_add_two_mul {M x a b : ℕ} (hM : M % 2 = 1) (ha : a < M) (hb : b < M)
    (hxa : M ∣ x + 2 * a) (hxb : M ∣ x + 2 * b) : a = b := by
  wlog h : a ≤ b generalizing a b
  · exact (this hb ha hxb hxa (by omega)).symm
  have hd := Nat.dvd_sub hxb hxa
  rw [show x + 2 * b - (x + 2 * a) = 2 * (b - a) by omega] at hd
  have := Nat.eq_zero_of_dvd_of_lt (dvd_of_dvd_two_mul hM hd) (by omega)
  omega

/-- For $M > 0$, every $x$ has a complement $c < M$ with $M \mid x + c$. -/
private lemma exists_dvd_add {M : ℕ} (hM : 0 < M) (x : ℕ) : ∃ c < M, M ∣ x + c := by
  have h := Nat.div_add_mod x M
  have hr := Nat.mod_lt x hM
  by_cases h0 : x % M = 0
  · exact ⟨0, hM, by rw [Nat.add_zero]; exact Nat.dvd_of_mod_eq_zero h0⟩
  · refine ⟨M - x % M, by omega, x / M + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Every seat lies on the cycle of length $2m - 1$. -/
private lemma parallelSeat_lt {m x : ℕ} (hx : x < 2 * m) : parallelSeat m x < 2 * m - 1 := by
  unfold parallelSeat; split_ifs <;> omega

/-- Players $1, \dots, 2m - 1$ occupy distinct seats. -/
private lemma parallelSeat_inj {m x y : ℕ} (hx0 : x ≠ 0) (hx : x < 2 * m) (hy0 : y ≠ 0)
    (hy : y < 2 * m) (h : parallelSeat m x = parallelSeat m y) : x = y := by
  unfold parallelSeat at h; split_ifs at h <;> omega

/-- Every seat of the cycle is occupied by one of the players $1, \dots, 2m - 1$. -/
private lemma exists_parallelSeat_eq {m c : ℕ} (hc : c < 2 * m - 1) :
    ∃ x, x ≠ 0 ∧ x < 2 * m ∧ parallelSeat m x = c := by
  by_cases h0 : c = 0
  · exact ⟨1, by omega, by omega, by simp [parallelSeat, h0]⟩
  by_cases h1 : c < m
  · refine ⟨2 * c, by omega, by omega, ?_⟩
    unfold parallelSeat; split_ifs <;> omega
  · refine ⟨4 * m - 1 - 2 * c, by omega, by omega, ?_⟩
    unfold parallelSeat; split_ifs <;> omega

/-- Sitting at the same table is a symmetric relation. -/
private lemma parallelPaired_comm {m k a b : ℕ} :
    ParallelPaired m k a b ↔ ParallelPaired m k b a := by
  unfold ParallelPaired
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · simp only [ha, hb, ↓reduceIte]
    rw [Nat.add_comm (parallelSeat m a)]

/-- In each round every player has at most one opponent. -/
private lemma parallelPaired_unique {m k a b b' : ℕ} (ha : a < 2 * m)
    (hb : b < 2 * m) (hb' : b' < 2 * m) (hab : a ≠ b) (hab' : a ≠ b')
    (h : ParallelPaired m k a b) (h' : ParallelPaired m k a b') : b = b' := by
  unfold ParallelPaired at h h'
  have hsa := parallelSeat_lt ha
  have hsb := parallelSeat_lt hb
  have hsb' := parallelSeat_lt hb'
  by_cases ha0 : a = 0
  · rw [ite_eq_left ha0] at h h'
    refine parallelSeat_inj (by omega) hb (by omega) hb' (eq_of_dvd_add (x := k) hsb hsb' ?_ ?_)
    · rw [Nat.add_comm]; exact h
    · rw [Nat.add_comm]; exact h'
  rw [ite_eq_right ha0] at h h'
  by_cases hb0 : b = 0 <;> by_cases hb0' : b' = 0
  · rw [hb0, hb0']
  · rw [ite_eq_left hb0] at h
    rw [ite_eq_right hb0'] at h'
    have h2 : 2 * m - 1 ∣ parallelSeat m a + k + (parallelSeat m b' + k) := by
      rw [show parallelSeat m a + k + (parallelSeat m b' + k) =
        parallelSeat m a + parallelSeat m b' + 2 * k by ring]
      exact h'
    have h3 := (Nat.dvd_add_right h).1 h2
    have := parallelSeat_inj ha0 ha hb0' hb' (eq_of_dvd_add hsa hsb' (by rwa [Nat.add_comm])
      (by rwa [Nat.add_comm]))
    exact absurd this hab'
  · rw [ite_eq_right hb0] at h
    rw [ite_eq_left hb0'] at h'
    have h2 : 2 * m - 1 ∣ parallelSeat m a + k + (parallelSeat m b + k) := by
      rw [show parallelSeat m a + k + (parallelSeat m b + k) =
        parallelSeat m a + parallelSeat m b + 2 * k by ring]
      exact h
    have h3 := (Nat.dvd_add_right h').1 h2
    have := parallelSeat_inj ha0 ha hb0 hb (eq_of_dvd_add hsa hsb (by rwa [Nat.add_comm])
      (by rwa [Nat.add_comm]))
    exact absurd this hab
  · rw [ite_eq_right hb0] at h
    rw [ite_eq_right hb0'] at h'
    refine parallelSeat_inj hb0 hb hb0' hb'
      (eq_of_dvd_add (x := parallelSeat m a + 2 * k) hsb hsb' ?_ ?_)
    · rwa [Nat.add_right_comm] at h
    · rwa [Nat.add_right_comm] at h'

/-- In each round $k < 2m - 1$ every player has an opponent. -/
private lemma exists_parallelPaired {m k a : ℕ} (hk : k < 2 * m - 1) (ha : a < 2 * m) :
    ∃ b < 2 * m, a ≠ b ∧ ParallelPaired m k a b := by
  have hM : 0 < 2 * m - 1 := by omega
  unfold ParallelPaired
  by_cases ha0 : a = 0
  · obtain ⟨c, hc, hdvd⟩ := exists_dvd_add hM k
    obtain ⟨b, hb0, hb, rfl⟩ := exists_parallelSeat_eq hc
    refine ⟨b, hb, by omega, ?_⟩
    rw [ite_eq_left ha0, Nat.add_comm]
    exact hdvd
  · by_cases hak : 2 * m - 1 ∣ parallelSeat m a + k
    · exact ⟨0, by omega, ha0, by rw [ite_eq_right ha0, ite_eq_left rfl]; exact hak⟩
    · obtain ⟨c, hc, hdvd⟩ := exists_dvd_add hM (parallelSeat m a + 2 * k)
      obtain ⟨b, hb0, hb, rfl⟩ := exists_parallelSeat_eq hc
      refine ⟨b, hb, fun hab => hak ?_, ?_⟩
      · rw [← hab] at hdvd
        refine dvd_of_dvd_two_mul (by omega) ?_
        rw [show 2 * (parallelSeat m a + k) =
          parallelSeat m a + 2 * k + parallelSeat m a by ring]
        exact hdvd
      · rw [ite_eq_right ha0, ite_eq_right hb0, Nat.add_right_comm]
        exact hdvd

/-- Every pair $i < j$ of players meets in exactly one round $k < 2m - 1$. -/
private lemma existsUnique_parallelPaired {m i j : ℕ} (hij : i < j) (hj : j < 2 * m) :
    ∃! k, k < 2 * m - 1 ∧ ParallelPaired m k i j := by
  have hM : 0 < 2 * m - 1 := by omega
  have hj0 : j ≠ 0 := by omega
  have hsi := parallelSeat_lt (m := m) (x := i) (by omega)
  have hsj := parallelSeat_lt hj
  unfold ParallelPaired
  by_cases hi0 : i = 0
  · simp only [ite_eq_left hi0]
    obtain ⟨k, hk, hdvd⟩ := exists_dvd_add hM (parallelSeat m j)
    exact ⟨k, ⟨hk, hdvd⟩, fun k' hk' => eq_of_dvd_add hk'.1 hk hk'.2 hdvd⟩
  · simp only [ite_eq_right hi0, ite_eq_right hj0]
    obtain ⟨k, hk, t, ht⟩ : ∃ k < 2 * m - 1, ∃ t,
        parallelSeat m i + parallelSeat m j + 2 * k = (2 * m - 1) * t := by
      by_cases hev : (parallelSeat m i + parallelSeat m j) % 2 = 0
      · by_cases h0 : parallelSeat m i + parallelSeat m j = 0
        · exact ⟨0, hM, 0, by omega⟩
        · exact ⟨2 * m - 1 - (parallelSeat m i + parallelSeat m j) / 2, by omega, 2, by omega⟩
      · by_cases hle : parallelSeat m i + parallelSeat m j ≤ 2 * m - 1
        · exact ⟨(2 * m - 1 - (parallelSeat m i + parallelSeat m j)) / 2, by omega, 1, by omega⟩
        · exact ⟨(3 * (2 * m - 1) - (parallelSeat m i + parallelSeat m j)) / 2, by omega, 3,
            by omega⟩
    exact ⟨k, ⟨hk, t, ht⟩, fun k' hk' =>
      eq_of_dvd_add_two_mul (by omega) hk'.1 hk hk'.2 ⟨t, ht⟩⟩

/-- **Section 8.5.7** of [golub2013matrix], the parallel ordering is a one-factorization of the
complete graph $K_{2m}$. For every $m$:

* each rotation set consists of pairs $(i, j)$ with $i < j$;
* two distinct pairs of one rotation set share no index, so the subproblems of one round do not
  conflict;
* each rotation set has exactly $m$ pairs;
* every pair $i < j$ of the $2m$ indices lies in exactly one of the $2m - 1$ rotation sets.

Hence the rotation sets partition the $m(2m - 1)$ off-diagonal index pairs $i < j$. -/
theorem parallelOrdering_spec (m : ℕ) :
    (∀ k, ∀ ij ∈ parallelOrdering m k, ij.1 < ij.2) ∧
    (∀ k, ∀ ij ∈ parallelOrdering m k, ∀ ij' ∈ parallelOrdering m k, ij ≠ ij' →
      ij.1 ≠ ij'.1 ∧ ij.1 ≠ ij'.2 ∧ ij.2 ≠ ij'.1 ∧ ij.2 ≠ ij'.2) ∧
    (∀ k, (parallelOrdering m k).card = m) ∧
    ∀ i j : Fin (2 * m), i < j → ∃! k, (i, j) ∈ parallelOrdering m k := by
  have hmem : ∀ k ij, ij ∈ parallelOrdering m k ↔ ij.1 < ij.2 ∧ ParallelPaired m k ij.1 ij.2 :=
    fun k ij => by simp only [parallelOrdering, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlt : ∀ k, ∀ ij ∈ parallelOrdering m k, ij.1 < ij.2 := fun k ij h => ((hmem k ij).1 h).1
  have hP : ∀ k, ∀ ij ∈ parallelOrdering m k,
      ParallelPaired m k ij.1 ij.2 ∧ ParallelPaired m k ij.2 ij.1 := fun k ij h =>
    ⟨((hmem k ij).1 h).2, parallelPaired_comm.1 ((hmem k ij).1 h).2⟩
  have key : ∀ (k : Fin (2 * m - 1)) (a b b' : Fin (2 * m)), a ≠ b → a ≠ b' →
      ParallelPaired m k a b → ParallelPaired m k a b' → b = b' := fun k a b b' h1 h2 h3 h4 =>
    Fin.ext (parallelPaired_unique a.2 b.2 b'.2 (fun h => h1 (Fin.ext h))
      (fun h => h2 (Fin.ext h)) h3 h4)
  have hdisj : ∀ k, ∀ ij ∈ parallelOrdering m k, ∀ ij' ∈ parallelOrdering m k, ij ≠ ij' →
      ij.1 ≠ ij'.1 ∧ ij.1 ≠ ij'.2 ∧ ij.2 ≠ ij'.1 ∧ ij.2 ≠ ij'.2 := by
    intro k ij h ij' h' hne
    obtain ⟨p1, p2⟩ := hP k ij h
    obtain ⟨q1, q2⟩ := hP k ij' h'
    have l := hlt k ij h
    have l' := hlt k ij' h'
    refine ⟨fun e => hne ?_, fun e => ?_, fun e => ?_, fun e => hne ?_⟩
    · rw [← e] at q1 l'
      exact Prod.ext e (key k ij.1 _ _ l.ne l'.ne p1 q1)
    · rw [← e] at q2 l'
      have e' := key k ij.1 _ _ l.ne l'.ne' p1 q2
      rw [← e'] at l'
      exact absurd l (lt_asymm l')
    · rw [← e] at q1 l'
      have e' := key k ij.2 _ _ l.ne' l'.ne p2 q1
      rw [← e'] at l'
      exact absurd l (lt_asymm l')
    · rw [← e] at q2 l'
      exact Prod.ext (key k ij.2 _ _ l.ne' l'.ne' p2 q2) e
  refine ⟨hlt, hdisj, fun k => ?_, fun i j hij => ?_⟩
  · -- a rotation set times `Bool` is in bijection with the players
    have hinj : ∀ x ∈ parallelOrdering m k ×ˢ (Finset.univ : Finset Bool),
        ∀ y ∈ parallelOrdering m k ×ˢ (Finset.univ : Finset Bool),
        (bif x.2 then x.1.1 else x.1.2) = (bif y.2 then y.1.1 else y.1.2) → x = y := by
      rintro ⟨ij, b⟩ hx ⟨ij', b'⟩ hy he
      rw [Finset.mem_product] at hx hy
      have hd := hdisj k ij hx.1 ij' hy.1
      cases b <;> cases b' <;> simp only [Bool.cond_true, Bool.cond_false] at he
      · rw [Classical.byContradiction fun hne => (hd hne).2.2.2 he]
      · have e : ij = ij' := Classical.byContradiction fun hne => (hd hne).2.2.1 he
        subst e
        exact absurd he (hlt k ij hx.1).ne'
      · have e : ij = ij' := Classical.byContradiction fun hne => (hd hne).2.1 he
        subst e
        exact absurd he (hlt k ij hx.1).ne
      · rw [Classical.byContradiction fun hne => (hd hne).1 he]
    have hsurj : ∀ a ∈ (Finset.univ : Finset (Fin (2 * m))),
        ∃ x, ∃ (_ : x ∈ parallelOrdering m k ×ˢ (Finset.univ : Finset Bool)),
          (bif x.2 then x.1.1 else x.1.2) = a := by
      intro a _
      obtain ⟨b, hb, hab, hp⟩ := exists_parallelPaired k.2 a.2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨((a, ⟨b, hb⟩), true),
          Finset.mem_product.2 ⟨(hmem _ _).2 ⟨Fin.lt_def.2 h, hp⟩,
            Finset.mem_univ _⟩, rfl⟩
      · exact ⟨((⟨b, hb⟩, a), false),
          Finset.mem_product.2 ⟨(hmem _ _).2 ⟨Fin.lt_def.2 h,
            parallelPaired_comm.1 hp⟩, Finset.mem_univ _⟩, rfl⟩
    have h := Finset.card_bij
      (fun (x : (Fin (2 * m) × Fin (2 * m)) × Bool) _ => bif x.2 then x.1.1 else x.1.2)
      (fun _ _ => Finset.mem_univ _) hinj hsurj
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, Fintype.card_fin] at h
    omega
  · obtain ⟨k, ⟨hk, hkP⟩, hku⟩ := existsUnique_parallelPaired (m := m)
      (Fin.lt_def.1 hij) j.2
    exact ⟨⟨k, hk⟩, (hmem _ _).2 ⟨hij, hkP⟩,
      fun k' hk' => Fin.ext (hku k' ⟨k'.2, ((hmem _ _).1 hk').2⟩)⟩

/-- **Section 8.5.7** of [golub2013matrix], the case $m = 4$. The seven rounds of the parallel
ordering for $8$ players are the rotation sets $\mathrm{rot.set}(1), \dots, \mathrm{rot.set}(7)$
of the source, with players numbered from $0$. -/
theorem parallelOrdering_four :
    parallelOrdering 4 ⟨0, by decide⟩ = {(0, 1), (2, 3), (4, 5), (6, 7)} ∧
    parallelOrdering 4 ⟨1, by decide⟩ = {(0, 3), (1, 5), (2, 7), (4, 6)} ∧
    parallelOrdering 4 ⟨2, by decide⟩ = {(0, 5), (3, 7), (1, 6), (2, 4)} ∧
    parallelOrdering 4 ⟨3, by decide⟩ = {(0, 7), (5, 6), (3, 4), (1, 2)} ∧
    parallelOrdering 4 ⟨4, by decide⟩ = {(0, 6), (4, 7), (2, 5), (1, 3)} ∧
    parallelOrdering 4 ⟨5, by decide⟩ = {(0, 4), (2, 6), (1, 7), (3, 5)} ∧
    parallelOrdering 4 ⟨6, by decide⟩ = {(0, 2), (1, 4), (3, 6), (5, 7)} := by
  decide

end GolubVanLoan.Chapter08
