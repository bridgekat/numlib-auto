/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Iterate
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.Subspace
import NumlibSurface.FongSaunders.Section04

/-!
# Fong and Saunders, Section 5: Table 5.1, the summary of monotonicity properties

This module formalizes Table 5.1 of [fong2012cg], which collects the monotonicity properties of CG
and MINRES on a symmetric positive definite system $Ax = b$ from $x_0 = 0$. The table has five rows:
$\|x_k\|$ increases, and $\|x^* - x_k\|$, $\|x^* - x_k\|_A$, $\|r_k\|$ and $\|r_k\| / \|x_k\|$
decrease. All five rows hold for MINRES; the first three hold for CG, and the table leaves the CG
entries of the last two rows blank ("not monotonic"). The structures `FongSaunders.MonotoneProfile`
and `FongSaunders.MINRESProfile` package the rows, and `FongSaunders.cg_profile`,
`FongSaunders.minres_profile` and `FongSaunders.cr_profile` prove the monotone entries from Sections
2 and 3. The two blank entries are proved by explicit counterexamples on diagonal matrices.

The module also formalizes the indefinite example (4.2) of Section 4.2, $$A = \begin{bmatrix} 2 & 1
& 1 \\ 1 & 0 & 1 \\ 1 & 1 & 2 \end{bmatrix}, \qquad b = \begin{bmatrix} 0 \\ 1 \\ 1 \end{bmatrix},$$
because it has the same form and shows that the MINRES column of the table needs $A \succ 0$. On
this nonsingular, symmetric, indefinite system both $\|x_k\|$ and $\|r_k\| / \|x_k\|$ fail to be
monotone for MINRES.

## Main definitions

* Table 5.1, `FongSaunders.MonotoneProfile`: rows 1–3 of the table for a sequence of iterates.
* Table 5.1, `FongSaunders.MINRESProfile`: all five rows of the table for a sequence of iterates.

## Main results

* Table 5.1, `FongSaunders.cg_profile`: the CG column, rows 1–3.
* Table 5.1, `FongSaunders.minres_profile`: the MINRES column, all five rows.
* Table 5.1, `FongSaunders.cr_profile`: the MINRES column for the CR iterates.
* Table 5.1, `FongSaunders.cg_norm_residual_not_antitone`: a symmetric positive definite system on
  which $\|r_k^C\|$ is not monotone.
* Table 5.1, `FongSaunders.cg_backwardError_not_antitoneOn`: a symmetric positive definite system on
  which $\|r_k^C\| / \|x_k^C\|$ is not monotone for $k \ge 1$.
* Section 4.2, `FongSaunders.indefinite_witness`: the matrix of (4.2) is symmetric, nonsingular and
  indefinite.
* Section 4.2, `FongSaunders.minres_norm_iterate_not_monotone`: on the system (4.2), $\|x_k\|$ is
  not monotone for MINRES.
* Section 4.2, `FongSaunders.minres_backwardError_not_antitoneOn`: on the system (4.2),
  $\|r_k\| / \|x_k\|$ is not monotone for MINRES.

## Implementation notes

* The import `Mathlib.Algebra.Order.Star.Real` provides the instance `StarOrderedRing ℝ`, which
  `Matrix.posDef_diagonal_iff` needs in the counterexamples.
* The matrix of (4.2) is nonsingular, so the MINRES iterate is unique at every step. The two results
  on (4.2) therefore hold for every sequence of MINRES iterates.

## Deviations from the source

* **The blank CG entries of Table 5.1** (reading). A blank entry is read as the existence of a
  symmetric positive definite system on which the row fails to be monotone. See
  `FongSaunders.cg_norm_residual_not_antitone` and `FongSaunders.cg_backwardError_not_antitoneOn`.
* **The row $\|r_k\| / \|x_k\|$ of Table 5.1** (reading). The ratio is undefined at $k = 0$ because
  $x_0 = 0$; the row is stated for $k \ge 1$. See `FongSaunders.MINRESProfile`.

## Not formalized

* **Table 5.2.** It states results of other papers.
* **The discussion of LSQR and LSMR in Section 5.** It states results of other papers.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

/-! ### The rows of Table 5.1 -/

/-- **Table 5.1** of [fong2012cg], rows 1–3. Let $A \in \mathbb{R}^{n \times n}$,
$x^* \in \mathbb{R}^n$, and let $(x_k)$ be a sequence in $\mathbb{R}^n$. The sequence has the
**monotone profile** of rows 1–3 if the norm of the iterate increases and the error and the
energy norm of the error decrease: for $k \le l$, $$\|x_k\| \le \|x_l\|, \qquad \|x^* - x_l\|
\le \|x^* - x_k\|, \qquad \|x^* - x_l\|_A \le \|x^* - x_k\|_A.$$
-/
structure MonotoneProfile (A : Matrix (Fin n) (Fin n) ℝ) (xstar : Vec n) (x : ℕ → Vec n) :
    Prop where
  /-- The norm of the iterate increases monotonically: $\|x_k\| \le \|x_l\|$ for $k \le l$. For CG
  this is Theorem 2.1 of [steihaug1983conjugate]; for MINRES it is Theorem 2.3. -/
  norm_iterate : Monotone fun k => ‖x k‖
  /-- The error decreases monotonically: $\|x^* - x_l\| \le \|x^* - x_k\|$ for $k \le l$. For CG
  this is Theorem 4:3 of [hestenes1952methods]; for MINRES it is Theorem 2.4. -/
  norm_error : Antitone fun k => ‖xstar - x k‖
  /-- The energy norm of the error decreases monotonically: $\|x^* - x_l\|_A \le \|x^* - x_k\|_A$
  for $k \le l$. For CG this is Theorem 6:3 of [hestenes1952methods]; for MINRES it is Theorem
  2.5. -/
  energyNorm_error : Antitone fun k => energyNorm A (xstar - x k)

/-- **Table 5.1** of [fong2012cg], all five rows. Let $A \in \mathbb{R}^{n \times n}$,
$b, x^* \in \mathbb{R}^n$, and let $(x_k)$ be a sequence in $\mathbb{R}^n$ with residuals
$r_k = b - A x_k$. The sequence has the **MINRES profile** if it has the monotone profile of
rows 1–3 (`FongSaunders.MonotoneProfile`), the residual norm decreases, and the ratio
$\|r_k\| / \|x_k\|$ decreases from step $1$ on: $$\|r_l\| \le \|r_k\| \quad \text{for } k \le l,
\qquad \frac{\|r_l\|}{\|x_l\|} \le \frac{\|r_k\|}{\|x_k\|} \quad \text{for } 1 \le k \le l.$$

**Reading.** The paper's ratio $\|r_0\| / \|x_0\|$ is undefined, because $x_0 = 0$. In Lean it
is $\|b\| / 0 = 0$, which is below every later value, so a decrease over all $k$ would be false.
The last row is therefore stated for $k \ge 1$. -/
structure MINRESProfile (A : Matrix (Fin n) (Fin n) ℝ) (b xstar : Vec n) (x : ℕ → Vec n) : Prop
    extends MonotoneProfile A xstar x where
  /-- The residual norm decreases monotonically: $\|b - A x_l\| \le \|b - A x_k\|$ for $k \le l$.
  This is Theorem 7:2 of [hestenes1952methods]. -/
  norm_residual : Antitone fun k => ‖b - A ⬝ x k‖
  /-- The ratio $\|r_k\| / \|x_k\|$ decreases monotonically for $1 \le k \le l$; this is the row of
  Theorem 3.1. At $k = 0$ the ratio is $\|b\| / 0$, so the row starts at $k = 1$. -/
  backwardError : AntitoneOn (fun k => ‖b - A ⬝ x k‖ / ‖x k‖) (Set.Ici 1)

/-! ### The monotone entries of Table 5.1 -/

/-- **Table 5.1** of [fong2012cg], the CG column. Let $A \in \mathbb{R}^{n \times n}$ be positive
definite, and let $Ax^* = b$. Then the CG iterates $x_k^C$ have the monotone profile of rows
1–3: $\|x_k^C\|$ increases, and $\|x^* - x_k^C\|$ and $\|x^* - x_k^C\|_A$ decrease
monotonically. -/
theorem cg_profile (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    MonotoneProfile A xstar fun k => (cg A b k).x where
  norm_iterate := by
    simp only [cg_x]
    exact CG.norm_iterate_monotone b (isSymmetricCoercive_of_posDef hA)
  norm_error := by
    simp only [cg_x]
    exact CG.norm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar
  energyNorm_error := by
    simp only [energyNorm_eq, cg_x]
    exact CG.energyNorm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar

/-- **Table 5.1** of [fong2012cg], the MINRES column. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, let $b \neq 0$ and $Ax^* = b$, and let $(x_k)$ be a sequence such that each
$x_k$ is a MINRES iterate at step $k$. Then $(x_k)$ has the MINRES profile of all five rows:
$\|x_k\|$ increases; $\|x^* - x_k\|$, $\|x^* - x_k\|_A$ and $\|r_k\|$ decrease; and
$\|r_k\| / \|x_k\|$ decreases for $k \ge 1$. -/
theorem minres_profile (hA : A.PosDef) (hb : b ≠ 0) {xstar : Vec n} (hstar : A ⬝ xstar = b)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) : MINRESProfile A b xstar x where
  norm_iterate := theorem_2_3_minres hA hx
  norm_error := theorem_2_4_minres hA hstar hx
  energyNorm_error := theorem_2_5_minres_antitone hA hstar hx
  norm_residual :=
    Krylov.IsMinResidualIterate.norm_residual_antitone fun k => isMINRESIterate_iff.1 (hx k)
  backwardError :=
    Krylov.IsMinResidualIterate.norm_residual_div_norm_antitoneOn
      (isSymmetricCoercive_of_posDef hA) (fun k => isMINRESIterate_iff.1 (hx k)) hb

/-- **Table 5.1** of [fong2012cg], the MINRES column for CR. Let $A \in \mathbb{R}^{n \times n}$ be
positive definite, and let $b \neq 0$ and $Ax^* = b$. Then the CR iterates $x_k$ have the MINRES
profile of all five rows.

The CR iterates are the MINRES iterates (`FongSaunders.isMINRESIterate_iff_eq_cr`). -/
theorem cr_profile (hA : A.PosDef) (hb : b ≠ 0) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    MINRESProfile A b xstar fun k => (cr A b k).x :=
  minres_profile hA hb hstar fun k => cr_isMINRESIterate hA k

/-!
### The two blank entries of the CG column

Table 5.1 leaves the CG entries for $\|r_k\|$ and $\|r_k\| / \|x_k\|$ blank ("not monotonic"). Read
faithfully, a blank entry asserts that there is a symmetric positive definite system on which the
quantity fails to be monotone. Both witnesses below are diagonal.
-/

section Counterexamples

open EuclideanSpace

/-- The inner product in coordinates: $u^T v = \sum_i u_i v_i$. -/
private theorem inner_eq (u v : Vec n) :
    ⟪u, v⟫_ℝ = ∑ i, WithLp.ofLp u i * WithLp.ofLp v i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The matrix $A = \operatorname{diag}(1, 9)$ of the $2 \times 2$ counterexample. -/
private def A2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 9]

/-- The vector $b = (3, 1)^T$ of the $2 \times 2$ counterexample. -/
private def b2 : Vec 2 := !₂[3, 1]

private theorem posDef_A2 : A2.PosDef := by
  rw [A2, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

private theorem rho2_zero : (cg A2 b2 0).ρ = 10 := by
  simp only [cg_zero, cgInit, real_norm_sq_eq, b2, Fin.sum_univ_two, cons_val_zero,
    cons_val_one]
  norm_num

private theorem rho2_one : (cg A2 b2 1).ρ = 160 / 9 := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_sub,
    WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b2, A2,
    Fin.sum_univ_two, mulVec_diagonal, cons_val_zero, cons_val_one]
  norm_num

/-- **Table 5.1** of [fong2012cg], the CG entry for $\|r_k\|$. There are a positive definite
$A \in \mathbb{R}^{2 \times 2}$ and $b \in \mathbb{R}^2$ such that the CG residual norm
$\|r_k^C\|$ is not monotonically decreasing.

**Reading.** The table leaves this entry blank, which is read as the existence of such a system.

The witness is $A = \operatorname{diag}(1, 9)$ and $b = (3, 1)^T$, for which $\|r_0^C\|^2 = 10$
and $\|r_1^C\|^2 = 160/9 > 10$. -/
theorem cg_norm_residual_not_antitone :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Vec 2), A.PosDef ∧
      ¬ Antitone fun k => ‖(cg A b k).r‖ := by
  refine ⟨A2, b2, posDef_A2, fun h => ?_⟩
  have h0 : ‖(cg A2 b2 0).r‖ ^ 2 = 10 := by rw [← cg_rho, rho2_zero]
  have h1 : ‖(cg A2 b2 1).r‖ ^ 2 = 160 / 9 := by rw [← cg_rho, rho2_one]
  have hle := h (Nat.zero_le 1)
  simp only at hle
  nlinarith [norm_nonneg (cg A2 b2 0).r, norm_nonneg (cg A2 b2 1).r]

/-- The matrix $A = \operatorname{diag}(1, 13, 16)$ of the $3 \times 3$ counterexample. -/
private def A3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 13, 16]

/-- The vector $b = (1, 5, 1)^T$ of the $3 \times 3$ counterexample. -/
private def b3 : Vec 3 := !₂[1, 5, 1]

private theorem posDef_A3 : A3.PosDef := by
  rw [A3, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

private theorem cg3_one_x : WithLp.ofLp (cg A3 b3 1).x = ![3 / 38, 15 / 38, 3 / 38] := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_add,
    WithLp.ofLp_sub, WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, b3, A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  funext i
  fin_cases i <;> norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons]

private theorem cg3_one_r : WithLp.ofLp (cg A3 b3 1).r = ![35 / 38, -5 / 38, -5 / 19] := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_sub,
    WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b3, A3,
    Fin.sum_univ_three,
    mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  funext i
  fin_cases i <;> norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons]

private theorem cg3_one_p :
    WithLp.ofLp (cg A3 b3 1).p = ![345 / 361, 15 / 361, -165 / 722] := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_add, WithLp.ofLp_sub,
    WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    b3, A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  funext i
  fin_cases i <;>
    norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons, vecHead, vecTail]

private theorem cg3_one_rho : (cg A3 b3 1).ρ = 675 / 722 := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_sub,
    WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b3, A3,
    Fin.sum_univ_three,
    mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  norm_num

private theorem cg3_two : cg A3 b3 2 = cgStep A3 (cg A3 b3 1) := cg_succ 1

private theorem cg3_two_x : WithLp.ofLp (cg A3 b3 2).x = ![7 / 12, 5 / 12, -1 / 24] := by
  rw [cg3_two]
  simp only [cgStep, inner_eq, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin,
    cg3_one_x, cg3_one_p, cg3_one_rho]
  simp only [A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_zero, cons_val_one, cons_val_two,
    tail_cons, head_cons]
  funext i
  fin_cases i <;>
    norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons, vecHead, vecTail]

private theorem cg3_two_r : WithLp.ofLp (cg A3 b3 2).r = ![5 / 12, -5 / 12, 5 / 3] := by
  rw [cg3_two]
  simp only [cgStep, inner_eq, WithLp.ofLp_sub, WithLp.ofLp_smul, Matrix.ofLp_toEuclideanLin,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cg3_one_r, cg3_one_p, cg3_one_rho]
  simp only [A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_zero, cons_val_one, cons_val_two,
    tail_cons, head_cons]
  funext i
  fin_cases i <;>
    norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons, vecHead, vecTail]

/-- **Table 5.1** of [fong2012cg], the CG entry for $\|r_k\| / \|x_k\|$. There are $n$, a positive
definite $A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$ such that the ratio
$\|r_k^C\| / \|x_k^C\|$ is not monotonically decreasing on $k \ge 1$.

**Reading.** The table leaves this entry blank, which is read as the existence of such a system.
The ratio is considered for $k \ge 1$, as in the MINRES column.

The witness is $A = \operatorname{diag}(1, 13, 16)$ and $b = (1, 5, 1)^T$, for which $(\|r_1^C\|
/ \|x_1^C\|)^2 = 50/9 < 200/33 = (\|r_2^C\| / \|x_2^C\|)^2$. No $2 \times 2$ witness exists: CG
on a system of order $2$ terminates with $r_2^C = 0$, so the ratio is $0$ from $k = 2$ on. -/
theorem cg_backwardError_not_antitoneOn :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n), A.PosDef ∧
      ¬ AntitoneOn (fun k => ‖(cg A b k).r‖ / ‖(cg A b k).x‖) (Set.Ici 1) := by
  refine ⟨3, A3, b3, posDef_A3, fun h => ?_⟩
  have hx1 : ‖(cg A3 b3 1).x‖ ^ 2 = 243 / 1444 := by
    rw [real_norm_sq_eq, cg3_one_x]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hr1 : ‖(cg A3 b3 1).r‖ ^ 2 = 675 / 722 := by
    rw [real_norm_sq_eq, cg3_one_r]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hx2 : ‖(cg A3 b3 2).x‖ ^ 2 = 33 / 64 := by
    rw [real_norm_sq_eq, cg3_two_x]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hr2 : ‖(cg A3 b3 2).r‖ ^ 2 = 25 / 8 := by
    rw [real_norm_sq_eq, cg3_two_r]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hx1p : 0 < ‖(cg A3 b3 1).x‖ := by nlinarith [norm_nonneg (cg A3 b3 1).x]
  have hx2p : 0 < ‖(cg A3 b3 2).x‖ := by nlinarith [norm_nonneg (cg A3 b3 2).x]
  have hkey : ‖(cg A3 b3 1).r‖ * ‖(cg A3 b3 2).x‖ < ‖(cg A3 b3 2).r‖ * ‖(cg A3 b3 1).x‖ := by
    have hsq : (‖(cg A3 b3 1).r‖ * ‖(cg A3 b3 2).x‖) ^ 2
        < (‖(cg A3 b3 2).r‖ * ‖(cg A3 b3 1).x‖) ^ 2 := by
      rw [mul_pow, mul_pow, hr1, hx2, hr2, hx1]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hle := h (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by norm_num)) (by norm_num : (1 : ℕ) ≤ 2)
  simp only at hle
  rw [div_le_div_iff₀ hx2p hx1p] at hle
  linarith

end Counterexamples

/-!
### The indefinite example (4.2)

Section 4.2 of [fong2012cg] gives the nonsingular, symmetric, indefinite system $$A =
\begin{bmatrix} 2 & 1 & 1 \\ 1 & 0 & 1 \\ 1 & 1 & 2 \end{bmatrix}, \qquad b = \begin{bmatrix} 0 \\ 1
\\ 1 \end{bmatrix},$$ on which MINRES gives solution norms that are not monotone, and hence backward
errors that are not monotone (Figure 4.6). Theorems 2.3 and 3.1 assume $A \succ 0$, and this example
shows that the assumption cannot be dropped.

The matrix is nonsingular, with $\det A = -2$. So the MINRES iterate is unique at every step
(`Krylov.existsUnique_isMinResidualIterate_of_injective`), and the two theorems below hold for every
sequence of MINRES iterates, without a positive definiteness assumption.
-/

section Indefinite

open EuclideanSpace

/-- The matrix $A$ of the example (4.2). -/
private def A4 : Matrix (Fin 3) (Fin 3) ℝ := !![2, 1, 1; 1, 0, 1; 1, 1, 2]

/-- The right-hand side $b = (0, 1, 1)^T$ of the example (4.2). -/
private def b4 : Vec 3 := !₂[0, 1, 1]

/-- The first MINRES iterate $x_1 = \frac{2}{7} b = (0, 2/7, 2/7)^T$ of the example (4.2). -/
private noncomputable def x4one : Vec 3 := !₂[0, 2 / 7, 2 / 7]

/-- The second MINRES iterate $x_2 = \frac{2}{19} b + \frac{1}{19} Ab = (2/19, 3/19, 5/19)^T$ of the
example (4.2). -/
private noncomputable def x4two : Vec 3 := !₂[2 / 19, 3 / 19, 5 / 19]

/-- The identity matrix maps every vector to itself: $Iv = v$. -/
private theorem one_mulVecE (v : Vec n) : (1 : Matrix (Fin n) (Fin n) ℝ) ⬝ v = v := by
  change Matrix.toEuclideanLin 1 v = v
  rw [Matrix.toEuclideanLin_one]
  rfl

private theorem isSymm_A4 : A4.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A4]

private theorem det_A4 : A4.det = -2 := by
  norm_num [A4, Matrix.det_fin_three, cons_val_two, tail_cons, head_cons]

private theorem isUnit_det_A4 : IsUnit A4.det := by
  rw [det_A4]
  exact isUnit_iff_ne_zero.2 (by norm_num)

private theorem injective_A4 : Function.Injective (Matrix.toEuclideanLin A4) := by
  have h : Function.Injective A4.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det A4).2 isUnit_det_A4)
  intro u v huv
  refine WithLp.ofLp_injective 2 (h ?_)
  rw [← Matrix.ofLp_toEuclideanLin, ← Matrix.ofLp_toEuclideanLin]
  exact congrArg WithLp.ofLp huv

/-- In the example (4.2), $Ab = (2, 1, 3)^T$. -/
private theorem ofLp_A4_b4 : WithLp.ofLp (A4 ⬝ b4) = ![2, 1, 3] := by
  rw [Matrix.ofLp_toEuclideanLin]
  funext i
  fin_cases i <;>
    norm_num [A4, b4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]

/-- In the example (4.2), $A^2 b = (8, 5, 9)^T$. -/
private theorem ofLp_A4_A4_b4 : WithLp.ofLp (A4 ⬝ (A4 ⬝ b4)) = ![8, 5, 9] := by
  rw [Matrix.ofLp_toEuclideanLin, ofLp_A4_b4]
  funext i
  fin_cases i <;>
    norm_num [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]

/-- In the example (4.2), the residual of $x_1$ is $r_1 = (-4/7, 5/7, 1/7)^T$. -/
private theorem ofLp_res_one : WithLp.ofLp (b4 - A4 ⬝ x4one) = ![-4 / 7, 5 / 7, 1 / 7] := by
  rw [WithLp.ofLp_sub, Matrix.ofLp_toEuclideanLin]
  funext i
  fin_cases i <;>
    norm_num [A4, b4, x4one, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two,
      tail_cons, head_cons]

/-- In the example (4.2), the residual of $x_2$ is $r_2 = (-12/19, 12/19, 4/19)^T$. -/
private theorem ofLp_res_two : WithLp.ofLp (b4 - A4 ⬝ x4two) = ![-12 / 19, 12 / 19, 4 / 19] := by
  rw [WithLp.ofLp_sub, Matrix.ofLp_toEuclideanLin]
  funext i
  fin_cases i <;>
    norm_num [A4, b4, x4two, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two,
      tail_cons, head_cons]

/-- If $r^T A (A^i b) = 0$ for every $i < m$, then $r^T A z = 0$ for every
$z \in \mathcal{K}_m(A, b)$. -/
private theorem inner_mulVecE_eq_zero_of_generators {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {b r : Vec n} (h : ∀ i < m, ⟪r, A ⬝ ((A ^ i) ⬝ b)⟫_ℝ = 0) :
    ∀ z ∈ krylov A b m, ⟪r, A ⬝ z⟫_ℝ = 0 := by
  intro z hz
  simp only [krylov] at hz
  induction hz using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i i.2
  | zero => rw [mulVecE_zero, inner_zero_right]
  | add u v _ _ hu hv => rw [mulVecE_add, inner_add_right, hu, hv, add_zero]
  | smul c u _ hu => rw [mulVecE_smul, real_inner_smul_right, hu, mul_zero]

/-- A point $x \in \mathcal{K}_k(A, b)$ whose residual $b - Ax$ is orthogonal to
$A \mathcal{K}_k(A, b)$ is a MINRES iterate at step $k$. -/
private theorem isMINRESIterate_of_orth {k : ℕ} {x : Vec n} (hmem : x ∈ krylov A b k)
    (horth : ∀ z ∈ krylov A b k, ⟪b - A ⬝ x, A ⬝ z⟫_ℝ = 0) : IsMINRESIterate A b k x := by
  refine ⟨hmem, fun y hy => ?_⟩
  have hres : b - A ⬝ y = (b - A ⬝ x) - A ⬝ (y - x) := by rw [mulVecE_sub]; abel
  have h0 : ⟪b - A ⬝ x, A ⬝ (y - x)⟫_ℝ = 0 := horth _ (Submodule.sub_mem _ hy hmem)
  have hsq : ‖b - A ⬝ y‖ ^ 2 = ‖b - A ⬝ x‖ ^ 2 + ‖A ⬝ (y - x)‖ ^ 2 := by
    rw [hres, @norm_sub_sq_real, h0]
    ring
  nlinarith [norm_nonneg (b - A ⬝ y), norm_nonneg (b - A ⬝ x), sq_nonneg ‖A ⬝ (y - x)‖]

private theorem isMINRESIterate_x4one : IsMINRESIterate A4 b4 1 x4one := by
  refine isMINRESIterate_of_orth ?_ (inner_mulVecE_eq_zero_of_generators ?_)
  · have hb : b4 ∈ krylov A4 b4 1 := by
      simp only [krylov]
      exact Submodule.subset_span ⟨0, by simp [one_mulVecE]⟩
    have hx : x4one = (2 / 7 : ℝ) • b4 := by
      refine WithLp.ofLp_injective 2 ?_
      funext i
      fin_cases i <;> norm_num [x4one, b4]
    rw [hx]
    exact Submodule.smul_mem _ _ hb
  · intro i hi
    interval_cases i
    rw [pow_zero, one_mulVecE, inner_eq, ofLp_res_one, ofLp_A4_b4]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]

private theorem isMINRESIterate_x4two : IsMINRESIterate A4 b4 2 x4two := by
  refine isMINRESIterate_of_orth ?_ (inner_mulVecE_eq_zero_of_generators ?_)
  · have hb : b4 ∈ krylov A4 b4 2 := by
      simp only [krylov]
      exact Submodule.subset_span ⟨0, by simp [one_mulVecE]⟩
    have hAb : A4 ⬝ b4 ∈ krylov A4 b4 2 := by
      simp only [krylov]
      exact Submodule.subset_span ⟨1, by simp⟩
    have hx : x4two = (2 / 19 : ℝ) • b4 + (1 / 19 : ℝ) • (A4 ⬝ b4) := by
      refine WithLp.ofLp_injective 2 ?_
      rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, ofLp_A4_b4]
      funext i
      fin_cases i <;> norm_num [x4two, b4]
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hAb)
  · intro i hi
    interval_cases i
    · rw [pow_zero, one_mulVecE, inner_eq, ofLp_res_two, ofLp_A4_b4]
      norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
    · rw [pow_one, inner_eq, ofLp_res_two, ofLp_A4_A4_b4]
      norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]

/-- In the example (4.2), any two MINRES iterates at the same step are equal, because $A$ is
nonsingular. -/
private theorem eq_of_isMINRESIterate {k : ℕ} {x y : Vec 3} (hx : IsMINRESIterate A4 b4 k x)
    (hy : IsMINRESIterate A4 b4 k y) : x = y := by
  obtain ⟨z, _, hz⟩ := Krylov.existsUnique_isMinResidualIterate_of_injective injective_A4 b4 0 k
  rw [hz x (isMINRESIterate_iff.1 hx), hz y (isMINRESIterate_iff.1 hy)]

private theorem norm_sq_x4one : ‖x4one‖ ^ 2 = 8 / 49 := by
  rw [real_norm_sq_eq]
  simp [x4one, Fin.sum_univ_three]
  norm_num

private theorem norm_sq_x4two : ‖x4two‖ ^ 2 = 2 / 19 := by
  rw [real_norm_sq_eq]
  simp [x4two, Fin.sum_univ_three]
  norm_num

private theorem norm_sq_res_one : ‖b4 - A4 ⬝ x4one‖ ^ 2 = 6 / 7 := by
  rw [real_norm_sq_eq, ofLp_res_one]
  simp [Fin.sum_univ_three]
  norm_num

private theorem norm_sq_res_two : ‖b4 - A4 ⬝ x4two‖ ^ 2 = 16 / 19 := by
  rw [real_norm_sq_eq, ofLp_res_two]
  simp [Fin.sum_univ_three]
  norm_num

/-- **Section 4.2** of [fong2012cg], the example (4.2) is indefinite. There are a matrix
$A \in \mathbb{R}^{3 \times 3}$ and vectors $u, w \in \mathbb{R}^3$ such that $A$ is symmetric
and nonsingular, $u^T A u > 0$ and $w^T A w < 0$.

The witness is the matrix $A$ of (4.2), with $u = e_1$, where $u^T A u = 2$, and
$w = (1, -2, 1)^T$, where $w^T A w = -2$. So the assumption $A \succ 0$ of Theorems 2.3 and 3.1
fails for this matrix, while MINRES is defined at every step because $A$ is nonsingular. -/
theorem indefinite_witness :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (u w : Vec 3), A.IsSymm ∧ IsUnit A.det ∧
      0 < ⟪u, A ⬝ u⟫_ℝ ∧ ⟪w, A ⬝ w⟫_ℝ < 0 := by
  refine ⟨A4, !₂[1, 0, 0], !₂[1, -2, 1], isSymm_A4, isUnit_det_A4, ?_, ?_⟩
  · rw [inner_eq, Matrix.ofLp_toEuclideanLin]
    norm_num [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]
  · rw [inner_eq, Matrix.ofLp_toEuclideanLin]
    norm_num [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]

/-- **Section 4.2** of [fong2012cg], the example (4.2), solution norms. There are a symmetric
nonsingular $A \in \mathbb{R}^{3 \times 3}$ and $b \in \mathbb{R}^3$ such that for every
sequence $(x_k)$ in which each $x_k$ is a MINRES iterate at step $k$, the norms $\|x_k\|$ are
not monotonically increasing.

The witness is the system (4.2). Its MINRES iterates are $x_1 = (0, 2/7, 2/7)^T$ and
$x_2 = (2/19, 3/19, 5/19)^T$, with $\|x_1\|^2 = 8/49 > 2/19 = \|x_2\|^2$. So Theorem 2.3 fails
when the assumption $A \succ 0$ is dropped. -/
theorem minres_norm_iterate_not_monotone :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3), A.IsSymm ∧ IsUnit A.det ∧
      ∀ x : ℕ → Vec 3, (∀ k, IsMINRESIterate A b k (x k)) → ¬ Monotone fun k => ‖x k‖ := by
  refine ⟨A4, b4, isSymm_A4, isUnit_det_A4, fun x hx hmono => ?_⟩
  have h1 : x 1 = x4one := eq_of_isMINRESIterate (hx 1) isMINRESIterate_x4one
  have h2 : x 2 = x4two := eq_of_isMINRESIterate (hx 2) isMINRESIterate_x4two
  have hle := hmono (by norm_num : (1 : ℕ) ≤ 2)
  simp only [h1, h2] at hle
  nlinarith [norm_sq_x4one, norm_sq_x4two, norm_nonneg x4one, norm_nonneg x4two]

/-- **Section 4.2** of [fong2012cg], the example (4.2), backward errors. There are a symmetric
nonsingular $A \in \mathbb{R}^{3 \times 3}$ and $b \in \mathbb{R}^3$ such that for every
sequence $(x_k)$ in which each $x_k$ is a MINRES iterate at step $k$, the ratios
$\|r_k\| / \|x_k\|$ with $r_k = b - A x_k$ are not monotonically decreasing on $k \ge 1$.

The witness is the system (4.2), with $(\|r_1\| / \|x_1\|)^2 = 21/4 < 8 = (\|r_2\| /
\|x_2\|)^2$. So Theorem 3.1 also fails when the assumption $A \succ 0$ is dropped. This is the
content of Figure 4.6. -/
theorem minres_backwardError_not_antitoneOn :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3), A.IsSymm ∧ IsUnit A.det ∧
      ∀ x : ℕ → Vec 3, (∀ k, IsMINRESIterate A b k (x k)) →
        ¬ AntitoneOn (fun k => ‖b - A ⬝ x k‖ / ‖x k‖) (Set.Ici 1) := by
  refine ⟨A4, b4, isSymm_A4, isUnit_det_A4, fun x hx hanti => ?_⟩
  have h1 : x 1 = x4one := eq_of_isMINRESIterate (hx 1) isMINRESIterate_x4one
  have h2 : x 2 = x4two := eq_of_isMINRESIterate (hx 2) isMINRESIterate_x4two
  have hx1p : 0 < ‖x4one‖ := by nlinarith [norm_sq_x4one, norm_nonneg x4one]
  have hx2p : 0 < ‖x4two‖ := by nlinarith [norm_sq_x4two, norm_nonneg x4two]
  have hle := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by norm_num)) (by norm_num : (1:ℕ) ≤ 2)
  simp only [h1, h2] at hle
  rw [div_le_div_iff₀ hx2p hx1p] at hle
  have hkey : ‖b4 - A4 ⬝ x4one‖ * ‖x4two‖ < ‖b4 - A4 ⬝ x4two‖ * ‖x4one‖ := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    rw [mul_pow, mul_pow, norm_sq_res_one, norm_sq_x4two, norm_sq_res_two, norm_sq_x4one]
    norm_num
  linarith

end Indefinite

end FongSaunders
