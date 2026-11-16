/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.RayleighQuotientIteration
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section04

/-!
# Golub and Van Loan, Section 7.5: The practical QR algorithm

This module formalizes §7.5 of [golub2013matrix], the practical QR algorithm, which computes the
real Schur form of $A \in \mathbb{R}^{n \times n}$. One step of the shifted QR iteration on an upper
Hessenberg $H$ factors $H - \mu I = UR$ and sets $H_+ = RU + \mu I = U^T H U$ (7.5.3). The module
proves the rate of convergence of the subdiagonal entries for a fixed shift (§7.5.2), the deflation
of the last row by an exact eigenvalue as shift (Theorem 7.5.1), and the local quadratic convergence
of the single-shift iteration (§7.5.3). For the double shift of §7.5.4, with the eigenvalues
$a_1, a_2$ of the trailing $2 \times 2$ block, two steps give $H_2 = (U_1 U_2)^H H (U_1 U_2)$ with
$(U_1 U_2)(R_2 R_1) = M = (H - a_1 I)(H - a_2 I)$, and $M = H^2 - sH + tI$ is real, with
$s = a_1 + a_2$ and $t = a_1 a_2$ ((7.5.5)–(7.5.8)).

The Francis QR step (Algorithm 7.5.1, §7.5.5) computes $H' = Z^T H Z$ in real arithmetic. It starts
from the first column of $M$, which has only three nonzero entries, and chases a bulge down the
matrix with $3 \times 3$ Householder reflectors. The module proves that the exact Algorithm 7.5.1
gives an upper Hessenberg $H'$ with $Z^T M$ upper triangular, and that $H'$ equals the explicit
double-shift step up to a $\pm 1$ diagonal similarity. The QR algorithm (Algorithm 7.5.2, §7.5.6)
reduces $A$ to Hessenberg form, then repeats deflation and Francis steps on the unreduced diagonal
block, and at the end triangularizes the $2 \times 2$ diagonal blocks with real eigenvalues. In
exact arithmetic its output is the real Schur form of a perturbation $A + E$, where $E$ comes from
the deflations. The proofs specialize `Numlib.Eigen.QRAlgorithm`,
`Numlib.Eigen.RayleighQuotientIteration` and `Numlib.LinearAlgebra.Matrix.UnreducedHessenberg`, and
the programs use the Householder and Givens helpers of §5.1.

## Main definitions

* Algorithm 7.5.1, `GolubVanLoan.Chapter07.algorithm_7_5_1`: the Francis QR step on a window of
  consecutive indices, which returns the new matrix and the Householder data of $Z$.
* Algorithm 7.5.1, `GolubVanLoan.Chapter07.IsFrancisStepOn`: $Z$ performs a Francis step on the
  diagonal block $H_{22}$ of a window.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.triangularize2x2`: the upper triangularization of a
  $2 \times 2$ diagonal block with real eigenvalues by a Givens rotation.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.IsQRDeflation`: the deflation, which sets the small
  subdiagonal entries to zero.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.IsQRPass`: one pass of the loop, a deflation followed by
  a Francis step on the unreduced block.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.algorithm_7_5_2`: the QR algorithm.

## Main results

* (7.5.3), `GolubVanLoan.Chapter07.equation_7_5_3`: if $H - \mu I = UR$ with $U$ orthogonal, then
  $RU + \mu I = U^T H U$.
* §7.5.2, `GolubVanLoan.Chapter07.shiftedQr_rate`: for a fixed shift $\mu$, the subdiagonal entry
  $(p+1, p)$ of $H_k$ is at most $C (r / |\lambda_p - \mu|)^k$ for every
  $r > |\lambda_{p+1} - \mu|$.
* Theorem 7.5.1, `GolubVanLoan.Chapter07.theorem_7_5_1`: if $\mu$ is an eigenvalue of an unreduced
  $H$, the last row of $RU + \mu I$ is $\mu e_n^T$.
* §7.5.3, `GolubVanLoan.Chapter07.single_shift_quadratic`: near an algebraically simple real
  eigenvalue, one single-shift step makes $|h_{n,n-1}|$ at most a constant times its square.
* (7.5.6)–(7.5.7), `GolubVanLoan.Chapter07.equation_7_5_7`: two shifted steps give
  $(U_1 U_2)(R_2 R_1) = (H - a_1 I)(H - a_2 I)$ and $H_2 = (U_1 U_2)^H H (U_1 U_2)$.
* (7.5.5) and (7.5.8), `GolubVanLoan.Chapter07.equation_7_5_8`: $a_1 + a_2$ and $a_1 a_2$ are the
  trace and the determinant of the trailing block, and $M = H^2 - sH + tI$ is real.
* §7.5.4, `GolubVanLoan.Chapter07.double_shift_real`: for real $H$ and the shifts $a, \bar a$, the
  double-shift step is the real matrix $Z^T H Z$, where $Z$ is the orthogonal factor of $M$.
* §7.5.5, `GolubVanLoan.Chapter07.francis_first_column`: $M e_1 = (x, y, z, 0, \dots, 0)^T$ with
  explicit $x$, $y$ and $z$.
* Algorithm 7.5.1, `GolubVanLoan.Chapter07.algorithm_7_5_1_window`: the exact run on a window is a
  block similarity, and it performs a Francis step on an unreduced window block.
* Algorithm 7.5.1, `GolubVanLoan.Chapter07.algorithm_7_5_1_spec`: the exact run on an unreduced $H$
  is a Francis step $H' = Z^T H Z$.
* §7.5.5, `GolubVanLoan.Chapter07.algorithm_7_5_1_essential`: the output of Algorithm 7.5.1 is
  $D (Z^T H Z) D$, where $Z$ is the orthogonal factor of $M$ and $D = \operatorname{diag}(\pm 1)$.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.triangularize2x2_spec`: the exact standardization of a
  $2 \times 2$ block is a Givens similarity, which makes a block with real eigenvalues upper
  triangular.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.qrPass_isQRPass`: each exact pass of the program is a
  deflation followed by a Francis step on the unreduced block.
* Algorithm 7.5.2, `GolubVanLoan.Chapter07.algorithm_7_5_2_spec`: the exact output is
  $T = Q^T (A + E) Q$ with $Q$ orthogonal and $\|E\|_F \le ((1 + 2\,\mathrm{tol})^{n \cdot
  \mathrm{fuel}} - 1) \|A\|_F$, and $T$ is in real Schur form when the loop has ended.

## Conventions

* Matrices are real, `Matrix (Fin n) (Fin n) ℝ`. A complex shift acts on a real matrix through
  `Matrix.complexify`, the entrywise embedding of the real matrices in the complex matrices.
* A QR factorization is given as data: a unitary (over $\mathbb{R}$, orthogonal) $U$ and an upper
  triangular $R$ with $H - \mu I = UR$. So the statements hold for every QR factorization, as in the
  source. The predicate `Matrix.IsShiftedQrStep μ H H'` says that $H'$ is one shifted QR step of $H$
  for some QR factorization. The canonical steps `Matrix.shiftedQrStep` and
  `Matrix.doubleShiftQrStep` of `Numlib.Eigen.QRAlgorithm` use the QR factorization by Gram–Schmidt,
  and `Matrix.IsFrancisStep s t H H'` specifies a Francis step.
* Indices are 0-based. The source's $h_{11}$ is `H 0 0`, and its $h_{n,n-1}$ is
  `H (Fin.last _) (Fin.castSucc (Fin.last _))`.
* The window $[p, m)$ is the list of the indices $i$ with $p \le i < m$,
  `GolubVanLoan.Chapter07.francisWindow n p m`. In Algorithm 7.5.2 the blocks $H_{11}$, $H_{22}$ and
  $H_{33}$ have the index sets $[0, p)$, $[p, m)$ and $[m, n)$, so $q = n - m$.

## Implementation notes

* The programs follow the algorithm conventions of `NumlibSurface.GolubVanLoan`: they are generic in
  a monad `M` and a rounding hook `rnd`, and they call the helpers of §5.1,
  `GolubVanLoan.Chapter05.houseOn`, `GolubVanLoan.Chapter05.householderApplyLeft` and
  `GolubVanLoan.Chapter05.householderApplyRight`.
* `GolubVanLoan.Chapter07.algorithm_7_5_1` runs on a window `w` of consecutive indices. The
  algorithm of the source is the full window `List.finRange n`, and Algorithm 7.5.2 runs it on the
  unreduced block $H_{22}$. The bulge chasing applies each reflector over the restricted row and
  column ranges of the source (`GolubVanLoan.Chapter07.francisReflect`,
  `GolubVanLoan.Chapter07.francisChaseStep`). The program returns the reflector data, so that $Z$ is
  `GolubVanLoan.Chapter05.householderProduct data`.
* The exact semantics of Algorithm 7.5.1 rests on the bulge pattern
  `GolubVanLoan.Chapter07.IsFrancisBulge`. Each reflector annihilates the bulge column, and the
  restricted ranges miss only zero entries, so each step is the full similarity $P H P$. The
  triangularity of $Z^T (H - a_1 I)(H - a_2 I)$ is the implicit-shift principle
  `Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`, in the form
  `GolubVanLoan.Chapter07.isFrancisStep_of_first_reflector`. On a window $[p, p + N + 3)$, the block
  $H_{22}$ is indexed by `GolubVanLoan.Chapter07.windowEmb` and read by
  `GolubVanLoan.Chapter07.windowBlock`, and the run is a Francis step on $H_{22}$
  (`GolubVanLoan.Chapter07.algorithm_7_5_1_window`, `GolubVanLoan.Chapter07.IsFrancisStepOn`).
* `GolubVanLoan.Chapter07.triangularize2x2` carries out the last step of Algorithm 7.5.2, "upper
  triangularize all 2-by-2 diagonal blocks with real eigenvalues", by an eigenvector of the block
  and then `GolubVanLoan.Chapter05.algorithm_5_1_3` (givens). Its exact semantics is
  `GolubVanLoan.Chapter07.triangularize2x2_spec`.
* `GolubVanLoan.Chapter07.algorithm_7_5_2` runs Algorithm 7.4.2, the backward accumulation of its
  reflectors, at most `fuel` passes of deflation and Francis step
  (`GolubVanLoan.Chapter07.qrDeflate`, `GolubVanLoan.Chapter07.schurTrailingStart`,
  `GolubVanLoan.Chapter07.unreducedStart`, `GolubVanLoan.Chapter07.qrPass`), and the final
  standardization. Each deflation changes $H$ by at most $2\,\mathrm{tol}\,\|H\|_F$
  (`GolubVanLoan.Chapter07.qrDeflate_spec`). The Francis step on the window $[p, m)$ and the updates
  outside the block (`GolubVanLoan.Chapter07.offBlockConj`) are together the exact similarity by
  $\operatorname{diag}(I_p, Z, I_q)$ (`GolubVanLoan.Chapter07.offBlockConj_blockConj`). The search
  for the partition finds a decoupled upper quasi-triangular $H_{33}$
  (`GolubVanLoan.Chapter07.schurTrailingStart_spec`, `GolubVanLoan.Chapter07.NoTwoSubdiag`,
  `GolubVanLoan.Chapter07.isQuasiUpperTriangular_of_noTwoSubdiag`).
* Each pass is the loop body of the source (`GolubVanLoan.Chapter07.qrPass_isQRPass`): the deflation
  `GolubVanLoan.Chapter07.IsQRDeflation` (`GolubVanLoan.Chapter07.qrDeflate_isQRDeflation`) followed
  by a Francis step on the unreduced block (`GolubVanLoan.Chapter07.IsQRPass`,
  `GolubVanLoan.Chapter07.IsQRFrancisPass`). The specification
  `GolubVanLoan.Chapter07.algorithm_7_5_2_spec` records this sequence of passes.

## Deviations from the source

* **(7.5.3) and (7.5.6)–(7.5.7)** (generalization). The source takes the factorizations to be QR
  factorizations. The identities hold for any second factor $R$, $R_1$, $R_2$. See
  `GolubVanLoan.Chapter07.equation_7_5_3` and `GolubVanLoan.Chapter07.equation_7_5_7`.
* **§7.5.2, the rate of the fixed-shift iteration** (reading). The source states the rate
  $|(\lambda_{p+1} - \mu)/(\lambda_p - \mu)|^k$ by reference to the theory of §7.3. The theorem
  assumes a diagonalizable $A$ with real eigenvalues, distinct nonzero $|\lambda_i - \mu|$ and a
  general-position condition, and it gives the bound $C (r / |\lambda_p - \mu|)^k$ for every
  $r > |\lambda_{p+1} - \mu|$. See `GolubVanLoan.Chapter07.shiftedQr_rate`.
* **Theorem 7.5.1** (generalization). The source concludes $\tilde h_{n,n-1} = 0$ and
  $\tilde h_{nn} = \mu$. The theorem shows that the whole last row of $\tilde H$ is $\mu e_n^T$. See
  `GolubVanLoan.Chapter07.theorem_7_5_1`.
* **§7.5.3, the quadratic convergence** (reading). The source says that if $h_{n,n-1}$ converges to
  zero, it is likely to do so at a quadratic rate. The theorem is a local bound near an
  algebraically simple real eigenvalue. See `GolubVanLoan.Chapter07.single_shift_quadratic`.
* **§7.5.5, the essential uniqueness of the Francis step** (typo). The source cites "Theorem 7.4.3"
  for the implicit Q theorem, which is Theorem 7.4.2. See
  `GolubVanLoan.Chapter07.algorithm_7_5_1_essential`.
* **Algorithm 7.5.2, the last step** (reading). The source gives no algorithm to upper triangularize
  the $2 \times 2$ diagonal blocks with real eigenvalues. The library uses one Givens rotation built
  from an eigenvector of the block. See `GolubVanLoan.Chapter07.triangularize2x2`.
* **Algorithm 7.5.2** (reading). The source says that the algorithm computes the real Schur form
  $Q^T A Q = T$. The deflations set nonzero entries to zero, so in exact arithmetic the theorem
  states $T = Q^T (A + E) Q$ with a bound on $\|E\|_F$, and $E = 0$ if $\mathrm{tol} = 0$. See
  `GolubVanLoan.Chapter07.algorithm_7_5_2_spec`.

## Not formalized

* **The deflation criterion (7.5.2) as a heuristic, and the discussion of decoupling.** The
  criterion itself is the deflation step of Algorithm 7.5.2.
* **Stewart's worked example** $\tilde h_{n,n-1} = -\epsilon^2 b/(a^2 + \epsilon^2)$ of §7.5.3. Its
  rigorous content is `GolubVanLoan.Chapter07.single_shift_quadratic`.
* **The roundoff claims of §7.5.6.** The source states them with $\approx$ and gives no derivation.
* **Balancing (§7.5.7).**
* **Flop counts.**
-/

open Matrix Polynomial FloatingPoint

open GolubVanLoan.Chapter05 (houseOn houseOn_spec householderApplyLeft householderApplyRight
  householderApplyLeft_spec householderApplyRight_spec householderProduct householderProduct_concat
  householderProduct_cons householderProduct_nil householderProduct_mem_orthogonalGroup
  backwardAccumulation algorithm_5_1_3 algorithm_5_1_3_spec givensRotation
  givensRotation_mem_orthogonalGroup givensRotation_transpose_mulVec_apply givensApplyLeft
  givensApplyRight givensApplyLeft_spec givensApplyRight_spec givensApplyRight_spec_of_forall_mem
  mul_one_sub_smul_vecMulVec_apply one_sub_smul_vecMulVec_mul_apply_of_notMem
  one_sub_smul_vecMulVec_mul_apply_of_forall householderProduct_mulVec_single
  one_sub_smul_vecMulVec_mul_apply_eq_mulVec)

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.5.2 The shifted QR iteration -/

/-- **Equation (7.5.3)** of [golub2013matrix]. Let $H, U, R \in \mathbb{R}^{n \times n}$ and
$\mu \in \mathbb{R}$, with $U$ orthogonal and $H - \mu I = UR$. Then each matrix of the shifted
QR iteration is orthogonally similar to its predecessor:
$$RU + \mu I = U^T (UR + \mu I) U = U^T H U.$$

**Generalization.** The source takes $H - \mu I = UR$ to be a QR factorization. The identity
holds for any $R$: only the orthogonality of $U$ is used. -/
theorem equation_7_5_3 {H U R : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hU : U ∈ orthogonalGroup (Fin n) ℝ) (hQR : H - μ • 1 = U * R) :
    R * U + μ • 1 = Uᵀ * H * U := by
  have h := mul_add_smul_one_eq_star_mul_mul hU hQR
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- **Section 7.5.2** of [golub2013matrix], the rate of the fixed-shift QR iteration. Let
$A, X \in \mathbb{R}^{n \times n}$ with $X$ nonsingular and $X^{-1} A X =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$, and let $\mu \in \mathbb{R}$ with
$$|\lambda_1 - \mu| > |\lambda_2 - \mu| > \dots > |\lambda_n - \mu| > 0.$$
Assume that every leading principal submatrix of $X^{-1}$ is nonsingular. Let $H_0 = A$, and let
each $H_{k+1}$ be a shifted QR step of $H_k$ with the shift $\mu$: $H_k - \mu I = U_k R_k$ for
some QR factorization, and $H_{k+1} = R_k U_k + \mu I$. Then for every $p$ with $1 \le p < n$
and every $r > |\lambda_{p+1} - \mu|$ there is a constant $C$ with
$$|(H_k)_{p+1,p}| \le C \left( \frac{r}{|\lambda_p - \mu|} \right)^k \quad \text{for all } k \ge
  0.$$

**Reading.** The source says: "If $\mu$ is a fixed shift and the eigenvalues $\lambda_i$ of $H$
are ordered so that $|\lambda_1 - \mu| \ge \dots \ge |\lambda_n - \mu|$, then the theory of §7.3
says that the $p$th subdiagonal entry in $H_k$ converges to zero with rate
$|(\lambda_{p+1} - \mu)/(\lambda_p - \mu)|^k$." The theorem makes the hypotheses of the theory
of §7.3 explicit: $A$ is diagonalizable with real eigenvalues, the numbers $|\lambda_i - \mu|$
are distinct and nonzero, and $X^{-1}$ is in general position. The rate holds with every $r$
larger than $|\lambda_{p+1} - \mu|$.

The Lean indices are 0-based: the entry is `H k q p` with `q = p + 1`, and the eigenvalues are
`l : Fin n → ℝ`. Each step is `Matrix.IsShiftedQrStep μ (H k) (H (k + 1))`. -/
theorem shiftedQr_rate {A X : Matrix (Fin n) (Fin n) ℝ} {l : Fin n → ℝ} {μ : ℝ}
    (hX : IsUnit X.det) (hXA : X⁻¹ * A * X = diagonal l)
    (hsep : ∀ j k : Fin n, j < k → |l k - μ| < |l j - μ|) (hμ : ∀ j, l j ≠ μ)
    (hgen : ∀ (m : ℕ) (hm : m ≤ n),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det)
    {H : ℕ → Matrix (Fin n) (Fin n) ℝ} (hH0 : H 0 = A)
    (hH : ∀ k, IsShiftedQrStep μ (H k) (H (k + 1))) {p q : Fin n} (hpq : (q : ℕ) = p + 1)
    {r : ℝ} (hr : |l q - μ| < r) :
    ∃ C : ℝ, ∀ k, |H k q p| ≤ C * (r / |l p - μ|) ^ k := by
  set B := A - μ • (1 : Matrix (Fin n) (Fin n) ℝ) with hBdef
  have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 hX
  have hXB : X⁻¹ * B * X = diagonal fun j => l j - μ := by
    rw [hBdef, Matrix.mul_sub, Matrix.sub_mul, hXA, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, nonsing_inv_mul _ hX]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hdetB : IsUnit B.det := by
    have h := congrArg det hXB
    rw [det_mul, det_mul, det_diagonal] at h
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero, zero_mul] at h
    exact (Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hμ j)) h.symm
  have hpq' : p < q := Fin.lt_def.2 (by omega)
  set L := |l p - μ| with hLdef
  set ρ := |l q - μ| with hρdef
  have hρL : ρ < L := hsep p q hpq'
  set r' := min r ((ρ + L) / 2) with hr'def
  have hr'0 : 0 ≤ r' := le_min ((abs_nonneg _).trans hr.le) (by positivity)
  have hr'r : r' ≤ r := min_le_left _ _
  have hρr' : ρ < r' := lt_min hr (by linarith)
  have hr'L : r' < L := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨C, hC⟩ := exists_norm_apply_le_of_isShiftedQrStep hdetB
    (linearIndependent_euclideanCol hX) (span_range_euclideanCol_eq_top hX)
    (toEuclideanLin_euclideanCol_of_conj_eq_diagonal hXu hXA)
    (fun j k hjk => by simpa [Real.norm_eq_abs] using hsep j k hjk)
    ((forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal hX).2 hgen) hH0 hH hpq' hr'0
    (fun j' hj' => by
      simp only [Real.norm_eq_abs]
      rcases eq_or_lt_of_le (Fin.le_def.2 (show (q : ℕ) ≤ j' by
        have := Fin.lt_def.1 hj'; omega)) with h | h
      · rw [← h]; exact hρr'.le
      · exact ((hsep q j' h).trans hρr').le)
    (by simpa [Real.norm_eq_abs] using hr'L)
  have hL0 : 0 < L := (abs_nonneg _).trans_lt hρL
  refine ⟨max C 0, fun k => ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖H k q p‖ ≤ C * (r' / ‖l p - μ‖) ^ k := hC k
    _ ≤ max C 0 * (r' / L) ^ k := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (r / L) ^ k := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k)
          (le_max_right _ _)
        exact div_le_div_of_nonneg_right hr'r hL0.le


/-- **Theorem 7.5.1** of [golub2013matrix] (the exact shift). Let $H \in \mathbb{R}^{n \times n}$ be
unreduced upper Hessenberg, and let $\mu \in \mathbb{C}$ be an eigenvalue of $H$. Let
$H - \mu I = UR$ with $U \in \mathbb{C}^{n \times n}$ unitary and $R$ upper triangular, and let
$\tilde H = RU + \mu I$. Then the last row of $\tilde H$ is $\mu e_n^T$. In particular
$\tilde h_{n,n-1} = 0$ and $\tilde h_{nn} = \mu$.

**Generalization.** The source concludes $\tilde h_{n,n-1} = 0$ and $\tilde h_{nn} = \mu$. The
theorem shows that all the other entries of the last row vanish too.

The statement is over $\mathbb{C}$, as in the source, because the eigenvalue $\mu$ of the real
$H$ can be complex; $H$ enters as `H.complexify`. The size is $n = N + 1$, and the last row is
`Fin.last N`. -/
theorem theorem_7_5_1 {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hH : IsUnreduced H)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ H.complexify) {U R H' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hU : U ∈ unitaryGroup (Fin (N + 1)) ℂ) (hR : R.IsUpperTriangular)
    (hQR : H.complexify - μ • 1 = U * R) (hH' : H' = R * U + μ • 1) (j : Fin (N + 1)) :
    H' (Fin.last N) j = if j = Fin.last N then μ else 0 :=
  IsUnreducedUpperHessenberg.isShiftedQrStep_apply_last
    (hH.map (f := Complex.ofRealHom) Complex.ofReal_injective) hμ ⟨U, hU, R, hR, hQR, hH'⟩ j

/-! ### §7.5.3 The single-shift strategy -/

/-- **Section 7.5.3** of [golub2013matrix], the quadratic convergence of the single-shift iteration
(7.5.4). Let $A \in \mathbb{R}^{n \times n}$ with $n \ge 2$, and let $\lambda \in \mathbb{R}$ be
an algebraically simple eigenvalue of $A$. Then there are constants $C$ and $\delta > 0$ with
the following property. Let $Q$ be orthogonal, let $T = Q^T A Q$ be upper Hessenberg, and assume
that $T - t_{nn} I$ is nonsingular, $|t_{n,n-1}| \le \delta$ and
$|t_{nn} - \lambda| \le \delta$. If $T'$ is a shifted QR step of $T$ with the shift $t_{nn}$
($T - t_{nn} I = UR$ for some QR factorization, and $T' = RU + t_{nn} I$), then
$$|t'_{n,n-1}| \le C\, t_{n,n-1}^2, \qquad |t'_{nn} - \lambda| \le C\, t_{n,n-1}^2.$$

**Reading.** The source says: "If the $(n, n-1)$ entry converges to zero, it is likely to do so
at a quadratic rate." The theorem is a rigorous local form of this claim near an algebraically
simple real eigenvalue.

The eigenvalue is algebraically simple in the sense `A.charpoly.rootMultiplicity l = 1`. The
size is $n = N + 2$, and the index $n$ is `Fin.last (N + 1)`. The last row of a shifted QR step
is one step of Rayleigh quotient iteration on $T^T$, and the proof applies
`Matrix.abs_shiftedQrStep_last_le_of_conj`. -/
theorem single_shift_quadratic {N : ℕ} {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ} {l : ℝ}
    (hl : A.charpoly.rootMultiplicity l = 1) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ Q T T' : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ,
      Q ∈ orthogonalGroup (Fin (N + 2)) ℝ → T = Qᵀ * A * Q → T.IsUpperHessenberg →
      IsUnit (T - T (Fin.last (N + 1)) (Fin.last (N + 1)) • 1) →
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ δ →
      |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ δ →
      IsShiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T T' →
      |T' (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤
          C * |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 ∧
        |T' (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤
          C * |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 :=
  exists_abs_isShiftedQrStep_last_le_sq hl


/-! ### §7.5.4 The double-shift strategy -/

/-- **Equations (7.5.6) and (7.5.7)** of [golub2013matrix]. Let $H, H_1, H_2, U_1, U_2, R_1, R_2 \in
\mathbb{C}^{n \times n}$ and $a_1, a_2 \in \mathbb{C}$, with $U_1$ and $U_2$ unitary and
$$H - a_1 I = U_1 R_1, \quad H_1 = R_1 U_1 + a_1 I, \quad H_1 - a_2 I = U_2 R_2, \quad H_2 = R_2
  U_2 + a_2 I.$$
Then
$$(U_1 U_2)(R_2 R_1) = M, \qquad H_2 = (U_1 U_2)^H H (U_1 U_2),$$
where $M = (H - a_1 I)(H - a_2 I)$ is the matrix of (7.5.8).

**Generalization.** The source takes the two factorizations to be QR factorizations. The
identities hold for any $R_1$ and $R_2$.

The matrices and the shifts are complex, because the shifts $a_1$ and $a_2$ of the double-shift
strategy can be complex. -/
theorem equation_7_5_7 {H H₁ H₂ U₁ U₂ R₁ R₂ : Matrix (Fin n) (Fin n) ℂ} {a₁ a₂ : ℂ}
    (hU₁ : U₁ ∈ unitaryGroup (Fin n) ℂ) (hU₂ : U₂ ∈ unitaryGroup (Fin n) ℂ)
    (h₁ : H - a₁ • 1 = U₁ * R₁) (hH₁ : H₁ = R₁ * U₁ + a₁ • 1)
    (h₂ : H₁ - a₂ • 1 = U₂ * R₂) (hH₂ : H₂ = R₂ * U₂ + a₂ • 1) :
    U₁ * U₂ * (R₂ * R₁) = (H - a₁ • 1) * (H - a₂ • 1) ∧
      H₂ = star (U₁ * U₂) * H * (U₁ * U₂) := by
  constructor
  · have hstep : U₂ * R₂ = R₁ * U₁ + (a₁ - a₂) • 1 := by
      rw [← h₂, hH₁, sub_smul]; abel
    calc U₁ * U₂ * (R₂ * R₁) = U₁ * (U₂ * R₂) * R₁ := by simp only [Matrix.mul_assoc]
      _ = U₁ * R₁ * (U₁ * R₁) + (a₁ - a₂) • (U₁ * R₁) := by
          rw [hstep]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, Matrix.mul_assoc]
      _ = (H - a₁ • 1) * (H - a₂ • 1) := by
          rw [← h₁]
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.one_mul, Matrix.mul_one, sub_smul, smul_sub, smul_smul]
          module
  · rw [hH₂, mul_add_smul_one_eq_star_mul_mul hU₂ h₂, hH₁, mul_add_smul_one_eq_star_mul_mul hU₁ h₁,
      star_mul]
    simp only [Matrix.mul_assoc]

/-- **Equations (7.5.5) and (7.5.8)** of [golub2013matrix]. Let $H \in \mathbb{R}^{n \times n}$ with
$n \ge 2$, let
$$G = \begin{bmatrix} h_{mm} & h_{mn} \\ h_{nm} & h_{nn} \end{bmatrix}, \qquad m = n - 1,$$
be its trailing $2 \times 2$ block, and let $a_1, a_2 \in \mathbb{C}$ be the eigenvalues of $G$,
counted with multiplicity. Then $s = a_1 + a_2 = \operatorname{tr} G$ and $t = a_1 a_2 = \det G$
are real, and
$$M = (H - a_1 I)(H - a_2 I) = H^2 - sH + tI$$
is a real matrix, even when $a_1$ and $a_2$ are complex.

The size is $n = N + 2$, and $G$ is `H.submatrix (Fin.natAdd N) (Fin.natAdd N)`. The eigenvalues
are the roots of the characteristic polynomial of the complexification of $G$. That $M$ is real
is stated as the equality of $(H - a_1 I)(H - a_2 I)$ with the complexification of the real
matrix $H^2 - sH + tI$. -/
theorem equation_7_5_8 {N : ℕ} (H : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) {a₁ a₂ : ℂ}
    (ha : (H.submatrix (Fin.natAdd N) (Fin.natAdd N)).complexify.charpoly.roots = {a₁, a₂}) :
    a₁ + a₂ = ((H.submatrix (Fin.natAdd N) (Fin.natAdd N)).trace : ℂ) ∧
      a₁ * a₂ = ((H.submatrix (Fin.natAdd N) (Fin.natAdd N)).det : ℂ) ∧
      (H.complexify - a₁ • 1) * (H.complexify - a₂ • 1) =
        (H * H - (H.submatrix (Fin.natAdd N) (Fin.natAdd N)).trace • H +
          (H.submatrix (Fin.natAdd N) (Fin.natAdd N)).det • 1).complexify := by
  set G := H.submatrix (Fin.natAdd N) (Fin.natAdd N)
  have htr : a₁ + a₂ = (G.trace : ℂ) := by
    have h := trace_eq_sum_roots_charpoly G.complexify
    rw [ha] at h
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at h
    rw [← h]
    simp [Matrix.trace, complexify, Fin.sum_univ_two]
  have hdet : a₁ * a₂ = (G.det : ℂ) := by
    have h := det_eq_prod_roots_charpoly G.complexify
    rw [ha] at h
    simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton] at h
    rw [← h]
    simp [det_fin_two, complexify]
  refine ⟨htr, hdet, ?_⟩
  rw [complexify_add, complexify_sub, complexify_mul, complexify_smul, complexify_smul,
    complexify_one, ← htr, ← hdet]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, add_smul]
  module

/-- **Section 7.5.4** of [golub2013matrix], the reality of the double-shift step. The source says:
"(7.5.7) is the QR factorization of a real matrix and we may choose $U_1$ and $U_2$ so that
$Z = U_1 U_2$ is real orthogonal. It then follows that $H_2 = Z^T H Z$ is real." Let
$H \in \mathbb{R}^{n \times n}$, and let $a \in \mathbb{C}$ not be an eigenvalue of $H$. Let
$M = H^2 - 2 \operatorname{Re}(a) H + |a|^2 I$, and let $Z$ be the orthogonal factor of the QR
factorization of $M$ by Gram–Schmidt. Then:
* $Z$ is real orthogonal;
* the canonical double-shift QR step of $H$ with the shifts $a_1 = a$ and $a_2 = \bar a$ is
  $Z^T H Z$, so it is real;
* if $H_1$ is a shifted QR step of $H$ with the shift $a$, and $H_2$ is a shifted QR step of
  $H_1$ with the shift $\bar a$, for any QR factorizations, then $H_2 = D^H (Z^T H Z) D$ for a
  diagonal matrix $D$ whose diagonal entries have modulus $1$.

$Z$ is `Matrix.qrQ M`, and the canonical double-shift step is
`Matrix.doubleShiftQrStep H.complexify a`. The second statement says that this step is the
complexification of $Z^T H Z$. -/
theorem double_shift_real (H : Matrix (Fin n) (Fin n) ℝ) {a : ℂ}
    (ha : a ∉ spectrum ℂ H.complexify) :
    qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1) ∈ orthogonalGroup (Fin n) ℝ ∧
      doubleShiftQrStep H.complexify a =
        ((qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1))ᵀ * H *
          qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1)).complexify ∧
      ∀ H₁ H₂ : Matrix (Fin n) (Fin n) ℂ, IsShiftedQrStep a H.complexify H₁ →
        IsShiftedQrStep (starRingEnd ℂ a) H₁ H₂ →
        ∃ d : Fin n → ℂ, (∀ i, ‖d i‖ = 1) ∧
          H₂ = star (diagonal d) * doubleShiftQrStep H.complexify a * diagonal d := by
  refine ⟨qrQ_mem_unitaryGroup _, doubleShiftQrStep_map_ofReal H ha, fun H₁ H₂ h₁ h₂ => ?_⟩
  have hdet₁ : IsUnit (H.complexify - a • 1).det := isUnit_det_sub_smul_one_of_notMem_spectrum ha
  obtain ⟨d, hd, hH₁⟩ := (isShiftedQrStep_shiftedQrStep a H.complexify).unique_of_isUnit h₁ hdet₁
  -- the canonical second step, taken from `H₁`
  have hc₂ : IsShiftedQrStep (starRingEnd ℂ a) H₁
      (shiftedQrStep (starRingEnd ℂ a) (shiftedQrStep a H.complexify)) := by
    rw [hH₁]
    exact (isShiftedQrStep_shiftedQrStep _ _).diagonal_conj hd
  -- `H₁ - ā I` is nonsingular: `ā` is not an eigenvalue of the real `H`, nor of its conjugates
  have hā : starRingEnd ℂ a ∉ spectrum ℂ H.complexify := fun h =>
    ha ((star_mem_spectrum_complexify_iff H a).1 h)
  obtain ⟨V, hV, hHV⟩ := h₁.eq_conj
  have hdet₂ : IsUnit (H₁ - starRingEnd ℂ a • 1).det := by
    have hVV : star V * V = 1 := mem_unitaryGroup_iff'.1 hV
    have hVV' : V * star V = 1 := mem_unitaryGroup_iff.1 hV
    have hsim : H₁ - starRingEnd ℂ a • 1 = star V * (H.complexify - starRingEnd ℂ a • 1) * V := by
      rw [hHV, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        hVV]
    rw [hsim, det_mul, det_mul]
    exact ((isUnit_det_of_right_inverse hVV).mul
      (isUnit_det_sub_smul_one_of_notMem_spectrum hā)).mul (isUnit_det_of_right_inverse hVV')
  obtain ⟨e, he, hH₂⟩ := hc₂.unique_of_isUnit h₂ hdet₂
  exact ⟨e, he, hH₂⟩

/-! ### §7.5.5 The Francis step -/

/-- **Section 7.5.5** of [golub2013matrix], the first column of $M$. Let
$H \in \mathbb{R}^{n \times n}$ with $n \ge 3$ be upper Hessenberg, let $s, t \in \mathbb{R}$,
and let $M = H^2 - sH + tI$. Then $M e_1 = (x, y, z, 0, \dots, 0)^T$ with
$$x = h_{11}^2 + h_{12} h_{21} - s h_{11} + t, \qquad y = h_{21} (h_{11} + h_{22} - s), \qquad
  z = h_{21} h_{32}.$$
So only the first three entries of the first column of $M$ can be nonzero, which is why the
Francis step starts with a $3 \times 3$ reflector.

The size is $n = N + 3$, and the Lean indices are 0-based: $h_{11}$ is `H 0 0`. -/
theorem francis_first_column {N : ℕ} {H : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    (hH : H.IsUpperHessenberg) (s t : ℝ) :
    (H * H - s • H + t • 1) 0 0 = H 0 0 * H 0 0 + H 0 1 * H 1 0 - s * H 0 0 + t ∧
      (H * H - s • H + t • 1) 1 0 = H 1 0 * (H 0 0 + H 1 1 - s) ∧
      (H * H - s • H + t • 1) ⟨2, by omega⟩ 0 = H 1 0 * H ⟨2, by omega⟩ 1 ∧
      ∀ i : Fin (N + 3), 3 ≤ (i : ℕ) → (H * H - s • H + t • 1) i 0 = 0 := by
  rw [isUpperHessenberg_iff_fin] at hH
  have hHH : ∀ i, (H * H) i 0 = H i 0 * H 0 0 + H i 1 * H 1 0 := by
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
    · rfl
    · intro k _
      rw [hH _ 0 (by simp), mul_zero]
  have hM : ∀ i, (H * H - s • H + t • 1) i 0 = H i 0 * H 0 0 + H i 1 * H 1 0 - s * H i 0 +
      t * (1 : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ) i 0 :=
    fun i => by
      rw [Matrix.add_apply, Matrix.sub_apply, hHH, Matrix.smul_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
  have h10 : (1 : Fin (N + 3)) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · rw [hM, one_apply_eq]
    ring
  · rw [hM, one_apply_ne h10]
    ring
  · have h20 : H ⟨2, by omega⟩ 0 = 0 := hH _ _ (by simp)
    have hne : (⟨2, by omega⟩ : Fin (N + 3)) ≠ 0 := fun h => by simp [Fin.ext_iff] at h
    rw [hM, one_apply_ne hne, h20]
    ring
  · have hne : i ≠ 0 := fun h => by rw [h] at hi; simp at hi
    have hi0 : H i 0 = 0 := hH i 0 (by simp; omega)
    have hi1 : H i 1 = 0 := hH i 1 (by simp; omega)
    rw [hM, one_apply_ne hne, hi0, hi1]
    ring

/-! ### §7.5.5 Algorithm 7.5.1 -/

/-! ### Programs -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The **window** $[p, m)$: the list of the indices $i$ with $p \le i < m$, in increasing order.
Algorithm 7.5.2 runs the Francis step on the window of the unreduced block $H_{22}$. -/
def francisWindow (n p m : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun i => p ≤ (i : ℕ) ∧ (i : ℕ) < m

/-- The list of the consecutive triples $(w_0, w_1, w_2), (w_1, w_2, w_3), \dots$ of a list $w$.
These are the index lists $o_k = [w_k, w_{k+1}, w_{k+2}]$ of the bulge-chasing steps of
Algorithm 7.5.1. A list with fewer than three elements has no triple. -/
def francisTriples {α : Type*} : List α → List (α × α × α)
  | a :: b :: c :: t => (a, b, c) :: francisTriples (b :: c :: t)
  | _ => []

/-- The first column of $(H - a_1 I)(H - a_2 I)$ in Algorithm 7.5.1, where $s$ and $t$ come from the
trailing $2 \times 2$ block $H([m, l], [m, l])$:
```
s = H(m,m) + H(l,l)
t = H(m,m)·H(l,l) - H(m,l)·H(l,m)
x = H(1,1)·H(1,1) + H(1,2)·H(2,1) - s·H(1,1) + t
y = H(2,1)·(H(1,1) + H(2,2) - s)
z = H(2,1)·H(3,2)
```
Each operation is rounded, in the printed order. The values $x$, $y$ and $z$ are placed at the
indices $a$, $b$ and $c$ (the source's $1$, $2$ and $3$), and the other entries are zero. -/
noncomputable def francisShiftVector (a b c m l : Fin n) (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Fin n → ℝ) := do
  let s ← rnd (H m m + H l l)
  let t ← rnd ((← rnd (H m m * H l l)) - (← rnd (H m l * H l m)))
  let x ← rnd ((← rnd ((← rnd ((← rnd (H a a * H a a)) + (← rnd (H a b * H b a)))) -
    (← rnd (s * H a a)))) + t)
  let y ← rnd (H b a * (← rnd ((← rnd (H a a + H b b)) - s)))
  let z ← rnd (H b a * H c b)
  pure fun i => if i = a then x else if i = b then y else if i = c then z else 0

/-- One two-sided Householder update of Algorithm 7.5.1 on the index list $o$:
$[v, \beta] = \mathrm{house}(u(o))$ by `GolubVanLoan.Chapter05.houseOn`, then $H(o,
\mathrm{cols}) = (I - \beta v v^T) H(o, \mathrm{cols})$ and $H(\mathrm{rows}, o) =
H(\mathrm{rows}, o) (I - \beta v v^T)$. It returns the new matrix and the reflector data
$(v, \beta)$. -/
noncomputable def francisReflect (o : List (Fin n)) (u : Fin n → ℝ) (cols rows : List (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ)) := do
  let vβ ← houseOn rnd o u
  let H ← householderApplyLeft rnd vβ.1 vβ.2 o cols H
  let H ← householderApplyRight rnd vβ.1 vβ.2 rows o H
  pure (H, vβ)

/-- One bulge-chasing step $k \ge 1$ of Algorithm 7.5.1 on the triple $t = (a, a+1, a+2)$ of the
window $w$. It computes $[v, \beta] = \mathrm{house}(H(a{:}a{+}2, a{-}1))$, applies the
two-sided update `GolubVanLoan.Chapter07.francisReflect` with the column range $q{:}n$ (the
window indices $j$ with $a \le j + 1$) and the row range $1{:}r$ (the window indices $i$ with
$i \le a + 3$), and appends the reflector data to the list. -/
noncomputable def francisChaseStep (w : List (Fin n))
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) (t : Fin n × Fin n × Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) := do
  let r ← francisReflect rnd [t.1, t.2.1, t.2.2]
    (fun i => st.1 i ⟨(t.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.1.isLt⟩)
    (w.filter fun j => (t.1 : ℕ) ≤ j + 1) (w.filter fun i => (i : ℕ) ≤ t.1 + 3) st.1
  pure (r.1, st.2 ++ [r.2])

/-- **Algorithm 7.5.1** of [golub2013matrix] (Francis QR step). Given the unreduced upper Hessenberg
matrix $H \in \mathbb{R}^{n \times n}$ whose trailing $2 \times 2$ principal submatrix has the
eigenvalues $a_1$ and $a_2$, the algorithm overwrites $H$ with $Z^T H Z$, where $Z$ is a product
of Householder matrices and $Z^T (H - a_1 I)(H - a_2 I)$ is upper triangular.
```
m = n - 1
s = H(m,m) + H(n,n);  t = H(m,m)·H(n,n) - H(m,n)·H(n,m)
x = H(1,1)·H(1,1) + H(1,2)·H(2,1) - s·H(1,1) + t
y = H(2,1)·(H(1,1) + H(2,2) - s);  z = H(2,1)·H(3,2)
for k = 0:n-3
    [v, β] = house([x y z]ᵀ)
    q = max{1, k};  H(k+1:k+3, q:n) = (I - β v vᵀ) H(k+1:k+3, q:n)
    r = min{k+4, n};  H(1:r, k+1:k+3) = H(1:r, k+1:k+3) (I - β v vᵀ)
    x = H(k+2, k+1);  y = H(k+3, k+1);  if k < n-3, z = H(k+4, k+1) end
end
[v, β] = house([x y]ᵀ)
H(n-1:n, n-2:n) = (I - β v vᵀ) H(n-1:n, n-2:n)
H(1:n, n-1:n) = H(1:n, n-1:n) (I - β v vᵀ)
```
The program runs on a window $w$ of consecutive indices. The algorithm of the source is the full
window `List.finRange n`, and Algorithm 7.5.2 runs the program on the unreduced block $H_{22}$.
Only the block $H(w, w)$ changes. The program returns the new $H$ and the reflector data in the
order of application, so that $Z$ is `GolubVanLoan.Chapter05.householderProduct data`. On a
window of fewer than three indices it does nothing.

The step $k$ works on the triple $o_k = (a, a+1, a+2)$ of window indices
(`GolubVanLoan.Chapter07.francisTriples`). For $k \ge 1$, the vector $[x\ y\ z]^T$ is column
$a - 1$ of $H$ on $o_k$, which `GolubVanLoan.Chapter05.houseOn` reads in place. With 0-based
indices, the column range $q{:}n$ is the window indices $j$ with $a \le j + 1$, and the row
range $1{:}r$ is the window indices $i$ with $i \le a + 3$. The program has no hypothesis on
$H$. Its exact semantics is `GolubVanLoan.Chapter07.algorithm_7_5_1_spec`. -/
noncomputable def algorithm_7_5_1 (w : List (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) :=
  match francisTriples w with
  | [] => pure (H, [])
  | t₀ :: ts => do
    let tl := (t₀ :: ts).getLast (List.cons_ne_nil _ _)
    let u ← francisShiftVector rnd t₀.1 t₀.2.1 t₀.2.2 tl.2.1 tl.2.2 H
    let st ← francisReflect rnd [t₀.1, t₀.2.1, t₀.2.2] u
      (w.filter fun j => (t₀.1 : ℕ) ≤ j + 1) (w.filter fun i => (i : ℕ) ≤ t₀.1 + 3) H
    let st ← ts.foldlM (francisChaseStep rnd w) (st.1, [st.2])
    let r ← francisReflect rnd [tl.2.1, tl.2.2] (fun i => st.1 i tl.1)
      (w.filter fun j => (tl.1 : ℕ) ≤ j) w st.1
    pure (r.1, st.2 ++ [r.2])

end Programs

/-! ### Index bookkeeping -/

section Triples

variable {α : Type*}

/-- A list of length $\ell$ has $\ell - 2$ consecutive triples, in truncated subtraction, so none
when $\ell < 3$. -/
theorem length_francisTriples : ∀ w : List α, (francisTriples w).length = w.length - 2
  | a :: b :: c :: t => by
    rw [francisTriples, List.length_cons, length_francisTriples (b :: c :: t)]
    simp
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl

/-- The $k$-th consecutive triple of a list $w$ is $(w_k, w_{k+1}, w_{k+2})$. -/
theorem getElem_francisTriples : ∀ (w : List α) (k : ℕ) (hk : k < (francisTriples w).length),
    (francisTriples w)[k] =
      (w[k]'(by rw [length_francisTriples] at hk; omega),
        w[k + 1]'(by rw [length_francisTriples] at hk; omega),
        w[k + 2]'(by rw [length_francisTriples] at hk; omega))
  | a :: b :: c :: t, 0, _ => rfl
  | a :: b :: c :: t, k + 1, hk => by
    have hk' : k < (francisTriples (b :: c :: t)).length := by
      rw [francisTriples, List.length_cons] at hk; omega
    exact getElem_francisTriples (b :: c :: t) k hk'
  | [], _, hk => absurd hk (by simp [francisTriples])
  | [_], _, hk => absurd hk (by simp [francisTriples])
  | [_, _], _, hk => absurd hk (by simp [francisTriples])

end Triples

/-! ### Windows and block similarities -/

section Window

/-- An index $i$ lies in the window $[p, m)$ if and only if $p \le i < m$. -/
theorem mem_francisWindow {p m : ℕ} {i : Fin n} :
    i ∈ francisWindow n p m ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < m := by
  simp [francisWindow]

/-- The window $[p, m)$ has no repeated index. -/
theorem nodup_francisWindow (n p m : ℕ) : (francisWindow n p m).Nodup :=
  (List.nodup_finRange n).filter _

/-- The window $[0, n)$ is the full index list `List.finRange n`. -/
theorem francisWindow_zero (n : ℕ) : francisWindow n 0 n = List.finRange n :=
  List.filter_eq_self.2 fun i _ => by simp

/-- For $k < n$, the value of `Fin.ofNat n k` is $k$. -/
private theorem val_ofNat_lt [NeZero n] {k : ℕ} (hk : k < n) : (Fin.ofNat n k : ℕ) = k := by
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt hk]

/-- For $m \le n$, the window $[p, m)$ is the list $p, p + 1, \dots, m - 1$. -/
theorem francisWindow_eq_map [NeZero n] {p m : ℕ} (hm : m ≤ n) :
    francisWindow n p m = (List.range (m - p)).map fun k => Fin.ofNat n (p + k) := by
  have hmap : ∀ k ∈ List.range (m - p), (Fin.ofNat n (p + k) : ℕ) = p + k := fun k hk => by
    rw [List.mem_range] at hk
    exact val_ofNat_lt (by omega)
  refine List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl a))
    ((List.pairwise_lt_finRange n).filter _) ?_ ?_
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
    rw [Fin.lt_def, hmap a ha, hmap b hb]
    omega
  · rw [List.perm_ext_iff_of_nodup (nodup_francisWindow n p m)]
    · intro i
      rw [mem_francisWindow, List.mem_map]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(i : ℕ) - p, List.mem_range.2 (by omega), Fin.ext ?_⟩
        rw [val_ofNat_lt (by omega)]
        omega
      · rintro ⟨k, hk, rfl⟩
        rw [hmap k hk]
        rw [List.mem_range] at hk
        omega
    · refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
      have := congrArg Fin.val hab
      rw [hmap a ha, hmap b hb] at this
      omega

/-- For $m \le n$, the window $[p, m)$ has length $m - p$. -/
theorem length_francisWindow {p m : ℕ} (hm : m ≤ n) :
    (francisWindow n p m).length = m - p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [francisWindow]
    omega
  · have : NeZero n := ⟨hn.ne'⟩
    rw [francisWindow_eq_map hm, List.length_map, List.length_range]

/-- For $m \le n$, the $k$-th index of the window $[p, m)$ is $p + k$. -/
theorem val_getElem_francisWindow {p m : ℕ} (hm : m ≤ n) (k : ℕ)
    (hk : k < (francisWindow n p m).length) : ((francisWindow n p m)[k] : ℕ) = p + k := by
  have hk' := hk
  rw [length_francisWindow hm] at hk'
  have : NeZero n := ⟨by omega⟩
  rw [List.getElem_of_eq (francisWindow_eq_map hm) hk]
  simp only [List.getElem_map, List.getElem_range, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- The triple $(k, k+1, k+2)$ of indices in `Fin n`, each taken modulo $n$. -/
def francisTri (n : ℕ) [NeZero n] (k : ℕ) : Fin n × Fin n × Fin n :=
  (Fin.ofNat n k, Fin.ofNat n (k + 1), Fin.ofNat n (k + 2))

/-- If $k + 2 < n$, the triple `GolubVanLoan.Chapter07.francisTri n k` has the values $k$, $k + 1$
and $k + 2$. -/
theorem francisTri_val [NeZero n] {k : ℕ} (hk : k + 2 < n) :
    ((francisTri n k).1 : ℕ) = k ∧ ((francisTri n k).2.1 : ℕ) = k + 1 ∧
      ((francisTri n k).2.2 : ℕ) = k + 2 :=
  ⟨val_ofNat_lt (by omega), val_ofNat_lt (by omega), val_ofNat_lt hk⟩

/-- For $m \le n$, the consecutive triples of the window $[p, m)$ are the triples
$(p + k, p + k + 1, p + k + 2)$ for $k = 0, \dots, m - p - 3$. -/
theorem francisTriples_francisWindow [NeZero n] {p m : ℕ} (hm : m ≤ n) :
    francisTriples (francisWindow n p m) =
      (List.range (m - p - 2)).map fun k => francisTri n (p + k) := by
  rw [francisWindow_eq_map hm]
  refine List.ext_getElem (by simp [length_francisTriples]) fun k h₁ h₂ => ?_
  rw [getElem_francisTriples]
  simp only [List.getElem_map, List.getElem_range, francisTri, Nat.add_assoc]

/-- The **block similarity** on the block $[p, m) \times [p, m)$: the matrix that equals $Q^T H Q$
on the block and $H$ elsewhere. This is what Algorithm 7.5.1 does to a matrix when it runs on
the window $[p, m)$. -/
def blockConj (p m : ℕ) (Q H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) then
    (Qᵀ * H * Q) i j else H i j

/-- On the full window $[0, n)$, the block similarity by $Q$ of $H$ is the similarity $Q^T H Q$. -/
theorem blockConj_zero (Q H : Matrix (Fin n) (Fin n) ℝ) : blockConj 0 n Q H = Qᵀ * H * Q := by
  ext i j
  simp [blockConj]

/-- A matrix $Q$ **acts on the block** $[p, m)$ if it agrees with the identity outside
$[p, m) \times [p, m)$. -/
def IsBlockSupported (p m : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, ¬ ((p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)) →
    Q i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j

/-- The identity acts on every block. -/
theorem isBlockSupported_one (p m : ℕ) : IsBlockSupported p m (1 : Matrix (Fin n) (Fin n) ℝ) :=
  fun _ _ _ => rfl

/-- A reflector $I - \beta v v^T$ whose vector $v$ vanishes outside $[p, m)$ acts on the block
$[p, m)$. -/
theorem isBlockSupported_reflector {p m : ℕ} {v : Fin n → ℝ} (β : ℝ)
    (hv : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v i = 0) :
    IsBlockSupported p m (1 - β • vecMulVec v v) := fun i j hij => by
  rw [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
  · rw [hv j fun hj => hij ⟨hi, hj⟩, mul_zero, mul_zero, sub_zero]
  · rw [hv i hi, zero_mul, mul_zero, sub_zero]

/-- The product of two matrices that act on the block $[p, m)$ acts on it. -/
theorem IsBlockSupported.mul {p m : ℕ} {Q P : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsBlockSupported p m Q) (hP : IsBlockSupported p m P) : IsBlockSupported p m (Q * P) :=
  fun i j hij => by
    by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
    · have hj : ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) := fun hj => hij ⟨hi, hj⟩
      rw [Matrix.mul_apply, Finset.sum_eq_single j, hP j j (fun h => hj h.2), one_apply_eq, mul_one,
        hQ i j hij]
      · intro k _ hkj
        rw [hP k j (fun h => hj h.2), one_apply_ne hkj, mul_zero]
      · simp
    · rw [Matrix.mul_apply, Finset.sum_eq_single i, hQ i i (fun h => hi h.1), one_apply_eq, one_mul,
        hP i j (fun h => hi h.1)]
      · intro k _ hki
        rw [hQ i k (fun h => hi h.1), one_apply_ne (Ne.symm hki), zero_mul]
      · simp

/-- If every vector of the reflector data vanishes outside $[p, m)$, the product of the reflectors
acts on the block $[p, m)$. -/
theorem isBlockSupported_householderProduct {p m : ℕ} {data : List ((Fin n → ℝ) × ℝ)}
    (h : ∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0) :
    IsBlockSupported p m (householderProduct data) := by
  induction data with
  | nil => exact isBlockSupported_one p m
  | cons q data ih =>
    rw [householderProduct_cons]
    exact (isBlockSupported_reflector q.2 (h q List.mem_cons_self)).mul
      (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- If $P$ acts on the block $[p, m)$ and $X$ and $Y$ agree on the block, then $P^T X P$ and
$P^T Y P$ agree on the block. -/
private theorem transpose_mul_mul_apply_congr {p m : ℕ} {P X Y : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsBlockSupported p m P)
    (hXY : ∀ k l : Fin n, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → (p ≤ (l : ℕ) ∧ (l : ℕ) < m) →
      X k l = Y k l) {i j : Fin n} (hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m)
    (hj : p ≤ (j : ℕ) ∧ (j : ℕ) < m) : (Pᵀ * X * P) i j = (Pᵀ * Y * P) i j := by
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
  · by_cases hl : p ≤ (l : ℕ) ∧ (l : ℕ) < m
    · rw [hXY k l hk hl]
    · rw [hP l j (fun h => hl h.1), one_apply_ne (fun e => hl (by rw [e]; exact hj)), mul_zero,
        mul_zero]
  · rw [hP k i (fun h => hk h.1), one_apply_ne (fun e => hk (by rw [e]; exact hi)), zero_mul,
      zero_mul,
      zero_mul, zero_mul]

/-- **Block similarities compose**: if $P$ acts on the block $[p, m)$, then the block similarity by
$P$ of the block similarity by $Z$ of $H$ is the block similarity by $ZP$ of $H$. -/
theorem blockConj_blockConj {p m : ℕ} {Z P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsBlockSupported p m P) (H : Matrix (Fin n) (Fin n) ℝ) :
    blockConj p m P (blockConj p m Z H) = blockConj p m (Z * P) H := by
  ext i j
  simp only [blockConj, of_apply]
  split_ifs with hin
  · rw [transpose_mul_mul_apply_congr hP (Y := Zᵀ * H * Z) (fun k l hk hl => by
      simp only [of_apply, hk, hl, and_self, ↓reduceIte]) hin.1 hin.2, transpose_mul]
    simp only [Matrix.mul_assoc]
  · rfl

/-- Let $Z$ act on the block $[p, m)$, and let $X$ be decoupled along the block:
$x_{ij} = x_{ji} = 0$ whenever $i$ lies in $[p, m)$ and $j$ does not. Then the block similarity
by $Z$ of $X$ is $Z^T X Z$. -/
theorem blockConj_eq_of_decoupled {p m : ℕ} {Z X : Matrix (Fin n) (Fin n) ℝ}
    (hZ : IsBlockSupported p m Z)
    (hX : ∀ i j : Fin n, (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) →
      X i j = 0 ∧ X j i = 0) :
    blockConj p m Z X = Zᵀ * X * Z := by
  have hZo : ∀ k l : Fin n, ¬ (p ≤ (k : ℕ) ∧ (k : ℕ) < m) ∨ ¬ (p ≤ (l : ℕ) ∧ (l : ℕ) < m) →
      Z k l = if k = l then 1 else 0 := fun k l h => by
    rw [hZ k l (fun h' => h.elim (fun h1 => h1 h'.1) (fun h2 => h2 h'.2)), Matrix.one_apply]
  ext i j
  simp only [blockConj, of_apply]
  split_ifs with hin
  · rfl
  by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
  · have hj : ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) := fun hj => hin ⟨hi, hj⟩
    rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_zero, (hX i j hi hj).1]
    intro k _
    rw [transpose_apply, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hZo j j (Or.inl hj), ite_eq_left rfl, mul_one]
      by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
      · rw [(hX k j hk hj).1, mul_zero]
      · rw [hZo k i (Or.inl hk), ite_eq_right (fun e : k = i => hk (e ▸ hi)), zero_mul]
    · intro l _ hlj
      rw [hZo l j (Or.inr hj), ite_eq_right hlj, mul_zero]
    · simp
  · have hrow : ∀ l, (Zᵀ * X) i l = X i l := fun l => by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [transpose_apply, hZo i i (Or.inl hi), ite_eq_left rfl, one_mul]
      · intro k _ hki
        rw [transpose_apply, hZo k i (Or.inr hi), ite_eq_right hki, zero_mul]
      · simp
    rw [Matrix.mul_apply]
    simp only [hrow]
    rw [Finset.sum_eq_single j]
    · by_cases hj : p ≤ (j : ℕ) ∧ (j : ℕ) < m
      · rw [(hX j i hj hi).2, zero_mul]
      · rw [hZo j j (Or.inl hj), ite_eq_left rfl, mul_one]
    · intro l _ hlj
      by_cases hl : p ≤ (l : ℕ) ∧ (l : ℕ) < m
      · rw [(hX l i hl hi).2, zero_mul]
      · rw [hZo l j (Or.inl hl), ite_eq_right hlj, mul_zero]
    · simp

end Window

/-! ### The bulge-chasing invariant -/

section Bulge

/-- The **bulge pattern** of Algorithm 7.5.1 on the window $[p, m)$ before the step on the triple
$(a, a+1, a+2)$. The matrix is upper Hessenberg except for the bulge entries $(a+1, a-1)$,
$(a+2, a-1)$ and $(a+2, a)$ inside the window, and for $a = p$ only the entry $(p+2, p)$:
$h_{ij} = 0$ for $j + 1 < i$ unless $p \le j$, $i < m$, $a \le j + 1$, $j \le a$ and
$i \le a + 2$. -/
def IsFrancisBulge (p m a : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (j : ℕ) + 1 < i →
    ¬ (p ≤ (j : ℕ) ∧ (i : ℕ) < m ∧ a ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ a ∧ (i : ℕ) ≤ a + 2) → H i j = 0

/-- An upper Hessenberg matrix has the bulge pattern for all $p$, $m$ and $a$. -/
theorem isFrancisBulge_of_isUpperHessenberg {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsUpperHessenberg) (p m a : ℕ) : IsFrancisBulge p m a H := fun i j hij _ =>
  hH i j ⟨⟨(j : ℕ) + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simpa using hij)⟩

variable {v u : Fin n → ℝ} {β : ℝ}

/-- **One bulge-chasing step keeps the pattern**, as in the pictures of the Francis step in §7.5.5
of [golub2013matrix]. Let $H$ have the bulge pattern on the window $[p, m)$ before the step on
$(a, a+1, a+2)$. Let $v$ vanish outside the indices $a$, $a+1$, $a+2$, let
$P = I - \beta v v^T$, and let $u$ be a vector with $(Pu)_{a+1} = (Pu)_{a+2} = 0$ that equals
column $a - 1$ of $H$ if $p < a$. Then the block similarity by $P$ of $H$ has the bulge pattern
before the step on $(a+1, a+2, a+3)$. -/
theorem IsFrancisBulge.conj {p m a : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsFrancisBulge p m a H)
    (hv : ∀ i : Fin n, (i : ℕ) < a ∨ a + 2 < (i : ℕ) → v i = 0)
    (hPu : ∀ i : Fin n, a < (i : ℕ) → (i : ℕ) ≤ a + 2 → ((1 - β • vecMulVec v v) *ᵥ u) i = 0)
    (hu : ∀ j : Fin n, p ≤ (j : ℕ) → (j : ℕ) + 1 = a → ∀ r, H r j = u r) :
    IsFrancisBulge p m (a + 1) (blockConj p m (1 - β • vecMulVec v v) H) := by
  intro i j hij hex
  have hv' : ∀ r : Fin n, ¬ (a ≤ (r : ℕ) ∧ (r : ℕ) ≤ a + 2) → v r = 0 := fun r hr =>
    hv r (by omega)
  simp only [blockConj, of_apply]
  split_ifs with hin
  swap
  · exact hB i j hij (by omega)
  rw [transpose_one_sub_smul_vecMulVec, mul_one_sub_smul_vecMulVec_apply, dotProduct]
  by_cases hj : a ≤ (j : ℕ) ∧ (j : ℕ) ≤ a + 2
  · -- a column of the active block: row `i ≥ a + 4` is outside the block and vanishes on it
    have hi : a + 3 < (i : ℕ) := by omega
    have hrow : ∀ r : Fin n, ((1 - β • vecMulVec v v) * H) i r = H i r := fun r =>
      one_sub_smul_vecMulVec_mul_apply_of_notMem hv' _ H (by omega) r
    have hHi : ∀ r : Fin n, (r : ℕ) ≤ a + 2 → H i r = 0 := fun r hr =>
      hB i r (by omega) (by omega)
    rw [hrow, hHi j hj.2, Finset.sum_eq_zero, mul_zero, zero_mul, sub_zero]
    intro r _
    rw [hrow]
    by_cases hr : a ≤ (r : ℕ) ∧ (r : ℕ) ≤ a + 2
    · rw [hHi r hr.2, zero_mul]
    · rw [hv' r hr, mul_zero]
  · rw [hv' j hj, mul_zero, sub_zero]
    by_cases hi : a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + 2
    · -- a row of the active block: `j < a`
      rcases Nat.lt_or_ge ((j : ℕ) + 1) a with hja | hja
      · rw [one_sub_smul_vecMulVec_mul_apply_of_forall hv' _ _ (fun r hr => hB r j (by omega)
          (by omega))]
        exact hB i j hij (by omega)
      · rw [one_sub_smul_vecMulVec_mul_apply_eq_mulVec hv' _ H u
          (fun l _ => hu j hin.2.1 (by omega) l) hi]
        exact hPu i (by omega) hi.2
    · rw [one_sub_smul_vecMulVec_mul_apply_of_notMem hv' _ H hi]
      exact hB i j hij (by omega)

/-- **The last step of Algorithm 7.5.1 restores the Hessenberg form.** Let $a + 3 = m$, and let $H$
have the bulge pattern on the window $[p, m)$ before the step on $(a+1, a+2, a+3)$, so that
$(a+2, a)$ is the only entry below the subdiagonal inside the window that can be nonzero. Let
$v$ vanish outside the indices $a+1$ and $a+2$, let $P = I - \beta v v^T$, and let $u$ be column
$a$ of $H$, with $(Pu)_{a+2} = 0$. Then the block similarity by $P$ of $H$ is upper Hessenberg. -/
theorem IsFrancisBulge.conj_last {p m a : ℕ} (ham : a + 3 = m)
    {H : Matrix (Fin n) (Fin n) ℝ} (hB : IsFrancisBulge p m (a + 1) H)
    (hv : ∀ i : Fin n, (i : ℕ) ≤ a ∨ a + 2 < (i : ℕ) → v i = 0)
    (hPu : ∀ i : Fin n, (i : ℕ) = a + 2 → ((1 - β • vecMulVec v v) *ᵥ u) i = 0)
    (hu : ∀ j : Fin n, (j : ℕ) = a → ∀ r, H r j = u r) :
    (blockConj p m (1 - β • vecMulVec v v) H).IsUpperHessenberg := by
  intro i j ⟨k, hjk, hki⟩
  have hij : (j : ℕ) + 1 < i := by
    have := Fin.lt_def.1 hjk
    have := Fin.lt_def.1 hki
    omega
  have hv' : ∀ r : Fin n, ¬ (a + 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ a + 2) → v r = 0 := fun r hr =>
    hv r (by omega)
  simp only [blockConj, of_apply]
  split_ifs with hin
  swap
  · exact hB i j hij (by omega)
  rw [transpose_one_sub_smul_vecMulVec, mul_one_sub_smul_vecMulVec_apply, hv' j (by omega),
    mul_zero, sub_zero]
  by_cases hi : a + 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + 2
  · rcases Nat.lt_or_ge (j : ℕ) a with hja | hja
    · rw [one_sub_smul_vecMulVec_mul_apply_of_forall hv' _ _ (fun r hr => hB r j (by omega)
        (by omega))]
      exact hB i j hij (by omega)
    · rw [one_sub_smul_vecMulVec_mul_apply_eq_mulVec hv' _ H u (fun l _ => hu j (by omega) l) hi]
      exact hPu i (by omega)
  · rw [one_sub_smul_vecMulVec_mul_apply_of_notMem hv' _ H hi]
    exact hB i j hij (by omega)

end Bulge

/-! ### Algorithm 7.5.1: the exact semantics of one step -/

section FrancisSpec

/-- **The exact two-sided update on a window.** Let $o$ be a nonempty list of distinct indices, and
let the lists cols and rows have no repeated index and consist of the indices of the window
$[p, m)$ that satisfy the conditions $C$ and $R$, respectively. Assume that every index of $o$
lies in the window and satisfies $C$ and $R$, that $h_{kq} = 0$ for $k \in o$ and every window
column $q$ that does not satisfy $C$, and that $h_{rk} = 0$ for $k \in o$ and every window row
$r$ that does not satisfy $R$. Then the exact `GolubVanLoan.Chapter07.francisReflect` returns
the block similarity by $P = I - \beta v v^T$ of $H$, where $(v, \beta) = \mathrm{house}(u(o))$,
together with $(v, \beta)$. -/
theorem francisReflect_window {p m : ℕ} {o : List (Fin n)} (ho : o.Nodup) (hne : o ≠ [])
    (u : Fin n → ℝ) {cols rows : List (Fin n)} (hcols : cols.Nodup) (hrows : rows.Nodup)
    {C R : Fin n → Prop} (hcm : ∀ q, q ∈ cols ↔ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) ∧ C q)
    (hrm : ∀ r, r ∈ rows ↔ (p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ R r)
    (hoin : ∀ k ∈ o, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) ∧ C k ∧ R k) {H : Matrix (Fin n) (Fin n) ℝ}
    (hc : ∀ q : Fin n, p ≤ (q : ℕ) → (q : ℕ) < m → ¬ C q → ∀ k ∈ o, H k q = 0)
    (hr : ∀ r : Fin n, p ≤ (r : ℕ) → (r : ℕ) < m → ¬ R r → ∀ k ∈ o, H r k = 0) :
    Id.run (francisReflect pure o u cols rows H) =
      (blockConj p m (1 - (Id.run (houseOn pure o u)).2 • vecMulVec (Id.run (houseOn pure o u)).1
        (Id.run (houseOn pure o u)).1) H, Id.run (houseOn pure o u)) := by
  have hv := (houseOn_spec ho hne u).2.1
  change (Id.run (householderApplyRight pure (Id.run (houseOn pure o u)).1
      (Id.run (houseOn pure o u)).2 rows o
      (Id.run (householderApplyLeft pure (Id.run (houseOn pure o u)).1
        (Id.run (houseOn pure o u)).2 o cols H))), Id.run (houseOn pure o u)) = _
  generalize Id.run (houseOn pure o u) = vβ at hv ⊢
  obtain ⟨v, β⟩ := vβ
  simp only at hv ⊢
  have hvS : ∀ k : Fin n, ¬ (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → v k = 0 := fun k hk =>
    hv k fun h => hk (hoin k h).1
  rw [householderApplyLeft_spec ho hcols hv]
  set L : Matrix (Fin n) (Fin n) ℝ :=
    of fun i q => if q ∈ cols then ((1 - β • vecMulVec v v) * H) i q else H i q with hL
  have hLin : ∀ i q : Fin n, (p ≤ (q : ℕ) ∧ (q : ℕ) < m) →
      L i q = ((1 - β • vecMulVec v v) * H) i q := by
    intro i q hq
    rw [hL, of_apply]
    by_cases hqc : q ∈ cols
    · simp only [hqc, ↓reduceIte]
    · have hC : ¬ C q := fun h => hqc ((hcm q).2 ⟨hq, h⟩)
      simp only [hqc, ↓reduceIte]
      exact (one_sub_smul_vecMulVec_mul_apply_of_forall hv _ _ (fun k hk =>
        hc q hq.1 hq.2 hC k hk) i).symm
  have hLout : ∀ i q : Fin n, ¬ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) → L i q = H i q := by
    intro i q hq
    have hqc : q ∉ cols := fun h => hq ((hcm q).1 h).1
    rw [hL, of_apply]
    simp only [hqc, ↓reduceIte]
  have hsum : ∀ r : Fin n, L r ⬝ᵥ v = ((1 - β • vecMulVec v v) * H) r ⬝ᵥ v :=
    fun r => Finset.sum_congr rfl fun k _ => by
      by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
      · rw [hLin r k hk]
      · rw [hvS k hk, mul_zero, mul_zero]
  rw [householderApplyRight_spec hrows ho hv]
  congr 1
  ext r c
  simp only [of_apply, blockConj, transpose_one_sub_smul_vecMulVec]
  by_cases hrB : p ≤ (r : ℕ) ∧ (r : ℕ) < m
  · by_cases hcB : p ≤ (c : ℕ) ∧ (c : ℕ) < m
    · simp only [hrB, hcB, and_self, ↓reduceIte]
      by_cases hrR : R r
      · have hrr : r ∈ rows := (hrm r).2 ⟨hrB, hrR⟩
        simp only [hrr, ↓reduceIte]
        rw [mul_one_sub_smul_vecMulVec_apply, mul_one_sub_smul_vecMulVec_apply, hsum,
          hLin r c hcB]
      · have hrr : r ∉ rows := fun h => hrR ((hrm r).1 h).2
        have hro : r ∉ o := fun h => hrR (hoin r h).2.2
        simp only [hrr, ↓reduceIte]
        rw [hLin r c hcB, mul_one_sub_smul_vecMulVec_apply, dotProduct, Finset.sum_eq_zero,
          mul_zero, zero_mul, sub_zero]
        intro k _
        rw [one_sub_smul_vecMulVec_mul_apply_of_notMem hv _ H hro]
        by_cases hk : k ∈ o
        · rw [hr r hrB.1 hrB.2 hrR k hk, zero_mul]
        · rw [hv k hk, mul_zero]
    · have hcond : ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (c : ℕ) ∧ (c : ℕ) < m)) :=
        fun h => hcB h.2
      simp only [hcond, ↓reduceIte]
      split_ifs with hrr
      · rw [mul_one_sub_smul_vecMulVec_apply, hvS c hcB, mul_zero, sub_zero, hLout r c hcB]
      · exact hLout r c hcB
  · have hcond : ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (c : ℕ) ∧ (c : ℕ) < m)) :=
      fun h => hrB h.1
    have hrr : r ∉ rows := fun h => hrB ((hrm r).1 h).1
    simp only [hcond, hrr, ↓reduceIte]
    by_cases hcB : p ≤ (c : ℕ) ∧ (c : ℕ) < m
    · rw [hLin r c hcB, one_sub_smul_vecMulVec_mul_apply_of_notMem hv _ H
        (fun h => hrB (hoin r h).1)]
    · exact hLout r c hcB

/-- **One bulge-chasing step on a window, in exact arithmetic.** Let $b = a + 1$, $c = a + 2$,
$p \le a$ and $a + 2 < m$, let $H$ have the bulge pattern on the window $[p, m)$ before the step
on $(a, b, c)$, and let $u$ equal column $a - 1$ of $H$ if $p < a$. Let
$(v, \beta) = \mathrm{house}(u([a, b, c]))$ and $P = I - \beta v v^T$. Then the two restricted
updates of Algorithm 7.5.1 compute the block similarity by $P$ of $H$, and this matrix has the
bulge pattern before the step on $(a+1, a+2, a+3)$. Moreover $\beta = 0$ or $\beta v^T v = 2$,
$v$ vanishes outside $a$, $b$, $c$, and $Pu$ has the entry $\|(u_a, u_b, u_c)\|_2$ at $a$, zeros
at $b$ and $c$, and the entries of $u$ elsewhere. -/
theorem francis_step {p m : ℕ} {a b c : Fin n} (hb : (b : ℕ) = a + 1) (hc : (c : ℕ) = a + 2)
    (hpa : p ≤ a) (ham : (a : ℕ) + 2 < m) {H : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsFrancisBulge p m a H) {u : Fin n → ℝ}
    (hu : ∀ j : Fin n, p ≤ (j : ℕ) → (j : ℕ) + 1 = a → ∀ r, H r j = u r) {v : Fin n → ℝ} {β : ℝ}
    (hvβ : Id.run (houseOn pure [a, b, c] u) = (v, β)) :
    Id.run (francisReflect pure [a, b, c] u
        ((francisWindow n p m).filter fun j => (a : ℕ) ≤ j + 1)
        ((francisWindow n p m).filter fun i => (i : ℕ) ≤ a + 3) H) =
      (blockConj p m (1 - β • vecMulVec v v) H, (v, β)) ∧
      IsFrancisBulge p m (a + 1) (blockConj p m (1 - β • vecMulVec v v) H) ∧
      (β = 0 ∨ β * (v ⬝ᵥ v) = 2) ∧ (∀ i : Fin n, (i : ℕ) < a ∨ (a : ℕ) + 2 < i → v i = 0) ∧
      (1 - β • vecMulVec v v) *ᵥ u = fun i => if i = a then
          ‖(WithLp.toLp 2 (fun j : {j // j ∈ [a, b, c]} => u j) :
            EuclideanSpace ℝ {j // j ∈ [a, b, c]})‖
        else if i ∈ [a, b, c] then 0 else u i := by
  have hmem : ∀ i : Fin n, i ∈ [a, b, c] ↔ (a : ℕ) ≤ i ∧ (i : ℕ) ≤ a + 2 := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc]
    omega
  have hnd : [a, b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc,
      List.nodup_nil, not_false_eq_true, and_true]
    omega
  have hspec := houseOn_spec hnd (List.cons_ne_nil _ _) u
  rw [hvβ] at hspec
  obtain ⟨-, hvout, hβ, -, hPu⟩ := hspec
  have hv : ∀ i : Fin n, (i : ℕ) < a ∨ (a : ℕ) + 2 < i → v i = 0 := fun i hi =>
    hvout i fun h => by rw [hmem] at h; omega
  have hPu' : ∀ i : Fin n, (a : ℕ) < i → (i : ℕ) ≤ a + 2 →
      ((1 - β • vecMulVec v v) *ᵥ u) i = 0 := fun i h1 h2 => by
    rw [hPu]
    have hia : i ≠ a := fun e => by rw [e] at h1; omega
    simp only [List.head_cons, hia, ↓reduceIte, (hmem i).2 ⟨h1.le, h2⟩]
  refine ⟨?_, hB.conj hv hPu' hu, hβ, hv, hPu⟩
  rw [francisReflect_window (p := p) (m := m) hnd (List.cons_ne_nil _ _) u
    ((nodup_francisWindow n p m).filter _) ((nodup_francisWindow n p m).filter _)
    (C := fun j => (a : ℕ) ≤ j + 1) (R := fun i => (i : ℕ) ≤ a + 3)
    (fun q => by simp [List.mem_filter, mem_francisWindow])
    (fun r => by simp [List.mem_filter, mem_francisWindow])
    (fun k hk => by
      rw [hmem] at hk
      exact ⟨⟨by omega, by omega⟩, show (a : ℕ) ≤ k + 1 by omega, show (k : ℕ) ≤ a + 3 by omega⟩),
    hvβ]
  · intro q hq1 hq2 hC k hk
    have hC' : ¬ ((a : ℕ) ≤ q + 1) := hC
    rw [hmem] at hk
    exact hB k q (by omega) (by omega)
  · intro r hr1 hr2 hR k hk
    have hR' : ¬ ((r : ℕ) ≤ a + 3) := hR
    rw [hmem] at hk
    exact hB r k (by omega) (by omega)

/-- **The last step of Algorithm 7.5.1 on a window, in exact arithmetic.** Let $b = a + 1$,
$c = a + 2$, $p \le a$ and $a + 3 = m$, and let $H$ have the bulge pattern on the window
$[p, m)$ before the step on $(a+1, a+2, a+3)$. Let $(v, \beta) = \mathrm{house}(H([b, c], a))$
and $P = I - \beta v v^T$. Then the restricted updates compute the block similarity by $P$ of
$H$, this matrix is upper Hessenberg, $\beta = 0$ or $\beta v^T v = 2$, and $v$ vanishes outside
$b$ and $c$. -/
theorem francis_step_last {p m : ℕ} {a b c : Fin n} (hb : (b : ℕ) = a + 1)
    (hc : (c : ℕ) = a + 2) (hpa : p ≤ a) (ham : (a : ℕ) + 3 = m) {H : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsFrancisBulge p m (a + 1) H) {v : Fin n → ℝ} {β : ℝ}
    (hvβ : Id.run (houseOn pure [b, c] (fun i => H i a)) = (v, β)) :
    Id.run (francisReflect pure [b, c] (fun i => H i a)
        ((francisWindow n p m).filter fun j => (a : ℕ) ≤ j) (francisWindow n p m) H) =
      (blockConj p m (1 - β • vecMulVec v v) H, (v, β)) ∧
      (blockConj p m (1 - β • vecMulVec v v) H).IsUpperHessenberg ∧
      (β = 0 ∨ β * (v ⬝ᵥ v) = 2) ∧ (∀ i : Fin n, (i : ℕ) ≤ a ∨ (a : ℕ) + 2 < i → v i = 0) := by
  have hmem : ∀ i : Fin n, i ∈ [b, c] ↔ (a : ℕ) + 1 ≤ i ∧ (i : ℕ) ≤ a + 2 := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc]
    omega
  have hnd : [b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc,
      List.nodup_nil, not_false_eq_true, and_true]
    omega
  have hspec := houseOn_spec hnd (List.cons_ne_nil _ _) (fun i => H i a)
  rw [hvβ] at hspec
  obtain ⟨-, hvout, hβ, -, hPu⟩ := hspec
  have hv : ∀ i : Fin n, (i : ℕ) ≤ a ∨ (a : ℕ) + 2 < i → v i = 0 := fun i hi =>
    hvout i fun h => by rw [hmem] at h; omega
  have hPu' : ∀ i : Fin n, (i : ℕ) = a + 2 →
      ((1 - β • vecMulVec v v) *ᵥ fun i => H i a) i = 0 := fun i h => by
    rw [hPu]
    have hib : i ≠ b := fun e => by rw [e] at h; omega
    simp only [List.head_cons, hib, ↓reduceIte, (hmem i).2 ⟨by omega, h.le⟩]
  refine ⟨?_, hB.conj_last ham hv hPu' (fun j hj r => by rw [show j = a from Fin.ext hj]),
    hβ, hv⟩
  rw [francisReflect_window (p := p) (m := m) hnd (List.cons_ne_nil _ _) _
    ((nodup_francisWindow n p m).filter _) (nodup_francisWindow n p m)
    (C := fun j => (a : ℕ) ≤ j) (R := fun _ => True)
    (fun q => by simp [List.mem_filter, mem_francisWindow])
    (fun r => by simp [mem_francisWindow])
    (fun k hk => by
      rw [hmem] at hk
      exact ⟨⟨by omega, by omega⟩, show (a : ℕ) ≤ k by omega, trivial⟩), hvβ]
  · intro q hq1 hq2 hC k hk
    have hC' : ¬ ((a : ℕ) ≤ q) := hC
    rw [hmem] at hk
    exact hB k q (by omega) (by omega)
  · intro r _ _ hR
    exact absurd trivial hR

end FrancisSpec

/-! ### The Francis step on a window -/

section WindowBlock

/-- In exact arithmetic, `GolubVanLoan.Chapter07.francisShiftVector` returns the vector with the
entry $h_{aa}^2 + h_{ab} h_{ba} - s h_{aa} + t$ at $a$, the entry $h_{ba} (h_{aa} + h_{bb} - s)$
at $b$, the entry $h_{ba} h_{cb}$ at $c$, and zero elsewhere, where $s = h_{mm} + h_{ll}$ and
$t = h_{mm} h_{ll} - h_{ml} h_{lm}$. If two of $a$, $b$, $c$ coincide, the first one in this
order determines the entry. -/
theorem francisShiftVector_pure (a b c m l : Fin n) (H : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (francisShiftVector pure a b c m l H) = fun i =>
      if i = a then H a a * H a a + H a b * H b a - (H m m + H l l) * H a a +
          (H m m * H l l - H m l * H l m)
      else if i = b then H b a * (H a a + H b b - (H m m + H l l))
      else if i = c then H b a * H c b else 0 := rfl

/-- The polynomial $X^2 - sX + t$, evaluated at a matrix $H$, is $H^2 - sH + tI$. -/
theorem aeval_francisPoly (H : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    aeval H (X ^ 2 - C s * X + C t) = H * H - s • H + t • 1 := by
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, sq]

/-- The **window embedding** $i \mapsto p + i$ of `Fin k` into `Fin n`, for $p + k \le n$. It
indexes the diagonal block $H_{22}$ of Algorithms 7.5.2 and 7.7.3. -/
def windowEmb (p : ℕ) {k : ℕ} (h : p + k ≤ n) (i : Fin k) : Fin n := ⟨p + i, by omega⟩

/-- The window embedding maps $i$ to $p + i$. -/
@[simp]
theorem val_windowEmb (p : ℕ) {k : ℕ} (h : p + k ≤ n) (i : Fin k) :
    (windowEmb p h i : ℕ) = p + i := rfl

/-- The window embedding is injective. -/
theorem windowEmb_injective (p : ℕ) {k : ℕ} (h : p + k ≤ n) :
    Function.Injective (windowEmb p h) := fun i j hij => by
  have := congrArg Fin.val hij
  simp only [val_windowEmb] at this
  exact Fin.ext (by omega)

/-- An index $i$ lies in the range of the window embedding if and only if $p \le i < p + k$. -/
theorem mem_range_windowEmb {p k : ℕ} (h : p + k ≤ n) {i : Fin n} :
    i ∈ Set.range (windowEmb p h) ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + k := by
  constructor
  · rintro ⟨j, rfl⟩
    have := j.isLt
    simp only [val_windowEmb]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(i : ℕ) - p, by omega⟩, Fin.ext (by simp only [val_windowEmb]; omega)⟩

/-- The window embedding takes its values in the window $[p, p + k)$. -/
theorem windowEmb_mem {p k : ℕ} (h : p + k ≤ n) (i : Fin k) :
    p ≤ (windowEmb p h i : ℕ) ∧ (windowEmb p h i : ℕ) < p + k :=
  (mem_range_windowEmb h).1 ⟨i, rfl⟩

/-- The **window block** of $X$: the $k \times k$ diagonal block of $X$ in the rows and columns
$p, p + 1, \dots, p + k - 1$, indexed by `Fin k`. -/
def windowBlock (p : ℕ) {k : ℕ} (h : p + k ≤ n) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  X.submatrix (windowEmb p h) (windowEmb p h)

/-- The entry $(i, j)$ of the window block of $X$ is the entry $(p + i, p + j)$ of $X$. -/
@[simp]
theorem windowBlock_apply (p : ℕ) {k : ℕ} (h : p + k ≤ n) (X : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin k) : windowBlock p h X i j = X (windowEmb p h i) (windowEmb p h j) := rfl

/-- The window block of $X^T$ is the transpose of the window block of $X$. -/
theorem windowBlock_transpose (p : ℕ) {k : ℕ} (h : p + k ≤ n) (X : Matrix (Fin n) (Fin n) ℝ) :
    windowBlock p h Xᵀ = (windowBlock p h X)ᵀ := rfl

/-- The window block of the identity is the identity. -/
theorem windowBlock_one (p : ℕ) {k : ℕ} (h : p + k ≤ n) :
    windowBlock p h (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  submatrix_one _ (windowEmb_injective p h)

/-- If $f$ vanishes outside the window $[p, p + k)$, then $\sum_i f(i)$ is the sum of $f$ over the
window. -/
theorem sum_eq_sum_windowEmb {p k : ℕ} (h : p + k ≤ n) {f : Fin n → ℝ}
    (hf : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + k) → f i = 0) :
    ∑ i, f i = ∑ a, f (windowEmb p h a) :=
  (Fintype.sum_of_injective _ (windowEmb_injective p h) _ _
    (fun i hi => hf i fun hw => hi ((mem_range_windowEmb h).2 hw)) fun _ => rfl).symm

/-- The transpose of a matrix that acts on a block acts on the same block. -/
theorem IsBlockSupported.transpose {p m : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsBlockSupported p m Q) : IsBlockSupported p m Qᵀ := fun i j hij => by
  simpa [Matrix.one_apply, eq_comm] using hQ j i fun h => hij ⟨h.2, h.1⟩

/-- If $Q$ acts on the window $[p, p + k)$, then $q_{ij} = 0$ whenever exactly one of $i$ and $j$
lies in the window. -/
theorem IsBlockSupported.apply_eq_zero {p k : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsBlockSupported p (p + k) Q) {i j : Fin n}
    (h : ¬ ((p ≤ (i : ℕ) ∧ (i : ℕ) < p + k) ↔ (p ≤ (j : ℕ) ∧ (j : ℕ) < p + k))) : Q i j = 0 := by
  rw [hQ i j fun hh => h ⟨fun _ => hh.2, fun _ => hh.1⟩,
    one_apply_ne fun e => h (by rw [e])]

/-- **The window block of a product, with a matrix that acts on the window on the right**: if $Y$
acts on the window, then $(XY)_{22} = X_{22} Y_{22}$. -/
theorem windowBlock_mul_of_isBlockSupported_right {p k : ℕ} (h : p + k ≤ n)
    {Y : Matrix (Fin n) (Fin n) ℝ} (hY : IsBlockSupported p (p + k) Y)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    windowBlock p h (X * Y) = windowBlock p h X * windowBlock p h Y := by
  ext a b
  simp only [windowBlock_apply, Matrix.mul_apply]
  refine sum_eq_sum_windowEmb h fun l hl => ?_
  rw [hY.apply_eq_zero (fun e => hl (e.2 (windowEmb_mem h b))), mul_zero]

/-- **The window block of a product, with a matrix that acts on the window on the left**: if $X$
acts on the window, then $(XY)_{22} = X_{22} Y_{22}$. -/
theorem windowBlock_mul_of_isBlockSupported_left {p k : ℕ} (h : p + k ≤ n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsBlockSupported p (p + k) X)
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    windowBlock p h (X * Y) = windowBlock p h X * windowBlock p h Y := by
  ext a b
  simp only [windowBlock_apply, Matrix.mul_apply]
  refine sum_eq_sum_windowEmb h fun l hl => ?_
  rw [hX.apply_eq_zero (fun e => hl (e.1 (windowEmb_mem h a))), zero_mul]

/-- The window block of an orthogonal matrix that acts on the window is orthogonal. -/
theorem windowBlock_mem_orthogonalGroup {p k : ℕ} (h : p + k ≤ n)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (hZS : IsBlockSupported p (p + k) Z) : windowBlock p h Z ∈ orthogonalGroup (Fin k) ℝ := by
  rw [mem_orthogonalGroup_iff, ← windowBlock_transpose,
    ← windowBlock_mul_of_isBlockSupported_right h hZS.transpose,
    (mem_orthogonalGroup_iff (Fin n) ℝ).1 hZ, windowBlock_one]

/-- **The window block of an equivalence by matrices that act on the window**: if $Q$ and $Z$ act on
the window, then $(Q^T H Z)_{22} = Q_{22}^T H_{22} Z_{22}$. -/
theorem windowBlock_transpose_mul_mul {p k : ℕ} (h : p + k ≤ n)
    {Q Z : Matrix (Fin n) (Fin n) ℝ} (hQS : IsBlockSupported p (p + k) Q)
    (hZS : IsBlockSupported p (p + k) Z) (H : Matrix (Fin n) (Fin n) ℝ) :
    windowBlock p h (Qᵀ * H * Z) =
      (windowBlock p h Q)ᵀ * windowBlock p h H * windowBlock p h Z := by
  rw [windowBlock_mul_of_isBlockSupported_right h hZS,
    windowBlock_mul_of_isBlockSupported_left h hQS.transpose, windowBlock_transpose]

/-- The window block of the block similarity by $Z$ of $H$ on the window $[p, p + k)$ equals the
window block of $Z^T H Z$. -/
theorem windowBlock_blockConj {p k : ℕ} (h : p + k ≤ n) (Z H : Matrix (Fin n) (Fin n) ℝ) :
    windowBlock p h (blockConj p (p + k) Z H) = windowBlock p h (Zᵀ * H * Z) := by
  ext a b
  simp only [windowBlock_apply, blockConj, of_apply]
  rw [ite_eq_left ⟨windowEmb_mem h a, windowEmb_mem h b⟩]

/-- The window block of an upper Hessenberg matrix is upper Hessenberg. -/
theorem isUpperHessenberg_windowBlock {p k : ℕ} (h : p + k ≤ n) {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsUpperHessenberg) : (windowBlock p h H).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff_fin] at hH ⊢
  intro a b hab
  exact hH _ _ (by simp only [val_windowEmb]; omega)

/-- The window block of an upper triangular matrix is upper triangular. -/
theorem isUpperTriangular_windowBlock {p k : ℕ} (h : p + k ≤ n) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsUpperTriangular) : (windowBlock p h B).IsUpperTriangular := by
  rw [isUpperTriangular_iff_fin] at hB ⊢
  intro a b hab
  exact hB _ _ (by simp only [val_windowEmb]; omega)

/-- If $u$ vanishes outside the window, then $X_{22}$ times the window part of $u$ is the window
part of $Xu$. -/
theorem windowBlock_mulVec {p k : ℕ} (h : p + k ≤ n) (X : Matrix (Fin n) (Fin n) ℝ)
    {u : Fin n → ℝ} (hu : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + k) → u i = 0) (a : Fin k) :
    (windowBlock p h X *ᵥ (u ∘ windowEmb p h)) a = (X *ᵥ u) (windowEmb p h a) := by
  simp only [mulVec, dotProduct, windowBlock_apply, Function.comp_apply]
  exact (sum_eq_sum_windowEmb h (f := fun i => X (windowEmb p h a) i * u i)
    fun i hi => by rw [hu i hi, mul_zero]).symm

/-- Column $a$ of the window block of $X$ is the window part of column $p + a$ of $X$. -/
theorem windowBlock_mulVec_single {p k : ℕ} (h : p + k ≤ n) (X : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin k) :
    windowBlock p h X *ᵥ Pi.single a 1 = (X *ᵥ Pi.single (windowEmb p h a) 1) ∘ windowEmb p h := by
  funext b
  simp only [mulVec_single_one, col_apply, windowBlock_apply, Function.comp_apply]

/-- **The first reflector on the window.** Let $P$ act on the window $[p, p + N + 1)$, with
$P^2 = I$, and let $Z$ satisfy $Z e_p = P e_p$. Let $u$ vanish outside the window, and let $Pu$
vanish outside the index $p$. Then the window blocks satisfy the same conditions:
$P_{22}^2 = I$, $Z_{22} e_1 = P_{22} e_1$, and $P_{22} u_{22}$ vanishes outside the first index. -/
theorem windowBlock_first_reflector {p N : ℕ} (h : p + (N + 1) ≤ n)
    {Z P : Matrix (Fin n) (Fin n) ℝ} {u : Fin n → ℝ}
    (hPS : IsBlockSupported p (p + (N + 1)) P) (hP : P * P = 1)
    (hZP : Z *ᵥ Pi.single (windowEmb p h 0) 1 = P *ᵥ Pi.single (windowEmb p h 0) 1)
    (hu : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + (N + 1)) → u i = 0)
    (hPu : ∀ i, i ≠ windowEmb p h 0 → (P *ᵥ u) i = 0) :
    windowBlock p h P * windowBlock p h P = 1 ∧
      windowBlock p h Z *ᵥ Pi.single 0 1 = windowBlock p h P *ᵥ Pi.single 0 1 ∧
      ∀ a, a ≠ 0 → (windowBlock p h P *ᵥ (u ∘ windowEmb p h)) a = 0 := by
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · rw [← windowBlock_mul_of_isBlockSupported_right h hPS, hP, windowBlock_one]
  · rw [windowBlock_mulVec_single, windowBlock_mulVec_single, hZP]
  · rw [windowBlock_mulVec h P hu]
    exact hPu _ ((windowEmb_injective p h).ne ha)

/-- The trace $s = h_{n-1,n-1} + h_{nn}$ of the trailing $2 \times 2$ block of
$H \in \mathbb{R}^{n \times n}$, $n \ge 2$: the sum of the two shifts of the Francis step,
(7.5.8). -/
def trailingTrace {N : ℕ} (H : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : ℝ :=
  H (Fin.last N).castSucc (Fin.last N).castSucc + H (Fin.last (N + 1)) (Fin.last (N + 1))

/-- The determinant $t = h_{n-1,n-1} h_{nn} - h_{n-1,n} h_{n,n-1}$ of the trailing $2 \times 2$
block of $H \in \mathbb{R}^{n \times n}$, $n \ge 2$: the product of the two shifts of the
Francis step, (7.5.8). -/
def trailingDet {N : ℕ} (H : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : ℝ :=
  H (Fin.last N).castSucc (Fin.last N).castSucc * H (Fin.last (N + 1)) (Fin.last (N + 1)) -
    H (Fin.last N).castSucc (Fin.last (N + 1)) * H (Fin.last (N + 1)) (Fin.last N).castSucc

/-- **The implicit-shift argument of the Francis step** (§7.5.5 of [golub2013matrix], and §7.7.6 for
the QZ step). Let $H \in \mathbb{R}^{n \times n}$ with $n \ge 3$ be unreduced upper Hessenberg,
let $s, t \in \mathbb{R}$, and let $M = H^2 - sH + tI$. Let $Z$ be orthogonal with $Z^T H Z$
upper Hessenberg, and let $P$ satisfy $P^2 = I$, $Z e_1 = P e_1$, and
$P M e_1 \in \operatorname{span}\{e_1\}$. Then $Z^T M$ is upper triangular, $Z e_1$ lies in the
span of $M e_1$, and $Z^T H Z$ is a Francis step of $H$ (`Matrix.IsFrancisStep`).

The vector $M e_1$ is nonzero, since its third entry is $h_{21} h_{32}$. The triangularity is
`Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`. -/
theorem isFrancisStep_of_first_reflector {N : ℕ}
    {H Z P : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ} {s t : ℝ} (hH : IsUnreduced H)
    (hZ : Z ∈ orthogonalGroup (Fin (N + 3)) ℝ)
    (hG : (Zᵀ * H * Z).IsUpperHessenberg) (hP : P * P = 1)
    (hZP : Z *ᵥ Pi.single 0 1 = P *ᵥ Pi.single 0 1)
    (hPu : ∀ i, i ≠ 0 → (P *ᵥ (H * H - s • H + t • 1).col 0) i = 0) :
    (Zᵀ * (H * H - s • H + t • 1)).IsUpperTriangular ∧
      Z.col 0 ∈ Submodule.span ℝ {(H * H - s • H + t • 1).col 0} ∧
      IsFrancisStep s t H (Zᵀ * H * Z) := by
  set M := H * H - s • H + t • 1 with hM
  set u := M.col 0 with hudef
  have hu0 : u ≠ 0 := by
    intro hu
    have hz := congrFun hu ⟨2, by omega⟩
    rw [hudef, col_apply, Pi.zero_apply, hM, (francis_first_column hH.1 s t).2.2.1] at hz
    have hsub := (isUnreduced_iff.1 hH).2
    have e10 : H 1 0 ≠ 0 := by
      convert hsub 0 (by omega) using 2 <;> exact Fin.ext (by simp)
    have e21 : H ⟨2, by omega⟩ 1 ≠ 0 := by
      convert hsub 1 (by omega) using 2
      exact Fin.ext (by simp)
    exact mul_ne_zero e10 e21 hz
  set c := (P *ᵥ u) 0 with hc
  have hPu' : P *ᵥ u = c • Pi.single 0 1 := by
    funext i
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hi : i = 0
    · rw [hi, ite_eq_left rfl, mul_one]
    · rw [ite_eq_right hi, mul_zero]
      exact hPu i hi
  have hc0 : c ≠ 0 := by
    intro h0
    refine hu0 ?_
    rw [← one_mulVec u, ← hP, ← mulVec_mulVec, hPu', h0, zero_smul, mulVec_zero]
  have hPe : P *ᵥ Pi.single 0 1 = c⁻¹ • u := by
    have h' : u = c • (P *ᵥ Pi.single 0 1) := by
      rw [← mulVec_smul, ← hPu', mulVec_mulVec, hP, one_mulVec]
    rw [h', smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hcol : Z.col 0 ∈ Submodule.span ℝ {M.col 0} := by
    rw [← mulVec_single_one Z 0, hZP, hPe]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hstarZ : star Z = Zᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have htri : (Zᵀ * M).IsUpperTriangular := by
    have := IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval hH
      (X ^ 2 - C s * X + C t) hZ (by rw [hstarZ]; exact hG)
      (by rw [aeval_francisPoly, mulVec_single_one]; exact hcol)
    rwa [aeval_francisPoly, hstarZ] at this
  exact ⟨htri, hcol, Z, hZ, rfl, hG, htri⟩

/-- A **Francis step on the window** $[p, p + N + 3)$, the loop body of Algorithm 7.5.2 ("perform a
Francis QR step on $H_{22}$: $H_{22} = Z^T H_{22} Z$"). It holds when $Z$ is orthogonal and acts
on the window only, so that $Z = \operatorname{diag}(I_p, Z_{22}, I_q)$, the matrix
$Z_{22}^T H_{22} Z_{22}$ is upper Hessenberg, and $Z_{22}^T (H_{22}^2 - s H_{22} + t I)$ is
upper triangular. Here $s$ and $t$ are the trace and the determinant of the trailing
$2 \times 2$ block of $H_{22}$, so that $H_{22}^2 - s H_{22} + t I = (H_{22} - a_1 I)(H_{22} -
a_2 I)$ with the eigenvalues $a_1$, $a_2$ of that block. -/
def IsFrancisStepOn (p N : ℕ) (h : p + (N + 3) ≤ n) (H Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z ∈ orthogonalGroup (Fin n) ℝ ∧ IsBlockSupported p (p + (N + 3)) Z ∧
    ((windowBlock p h Z)ᵀ * windowBlock p h H * windowBlock p h Z).IsUpperHessenberg ∧
    ((windowBlock p h Z)ᵀ * (windowBlock p h H * windowBlock p h H -
      trailingTrace (windowBlock p h H) • windowBlock p h H +
      trailingDet (windowBlock p h H) • 1)).IsUpperTriangular

/-- If $Z$ performs a Francis step on the window, then the window block of $Z^T H Z$ is
$Z_{22}^T H_{22} Z_{22}$, and it is a Francis step of $H_{22}$ (`Matrix.IsFrancisStep`). -/
theorem IsFrancisStepOn.isFrancisStep {p N : ℕ} {h : p + (N + 3) ≤ n}
    {H Z : Matrix (Fin n) (Fin n) ℝ} (hF : IsFrancisStepOn p N h H Z) :
    windowBlock p h (Zᵀ * H * Z) =
        (windowBlock p h Z)ᵀ * windowBlock p h H * windowBlock p h Z ∧
      IsFrancisStep (trailingTrace (windowBlock p h H)) (trailingDet (windowBlock p h H))
        (windowBlock p h H) (windowBlock p h (Zᵀ * H * Z)) := by
  obtain ⟨hZ, hZS, hG, htri⟩ := hF
  have e := windowBlock_transpose_mul_mul h hZS hZS H
  exact ⟨e, windowBlock p h Z, windowBlock_mem_orthogonalGroup h hZ hZS, e, by rw [e]; exact hG,
    htri⟩

end WindowBlock

/-! ### Algorithm 7.5.1 on a window -/

section FrancisWindow

variable [NeZero n]

/-- The invariant of the loop of Algorithm 7.5.1 on the window $[p, m)$ after $k$ further steps: the
bulge pattern before the step on $(p+k+1, p+k+2, p+k+3)$, the accumulated block similarity by
the product of the reflectors, and for each reflector the dichotomy $\beta = 0$ or
$\beta v^T v = 2$, the support in the window, and, after the first reflector, the support in the
indices $> p$. -/
private def FrancisWinInv (p m : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (p₀ : (Fin n → ℝ) × ℝ)
    (k : ℕ) (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) : Prop :=
  IsFrancisBulge p m (p + k + 1) st.1 ∧ st.1 = blockConj p m (householderProduct st.2) H ∧
    (∀ q ∈ st.2, (q.2 = 0 ∨ q.2 * (q.1 ⬝ᵥ q.1) = 2) ∧
      ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0) ∧
    ∃ rest, st.2 = p₀ :: rest ∧ ∀ q ∈ rest, ∀ i : Fin n, (i : ℕ) ≤ p → q.1 i = 0

/-- The exact loop of Algorithm 7.5.1 on the window $[p, m)$ keeps its loop invariant. -/
private theorem francisWinLoop_inv {p m : ℕ} (hm : m ≤ n) {H : Matrix (Fin n) (Fin n) ℝ}
    {p₀ : (Fin n → ℝ) × ℝ} {st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (hst : FrancisWinInv p m H p₀ 0 st) :
    ∀ k, p + k + 3 ≤ m → FrancisWinInv p m H p₀ k
      (((List.range k).map fun k => francisTri n (p + (k + 1))).foldl
        (fun st t => Id.run (francisChaseStep pure (francisWindow n p m) st t)) st) := by
  intro k
  induction k with
  | zero => intro _; simpa using hst
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append]
    obtain ⟨hB, hconj, hdata, rest, hrest, h0⟩ := ih (by omega)
    generalize ((List.range k).map fun k => francisTri n (p + (k + 1))).foldl
      (fun st t => Id.run (francisChaseStep pure (francisWindow n p m) st t)) st = st' at *
    obtain ⟨ha, hb, hc⟩ := francisTri_val (n := n) (k := p + (k + 1)) (by omega)
    set u : Fin n → ℝ := fun i => st'.1 i ⟨((francisTri n (p + (k + 1))).1 : ℕ) - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) (francisTri n (p + (k + 1))).1.isLt⟩ with hu
    obtain ⟨⟨v, β⟩, hvβ⟩ : ∃ vβ, Id.run (houseOn pure [(francisTri n (p + (k + 1))).1,
        (francisTri n (p + (k + 1))).2.1, (francisTri n (p + (k + 1))).2.2] u) = vβ :=
      ⟨_, rfl⟩
    obtain ⟨hstep, hB', hβ', hv', -⟩ := francis_step (p := p) (m := m) (by rw [hb, ha])
      (by rw [hc, ha]) (by rw [ha]; omega) (by rw [ha]; omega) (H := st'.1) (u := u)
      (by rw [ha, ← Nat.add_assoc]; exact hB)
      (fun j _ hj r => by
        have hj' : j = ⟨((francisTri n (p + (k + 1))).1 : ℕ) - 1,
            lt_of_le_of_lt (Nat.sub_le _ _) (francisTri n (p + (k + 1))).1.isLt⟩ :=
          Fin.ext (by change (j : ℕ) = (francisTri n (p + (k + 1))).1 - 1; omega)
        rw [hu, hj']) hvβ
    have hvS : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v i = 0 := fun i hi =>
      hv' i (by rw [ha]; omega)
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    change FrancisWinInv p m H p₀ (k + 1)
      ((Id.run (francisReflect pure _ _ _ _ st'.1)).1,
        st'.2 ++ [(Id.run (francisReflect pure _ _ _ _ st'.1)).2])
    rw [hstep]
    refine ⟨by rw [ha] at hB'; exact hB', ?_, ?_, rest ++ [(v, β)],
      by rw [hrest]; rfl, ?_⟩
    · rw [hconj, blockConj_blockConj (isBlockSupported_reflector β hvS),
        householderProduct_concat]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hdata q hq
      · rw [List.mem_singleton.1 hq]; exact ⟨hβ', hvS⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h0 q hq
      · rw [List.mem_singleton.1 hq]
        exact fun i hi => hv' i (Or.inl (by rw [ha]; omega))

/-- For $p + 3 \le m \le n$, the consecutive triples of the window $[p, m)$ are the triple at $p$
followed by the triples at $p + k + 1$ for $k = 0, \dots, m - p - 4$. -/
private theorem francisTriples_francisWindow_cons {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m) :
    francisTriples (francisWindow n p m) =
      francisTri n p :: (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1)) := by
  rw [francisTriples_francisWindow hm, show m - p - 2 = m - p - 3 + 1 by omega,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- For $p + 3 \le m$, the last consecutive triple of the window $[p, m)$ is
$(m - 3, m - 2, m - 1)$. -/
private theorem getLast_francisTri {p m : ℕ} (hpm : p + 3 ≤ m) :
    (francisTri n p :: (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))).getLast
      (List.cons_ne_nil _ _) = francisTri n (m - 3) := by
  have hl : (francisTri n p :: (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))) =
      (List.range (m - p - 2)).map fun k => francisTri n (p + k) := by
    rw [show m - p - 2 = m - p - 3 + 1 by omega, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    rfl
  rw [List.getLast_congr _ (by simp; omega) hl, List.getLast_map, List.getLast_range,
    show p + (m - p - 2 - 1) = m - 3 by omega]

/-- The exact run of Algorithm 7.5.1 on the window $[p, m)$, with the loop unfolded. -/
private theorem algorithm_7_5_1_window_eq {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_7_5_1 pure (francisWindow n p m) H) =
      let L := (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))
      let tl := (francisTri n p :: L).getLast (List.cons_ne_nil _ _)
      let u := Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
        (francisTri n p).2.2 tl.2.1 tl.2.2 H)
      let st := Id.run (francisReflect pure [(francisTri n p).1, (francisTri n p).2.1,
        (francisTri n p).2.2] u
        ((francisWindow n p m).filter fun j => ((francisTri n p).1 : ℕ) ≤ j + 1)
        ((francisWindow n p m).filter fun i => (i : ℕ) ≤ (francisTri n p).1 + 3) H)
      let st := Id.run (L.foldlM (francisChaseStep pure (francisWindow n p m)) (st.1, [st.2]))
      let r := Id.run (francisReflect pure [tl.2.1, tl.2.2] (fun i => st.1 i tl.1)
        ((francisWindow n p m).filter fun j => (tl.1 : ℕ) ≤ j) (francisWindow n p m) st.1)
      (r.1, st.2 ++ [r.2]) := by
  rw [algorithm_7_5_1, francisTriples_francisWindow_cons hm hpm]
  rfl

/-- The internal form of `GolubVanLoan.Chapter07.algorithm_7_5_1_window`, which also describes the
first reflector and its action on the first column of $(H - a_1 I)(H - a_2 I)$. -/
private theorem algorithm_7_5_1_window_aux {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m)
    {H H' : Matrix (Fin n) (Fin n) ℝ} {data : List ((Fin n → ℝ) × ℝ)}
    (hH : H.IsUpperHessenberg)
    (h : Id.run (algorithm_7_5_1 pure (francisWindow n p m) H) = (H', data)) :
    householderProduct data ∈ orthogonalGroup (Fin n) ℝ ∧
      IsBlockSupported p m (householderProduct data) ∧
      (∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0) ∧
      H' = blockConj p m (householderProduct data) H ∧ H'.IsUpperHessenberg ∧
      ∃ v₀ β₀ rest, data = (v₀, β₀) :: rest ∧
        (∀ q ∈ rest, ∀ i : Fin n, (i : ℕ) ≤ p → q.1 i = 0) ∧
        (β₀ = 0 ∨ β₀ * (v₀ ⬝ᵥ v₀) = 2) ∧
        (1 - β₀ • vecMulVec v₀ v₀) *ᵥ Id.run (francisShiftVector pure (francisTri n p).1
          (francisTri n p).2.1 (francisTri n p).2.2 (francisTri n (m - 3)).2.1
          (francisTri n (m - 3)).2.2 H) = fun i => if i = (francisTri n p).1 then
            ‖(WithLp.toLp 2 (fun j : {j // j ∈ [(francisTri n p).1, (francisTri n p).2.1,
              (francisTri n p).2.2]} => Id.run (francisShiftVector pure (francisTri n p).1
                (francisTri n p).2.1 (francisTri n p).2.2 (francisTri n (m - 3)).2.1
                (francisTri n (m - 3)).2.2 H) j) :
              EuclideanSpace ℝ {j // j ∈ [(francisTri n p).1, (francisTri n p).2.1,
                (francisTri n p).2.2]})‖
          else if i ∈ [(francisTri n p).1, (francisTri n p).2.1, (francisTri n p).2.2] then 0
          else Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
            (francisTri n p).2.2 (francisTri n (m - 3)).2.1 (francisTri n (m - 3)).2.2 H) i := by
  obtain ⟨ha₀, hb₀, hc₀⟩ := francisTri_val (n := n) (k := p) (by omega)
  rw [algorithm_7_5_1_window_eq hm hpm] at h
  dsimp only at h
  rw [getLast_francisTri hpm] at h
  set u₀ := Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
    (francisTri n p).2.2 (francisTri n (m - 3)).2.1 (francisTri n (m - 3)).2.2 H) with hu₀
  obtain ⟨⟨v₀, β₀⟩, hvβ₀⟩ : ∃ vβ, Id.run (houseOn pure [(francisTri n p).1,
      (francisTri n p).2.1, (francisTri n p).2.2] u₀) = vβ := ⟨_, rfl⟩
  obtain ⟨hs₁, hB₁, hβ₁, hv₁, hPu₀⟩ := francis_step (p := p) (m := m) (by rw [hb₀, ha₀])
    (by rw [hc₀, ha₀]) (by rw [ha₀]) (by rw [ha₀]; omega)
    (isFrancisBulge_of_isUpperHessenberg hH _ _ _) (u := u₀) (fun j hj1 hj2 => by omega) hvβ₀
  rw [hs₁] at h
  dsimp only at h
  rw [List.idRun_foldlM] at h
  set P₀ := 1 - β₀ • vecMulVec v₀ v₀ with hP₀
  have hv₁S : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v₀ i = 0 := fun i hi =>
    hv₁ i (by rw [ha₀]; omega)
  have hinv0 : FrancisWinInv p m H (v₀, β₀) 0 (blockConj p m P₀ H, [(v₀, β₀)]) := by
    refine ⟨by rw [ha₀] at hB₁; simpa using hB₁, ?_, ?_, [], rfl, by simp⟩
    · simp only [householderProduct_cons, householderProduct_nil, Matrix.mul_one, hP₀]
    · intro q hq
      rw [List.mem_singleton.1 hq]
      exact ⟨hβ₁, hv₁S⟩
  have hloop := francisWinLoop_inv hm hinv0 (m - p - 3) (by omega)
  set st := ((List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))).foldl
    (fun st t => Id.run (francisChaseStep pure (francisWindow n p m) st t))
    (blockConj p m P₀ H, [(v₀, β₀)]) with hst
  obtain ⟨hB₂, hconj₂, hdata₂, rest, hrest, hrest0⟩ := hloop
  obtain ⟨hvN0, hvN1, hvN2⟩ := francisTri_val (n := n) (k := m - 3) (by omega)
  obtain ⟨⟨v₃, β₃⟩, hvβ₃⟩ : ∃ vβ, Id.run (houseOn pure [(francisTri n (m - 3)).2.1,
      (francisTri n (m - 3)).2.2] (fun i => st.1 i (francisTri n (m - 3)).1)) = vβ :=
    ⟨_, rfl⟩
  have hB₂' : IsFrancisBulge p m ((francisTri n (m - 3)).1 + 1) st.1 := by
    rw [hvN0, show m - 3 + 1 = p + (m - p - 3) + 1 by omega]
    exact hB₂
  obtain ⟨hs₃, hHess', hβ₃, hv₃⟩ := francis_step_last (p := p) (m := m)
    (by rw [hvN1, hvN0]) (by rw [hvN2, hvN0]) (by rw [hvN0]; omega) (by rw [hvN0]; omega) hB₂'
    hvβ₃
  rw [hs₃] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hv₃S : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v₃ i = 0 := fun i hi =>
    hv₃ i (by rw [hvN0]; omega)
  have hall : ∀ q ∈ st.2 ++ [(v₃, β₃)], (q.2 = 0 ∨ q.2 * (q.1 ⬝ᵥ q.1) = 2) ∧
      ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hdata₂ q hq
    · rw [List.mem_singleton.1 hq]; exact ⟨hβ₃, hv₃S⟩
  refine ⟨householderProduct_mem_orthogonalGroup fun q hq => (hall q hq).1,
    isBlockSupported_householderProduct fun q hq => (hall q hq).2,
    fun q hq => (hall q hq).2, ?_, hHess',
    v₀, β₀, rest ++ [(v₃, β₃)], by rw [hrest]; rfl, ?_, hβ₁, hPu₀⟩
  · rw [hconj₂, blockConj_blockConj (isBlockSupported_reflector β₃ hv₃S),
      householderProduct_concat]
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hrest0 q hq
    · rw [List.mem_singleton.1 hq]
      exact fun i hi => hv₃ i (Or.inl (by rw [hvN0]; omega))

/-- **Algorithm 7.5.1** of [golub2013matrix] on a window, as Algorithm 7.5.2 runs it on the
unreduced block $H_{22}$. Let $H \in \mathbb{R}^{n \times n}$ be upper Hessenberg, and let
$p + N + 3 \le n$. Let $(H', \mathrm{data})$ be the exact run of Algorithm 7.5.1 on the window
$[p, p + N + 3)$, and let $Z$ be the product of the reflectors in data. Then:
* $Z$ is orthogonal and acts on the window only;
* $H'$ is the block similarity by $Z$ of $H$: $H'$ equals $Z^T H Z$ on the block $H_{22}$ and
  $H$ elsewhere;
* $H'$ is upper Hessenberg;
* every reflector vector vanishes outside the window;
* if $H_{22}$ is unreduced, then $Z$ performs a Francis step on $H_{22}$.

$Z$ is `GolubVanLoan.Chapter05.householderProduct data`, the block similarity is
`GolubVanLoan.Chapter07.blockConj`, and the last statement is
`GolubVanLoan.Chapter07.IsFrancisStepOn`. In the unreduced case, the first reflector maps the
first column of $(H_{22} - a_1 I)(H_{22} - a_2 I)$ to a multiple of $e_1$ and the other
reflectors fix $e_1$, so that `GolubVanLoan.Chapter07.isFrancisStep_of_first_reflector` applies
to the window blocks. -/
theorem algorithm_7_5_1_window {p N : ℕ} (hm : p + (N + 3) ≤ n)
    {H H' : Matrix (Fin n) (Fin n) ℝ} {data : List ((Fin n → ℝ) × ℝ)}
    (hH : H.IsUpperHessenberg)
    (h : Id.run (algorithm_7_5_1 pure (francisWindow n p (p + (N + 3))) H) = (H', data)) :
    householderProduct data ∈ orthogonalGroup (Fin n) ℝ ∧
      IsBlockSupported p (p + (N + 3)) (householderProduct data) ∧
      H' = blockConj p (p + (N + 3)) (householderProduct data) H ∧ H'.IsUpperHessenberg ∧
      (∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + (N + 3)) → q.1 i = 0) ∧
      (IsUnreduced (windowBlock p hm H) → IsFrancisStepOn p N hm H (householderProduct data)) := by
  obtain ⟨hZ, hZS, hsupp, hH', hHess, v₀, β₀, rest, hdata, hrest0, hβ₁, hPu₀⟩ :=
    algorithm_7_5_1_window_aux hm (by omega) hH h
  refine ⟨hZ, hZS, hH', hHess, hsupp, fun hU => ?_⟩
  obtain ⟨ha₀, hb₀, hc₀⟩ := francisTri_val (n := n) (k := p) (by omega)
  obtain ⟨-, hvm, hvl⟩ := francisTri_val (n := n) (k := p + (N + 3) - 3) (by omega)
  set u₀ := Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
    (francisTri n p).2.2 (francisTri n (p + (N + 3) - 3)).2.1
    (francisTri n (p + (N + 3) - 3)).2.2 H) with hu₀
  set Z := householderProduct data with hZdef
  set P₀ : Matrix (Fin n) (Fin n) ℝ := 1 - β₀ • vecMulVec v₀ v₀ with hP₀
  have hP₀S : IsBlockSupported p (p + (N + 3)) P₀ :=
    isBlockSupported_reflector β₀ (hsupp _ (by rw [hdata]; exact List.mem_cons_self))
  have hP₀P₀ : P₀ * P₀ = 1 := by
    refine one_sub_smul_vecMulVec_mul_self_eq_one
      (one_sub_smul_vecMulVec_mem_orthogonalGroup ?_)
    rcases hβ₁ with hb | hb
    · rw [hb, zero_mul]
    · rw [hb, sub_self, mul_zero]
  have hZP : Z *ᵥ Pi.single (windowEmb p hm 0) 1 = P₀ *ᵥ Pi.single (windowEmb p hm 0) 1 := by
    rw [hZdef, hdata, householderProduct_cons, ← mulVec_mulVec,
      householderProduct_mulVec_single fun q hq => hrest0 q hq _ (by simp)]
  -- the window indices of the shift vector
  have hne : ∀ (a : Fin (N + 3)) (x : Fin n) (k : ℕ), (x : ℕ) = p + k → (a : ℕ) ≠ k →
      windowEmb p hm a ≠ x := fun a x k hx hak h' => hak (by
    have := congrArg Fin.val h'
    simp only [val_windowEmb] at this
    omega)
  have eA : windowEmb p hm 0 = (francisTri n p).1 := Fin.ext (by simp [ha₀])
  have eB : windowEmb p hm 1 = (francisTri n p).2.1 := Fin.ext (by simp [hb₀])
  have eC : windowEmb p hm ⟨2, by omega⟩ = (francisTri n p).2.2 := Fin.ext (by simp [hc₀])
  have eM : windowEmb p hm (Fin.last (N + 1)).castSucc = (francisTri n (p + (N + 3) - 3)).2.1 :=
    Fin.ext (by simp [hvm]; omega)
  have eL : windowEmb p hm (Fin.last (N + 2)) = (francisTri n (p + (N + 3) - 3)).2.2 :=
    Fin.ext (by simp [hvl]; omega)
  have hu0 : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < p + (N + 3)) → u₀ i = 0 := by
    intro i hi
    rw [hu₀, francisShiftVector_pure]
    dsimp only
    rw [ite_eq_right (fun h' => hi (by rw [h', ha₀]; omega)),
      ite_eq_right (fun h' => hi (by rw [h', hb₀]; omega)),
      ite_eq_right (fun h' => hi (by rw [h', hc₀]; omega))]
  have hPu : ∀ i, i ≠ windowEmb p hm 0 → (P₀ *ᵥ u₀) i = 0 := by
    intro i hi
    rw [hPu₀]
    dsimp only
    rw [ite_eq_right (fun h' => hi (by rw [h', eA]))]
    split_ifs with hl'
    · rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl'
      rw [hu₀, francisShiftVector_pure]
      simp [hl'.1, hl'.2.1, hl'.2.2]
  obtain ⟨hPP₂, hZP₂, hPu₂⟩ := windowBlock_first_reflector hm hP₀S hP₀P₀ hZP hu0 hPu
  have hG : ((windowBlock p hm Z)ᵀ * windowBlock p hm H *
      windowBlock p hm Z).IsUpperHessenberg := by
    rw [← windowBlock_transpose_mul_mul hm hZS hZS, ← windowBlock_blockConj, ← hH']
    exact isUpperHessenberg_windowBlock hm hHess
  have hMu : (windowBlock p hm H * windowBlock p hm H -
      trailingTrace (windowBlock p hm H) • windowBlock p hm H +
      trailingDet (windowBlock p hm H) • 1).col 0 = u₀ ∘ windowEmb p hm := by
    obtain ⟨fx, fy, fz, frest⟩ := francis_first_column hU.1 (trailingTrace (windowBlock p hm H))
      (trailingDet (windowBlock p hm H))
    funext a
    rw [col_apply, Function.comp_apply, hu₀, francisShiftVector_pure]
    dsimp only
    by_cases a0 : a = 0
    · rw [a0, fx, ite_eq_left eA]
      simp only [trailingTrace, trailingDet, windowBlock_apply, eA, eB, eM, eL]
    rw [ite_eq_right (hne a _ 0 (by rw [ha₀]; rfl) fun h' => a0 (Fin.ext h'))]
    by_cases a1 : a = 1
    · rw [a1, fy, ite_eq_left eB]
      simp only [trailingTrace, windowBlock_apply, eA, eB, eM, eL]
    rw [ite_eq_right (hne a _ 1 hb₀ fun h' => a1 (Fin.ext h'))]
    by_cases a2 : a = ⟨2, by omega⟩
    · rw [a2, fz, ite_eq_left eC]
      simp only [windowBlock_apply, eA, eB, eC]
    rw [ite_eq_right (hne a _ 2 hc₀ fun h' => a2 (Fin.ext h'))]
    refine frest a ?_
    have : (a : ℕ) ≠ 0 := fun h' => a0 (Fin.ext h')
    have : (a : ℕ) ≠ 1 := fun h' => a1 (Fin.ext h')
    have : (a : ℕ) ≠ 2 := fun h' => a2 (Fin.ext h')
    omega
  obtain ⟨htri, -, -⟩ := isFrancisStep_of_first_reflector hU
    (windowBlock_mem_orthogonalGroup hm hZ hZS) hG hPP₂ hZP₂ (by rw [hMu]; exact hPu₂)
  exact ⟨hZ, hZS, hG, htri⟩

end FrancisWindow

/-! ### Algorithm 7.5.1: the specification -/

section FrancisTheorem

variable {N : ℕ}

/-- **Algorithm 7.5.1** of [golub2013matrix], exact semantics. Let $H \in \mathbb{R}^{n \times n}$
with $n \ge 3$ be unreduced upper Hessenberg, and let $s$ and $t$ be the trace and the
determinant of its trailing $2 \times 2$ block, so that
$M = H^2 - sH + tI = (H - a_1 I)(H - a_2 I)$ by (7.5.8). Let $(H', \mathrm{data})$ be the exact
run of the program on the full window, and let $Z$ be the product of the reflectors in data.
Then $Z$ is orthogonal, $H' = Z^T H Z$ is upper Hessenberg, $Z^T M$ is upper triangular, and
$Z e_1$ is a multiple of $M e_1$. So $H'$ is a Francis step of $H$ (`Matrix.IsFrancisStep`).

The size is $n = N + 3$, and $Z$ is `GolubVanLoan.Chapter05.householderProduct data`. The proof
applies `GolubVanLoan.Chapter07.algorithm_7_5_1_window` to the full window: the bulge-chasing
invariant `GolubVanLoan.Chapter07.IsFrancisBulge` gives the similarity, and the implicit-shift
principle `Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval` gives the
triangularity. -/
theorem algorithm_7_5_1_spec {H H' : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    {data : List ((Fin (N + 3) → ℝ) × ℝ)} (hH : IsUnreduced H)
    (h : Id.run (algorithm_7_5_1 pure (List.finRange (N + 3)) H) = (H', data)) :
    let s := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc +
      H (Fin.last (N + 2)) (Fin.last (N + 2))
    let t := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc *
        H (Fin.last (N + 2)) (Fin.last (N + 2)) -
      H (Fin.last (N + 1)).castSucc (Fin.last (N + 2)) *
        H (Fin.last (N + 2)) (Fin.last (N + 1)).castSucc
    householderProduct data ∈ orthogonalGroup (Fin (N + 3)) ℝ ∧
      H' = (householderProduct data)ᵀ * H * householderProduct data ∧ H'.IsUpperHessenberg ∧
      ((householderProduct data)ᵀ * (H * H - s • H + t • 1)).IsUpperTriangular ∧
      (householderProduct data).col 0 ∈ Submodule.span ℝ {(H * H - s • H + t • 1).col 0} ∧
      IsFrancisStep s t H H' := by
  intro s t
  have hHess : H.IsUpperHessenberg := hH.1
  rw [← francisWindow_zero] at h
  obtain ⟨hZo, -, -, hH'eq, hHess', v₀, β₀, rest, hdata, hrest0, hβ₁, hPu₀⟩ :=
    algorithm_7_5_1_window_aux (p := 0) (m := N + 3) le_rfl (by omega) hHess h
  rw [blockConj_zero] at hH'eq
  obtain ⟨hv0, hv1, hv2⟩ := francisTri_val (n := N + 3) (k := 0) (by omega)
  obtain ⟨-, hvm, hvl⟩ := francisTri_val (n := N + 3) (k := N + 3 - 3) (by omega)
  have h0 : (francisTri (N + 3) 0).1 = 0 := Fin.ext (by rw [hv0]; simp)
  have h1 : (francisTri (N + 3) 0).2.1 = 1 := Fin.ext (by rw [hv1]; simp)
  have h2 : (francisTri (N + 3) 0).2.2 = ⟨2, by omega⟩ := Fin.ext (by rw [hv2])
  have hm : (francisTri (N + 3) (N + 3 - 3)).2.1 = (Fin.last (N + 1)).castSucc :=
    Fin.ext (by rw [hvm]; simp only [Fin.val_castSucc, Fin.val_last]; omega)
  have hl : (francisTri (N + 3) (N + 3 - 3)).2.2 = Fin.last (N + 2) :=
    Fin.ext (by rw [hvl]; simp only [Fin.val_last]; omega)
  set u₀ := Id.run (francisShiftVector pure (francisTri (N + 3) 0).1 (francisTri (N + 3) 0).2.1
    (francisTri (N + 3) 0).2.2 (francisTri (N + 3) (N + 3 - 3)).2.1
    (francisTri (N + 3) (N + 3 - 3)).2.2 H) with hu₀
  set Z := householderProduct data with hZ
  set P₀ := 1 - β₀ • vecMulVec v₀ v₀ with hP₀
  -- the first column of `Z`
  have hZcol : Z *ᵥ Pi.single 0 1 = P₀ *ᵥ Pi.single 0 1 := by
    rw [hZ, hdata, householderProduct_cons, ← mulVec_mulVec,
      householderProduct_mulVec_single fun q hq => hrest0 q hq 0 (by simp)]
  set M := H * H - s • H + t • 1 with hM
  have hMu : M.col 0 = u₀ := by
    obtain ⟨fx, fy, fz, frest⟩ := francis_first_column hHess s t
    funext i
    rw [hu₀, francisShiftVector_pure, h0, h1, h2, hm, hl, col_apply]
    by_cases hi0 : i = 0
    · subst hi0; simp only [↓reduceIte]; exact fx
    by_cases hi1 : i = 1
    · subst hi1; simp only [hi0, ↓reduceIte]; exact fy
    by_cases hi2 : i = ⟨2, by omega⟩
    · subst hi2; simp only [hi0, hi1, ↓reduceIte]; exact fz
    · simp only [hi0, hi1, hi2, ↓reduceIte]
      refine frest i ?_
      have : (i : ℕ) ≠ 0 := fun e => hi0 (Fin.ext e)
      have : (i : ℕ) ≠ 1 := fun e => hi1 (Fin.ext e)
      have : (i : ℕ) ≠ 2 := fun e => hi2 (Fin.ext e)
      omega
  -- the first reflector is an involution mapping `u₀` to a multiple of `e₀`
  have hP₀o : P₀ ∈ orthogonalGroup (Fin (N + 3)) ℝ := by
    refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
    rcases hβ₁ with hb | hb
    · rw [hb, zero_mul]
    · rw [hb, sub_self, mul_zero]
  have hPP : P₀ * P₀ = 1 := one_sub_smul_vecMulVec_mul_self_eq_one hP₀o
  set cn := ‖(WithLp.toLp 2 (fun j : {j // j ∈ [(francisTri (N + 3) 0).1,
    (francisTri (N + 3) 0).2.1, (francisTri (N + 3) 0).2.2]} => u₀ j) :
      EuclideanSpace ℝ {j // j ∈ [(francisTri (N + 3) 0).1, (francisTri (N + 3) 0).2.1,
        (francisTri (N + 3) 0).2.2]})‖ with hcn
  have hPu : P₀ *ᵥ u₀ = cn • Pi.single 0 1 := by
    rw [hPu₀]
    funext i
    rw [Pi.smul_apply, Pi.single_apply, h0]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte, smul_zero]
      split_ifs with hl'
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl'
        rw [hu₀, francisShiftVector_pure]
        simp [h0, hl'.1, hl'.2.1, hl'.2.2]
  obtain ⟨htri, hcol, hF⟩ := isFrancisStep_of_first_reflector (s := s) (t := t) hH hZo
    (by rw [← hH'eq]; exact hHess') hPP hZcol fun i hi => by
      rw [← hM, hMu, hPu, Pi.smul_apply, Pi.single_apply, ite_eq_right hi, smul_zero]
  rw [← hH'eq] at hF
  exact ⟨hZo, hH'eq, hHess', htri, hcol, hF⟩

end FrancisTheorem

section FrancisEssential

variable {N : ℕ}

/-- **Section 7.5.5** of [golub2013matrix], the essential uniqueness of the Francis step. The source
says: "we can assert that $Z_1$ essentially equals $Z$ provided that the upper Hessenberg
matrices $Z^T H Z$ and $Z_1^T H Z_1$ are each unreduced." Let $H \in \mathbb{R}^{n \times n}$
with $n \ge 3$ be unreduced upper Hessenberg, let $s$ and $t$ be the trace and the determinant
of its trailing $2 \times 2$ block, and assume that $M = H^2 - sH + tI$ is nonsingular. Let $H'$
be the output of the exact run of Algorithm 7.5.1 on $H$, and let $Z$ be the orthogonal factor
of the explicit QR factorization $M = ZR$ by Gram–Schmidt. Then there is
$D = \operatorname{diag}(d_1, \dots, d_n)$ with every $d_i = \pm 1$ such that
$$H' = D (Z^T H Z) D.$$
If moreover $s = 2 \operatorname{Re}(a)$ and $t = |a|^2$ for some $a \in \mathbb{C}$ that is not
an eigenvalue of $H$, then $H' = D H_2 D$ over $\mathbb{C}$, where $H_2$ is the double-shift QR
step of $H$ with the shifts $a$ and $\bar a$ of (7.5.6)–(7.5.7).

**Typo.** The source cites "Theorem 7.4.3" for this argument. The implicit Q theorem is Theorem
7.4.2 (`GolubVanLoan.Chapter07.theorem_7_4_2`).

$Z$ is `Matrix.qrQ M`, and $H_2$ is the canonical step
`Matrix.doubleShiftQrStep H.complexify a`. The proof applies
`Matrix.IsFrancisStep.eq_diagonal_conj`, which rests on the implicit Q theorem. -/
theorem algorithm_7_5_1_essential {H H' : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    {data : List ((Fin (N + 3) → ℝ) × ℝ)} (hH : IsUnreduced H)
    (h : Id.run (algorithm_7_5_1 pure (List.finRange (N + 3)) H) = (H', data)) :
    let s := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc +
      H (Fin.last (N + 2)) (Fin.last (N + 2))
    let t := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc *
        H (Fin.last (N + 2)) (Fin.last (N + 2)) -
      H (Fin.last (N + 1)).castSucc (Fin.last (N + 2)) *
        H (Fin.last (N + 2)) (Fin.last (N + 1)).castSucc
    IsUnit (H * H - s • H + t • 1).det →
    ∃ d : Fin (N + 3) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
      H' = diagonal d * ((qrQ (H * H - s • H + t • 1))ᵀ * H * qrQ (H * H - s • H + t • 1)) *
        diagonal d ∧
      ∀ a : ℂ, s = 2 * a.re → t = Complex.normSq a → a ∉ spectrum ℂ H.complexify →
        H'.complexify = (diagonal d).complexify * doubleShiftQrStep H.complexify a *
          (diagonal d).complexify := by
  intro s t hM
  obtain ⟨-, -, -, -, -, hF⟩ := algorithm_7_5_1_spec hH h
  obtain ⟨d, hd, hH'⟩ := hF.eq_diagonal_conj hH hM
  refine ⟨d, hd, hH', fun a hs ht ha => ?_⟩
  have hds := (double_shift_real H ha).2.1
  have hMM : H * H - (2 * a.re) • H + Complex.normSq a • 1 = H * H - s • H + t • 1 := by
    rw [hs, ht]
  rw [hds, hMM, hH', complexify_mul, complexify_mul]

end FrancisEssential

/-! ### §7.5.6 The overall process -/

section StandardizeProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 7.5.2** of [golub2013matrix], the last step: the upper triangularization of one
$2 \times 2$ diagonal block with real eigenvalues ("upper triangularize all 2-by-2 diagonal
blocks in $H$ that have real eigenvalues and accumulate the transformations"). The block is
$\begin{bmatrix} w & x \\ y & z \end{bmatrix}$ in the rows and columns $i$ and $j = i + 1$ of
$H$. The program computes $\delta = w - z$ and $d = \delta^2 + 4xy$. If $d \ge 0$, it computes
the eigenvalue $\lambda = (w + z)/2 + \operatorname{sign}(\delta) \sqrt{d} / 2$, its eigenvector
$(x, \lambda - w)$, or $(\lambda - z, y)$ when $x = 0$, and $(c, s) = \mathrm{givens}$ of this
eigenvector by Algorithm 5.1.3. It then applies the rotation to the rows $i, j$ of $H$ over the
columns $\ge i$, to the columns $i, j$ of $H$ over the rows $\le j$, and to the columns $i, j$
of $Q$. If $d < 0$, it does nothing.

**Reading.** The source gives no algorithm for this step. The program is one way to carry it
out.

The state is the pair $(H, Q)$. Every arithmetic operation is rounded, and the comparisons are
exact. The factor $\operatorname{sign}(\delta)$, with $\operatorname{sign}(0) = 1$, is applied
as a copy or a negation, which is exact. It selects the eigenvalue on the side of $w$, which
need not be the eigenvalue of larger modulus. -/
noncomputable def triangularize2x2 (i j : Fin n)
    (HQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let H := HQ.1
  let δ ← rnd (H i i - H j j)
  let d ← rnd ((← rnd (δ * δ)) + (← rnd ((← rnd (4 * H i j)) * H j i)))
  if 0 ≤ d then do
    let m ← rnd ((← rnd (H i i + H j j)) / 2)
    let r ← rnd ((← rnd √d) / 2)
    let lam ← rnd (m + if 0 ≤ δ then r else -r)
    let ab ← if H i j = 0 then do pure ((← rnd (lam - H j j)), H j i)
      else do pure (H i j, (← rnd (lam - H i i)))
    let cs ← algorithm_5_1_3 rnd ab.1 ab.2
    let H ← givensApplyLeft rnd i j cs.1 cs.2 ((List.finRange n).filter fun q => i ≤ q) H
    let H ← givensApplyRight rnd i j cs.1 cs.2 ((List.finRange n).filter fun r => r ≤ j) H
    let Q ← givensApplyRight rnd i j cs.1 cs.2 (List.finRange n) HQ.2
    pure (H, Q)
  else pure HQ

end StandardizeProgram

section Standardize

/-- The entry $(k, j)$ of $G^T M G$, for the plane rotation $G$ in the plane $(j, k)$ with the
entries $c$ and $s$, is $-s (c m_{jj} + s m_{jk}) + c (c m_{kj} + s m_{kk})$. -/
private theorem conj_planeRotation_apply_kj {j k : Fin n} (hjk : j ≠ k) (c s : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k j
      = -s * (c * M j j + s * M j k) + c * (c * M k j + s * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- A plane rotation in the plane $(i, j)$ has a zero entry $(r, q)$ whenever $p(r) \neq p(q)$, for
every block index $p$ with $p(i) = p(j)$. -/
private theorem planeRotation_apply_eq_zero_of_ne {i j : Fin n} (hij : i ≠ j) {p : Fin n → ℕ}
    (hp : p i = p j) (c s : ℝ) {r q : Fin n} (hrq : p r ≠ p q) : planeRotation i j c s r q = 0 := by
  rw [planeRotation_apply hij]
  have hrq' : r ≠ q := fun e => hrq (by rw [e])
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all

/-- **Conjugation by a rotation in the plane of one diagonal block keeps a block triangular
structure**, which is the rest of the quasi-triangular structure in the last step of Algorithm
7.5.2. Let $i \neq j$, let $p$ be a block index with $p(i) = p(j)$, and let $H$ be block upper
triangular for $p$. Then $G^T H G$ is block upper triangular for $p$, where $G$ is the rotation
`GolubVanLoan.Chapter05.givensRotation i j c s` for any $c, s \in \mathbb{R}$. -/
theorem blockTriangular_givens_conj {i j : Fin n} (hij : i ≠ j) {p : Fin n → ℕ} (hp : p i = p j)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.BlockTriangular p) (c s : ℝ) :
    ((givensRotation i j c s)ᵀ * H * givensRotation i j c s).BlockTriangular p := by
  have hG : (givensRotation i j c s).BlockTriangular p := fun r q hqr =>
    planeRotation_apply_eq_zero_of_ne hij hp c (-s) hqr.ne'
  have hGt : (givensRotation i j c s)ᵀ.BlockTriangular p := fun r q hqr => by
    rw [transpose_apply]
    exact planeRotation_apply_eq_zero_of_ne hij hp c (-s) hqr.ne
  exact (hGt.mul hH).mul hG

/-- The rotation $G(i, j, \theta)$ with the entries $c$ and $s$ maps $e_i$ to $c e_i - s e_j$. -/
private theorem givensRotation_mulVec_single {i j : Fin n} (hij : i ≠ j) (c s : ℝ) :
    givensRotation i j c s *ᵥ Pi.single i 1 = c • Pi.single i 1 - s • Pi.single j 1 := by
  funext t
  rw [mulVec_single_one, col_apply, givensRotation, planeRotation_apply hij]
  by_cases hti : t = i
  · subst hti; simp [hij]
  · by_cases htj : t = j
    · subst htj; simp [hij.symm]
    · simp [hti, htj]

/-- The entry $(j, i)$ of $G^T H G$, for the rotation $G$ in the plane $(i, j)$ with the entries $c$
and $s$, is $s (c h_{ii} - s h_{ij}) + c (c h_{ji} - s h_{jj})$. -/
private theorem givens_conj_apply_ji {i j : Fin n} (hij : i ≠ j) (c s : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) j i =
      s * (c * H i i - s * H i j) + c * (c * H j i - s * H j j) := by
  rw [givensRotation, conj_planeRotation_apply_kj hij]
  ring

/-- In exact arithmetic, $\mathrm{givens}(a, 0) = (1, 0)$. -/
private theorem algorithm_5_1_3_pure_zero (a : ℝ) : Id.run (algorithm_5_1_3 pure a 0) = (1, 0) := by
  simp [algorithm_5_1_3]

/-- The rotation with $c = 1$ and $s = 0$ is the identity. -/
private theorem givensRotation_one_zero {i j : Fin n} (hij : i ≠ j) :
    givensRotation i j 1 0 = 1 := by
  ext r q
  rw [givensRotation, planeRotation_apply hij, Matrix.one_apply]
  split_ifs <;> simp_all

/-- If $c^2 + s^2 = 1$, $sa + cb = 0$ and $\begin{bmatrix} w & x \\ y & z \end{bmatrix}
\begin{bmatrix} a \\ b \end{bmatrix} = \lambda \begin{bmatrix} a \\ b \end{bmatrix}$, then the
subdiagonal entry $s (cw - sx) + c (cy - sz)$ of the rotated block vanishes, provided that it
vanishes when $a = b = 0$. -/
private theorem givens_entry_eq_zero {w x y z lam a b c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hz : s * a + c * b = 0) (h1 : w * a + x * b = lam * a) (h2 : y * a + z * b = lam * b)
    (h0 : a = 0 → b = 0 → s * (c * w - s * x) + c * (c * y - s * z) = 0) :
    s * (c * w - s * x) + c * (c * y - s * z) = 0 := by
  set ρ := c * a - s * b with hρ
  have ha : a = ρ * c := by rw [hρ]; linear_combination (-a) * hcs + s * hz
  have hb : b = -ρ * s := by rw [hρ]; linear_combination (-b) * hcs + c * hz
  by_cases hρ0 : ρ = 0
  · exact h0 (by rw [ha, hρ0, zero_mul]) (by rw [hb, hρ0, neg_zero, zero_mul])
  · have e1 : ρ * (w * c - x * s) = ρ * (lam * c) := by
      rw [ha, hb] at h1; linear_combination h1
    have e2 : ρ * (y * c - z * s) = ρ * (-(lam * s)) := by
      rw [ha, hb] at h2; linear_combination h2
    have e1' := mul_left_cancel₀ hρ0 e1
    have e2' := mul_left_cancel₀ hρ0 e2
    linear_combination s * e1' + c * e2'

end Standardize


section GivensUpdates

open GolubVanLoan.Chapter05

/-- Let $i \neq k$, and let cols be a list without repeated index. If $a_{iq} = a_{kq} = 0$ for
every column $q$ outside the list, then the exact row update
`GolubVanLoan.Chapter05.givensApplyLeft` over the list gives the full product
$G(i, k, \theta)^T A$. -/
theorem givensApplyLeft_eq_mul {m p : ℕ} {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    {cols : List (Fin p)} (hcols : cols.Nodup) {A : Matrix (Fin m) (Fin p) ℝ}
    (hA : ∀ q, q ∉ cols → A i q = 0 ∧ A k q = 0) :
    Id.run (givensApplyLeft pure i k c s cols A) = (givensRotation i k c s)ᵀ * A := by
  rw [givensApplyLeft_spec hik c s hcols]
  ext r q
  rw [of_apply]
  split_ifs with hq
  · rfl
  · rw [givensRotation_transpose_mul_apply hik, (hA q hq).1, (hA q hq).2]
    split_ifs with h1 h2
    · subst h1; rw [(hA q hq).1]; ring
    · subst h2; rw [(hA q hq).2]; ring
    · rfl

/-- Let $i \neq k$, and let rows be a list without repeated index. If $a_{ri} = a_{rk} = 0$ for
every row $r$ outside the list, then the exact column update
`GolubVanLoan.Chapter05.givensApplyRight` over the list gives the full product
$A \, G(i, k, \theta)$. -/
theorem givensApplyRight_eq_mul {m p : ℕ} {i k : Fin p} (hik : i ≠ k) (c s : ℝ)
    {rows : List (Fin m)} (hrows : rows.Nodup) {A : Matrix (Fin m) (Fin p) ℝ}
    (hA : ∀ r, r ∉ rows → A r i = 0 ∧ A r k = 0) :
    Id.run (givensApplyRight pure i k c s rows A) = A * givensRotation i k c s := by
  rw [givensApplyRight_spec hik c s hrows]
  ext r q
  rw [of_apply]
  split_ifs with hr
  · rfl
  · rw [mul_givensRotation_apply hik, (hA r hr).1, (hA r hr).2]
    split_ifs with h1 h2
    · subst h1; rw [(hA r hr).1]; ring
    · subst h2; rw [(hA r hr).2]; ring
    · rfl

/-- In exact arithmetic, $\mathrm{givens}(a, b)$ (Algorithm 5.1.3) returns $(c, s)$ with
$c^2 + s^2 = 1$ and $sa + cb = 0$. -/
theorem givens_exact (a b : ℝ) :
    ∃ c s : ℝ, Id.run (algorithm_5_1_3 pure a b) = (c, s) ∧ c ^ 2 + s ^ 2 = 1 ∧
      s * a + c * b = 0 := by
  obtain ⟨h1, h2, -⟩ := algorithm_5_1_3_spec a b
  exact ⟨_, _, rfl, h1, h2⟩

end GivensUpdates

section Standardize2

/-- **Algorithm 7.5.2** of [golub2013matrix], the exact semantics of the last step
`GolubVanLoan.Chapter07.triangularize2x2`. Let $H, Q \in \mathbb{R}^{n \times n}$ and
$j = i + 1$. Assume that the rows $i$ and $j$ of $H$ vanish in the columns $< i$, and that the
columns $i$ and $j$ of $H$ vanish in the rows $> j$, so that the rows and columns $i, j$ form a
diagonal block of a block upper triangular matrix. Let the block be
$\begin{bmatrix} w & x \\ y & z \end{bmatrix}$. Then there are $c, s \in \mathbb{R}$ with
$c^2 + s^2 = 1$ such that, for the rotation $G = G(i, j, \theta)$ with the entries $c$ and $s$:
* the program returns $(G^T H G, QG)$;
* if the block has real eigenvalues, $(w - z)^2 + 4xy \ge 0$, then the entry $(j, i)$ of
  $G^T H G$ is zero;
* if $(w - z)^2 + 4xy < 0$, then the program returns $(H, Q)$ unchanged.

$G$ is `GolubVanLoan.Chapter05.givensRotation i j c s`, which is orthogonal by
`GolubVanLoan.Chapter05.givensRotation_mem_orthogonalGroup`. In the real case the first column
of $G$ is an eigenvector of the block. By `GolubVanLoan.Chapter07.blockTriangular_givens_conj`,
the rotation keeps every block triangular structure in which $i$ and $j$ lie in one block. -/
theorem triangularize2x2_spec {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (H Q : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ q : Fin n, (q : ℕ) < i → H i q = 0 ∧ H j q = 0)
    (hcol : ∀ r : Fin n, (j : ℕ) < r → H r i = 0 ∧ H r j = 0) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      Id.run (triangularize2x2 pure i j (H, Q)) =
        ((givensRotation i j c s)ᵀ * H * givensRotation i j c s, Q * givensRotation i j c s) ∧
      (0 ≤ (H i i - H j j) ^ 2 + 4 * H i j * H j i →
        ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) j i = 0) ∧
      ((H i i - H j j) ^ 2 + 4 * H i j * H j i < 0 →
        Id.run (triangularize2x2 pure i j (H, Q)) = (H, Q)) := by
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  set w := H i i with hw
  set x := H i j with hx
  set y := H j i with hy
  set z := H j j with hz
  set d := (w - z) * (w - z) + 4 * x * y with hd
  set lam := (w + z) / 2 + (if 0 ≤ w - z then √d / 2 else -(√d / 2)) with hlam
  set ab : ℝ × ℝ := if x = 0 then (lam - z, y) else (x, lam - w) with hab
  set cs := Id.run (algorithm_5_1_3 pure ab.1 ab.2) with hcs
  set G := givensRotation i j cs.1 cs.2 with hG
  set rest : ℝ × ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ := fun ab =>
    (Id.run (givensApplyRight pure i j (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).1
      (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).2 ((List.finRange n).filter fun r => r ≤ j)
      (Id.run (givensApplyLeft pure i j (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).1
        (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).2 ((List.finRange n).filter fun q => i ≤ q) H))),
      Id.run (givensApplyRight pure i j (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).1
        (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).2 (List.finRange n) Q)) with hrest
  have hrun : Id.run (triangularize2x2 pure i j (H, Q)) = if 0 ≤ d then rest ab else (H, Q) := by
    rw [hab, apply_ite rest]
    rfl
  by_cases hd0 : 0 ≤ d
  swap
  · refine ⟨1, 0, by norm_num, ?_, fun h => absurd (by rw [hd]; nlinarith) hd0,
      fun _ => by rw [hrun, ite_eq_right hd0]⟩
    rw [hrun, ite_eq_right hd0, givensRotation_one_zero hne, transpose_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_one]
  obtain ⟨hcs1, hcs2, -⟩ := algorithm_5_1_3_spec ab.1 ab.2
  rw [← hcs] at hcs1 hcs2
  refine ⟨cs.1, cs.2, hcs1, ?_, fun _ => ?_, fun h => absurd hd0 (by rw [hd]; nlinarith)⟩
  · rw [hrun, ite_eq_left hd0]
    change (Id.run (givensApplyRight pure i j cs.1 cs.2 ((List.finRange n).filter fun r => r ≤ j)
        (Id.run (givensApplyLeft pure i j cs.1 cs.2 ((List.finRange n).filter fun q => i ≤ q) H))),
        Id.run (givensApplyRight pure i j cs.1 cs.2 (List.finRange n) Q)) = _
    have hL : Id.run (givensApplyLeft pure i j cs.1 cs.2
        ((List.finRange n).filter fun q => i ≤ q) H) = Gᵀ * H :=
      givensApplyLeft_eq_mul hne _ _ ((List.nodup_finRange n).filter _) fun q hq => hrow q (by
        have : ¬ i ≤ q := fun h => hq (List.mem_filter.2 ⟨List.mem_finRange q, decide_eq_true h⟩)
        rw [Fin.le_def] at this
        omega)
    have hR : Id.run (givensApplyRight pure i j cs.1 cs.2
        ((List.finRange n).filter fun r => r ≤ j) (Gᵀ * H)) = Gᵀ * H * G := by
      refine givensApplyRight_eq_mul hne _ _ ((List.nodup_finRange n).filter _) fun r hr => ?_
      have hr' : (j : ℕ) < r := by
        have : ¬ r ≤ j := fun h => hr (List.mem_filter.2 ⟨List.mem_finRange r, decide_eq_true h⟩)
        rw [Fin.le_def] at this
        omega
      have hri : r ≠ i := fun e => by rw [e] at hr'; omega
      have hrj : r ≠ j := fun e => by rw [e] at hr'; omega
      have hrow' : ∀ p, (Gᵀ * H) r p = H r p := fun p => by
        have hGp : (Gᵀ * H) r p = (Gᵀ *ᵥ fun t => H t p) r := rfl
        rw [hGp, givensRotation_transpose_mulVec_apply hne, ite_eq_right hri, ite_eq_right hrj]
      rw [hrow' i, hrow' j]
      exact hcol r hr'
    rw [hL, hR, givensApplyRight_spec_of_forall_mem hne _ _ (List.nodup_finRange n)
      List.mem_finRange]
  · rw [givens_conj_apply_ji hne]
    have hsq := Real.mul_self_sqrt hd0
    have hkey : (lam - w) * (lam - z) = x * y := by
      rw [hlam]
      split_ifs <;> linear_combination (1 / 4 : ℝ) * hsq
    by_cases hx0 : x = 0
    · have hab' : ab = (lam - z, y) := by rw [hab, ite_eq_left hx0]
      rw [hab'] at hcs2 hcs
      refine givens_entry_eq_zero hcs1 hcs2 (lam := lam) ?_ ?_ ?_
      · change w * (lam - z) + x * y = lam * (lam - z)
        rw [hx0] at hkey ⊢
        linear_combination (-1 : ℝ) * hkey
      · change y * (lam - z) + z * y = lam * y
        ring
      · intro _ hy0
        have hy0' : y = 0 := hy0
        have hcs0 : cs = (1, 0) := by
          rw [hcs]
          change Id.run (algorithm_5_1_3 pure (lam - z) y) = (1, 0)
          rw [hy0']
          exact algorithm_5_1_3_pure_zero _
        rw [hcs0]
        change (0 : ℝ) * (1 * w - 0 * x) + 1 * (1 * y - 0 * z) = 0
        rw [hy0']
        ring
    · have hab' : ab = (x, lam - w) := by rw [hab, ite_eq_right hx0]
      rw [hab'] at hcs2
      refine givens_entry_eq_zero hcs1 hcs2 (lam := lam) ?_ ?_ ?_
      · change w * x + x * (lam - w) = lam * x
        ring
      · change y * x + z * (lam - w) = lam * (lam - w)
        linear_combination (-1 : ℝ) * hkey
      · intro ha0
        exact absurd ha0 hx0

end Standardize2

section QRAlgorithm

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The subdiagonal entry above row $i$ is zero or absent: $h_{i,i-1} = 0$ if $0 < i < n$, and the
condition holds if $i = 0$ or $i \ge n$. These are the positions where $H$ splits into diagonal
blocks in Algorithm 7.5.2. The test is a comparison, so the program evaluates it exactly. -/
def SubdiagZero (H : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : Prop :=
  ∀ h : i < n, 0 < i → H ⟨i, h⟩ ⟨i - 1, by omega⟩ = 0

noncomputable instance (H : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : Decidable (SubdiagZero H i) :=
  Classical.dec _

/-- **The start of the trailing quasi-triangular part** of an upper Hessenberg $H$, for the step of
Algorithm 7.5.2 "find the largest nonnegative $q$ … such that $H_{33}$ is upper
quasi-triangular". For the leading $m \times m$ block of $H$ (0-based rows), the value is $0$ if
$m \le 1$. For $m \ge 2$, it is the value for $m - 1$ if $h_{m-1,m-2} = 0$ (a $1 \times 1$ block
closes); otherwise it is the value for $m - 2$ if the subdiagonal entry above row $m - 2$ is
zero or absent (a $2 \times 2$ block closes); otherwise it is $m$. So the value is the first row
of the decoupled quasi-triangular trailing part, and $q$ is $n$ minus `schurTrailingStart H n`. -/
noncomputable def schurTrailingStart (H : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | m + 2 => if SubdiagZero H (m + 1) then schurTrailingStart H (m + 1)
      else if SubdiagZero H m then schurTrailingStart H m else m + 2

/-- **The start of the unreduced block that ends at row $e$**, for the step of Algorithm 7.5.2 "the
smallest non-negative $p$ such that … $H_{22}$ is unreduced": the largest row $r \le e$ whose
subdiagonal entry is zero or absent, which is $0$ if there is no other. -/
noncomputable def unreducedStart (H : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if SubdiagZero H (e + 1) then e + 1 else unreducedStart H e

/-- **One test of the deflation criterion** of Algorithm 7.5.2 on row $i$: for $i \ge 1$, set
$h_{i,i-1}$ to zero if $|h_{i,i-1}| \le \mathrm{tol} \cdot (|h_{ii}| + |h_{i-1,i-1}|)$. For
$i = 0$ nothing is done. The right side is computed with two rounded operations, and the
absolute values and the comparison are exact. -/
noncomputable def qrDeflateStep (tol : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  if 0 < (i : ℕ) then do
    let j : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    let b ← rnd (tol * (← rnd (|H i i| + |H j j|)))
    pure (if |H i j| ≤ b then H.updateRow i (Function.update (H i) j 0) else H)
  else pure H

/-- **The deflation step** of Algorithm 7.5.2, "set to zero all subdiagonal elements that satisfy
$|h_{i,i-1}| \le \mathrm{tol} \cdot (|h_{ii}| + |h_{i-1,i-1}|)$": the test
`GolubVanLoan.Chapter07.qrDeflateStep` on the rows $i = 0, \dots, n - 1$ in turn. -/
noncomputable def qrDeflate (tol : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (qrDeflateStep rnd tol) H

/-- One reflector $(v, \beta)$ of the Francis step on the window $[p, m)$, applied outside the block
$H_{22}$ in Algorithm 7.5.2. With $P = I - \beta v v^T$ on the window, it sets
$Q = Q \operatorname{diag}(I_p, P, I_q)$ (all rows, the window columns), $H_{12} = H_{12} P$
(the rows $< p$) and $H_{23} = P^T H_{23}$ (the columns $\ge m$). -/
noncomputable def francisOffBlockStep (p m : ℕ)
    (HQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (vβ : (Fin n → ℝ) × ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let Q ← householderApplyRight rnd vβ.1 vβ.2 (List.finRange n) (francisWindow n p m) HQ.2
  let H ← householderApplyRight rnd vβ.1 vβ.2
    ((List.finRange n).filter fun (i : Fin n) => (i : ℕ) < p) (francisWindow n p m) HQ.1
  let H ← householderApplyLeft rnd vβ.1 vβ.2 (francisWindow n p m)
    ((List.finRange n).filter fun (j : Fin n) => m ≤ (j : ℕ)) H
  pure (H, Q)

/-- One pass of the `until` loop of Algorithm 7.5.2 on the state $(H, Q, \mathrm{done})$. If done is
set, nothing changes. Otherwise the pass deflates $H$, finds $m = n - q$ by
`GolubVanLoan.Chapter07.schurTrailingStart` and $p$ by `GolubVanLoan.Chapter07.unreducedStart`,
and sets done if $q = n$. If $q < n$, it runs the Francis step (Algorithm 7.5.1) on the window
$[p, m)$ of $H_{22}$ and applies its reflectors to $Q$, $H_{12}$ and $H_{23}$ by
`GolubVanLoan.Chapter07.francisOffBlockStep`. -/
noncomputable def qrPass (tol : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2 then pure st else do
    let H ← qrDeflate rnd tol st.1
    let m := schurTrailingStart H n
    if m = 0 then pure (H, st.2.1, true) else do
      let p := unreducedStart H (m - 1)
      let r ← algorithm_7_5_1 rnd (francisWindow n p m) H
      let HQ ← r.2.foldlM (francisOffBlockStep rnd p m) (r.1, st.2.1)
      pure (HQ.1, HQ.2, false)

/-- The last step of Algorithm 7.5.2 at row $i$: if the rows and columns $i, i+1$ form a
$2 \times 2$ diagonal block, that is, $h_{i+1,i} \neq 0$ while the subdiagonal entries above the
rows $i$ and $i + 2$ are zero or absent, then the step standardizes the block by
`GolubVanLoan.Chapter07.triangularize2x2`. Otherwise it does nothing. -/
noncomputable def standardizeStep (HQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if h : (i : ℕ) + 1 < n then
    if ¬ SubdiagZero HQ.1 (i + 1) ∧ SubdiagZero HQ.1 i ∧ SubdiagZero HQ.1 (i + 2) then
      triangularize2x2 rnd i ⟨(i : ℕ) + 1, h⟩ HQ
    else pure HQ
  else pure HQ

/-- **Algorithm 7.5.2** of [golub2013matrix] (QR algorithm). Given $A \in \mathbb{R}^{n \times n}$
and a tolerance tol greater than the unit roundoff, the algorithm computes the real Schur
canonical form $Q^T A Q = T$.
```
Use Algorithm 7.4.2 to compute the Hessenberg reduction H = U₀ᵀ A U₀, Q = P₁ ⋯ P_{n-2}
until q = n
    Set to zero all subdiagonal elements that satisfy |h_{i,i-1}| ≤ tol·(|h_ii| + |h_{i-1,i-1}|)
    Find the largest nonnegative q and the smallest non-negative p such that
        H = [H₁₁ H₁₂ H₁₃; 0 H₂₂ H₂₃; 0 0 H₃₃]  (sizes p, n-p-q, q)
    where H₃₃ is upper quasi-triangular and H₂₂ is unreduced
    if q < n
        Perform a Francis QR step on H₂₂: H₂₂ = Zᵀ H₂₂ Z
        Q = Q·diag(I_p, Z, I_q);  H₁₂ = H₁₂ Z;  H₂₃ = Zᵀ H₂₃
    end
end
Upper triangularize all 2-by-2 diagonal blocks in H that have real eigenvalues and accumulate
the transformations
```
$H$ is the Hessenberg part (`GolubVanLoan.Chapter07.hessenbergPart`) of the array that Algorithm
7.4.2 returns, and $Q$ is the backward accumulation (§5.1.6) of the reflector data that
Algorithm 7.4.2 returns. The `until` loop is at most `fuel` passes of
`GolubVanLoan.Chapter07.qrPass`, which sets the flag done when $q = n$. The last step runs
`GolubVanLoan.Chapter07.standardizeStep` along the diagonal. The program returns
$(Q, T, \mathrm{done})$.

The program has no hypothesis on tol. Its exact semantics is
`GolubVanLoan.Chapter07.algorithm_7_5_2_spec`. -/
noncomputable def algorithm_7_5_2 (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let r ← algorithm_7_4_2 rnd A
  let Q ← backwardAccumulation rnd r.2
  let st ← (List.range fuel).foldlM (fun st _ => qrPass rnd tol st)
    (hessenbergPart r.1, Q, false)
  let HQ ← (List.finRange n).foldlM (standardizeStep rnd) (st.1, st.2.1)
  pure (HQ.2, HQ.1, st.2.2)

end QRAlgorithm

section QRAlgorithmSpec

/-! ### Algorithm 7.5.2: the partition -/

/-- Row $0$ has no subdiagonal entry above it, so `GolubVanLoan.Chapter07.SubdiagZero H 0` holds. -/
theorem subdiagZero_zero (H : Matrix (Fin n) (Fin n) ℝ) : SubdiagZero H 0 :=
  fun _ h => absurd h (lt_irrefl 0)

/-- A row $i \ge n$ has no subdiagonal entry, so `GolubVanLoan.Chapter07.SubdiagZero H i` holds. -/
theorem subdiagZero_of_le (H : Matrix (Fin n) (Fin n) ℝ) {i : ℕ} (hi : n ≤ i) :
    SubdiagZero H i :=
  fun h => absurd h (by omega)

/-- **The trailing quasi-triangular part found by Algorithm 7.5.2.** Let the subdiagonal entry above
row $k$ be zero or absent, and let $s$ be `schurTrailingStart H k`. Then $s \le k$, and the
subdiagonal entry above row $s$ is zero or absent. For $s < i$ and $i + 1 < k$, the subdiagonal
entries above the rows $i$ and $i + 1$ are not both nonzero, so a Hessenberg $H$ has an upper
quasi-triangular diagonal block in the rows $s, \dots, k - 1$. If $s \neq 0$, then $s \ge 3$ and
the subdiagonal entries above the rows $s - 1$ and $s - 2$ are nonzero. -/
theorem schurTrailingStart_spec (H : Matrix (Fin n) (Fin n) ℝ) :
    ∀ k, SubdiagZero H k → schurTrailingStart H k ≤ k ∧
      SubdiagZero H (schurTrailingStart H k) ∧
      (∀ i, schurTrailingStart H k < i → i + 1 < k → SubdiagZero H i ∨ SubdiagZero H (i + 1)) ∧
      (schurTrailingStart H k ≠ 0 → 3 ≤ schurTrailingStart H k ∧
        ¬ SubdiagZero H (schurTrailingStart H k - 1) ∧
        ¬ SubdiagZero H (schurTrailingStart H k - 2))
  | 0, _ => ⟨le_rfl, subdiagZero_zero H, fun _ _ h => absurd h (by omega), fun h => absurd rfl h⟩
  | 1, _ => ⟨by simp [schurTrailingStart], by simpa [schurTrailingStart] using subdiagZero_zero H,
      fun _ _ h => absurd h (by omega), fun h => absurd (by simp [schurTrailingStart]) h⟩
  | m + 2, hk => by
    rw [schurTrailingStart]
    split_ifs with h1 h2
    · obtain ⟨a, b, c, d⟩ := schurTrailingStart_spec H (m + 1) h1
      refine ⟨by omega, b, fun i hi hik => ?_, d⟩
      by_cases hik' : i + 1 < m + 1
      · exact c i hi hik'
      · right
        rwa [show i + 1 = m + 1 by omega]
    · obtain ⟨a, b, c, d⟩ := schurTrailingStart_spec H m h2
      refine ⟨by omega, b, fun i hi hik => ?_, d⟩
      by_cases hik' : i + 1 < m
      · exact c i hi hik'
      · by_cases him : i + 1 = m
        · right
          rwa [him]
        · left
          rwa [show i = m by omega]
    · have hm : m ≠ 0 := by
        rintro rfl
        exact h2 (subdiagZero_zero H)
      refine ⟨le_rfl, hk, fun i hi hik => absurd hik (by omega), fun _ => ⟨by omega, ?_, ?_⟩⟩
      · simpa using h1
      · simpa using h2

/-- **The unreduced block found by Algorithm 7.5.2.** The row $p$ = `unreducedStart H e` satisfies
$p \le e$, the subdiagonal entry above row $p$ is zero or absent, and the subdiagonal entry
above every row $k$ with $p < k \le e$ is nonzero. -/
theorem unreducedStart_spec (H : Matrix (Fin n) (Fin n) ℝ) :
    ∀ e, unreducedStart H e ≤ e ∧ SubdiagZero H (unreducedStart H e) ∧
      ∀ k, unreducedStart H e < k → k ≤ e → ¬ SubdiagZero H k
  | 0 => ⟨le_rfl, subdiagZero_zero H, fun _ h₁ h₂ => absurd h₂ (by omega)⟩
  | e + 1 => by
    rw [unreducedStart]
    split_ifs with h
    · exact ⟨le_rfl, h, fun _ h₁ h₂ => absurd h₂ (by omega)⟩
    · obtain ⟨a, b, c⟩ := unreducedStart_spec H e
      refine ⟨by omega, b, fun k h₁ h₂ => ?_⟩
      by_cases hk : k = e + 1
      · rwa [hk]
      · exact c k h₁ (by omega)

/-- No two consecutive subdiagonal entries of $H$ are nonzero: for every $i \ge 1$, the subdiagonal
entry above row $i$ or the one above row $i + 1$ is zero or absent. For an upper Hessenberg
matrix this means upper quasi-triangular
(`GolubVanLoan.Chapter07.isQuasiUpperTriangular_of_noTwoSubdiag`). -/
def NoTwoSubdiag (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, 0 < i → SubdiagZero H i ∨ SubdiagZero H (i + 1)

/-- **An upper Hessenberg matrix with no two consecutive nonzero subdiagonal entries is upper
quasi-triangular.** The proof applies `Matrix.isQuasiUpperTriangular_iff_fin`. -/
theorem isQuasiUpperTriangular_of_noTwoSubdiag {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsUpperHessenberg) (h2 : NoTwoSubdiag H) : H.IsQuasiUpperTriangular :=
  isQuasiUpperTriangular_iff_fin.2 ⟨hH, fun i hi => (h2 (i + 1) (by omega)).imp
    (fun h => h (by omega) (by omega)) (fun h => h hi (by omega))⟩

/-! ### Algorithm 7.5.2: the deflation -/

section Deflation

open scoped Matrix.Norms.Frobenius

/-- If $F$ is zero outside the entry $(i, j)$, then $\|F\|_F = |f_{ij}|$. -/
private theorem frobenius_norm_of_eq_zero {F : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n}
    (hF : ∀ r c, ¬ (r = i ∧ c = j) → F r c = 0) : ‖F‖ = ‖F i j‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · intro c _ hc
    rw [hF i c fun h => hc h.2, norm_zero, sq, mul_zero]
  · simp
  · intro r _ hr
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hF r c fun h => hr h.1, norm_zero, sq, mul_zero]
  · simp

/-- In exact arithmetic, the deflation test on a row $i \ge 1$ sets $h_{i,i-1}$ to zero if
$|h_{i,i-1}| \le \mathrm{tol} (|h_{ii}| + |h_{i-1,i-1}|)$ and otherwise leaves $H$ unchanged. On
row $0$ it leaves $H$ unchanged. -/
theorem qrDeflateStep_pure (tol : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Id.run (qrDeflateStep pure tol H i) =
      if 0 < (i : ℕ) then
        if |H i ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩| ≤
            tol * (|H i i| + |H ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
              ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩|) then
          H.updateRow i (Function.update (H i) ⟨(i : ℕ) - 1,
            lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ 0)
        else H
      else H :=
  rfl

/-- **One deflation test of Algorithm 7.5.2, in exact arithmetic.** Let $\mathrm{tol} \ge 0$, and
let $H'$ be the result of the test on row $i$. Then $\|H' - H\|_F \le 2\,\mathrm{tol}\,\|H\|_F$,
every entry of $H'$ equals the entry of $H$ or is $0$, and $H' = H$ if $\mathrm{tol} = 0$.

The change is at most $\mathrm{tol} (|h_{ii}| + |h_{i-1,i-1}|)$, which is at most
$2\,\mathrm{tol}\,\|H\|_F$. -/
theorem qrDeflateStep_spec {tol : ℝ} (htol : 0 ≤ tol) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ‖Id.run (qrDeflateStep pure tol H i) - H‖ ≤ 2 * tol * ‖H‖ ∧
      (∀ r c, Id.run (qrDeflateStep pure tol H i) r c = H r c ∨
        Id.run (qrDeflateStep pure tol H i) r c = 0) ∧
      (tol = 0 → Id.run (qrDeflateStep pure tol H i) = H) := by
  rw [qrDeflateStep_pure]
  set j : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ with hj
  have hH0 : 0 ≤ 2 * tol * ‖H‖ := by positivity
  split_ifs with hi hle
  · have hji : j ≠ i := fun h => by
      have := congrArg Fin.val h
      simp only [hj] at this
      omega
    have happ : ∀ r c, H.updateRow i (Function.update (H i) j 0) r c =
        if r = i ∧ c = j then 0 else H r c := by
      intro r c
      by_cases hr : r = i
      · subst hr
        by_cases hc : c = j
        · subst hc; simp
        · simp [hc]
      · simp [updateRow_apply, hr]
    refine ⟨?_, fun r c => ?_, fun h0 => ?_⟩
    · rw [frobenius_norm_of_eq_zero (i := i) (j := j) fun r c hrc => by
        rw [Matrix.sub_apply, happ, ite_eq_right hrc, sub_self]]
      rw [Matrix.sub_apply, happ, ite_eq_left ⟨rfl, rfl⟩, zero_sub, norm_neg, Real.norm_eq_abs]
      refine hle.trans ?_
      have h1 := norm_entry_le_frobenius_norm H i i
      have h2 := norm_entry_le_frobenius_norm H j j
      rw [Real.norm_eq_abs] at h1 h2
      nlinarith
    · rw [happ]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · subst h0
      have hz : H i j = 0 := abs_nonpos_iff.1 (by simpa using hle)
      ext r c
      rw [happ]
      split_ifs with hrc
      · rw [hrc.1, hrc.2, hz]
      · rfl
  · simpa using hH0
  · simpa using hH0

/-- **The deflation step of Algorithm 7.5.2, in exact arithmetic.** Let $\mathrm{tol} \ge 0$, let
$Q$ and $Z$ be orthogonal, and let $A, E \in \mathbb{R}^{n \times n}$ and $c \in \mathbb{R}$
with $\|E\|_F \le (c - 1) \|A\|_F$, where $E = 0$ if $\mathrm{tol} = 0$. Let $H = Q^T (A + E) Z$
be upper Hessenberg. Then the deflated matrix is $H' = Q^T (A + E') Z$ with
$$\|E'\|_F \le ((1 + 2\,\mathrm{tol})^n c - 1) \|A\|_F,$$
where $E' = 0$ if $\mathrm{tol} = 0$, and $H'$ is upper Hessenberg.

Each of the $n$ tests changes the matrix by at most $2\,\mathrm{tol}$ times its Frobenius norm,
and the given $H$ has $\|H\|_F \le c \|A\|_F$. The QR algorithm has $Z = Q$.
The deflation of $A$ in the QZ algorithm is the same sweep, `GolubVanLoan.Chapter07.qzDeflate`. -/
theorem qrDeflate_spec {tol : ℝ} (htol : 0 ≤ tol) {Q Z : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hZ : Z ∈ orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) {E H : Matrix (Fin n) (Fin n) ℝ} (hHE : H = Qᵀ * (A + E) * Z)
    {c : ℝ} (hE : ‖E‖ ≤ (c - 1) * ‖A‖) (hE0 : tol = 0 → E = 0) (hH : H.IsUpperHessenberg) :
    ∃ E', Id.run (qrDeflate pure tol H) = Qᵀ * (A + E') * Z ∧
      ‖E'‖ ≤ ((1 + 2 * tol) ^ n * c - 1) * ‖A‖ ∧ (tol = 0 → E' = 0) ∧
      (Id.run (qrDeflate pure tol H)).IsUpperHessenberg := by
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hQ
  have hQt := Matrix.transpose_mem_unitaryGroup_iff.2 hQ
  have hZt := Matrix.transpose_mem_unitaryGroup_iff.2 hZ
  have key : ∀ (l : List (Fin n)) (H E : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
      H = Qᵀ * (A + E) * Z → ‖E‖ ≤ (c - 1) * ‖A‖ → (tol = 0 → E = 0) →
        H.IsUpperHessenberg →
      ∃ E', l.foldl (fun H i => Id.run (qrDeflateStep pure tol H i)) H = Qᵀ * (A + E') * Z ∧
        ‖E'‖ ≤ ((1 + 2 * tol) ^ l.length * c - 1) * ‖A‖ ∧ (tol = 0 → E' = 0) ∧
        (l.foldl (fun H i => Id.run (qrDeflateStep pure tol H i)) H).IsUpperHessenberg := by
    intro l
    induction l with
    | nil => exact fun H E c hHE hE hE0 hH => ⟨E, hHE, by simpa using hE, hE0, hH⟩
    | cons i l ih =>
      intro H E c hHE hE hE0 hH
      obtain ⟨hF, hent, hF0⟩ := qrDeflateStep_spec htol H i
      set H' := Id.run (qrDeflateStep pure tol H i) with hH'
      have hHnorm : ‖H‖ = ‖A + E‖ := by
        rw [hHE]
        exact frobenius_norm_orthogonal_mul_mul_orthogonal hQt _ hZ
      have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
      have hE1 : H' = Qᵀ * (A + (E + Q * (H' - H) * Zᵀ)) * Z := by
        have : Qᵀ * (Q * (H' - H) * Zᵀ) * Z = H' - H := by
          rw [show Qᵀ * (Q * (H' - H) * Zᵀ) * Z = (Qᵀ * Q) * (H' - H) * (Zᵀ * Z) by
            simp only [Matrix.mul_assoc], hQQ, (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hZ,
            Matrix.one_mul, Matrix.mul_one]
        rw [← add_assoc, Matrix.mul_add, Matrix.add_mul, ← hHE, this]
        abel
      have hnorm : ‖E + Q * (H' - H) * Zᵀ‖ ≤ ((1 + 2 * tol) * c - 1) * ‖A‖ := by
        have h1 : ‖Q * (H' - H) * Zᵀ‖ = ‖H' - H‖ :=
          frobenius_norm_orthogonal_mul_mul_orthogonal hQ _ hZt
        have h2 : ‖A + E‖ ≤ ‖A‖ + ‖E‖ := norm_add_le _ _
        calc ‖E + Q * (H' - H) * Zᵀ‖ ≤ ‖E‖ + ‖H' - H‖ := by
              rw [← h1]; exact norm_add_le _ _
          _ ≤ (c - 1) * ‖A‖ + 2 * tol * (‖A‖ + (c - 1) * ‖A‖) := by
              rw [hHnorm] at hF
              have : 2 * tol * ‖A + E‖ ≤ 2 * tol * (‖A‖ + (c - 1) * ‖A‖) :=
                mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by positivity)
              linarith
          _ = ((1 + 2 * tol) * c - 1) * ‖A‖ := by ring
      have hHess : H'.IsUpperHessenberg := by
        intro r q hrq
        rcases hent r q with h | h
        · rw [h]; exact hH r q hrq
        · exact h
      obtain ⟨E', h1, h2, h3, h4⟩ := ih H' _ _ hE1 hnorm (fun h0 => by
        rw [hE0 h0, hF0 h0, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]) hHess
      refine ⟨E', h1, ?_, h3, h4⟩
      calc ‖E'‖ ≤ ((1 + 2 * tol) ^ l.length * ((1 + 2 * tol) * c) - 1) * ‖A‖ := h2
        _ = ((1 + 2 * tol) ^ (i :: l).length * c - 1) * ‖A‖ := by
          rw [List.length_cons, pow_succ]; ring
  have := key (List.finRange n) H E c hHE hE hE0 hH
  rw [List.length_finRange] at this
  unfold qrDeflate
  rw [List.idRun_foldlM]
  exact this

/-- **The deflation of Algorithm 7.5.2**, as a relation in exact arithmetic: $H_1$ is $H$ with every
subdiagonal entry $h_{i,i-1}$ that satisfies $|h_{i,i-1}| \le \mathrm{tol} (|h_{ii}| +
|h_{i-1,i-1}|)$ set to zero.

The tests read only entries that the sweep does not change, so the sequential sweep
`GolubVanLoan.Chapter07.qrDeflate` is this simultaneous deflation
(`GolubVanLoan.Chapter07.qrDeflate_isQRDeflation`). -/
def IsQRDeflation (tol : ℝ) (H H₁ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, H₁ i j =
    if (j : ℕ) + 1 = i ∧ |H i j| ≤ tol * (|H i i| + |H j j|) then 0 else H i j

/-- A deflation of an upper Hessenberg matrix is upper Hessenberg. -/
theorem IsQRDeflation.isUpperHessenberg {tol : ℝ} {H H₁ : Matrix (Fin n) (Fin n) ℝ}
    (h : IsQRDeflation tol H H₁) (hH : H.IsUpperHessenberg) : H₁.IsUpperHessenberg := by
  intro i j hij
  rw [h i j]
  split_ifs
  · rfl
  · exact hH i j hij

/-- **The deflation sweep of Algorithm 7.5.2 deflates**: in exact arithmetic, the result of
`GolubVanLoan.Chapter07.qrDeflate` is the simultaneous deflation
`GolubVanLoan.Chapter07.IsQRDeflation` of $H$. -/
theorem qrDeflate_isQRDeflation (tol : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    IsQRDeflation tol H (Id.run (qrDeflate pure tol H)) := by
  have key : ∀ l : List (Fin n), l.Nodup → ∀ G : Matrix (Fin n) (Fin n) ℝ,
      (∀ a, G a a = H a a) → (∀ i ∈ l, ∀ c, G i c = H i c) → ∀ i j,
      (l.foldl (fun H i => Id.run (qrDeflateStep pure tol H i)) G) i j =
        if i ∈ l ∧ (j : ℕ) + 1 = i ∧ |H i j| ≤ tol * (|H i i| + |H j j|) then 0 else G i j := by
    intro l
    induction l with
    | nil => intro _ G _ _ i j; simp
    | cons k l ih =>
      intro hnd G hdiag hrow i j
      obtain ⟨hk, hnd'⟩ := List.nodup_cons.1 hnd
      rw [List.foldl_cons]
      have hG' : ∀ r c, Id.run (qrDeflateStep pure tol G k) r c =
          if r = k ∧ (c : ℕ) + 1 = r ∧ |H r c| ≤ tol * (|H r r| + |H c c|) then 0
          else G r c := by
        intro r c
        rw [qrDeflateStep_pure]
        by_cases hk0 : 0 < (k : ℕ)
        · have hrowk := hrow k List.mem_cons_self
          simp only [hk0, ↓reduceIte, hrowk, hdiag]
          split_ifs with ht h2 h2
          · obtain ⟨hr, hc, -⟩ := h2
            have hcj : c = ⟨(k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ :=
              Fin.ext (by simp only; omega)
            rw [hr, hcj]
            simp [updateRow_apply]
          · rw [updateRow_apply]
            split_ifs with hr
            · rw [hr, Function.update_apply, ite_eq_right]
              intro hcj
              refine h2 ⟨hr, by rw [hcj, hr]; simp only; omega, ?_⟩
              rw [hr, hcj]
              exact ht
            · rfl
          · obtain ⟨hr, hc, ht'⟩ := h2
            have hcj : c = ⟨(k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ :=
              Fin.ext (by simp only; omega)
            rw [hr, hcj] at ht'
            exact absurd ht' ht
          · rfl
        · simp only [hk0, ↓reduceIte]
          rw [ite_eq_right]
          intro h'
          omega
      rw [ih hnd' _ (fun a => by
          rw [hG', ite_eq_right]
          · exact hdiag a
          · intro h'
            omega)
        (fun i' hi' c => by
          rw [hG', ite_eq_right]
          · exact hrow i' (List.mem_cons_of_mem _ hi') c
          · intro h'
            exact hk (h'.1 ▸ hi')),
        hG']
      by_cases hik : i = k
      · subst hik
        simp [hk]
      · simp [hik]
  have := key (List.finRange n) (List.nodup_finRange n) H (fun _ => rfl) (fun _ _ _ => rfl)
  intro i j
  unfold qrDeflate
  rw [List.idRun_foldlM, this]
  simp [List.mem_finRange]

end Deflation

/-! ### Algorithm 7.5.2: the Francis step on $H_{22}$ as a similarity of $H$ -/

section OffBlock

/-- **The off-block updates of Algorithm 7.5.2** for a transformation $Z$ of the window $[p, m)$:
the matrix that equals $HZ$ in the rows $< p$ and the window columns (the block $H_{12} Z$),
equals $Z^T H$ in the window rows and the columns $\ge m$ (the block $Z^T H_{23}$), and equals
$H$ elsewhere. -/
def offBlockConj (p m : ℕ) (Z H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) < p ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) then (H * Z) i j
    else if (p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ m ≤ (j : ℕ) then (Zᵀ * H) i j else H i j

variable {p m : ℕ} {Z : Matrix (Fin n) (Fin n) ℝ}

/-- If $Z$ acts on the window $[p, m)$ and the rows $i$ of $X$ and $Y$ agree on the window, then
$XZ$ and $YZ$ agree at $(i, j)$ for every $j$ in the window. -/
private theorem mul_apply_congr_of_isBlockSupported (hZ : IsBlockSupported p m Z)
    {X Y : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (hj : p ≤ (j : ℕ) ∧ (j : ℕ) < m)
    (hXY : ∀ k : Fin n, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → X i k = Y i k) :
    (X * Z) i j = (Y * Z) i j := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
  · rw [hXY k hk]
  · rw [hZ k j fun h => hk h.1, one_apply_ne fun e => hk (by rw [e]; exact hj), mul_zero,
      mul_zero]

/-- If $Z$ acts on the window $[p, m)$, then a column of $XZ$ outside the window is the same column
of $X$. -/
private theorem mul_apply_of_isBlockSupported (hZ : IsBlockSupported p m Z)
    (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) {j : Fin n}
    (hj : ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)) : (X * Z) i j = X i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j, hZ j j fun h => hj h.2, one_apply_eq, mul_one]
  · intro k _ hk
    rw [hZ k j fun h => hj h.2, one_apply_ne hk, mul_zero]
  · simp

/-- If $Z$ acts on the window $[p, m)$ and the columns $j$ of $X$ and $Y$ agree on the window, then
$Z^T X$ and $Z^T Y$ agree at $(i, j)$ for every $i$ in the window. -/
private theorem transpose_mul_apply_congr_of_isBlockSupported (hZ : IsBlockSupported p m Z)
    {X Y : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m)
    (hXY : ∀ k : Fin n, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → X k j = Y k j) :
    (Zᵀ * X) i j = (Zᵀ * Y) i j := by
  simp only [Matrix.mul_apply, transpose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
  · rw [hXY k hk]
  · rw [hZ k i fun h => hk h.1, one_apply_ne fun e => hk (by rw [e]; exact hi), zero_mul,
      zero_mul]

/-- If $Z$ acts on the window $[p, m)$, then a row of $Z^T X$ outside the window is the same row of
$X$. -/
private theorem transpose_mul_apply_of_isBlockSupported (hZ : IsBlockSupported p m Z)
    (X : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (j : Fin n)
    (hi : ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m)) : (Zᵀ * X) i j = X i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i, transpose_apply, hZ i i fun h => hi h.1,
    one_apply_eq, one_mul]
  · intro k _ hk
    rw [transpose_apply, hZ k i fun h => hi h.2, one_apply_ne hk, zero_mul]
  · simp

/-- For $Z = I$, the off-block updates leave $H$ unchanged. -/
theorem offBlockConj_one (p m : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) :
    offBlockConj p m 1 H = H := by
  ext i j
  simp only [offBlockConj, of_apply, Matrix.mul_one, transpose_one, Matrix.one_mul]
  split_ifs <;> rfl

/-- For every $Z$, the off-block updates of an upper Hessenberg matrix give an upper Hessenberg
matrix, since they change only entries above the diagonal. -/
theorem isUpperHessenberg_offBlockConj {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg)
    (p m : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) : (offBlockConj p m Z H).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff_fin] at hH ⊢
  intro i j hij
  simp only [GolubVanLoan.Chapter07.offBlockConj, of_apply]
  rw [ite_eq_right (fun h => by omega), ite_eq_right (fun h => by omega)]
  exact hH i j hij

/-- **One reflector of the off-block updates**, in exact arithmetic. Let $P = I - \beta v v^T$,
where $v$ vanishes outside the window $[p, m)$. Then
`GolubVanLoan.Chapter07.francisOffBlockStep` maps the state `(offBlockConj p m Z H, Q)` to
`(offBlockConj p m (Z * P) H, Q * P)`. -/
theorem francisOffBlockStep_pure {v : Fin n → ℝ} (β : ℝ)
    (hv : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v i = 0)
    (Z H Q : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (francisOffBlockStep pure p m (offBlockConj p m Z H, Q) (v, β)) =
      (offBlockConj p m (Z * (1 - β • vecMulVec v v)) H, Q * (1 - β • vecMulVec v v)) := by
  have hPS : IsBlockSupported p m (1 - β • vecMulVec v v) := isBlockSupported_reflector β hv
  have hPt : (1 - β • vecMulVec v v)ᵀ = 1 - β • vecMulVec v v := by
    ext a b
    simp [vecMulVec_apply, mul_comm, Matrix.one_apply, eq_comm]
  have hvW : ∀ j ∉ francisWindow n p m, v j = 0 := fun j hj =>
    hv j fun h => hj (mem_francisWindow.2 h)
  change (Id.run (householderApplyLeft pure v β (francisWindow n p m)
      ((List.finRange n).filter fun j : Fin n => m ≤ (j : ℕ))
      (Id.run (householderApplyRight pure v β
        ((List.finRange n).filter fun i : Fin n => (i : ℕ) < p) (francisWindow n p m)
        (offBlockConj p m Z H)))),
    Id.run (householderApplyRight pure v β (List.finRange n) (francisWindow n p m) Q)) = _
  rw [householderApplyRight_spec (List.nodup_finRange n) (nodup_francisWindow n p m) hvW,
    householderApplyRight_spec ((List.nodup_finRange n).filter _) (nodup_francisWindow n p m)
      hvW,
    householderApplyLeft_spec (nodup_francisWindow n p m) ((List.nodup_finRange n).filter _) hvW]
  generalize 1 - β • vecMulVec v v = P at hPS hPt ⊢
  set X₀ := GolubVanLoan.Chapter07.offBlockConj p m Z H with hX₀
  have ha : ∀ r c : Fin n, (r : ℕ) < p → (p ≤ (c : ℕ) ∧ (c : ℕ) < m) → X₀ r c = (H * Z) r c :=
    fun r c hr hc => by rw [hX₀, offBlockConj, of_apply, ite_eq_left ⟨hr, hc⟩]
  have hb : ∀ r c : Fin n, (p ≤ (r : ℕ) ∧ (r : ℕ) < m) → m ≤ (c : ℕ) → X₀ r c = (Zᵀ * H) r c :=
    fun r c hr hc => by
      rw [hX₀, offBlockConj, of_apply, ite_eq_right (fun h => by omega), ite_eq_left ⟨hr, hc⟩]
  have hc : ∀ r c : Fin n, ¬ ((r : ℕ) < p ∧ (p ≤ (c : ℕ) ∧ (c : ℕ) < m)) →
      ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ m ≤ (c : ℕ)) → X₀ r c = H r c :=
    fun r c h₁ h₂ => by rw [hX₀, offBlockConj, of_apply, ite_eq_right h₁, ite_eq_right h₂]
  have hL1 : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n), ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) →
      (P * X) i j = X i j := fun X i j hi => by
    have := transpose_mul_apply_of_isBlockSupported hPS X j hi
    rwa [hPt] at this
  have hL2 : ∀ {X Y : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n}, (p ≤ (i : ℕ) ∧ (i : ℕ) < m) →
      (∀ k : Fin n, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → X k j = Y k j) →
      (P * X) i j = (P * Y) i j := fun hi hXY => by
    have := transpose_mul_apply_congr_of_isBlockSupported hPS hi hXY
    rwa [hPt] at this
  refine Prod.ext ?_ ?_
  · ext i j
    simp only [of_apply, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      GolubVanLoan.Chapter07.offBlockConj]
    by_cases hj : m ≤ (j : ℕ)
    · have hjW : ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) := fun h => by omega
      simp only [hj, hjW, and_false, and_true, ↓reduceIte]
      by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
      · simp only [hi, and_self, ↓reduceIte]
        refine (hL2 (Y := Zᵀ * H) hi ?_).trans ?_
        · intro k hk
          have hkp : ¬ (k : ℕ) < p := by omega
          simp only [of_apply, hkp, ↓reduceIte]
          exact hb k j hk hj
        · rw [transpose_mul, hPt, Matrix.mul_assoc]
      · simp only [hi, ↓reduceIte]
        rw [hL1 _ i j hi, of_apply]
        split_ifs with hip
        · rw [mul_apply_of_isBlockSupported hPS _ i hjW]
          exact hc i j (fun h => hjW h.2) (fun h => hi h.1)
        · exact hc i j (fun h => hjW h.2) (fun h => hi h.1)
    · simp only [hj, and_false, ↓reduceIte]
      by_cases hip : (i : ℕ) < p
      · simp only [hip, true_and, ↓reduceIte]
        by_cases hjW : p ≤ (j : ℕ) ∧ (j : ℕ) < m
        · simp only [hjW, and_self, ↓reduceIte]
          rw [mul_apply_congr_of_isBlockSupported hPS (Y := H * Z) hjW fun k hk => ha i k hip hk,
            Matrix.mul_assoc]
        · simp only [hjW, ↓reduceIte]
          rw [mul_apply_of_isBlockSupported hPS _ i hjW]
          exact hc i j (fun h => hjW h.2) (fun h => hj h.2)
      · simp only [hip, false_and, ↓reduceIte]
        exact hc i j (fun h => hip h.1) (fun h => hj h.2)
  · ext i j
    simp [List.mem_finRange]

/-- **The off-block updates of Algorithm 7.5.2**, in exact arithmetic. If every reflector vector of
data vanishes outside the window $[p, m)$, then the fold of
`GolubVanLoan.Chapter07.francisOffBlockStep` over data maps the state
`(offBlockConj p m Z H, Q)` to `(offBlockConj p m (Z * Z') H, Q * Z')`, where $Z'$ is the
product `GolubVanLoan.Chapter05.householderProduct data` of the reflectors. -/
theorem francisOffBlock_foldl {data : List ((Fin n → ℝ) × ℝ)}
    (hdata : ∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0)
    (Z H Q : Matrix (Fin n) (Fin n) ℝ) :
    data.foldl (fun st q => Id.run (francisOffBlockStep pure p m st q))
        (offBlockConj p m Z H, Q) =
      (offBlockConj p m (Z * householderProduct data) H, Q * householderProduct data) := by
  induction data generalizing Z Q with
  | nil => simp [householderProduct_nil]
  | cons q data ih =>
    rcases q with ⟨v, β⟩
    rw [List.foldl_cons, francisOffBlockStep_pure β (hdata _ List.mem_cons_self) Z H Q,
      ih (fun q hq => hdata q (List.mem_cons_of_mem _ hq)), householderProduct_cons,
      Matrix.mul_assoc, Matrix.mul_assoc]

/-- **The off-block updates complete the Francis step to a similarity of the whole $H$.** Let $Z$
act on the window $[p, m)$, and let $h_{ij} = 0$ whenever $i \ge p > j$ or $i \ge m > j$, that
is, $H_{21} = 0$, $H_{31} = 0$ and $H_{32} = 0$. Then the off-block updates by $Z$ of the block
similarity by $Z$ of $H$ give $Z^T H Z$. So the three updates "$H_{22} = Z^T H_{22} Z$,
$H_{12} = H_{12} Z$, $H_{23} = Z^T H_{23}$" of the source together are the similarity by
$\operatorname{diag}(I_p, Z, I_q)$. -/
theorem offBlockConj_blockConj (hZ : IsBlockSupported p m Z) {H : Matrix (Fin n) (Fin n) ℝ}
    (hp : ∀ i j : Fin n, p ≤ (i : ℕ) → (j : ℕ) < p → H i j = 0)
    (hm : ∀ i j : Fin n, m ≤ (i : ℕ) → (j : ℕ) < m → H i j = 0) :
    offBlockConj p m Z (blockConj p m Z H) = Zᵀ * H * Z := by
  have hbc : ∀ i j : Fin n, ¬ ((p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)) →
      blockConj p m Z H i j = H i j := fun i j h => by
    rw [blockConj, of_apply, ite_eq_right h]
  ext i j
  simp only [offBlockConj, of_apply]
  split_ifs with h1 h2
  · have hi : ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) := fun h => by omega
    rw [Matrix.mul_assoc, transpose_mul_apply_of_isBlockSupported hZ _ j hi]
    exact mul_apply_congr_of_isBlockSupported hZ h1.2 fun k _ => hbc i k fun h => hi h.1
  · have hj : ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) := fun h => by omega
    rw [mul_apply_of_isBlockSupported hZ _ i hj]
    exact transpose_mul_apply_congr_of_isBlockSupported hZ h2.1 fun k _ =>
      hbc k j fun h => hj h.2
  · by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
    · by_cases hj : p ≤ (j : ℕ) ∧ (j : ℕ) < m
      · rw [blockConj, of_apply, ite_eq_left ⟨hi, hj⟩]
      · have hjp : (j : ℕ) < p := by omega
        rw [hbc i j (fun h => hj h.2), hp i j hi.1 hjp, mul_apply_of_isBlockSupported hZ _ i hj,
          transpose_mul_apply_congr_of_isBlockSupported hZ (X := H) (Y := 0) hi fun k hk => by
            rw [hp k j hk.1 hjp, Matrix.zero_apply], Matrix.mul_zero, Matrix.zero_apply]
    · rw [hbc i j (fun h => hi h.1), Matrix.mul_assoc,
        transpose_mul_apply_of_isBlockSupported hZ _ j hi]
      by_cases hj : p ≤ (j : ℕ) ∧ (j : ℕ) < m
      · have him : m ≤ (i : ℕ) := by omega
        rw [hm i j him hj.2, mul_apply_congr_of_isBlockSupported hZ (X := H) (Y := 0) hj
          fun k hk => by rw [hm i k him hk.2, Matrix.zero_apply], Matrix.zero_mul,
          Matrix.zero_apply]
      · rw [mul_apply_of_isBlockSupported hZ _ i hj]

end OffBlock

/-! ### Algorithm 7.5.2: the standardization of the $2 \times 2$ blocks -/

section StandardizeSpec

/-- If $j = i + 1$, then the subdiagonal entry above row $j$ is $h_{ji}$:
`GolubVanLoan.Chapter07.SubdiagZero H j` holds if and only if $h_{ji} = 0$. -/
theorem subdiagZero_iff {H : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    SubdiagZero H j ↔ H j i = 0 := by
  constructor
  · intro h
    have := h j.isLt (by omega)
    convert this using 2
    exact Fin.ext (by simp; omega)
  · intro h hj hpos
    convert h using 2
    exact Fin.ext (by simp; omega)

/-- For a rotation $G$ in the plane $(i, j)$, the matrix $G^T H G$ agrees with $H$ outside the rows
and the columns $i$ and $j$. -/
private theorem givens_conj_apply_of_ne {i j : Fin n} (hij : i ≠ j) (c s : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) {r q : Fin n} (hri : r ≠ i) (hrj : r ≠ j) (hqi : q ≠ i)
    (hqj : q ≠ j) :
    ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) r q = H r q := by
  simp only [givensRotation, mul_planeRotation_apply hij, transpose_planeRotation_mul_apply hij,
    hri, hrj, hqi, hqj, ↓reduceIte]

/-- If $H$ is upper Hessenberg with zero subdiagonal entries above the rows $i$ and $i + 2$, then
for every rotation $G$ in the plane $(i, i+1)$, the matrix $G^T H G$ is upper Hessenberg with
zero subdiagonal entries above the rows $i$ and $i + 2$. -/
private theorem givens_conj_hessenberg {i j : Fin n} (hij : (j : ℕ) = i + 1)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg) (hi : SubdiagZero H i)
    (hj : SubdiagZero H (i + 2)) (c s : ℝ) :
    ((givensRotation i j c s)ᵀ * H * givensRotation i j c s).IsUpperHessenberg ∧
      SubdiagZero ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) i ∧
      SubdiagZero ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) (i + 2) := by
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  rw [isUpperHessenberg_iff_fin] at hH
  set b : Fin n → ℕ := fun x => if (x : ℕ) < i then 0 else if (x : ℕ) ≤ j then 1 else 2 with hb
  have hbt : H.BlockTriangular b := by
    intro r q hqr
    by_cases h : (q : ℕ) + 1 < r
    · exact hH r q h
    have key : ((r : ℕ) = i ∧ (q : ℕ) + 1 = i) ∨ ((r : ℕ) = i + 2 ∧ (q : ℕ) = i + 1) := by
      simp only [hb] at hqr
      split_ifs at hqr <;> omega
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hi (by omega) (by omega)
      convert this using 2 <;> exact Fin.ext (by simp; omega)
    · have := hj (by omega) (by omega)
      convert this using 2 <;> exact Fin.ext (by simp; omega)
  have hbij : b i = b j := by
    simp only [hb]
    split_ifs <;> omega
  have hGb := blockTriangular_givens_conj hne hbij hbt c s
  refine ⟨?_, fun h hpos => hGb ?_, fun h hpos => hGb ?_⟩
  · rw [isUpperHessenberg_iff_fin]
    intro r q hrq
    by_cases hlt : b q < b r
    · exact hGb hlt
    have hr : r ≠ i ∧ r ≠ j ∧ q ≠ i ∧ q ≠ j := by
      simp only [hb] at hlt
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> split_ifs at hlt <;> omega
    rw [givens_conj_apply_of_ne hne c s H hr.1 hr.2.1 hr.2.2.1 hr.2.2.2]
    exact hH r q hrq
  · simp only [hb]
    split_ifs <;> omega
  · simp only [hb]
    split_ifs <;> omega

/-- One step of the standardization of Algorithm 7.5.2, in exact arithmetic, maps a state $(H, Q)$
with $Q$ orthogonal and $H = Q^T (A + E) Q$ upper Hessenberg to a state of the same form, and if
no two consecutive subdiagonal entries of $H$ are nonzero, it keeps this property, keeps the
other $2 \times 2$ diagonal blocks, and leaves the block at $k$ either split or with complex
eigenvalues. -/
private theorem standardizeStep_spec {A E H Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hHE : H = Qᵀ * (A + E) * Q) (hH : H.IsUpperHessenberg)
    (k : Fin n) :
    (Id.run (standardizeStep pure (H, Q) k)).2 ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (standardizeStep pure (H, Q) k)).1 =
        (Id.run (standardizeStep pure (H, Q) k)).2ᵀ * (A + E) *
          (Id.run (standardizeStep pure (H, Q) k)).2 ∧
      (Id.run (standardizeStep pure (H, Q) k)).1.IsUpperHessenberg ∧
      (NoTwoSubdiag H → NoTwoSubdiag (Id.run (standardizeStep pure (H, Q) k)).1 ∧
        (∀ i j : Fin n, (j : ℕ) = i + 1 → i ≠ k →
          (Id.run (standardizeStep pure (H, Q) k)).1 j i ≠ 0 →
          (Id.run (standardizeStep pure (H, Q) k)).1 j i = H j i ∧
          (Id.run (standardizeStep pure (H, Q) k)).1 i i = H i i ∧
          (Id.run (standardizeStep pure (H, Q) k)).1 i j = H i j ∧
          (Id.run (standardizeStep pure (H, Q) k)).1 j j = H j j) ∧
        ∀ j : Fin n, (j : ℕ) = k + 1 → (Id.run (standardizeStep pure (H, Q) k)).1 j k ≠ 0 →
          ((Id.run (standardizeStep pure (H, Q) k)).1 k k -
            (Id.run (standardizeStep pure (H, Q) k)).1 j j) ^ 2 +
            4 * (Id.run (standardizeStep pure (H, Q) k)).1 k j *
              (Id.run (standardizeStep pure (H, Q) k)).1 j k < 0) := by
  -- the step does nothing
  have hnone : Id.run (standardizeStep pure (H, Q) k) = (H, Q) →
      (NoTwoSubdiag H → ∀ j : Fin n, (j : ℕ) = k + 1 → H j k ≠ 0 →
        (H k k - H j j) ^ 2 + 4 * H k j * H j k < 0) →
      (Id.run (standardizeStep pure (H, Q) k)).2 ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (standardizeStep pure (H, Q) k)).1 =
        (Id.run (standardizeStep pure (H, Q) k)).2ᵀ * (A + E) *
          (Id.run (standardizeStep pure (H, Q) k)).2 ∧
      (Id.run (standardizeStep pure (H, Q) k)).1.IsUpperHessenberg ∧
      (NoTwoSubdiag H → NoTwoSubdiag (Id.run (standardizeStep pure (H, Q) k)).1 ∧
        (∀ i j : Fin n, (j : ℕ) = i + 1 → i ≠ k →
          (Id.run (standardizeStep pure (H, Q) k)).1 j i ≠ 0 →
          (Id.run (standardizeStep pure (H, Q) k)).1 j i = H j i ∧
          (Id.run (standardizeStep pure (H, Q) k)).1 i i = H i i ∧
          (Id.run (standardizeStep pure (H, Q) k)).1 i j = H i j ∧
          (Id.run (standardizeStep pure (H, Q) k)).1 j j = H j j) ∧
        ∀ j : Fin n, (j : ℕ) = k + 1 → (Id.run (standardizeStep pure (H, Q) k)).1 j k ≠ 0 →
          ((Id.run (standardizeStep pure (H, Q) k)).1 k k -
            (Id.run (standardizeStep pure (H, Q) k)).1 j j) ^ 2 +
            4 * (Id.run (standardizeStep pure (H, Q) k)).1 k j *
              (Id.run (standardizeStep pure (H, Q) k)).1 j k < 0) := by
    intro he hd
    rw [he]
    exact ⟨hQ, hHE, hH, fun h2 => ⟨h2, fun _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩, hd h2⟩⟩
  by_cases hk : (k : ℕ) + 1 < n
  swap
  · refine hnone (by simp [standardizeStep, hk]) fun _ j hj => absurd hj (by omega)
  set j : Fin n := ⟨(k : ℕ) + 1, hk⟩ with hjdef
  have hjk : (j : ℕ) = k + 1 := rfl
  have hne : k ≠ j := fun e => by rw [e] at hjk; omega
  by_cases hc : ¬ SubdiagZero H (k + 1) ∧ SubdiagZero H k ∧ SubdiagZero H (k + 2)
  swap
  · refine hnone (by simp [standardizeStep, hk, hc]) fun h2 j' hj' hj'k => absurd ?_ hc
    have hj'1 : ¬ SubdiagZero H (k + 1) := by rwa [← hj', subdiagZero_iff hj']
    refine ⟨hj'1, ?_, ?_⟩
    · by_cases hk0 : (k : ℕ) = 0
      · rw [hk0]; exact subdiagZero_zero H
      · exact (h2 k (by omega)).resolve_right hj'1
    · exact (h2 (k + 1) (by omega)).resolve_left hj'1
  have hrun : Id.run (standardizeStep pure (H, Q) k) = Id.run (triangularize2x2 pure k j (H, Q)) :=
    by simp [standardizeStep, hk, hc, hjdef]
  rw [isUpperHessenberg_iff_fin] at hH
  have hrow : ∀ q : Fin n, (q : ℕ) < k → H k q = 0 ∧ H j q = 0 := by
    intro q hq
    refine ⟨?_, hH j q (by omega)⟩
    by_cases hq' : (q : ℕ) + 1 < k
    · exact hH k q hq'
    · have := hc.2.1 k.isLt (by omega)
      convert this using 2
      exact Fin.ext (by simp; omega)
  have hcol : ∀ r : Fin n, (j : ℕ) < r → H r k = 0 ∧ H r j = 0 := by
    intro r hr
    refine ⟨hH r k (by omega), ?_⟩
    by_cases hr' : (j : ℕ) + 1 < r
    · exact hH r j hr'
    · have := hc.2.2 (by omega) (by omega)
      convert this using 2 <;> exact Fin.ext (by simp; omega)
  rw [← isUpperHessenberg_iff_fin] at hH
  obtain ⟨c, s, hcs, hrun2, hd0, hdneg⟩ := triangularize2x2_spec hjk H Q hrow hcol
  by_cases hd : 0 ≤ (H k k - H j j) ^ 2 + 4 * H k j * H j k
  swap
  · exact hnone (by rw [hrun, hdneg (not_le.1 hd)]) fun _ j' hj' _ => by
      obtain rfl : j' = j := Fin.ext hj'
      exact not_le.1 hd
  rw [hrun, hrun2]
  set G := givensRotation k j c s with hG
  obtain ⟨hHess, hsk, hsk2⟩ := givens_conj_hessenberg hjk hH hc.2.1 hc.2.2 c s
  have hjz : (Gᵀ * H * G) j k = 0 := hd0 hd
  have hout := fun {r q : Fin n} => givens_conj_apply_of_ne (r := r) (q := q) hne c s H
  refine ⟨mul_mem hQ (givensRotation_mem_orthogonalGroup hne hcs), ?_, hHess, fun h2 => ?_⟩
  · rw [hHE, transpose_mul]
    simp only [Matrix.mul_assoc]
  -- zero subdiagonal entries stay zero
  have hmono : ∀ t, SubdiagZero H t → SubdiagZero (Gᵀ * H * G) t := by
    intro t ht
    by_cases htk : t = k
    · rw [htk]; exact hsk
    by_cases htk1 : t = k + 1
    · rw [htk1, ← hjk, subdiagZero_iff hjk]; exact hjz
    by_cases htk2 : t = k + 2
    · rw [htk2]; exact hsk2
    intro h hpos
    rw [hout (fun e => htk (by rw [← e])) (fun e => htk1 (by rw [← hjk, ← e])) (fun e => by
        have := congrArg Fin.val e; simp at this; omega) (fun e => by
        have := congrArg Fin.val e; simp at this; omega)]
    exact ht h hpos
  refine ⟨fun i hi => (h2 i hi).imp (hmono i) (hmono (i + 1)), fun i' j' hj' hik hne' => ?_,
    fun j' hj' hne' => absurd (by rw [show j' = j from Fin.ext hj']; exact hjz) hne'⟩
  -- a block other than the one at `k` with a nonzero subdiagonal entry is untouched
  have hik1 : (i' : ℕ) + 1 ≠ k := by
    intro e
    exact hne' ((subdiagZero_iff (H := Gᵀ * H * G) (i := i') (j := j') hj').1
      (by rw [hj', e]; exact hsk))
  have hik2 : (i' : ℕ) ≠ k + 1 := by
    intro e
    exact hne' ((subdiagZero_iff (H := Gᵀ * H * G) (i := i') (j := j') hj').1
      (by rw [hj', e]; exact hsk2))
  have hik0 : (i' : ℕ) ≠ k := fun e => hik (Fin.ext e)
  have h1 : i' ≠ k := hik
  have h2' : i' ≠ j := fun e => hik2 (by rw [e])
  have h3 : j' ≠ k := fun e => hik1 (by rw [← hj', e])
  have h4 : j' ≠ j := fun e => hik0 (by have := congrArg Fin.val e; omega)
  exact ⟨hout h3 h4 h1 h2', hout h1 h2' h1 h2', hout h1 h2' h3 h4, hout h3 h4 h3 h4⟩

/-- The standardization of Algorithm 7.5.2 in exact arithmetic, a fold of
`GolubVanLoan.Chapter07.standardizeStep` over a list of rows, keeps the form $H = Q^T (A + E) Q$
upper Hessenberg, and under the condition $D$ that no two consecutive subdiagonal entries are
nonzero, every $2 \times 2$ diagonal block at a row treated before or in the list has complex
eigenvalues. -/
private theorem standardize_foldl {A E : Matrix (Fin n) (Fin n) ℝ} {D : Prop} (l : List (Fin n)) :
    ∀ (H Q : Matrix (Fin n) (Fin n) ℝ) (P : Fin n → Prop),
      Q ∈ orthogonalGroup (Fin n) ℝ → H = Qᵀ * (A + E) * Q → H.IsUpperHessenberg →
      (D → NoTwoSubdiag H ∧ ∀ i j : Fin n, (j : ℕ) = i + 1 → P i → H j i ≠ 0 →
        (H i i - H j j) ^ 2 + 4 * H i j * H j i < 0) →
      (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).2 ∈
          orthogonalGroup (Fin n) ℝ ∧
        (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 =
          (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).2ᵀ * (A + E) *
            (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).2 ∧
        (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1.IsUpperHessenberg ∧
        (D → NoTwoSubdiag (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 ∧
          ∀ i j : Fin n, (j : ℕ) = i + 1 → (P i ∨ i ∈ l) →
            (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 j i ≠ 0 →
            ((l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 i i -
              (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 j j) ^ 2 +
              4 * (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 i j *
                (l.foldl (fun HQ i => Id.run (standardizeStep pure HQ i)) (H, Q)).1 j i < 0) := by
  induction l with
  | nil =>
    intro H Q P hQ hHE hH hD
    refine ⟨hQ, hHE, hH, fun d => ⟨(hD d).1, fun i j hij hPi => ?_⟩⟩
    exact (hD d).2 i j hij (hPi.resolve_right (List.not_mem_nil))
  | cons k l ih =>
    intro H Q P hQ hHE hH hD
    obtain ⟨hQ₁, hHE₁, hH₁, hD₁⟩ := standardizeStep_spec hQ hHE hH k
    rw [List.foldl_cons]
    have := ih _ _ (fun i => P i ∨ i = k) hQ₁ hHE₁ hH₁ fun d => by
      obtain ⟨h2, hdisc⟩ := hD d
      obtain ⟨h2', hsame, hk⟩ := hD₁ h2
      refine ⟨h2', fun i j hij hPi hji => ?_⟩
      rcases hPi with hPi | rfl
      · by_cases hik : i = k
        · subst hik
          exact hk j hij hji
        · obtain ⟨e1, e2, e3, e4⟩ := hsame i j hij hik hji
          rw [e1, e2, e3, e4]
          exact hdisc i j hij hPi (by rw [← e1]; exact hji)
      · exact hk j hij hji
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a, b, c, fun hd => ⟨(d hd).1, fun i j hij hPi => (d hd).2 i j hij ?_⟩⟩
    rcases hPi with hPi | hPi
    · exact Or.inl (Or.inl hPi)
    · rcases List.mem_cons.1 hPi with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

end StandardizeSpec

/-! ### Algorithm 7.5.2: the specification -/

section QRSpec

open scoped Matrix.Norms.Frobenius

/-- In exact arithmetic, Algorithm 7.4.2 gives $H_0 = Q_0^T A Q_0$ upper Hessenberg, where $Q_0$ is
the orthogonal product of its reflectors. -/
private theorem qrInit (A : Matrix (Fin n) (Fin n) ℝ) :
    householderProduct (Id.run (algorithm_7_4_2 pure A)).2 ∈ orthogonalGroup (Fin n) ℝ ∧
      hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1 =
        (householderProduct (Id.run (algorithm_7_4_2 pure A)).2)ᵀ * A *
          householderProduct (Id.run (algorithm_7_4_2 pure A)).2 ∧
      (hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1).IsUpperHessenberg := by
  cases n with
  | zero =>
    exact ⟨(mem_orthogonalGroup_iff (Fin 0) ℝ).2 (by ext i; exact i.elim0),
      by ext i; exact i.elim0, fun i => i.elim0⟩
  | succ N =>
    exact ⟨(algorithm_7_4_2_spec A).1, (algorithm_7_4_2_spec A).2.1, (algorithm_7_4_2_spec A).2.2.1⟩

/-- **The Francis branch of a pass of Algorithm 7.5.2** on the deflated matrix $H_1$, with the
partition
$$H_1 = \begin{bmatrix} H_{11} & H_{12} & H_{13} \\ 0 & H_{22} & H_{23} \\ 0 & 0 & H_{33}
  \end{bmatrix},$$
where $H_{22}$ has the rows and columns $p, \dots, p + N + 2$ (0-based). It holds when the
subdiagonal entries above the rows $p$ and $p + N + 3$ are zero or absent, no two consecutive
subdiagonal entries above the rows $i$ and $i + 1$ with $i > p + N + 3$ are nonzero (so $H_{33}$
is upper quasi-triangular), $H_{22}$ is unreduced, $Z = \operatorname{diag}(I_p, Z_{22}, I_q)$
performs a Francis step on $H_{22}$ (`GolubVanLoan.Chapter07.IsFrancisStepOn`), and $Z^T H_1 Z$
is upper Hessenberg. -/
def IsQRFrancisPass (p N : ℕ) (h : p + (N + 3) ≤ n) (H₁ Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SubdiagZero H₁ p ∧ SubdiagZero H₁ (p + (N + 3)) ∧
    (∀ i, p + (N + 3) < i → SubdiagZero H₁ i ∨ SubdiagZero H₁ (i + 1)) ∧
    IsUnreduced (windowBlock p h H₁) ∧ IsFrancisStepOn p N h H₁ Z ∧
    (Zᵀ * H₁ * Z).IsUpperHessenberg

/-- **One unfinished pass of Algorithm 7.5.2, in exact arithmetic.** Let $H$ be upper Hessenberg,
and let $H_1$ be its deflation by `GolubVanLoan.Chapter07.qrDeflate`. Then the pass on the state
$(H, Q, \mathrm{false})$ does one of two things. Either no two consecutive subdiagonal entries
of $H_1$ are nonzero ($q = n$), and the pass returns $(H_1, Q, \mathrm{true})$. Or the pass
returns $(Z^T H_1 Z, QZ, \mathrm{false})$ for a Francis step
$Z = \operatorname{diag}(I_p, Z_{22}, I_q)$ on the unreduced block $H_{22}$ of $H_1$
(`GolubVanLoan.Chapter07.IsQRFrancisPass`). This is the source's "perform a Francis QR step on
$H_{22}$: $H_{22} = Z^T H_{22} Z$; $Q = Q \operatorname{diag}(I_p, Z, I_q)$;
$H_{12} = H_{12} Z$; $H_{23} = Z^T H_{23}$". -/
theorem qrPass_false_spec (tol : ℝ) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsUpperHessenberg)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    (NoTwoSubdiag (Id.run (qrDeflate pure tol H)) ∧
        Id.run (qrPass pure tol (H, Q, false)) = (Id.run (qrDeflate pure tol H), Q, true)) ∨
      ∃ (p N : ℕ) (h : p + (N + 3) ≤ n) (Z : Matrix (Fin n) (Fin n) ℝ),
        IsQRFrancisPass p N h (Id.run (qrDeflate pure tol H)) Z ∧
        Id.run (qrPass pure tol (H, Q, false)) =
          (Zᵀ * Id.run (qrDeflate pure tol H) * Z, Q * Z, false) := by
  have hrun : Id.run (qrPass pure tol (H, Q, false)) =
      (let H₁ := Id.run (qrDeflate pure tol H)
       if schurTrailingStart H₁ n = 0 then (H₁, Q, true) else
         let p := unreducedStart H₁ (schurTrailingStart H₁ n - 1)
         let r := Id.run (algorithm_7_5_1 pure
           (francisWindow n p (schurTrailingStart H₁ n)) H₁)
         let HQ := Id.run (r.2.foldlM
           (francisOffBlockStep pure p (schurTrailingStart H₁ n)) (r.1, Q))
         (HQ.1, HQ.2, false)) := rfl
  rw [hrun]
  have hH₁ := (qrDeflate_isQRDeflation tol H).isUpperHessenberg hH
  generalize Id.run (qrDeflate pure tol H) = H₁ at hH₁ ⊢
  dsimp only
  obtain ⟨hm_le, hmSZ, hquasi, hm3⟩ :=
    schurTrailingStart_spec H₁ n (subdiagZero_of_le H₁ le_rfl)
  generalize schurTrailingStart H₁ n = m at hm_le hmSZ hquasi hm3 ⊢
  have hq' : ∀ i, m < i → SubdiagZero H₁ i ∨ SubdiagZero H₁ (i + 1) := fun i hi => by
    by_cases hin : i + 1 < n
    · exact hquasi i hi hin
    · exact Or.inr (subdiagZero_of_le H₁ (by omega))
  split_ifs with hm0
  · refine Or.inl ⟨fun i hi => hq' i (by omega), rfl⟩
  obtain ⟨hm3', hm1, hm2⟩ := hm3 hm0
  obtain ⟨hp_le, hpSZ, hpU⟩ := unreducedStart_spec H₁ (m - 1)
  generalize unreducedStart H₁ (m - 1) = p at hp_le hpSZ hpU ⊢
  have hpm : p + 3 ≤ m := by
    have h1 : p ≠ m - 1 := fun e => hm1 (by rw [← e]; exact hpSZ)
    have h2 : p ≠ m - 2 := fun e => hm2 (by rw [← e]; exact hpSZ)
    omega
  obtain ⟨N, rfl⟩ : ∃ N, m = p + (N + 3) := ⟨m - p - 3, by omega⟩
  have : NeZero n := ⟨by omega⟩
  generalize hr : Id.run (algorithm_7_5_1 pure (francisWindow n p (p + (N + 3))) H₁) = r
  obtain ⟨H₂, data⟩ := r
  have hU : IsUnreduced (windowBlock p hm_le H₁) := by
    refine isUnreduced_iff.2 ⟨isUpperHessenberg_windowBlock hm_le hH₁, fun k hk h0 => ?_⟩
    refine hpU (p + k + 1) (by omega) (by omega) fun hlt _ => ?_
    rw [windowBlock_apply] at h0
    convert h0 using 2 <;> exact Fin.ext (by simp only [val_windowEmb]; omega)
  obtain ⟨hZ, hZS, hH₂, hH₂hess, hdata, hF⟩ := algorithm_7_5_1_window hm_le hH₁ hr
  dsimp only
  rw [List.idRun_foldlM]
  have hfold := francisOffBlock_foldl hdata 1 H₂ Q
  rw [offBlockConj_one, Matrix.one_mul] at hfold
  rw [hfold]
  have hH₁' := isUpperHessenberg_iff_fin.1 hH₁
  have hp0 : ∀ i j : Fin n, p ≤ (i : ℕ) → (j : ℕ) < p → H₁ i j = 0 := by
    intro i j hi hj
    by_cases hij : (j : ℕ) + 1 < i
    · exact hH₁' i j hij
    · have hip : (i : ℕ) = p := by omega
      exact (subdiagZero_iff (H := H₁) (i := j) (j := i) (by omega)).1
        (by rw [hip]; exact hpSZ)
  have hm0' : ∀ i j : Fin n, p + (N + 3) ≤ (i : ℕ) → (j : ℕ) < p + (N + 3) → H₁ i j = 0 := by
    intro i j hi hj
    by_cases hij : (j : ℕ) + 1 < i
    · exact hH₁' i j hij
    · have him : (i : ℕ) = p + (N + 3) := by omega
      exact (subdiagZero_iff (H := H₁) (i := j) (j := i) (by omega)).1
        (by rw [him]; exact hmSZ)
  have hconj : offBlockConj p (p + (N + 3)) (householderProduct data) H₂ =
      (householderProduct data)ᵀ * H₁ * householderProduct data := by
    rw [hH₂, offBlockConj_blockConj hZS hp0 hm0']
  refine Or.inr ⟨p, N, hm_le, householderProduct data,
    ⟨hpSZ, hmSZ, hq', hU, hF hU, ?_⟩, by rw [hconj]⟩
  rw [← hconj]
  exact isUpperHessenberg_offBlockConj hH₂hess _ _ _

/-- **One pass of Algorithm 7.5.2 in exact arithmetic**, as a relation between the states
$(H, Q, \mathrm{done})$ before and after. A finished state stays the same. An unfinished state
is deflated to $H_1$ (`GolubVanLoan.Chapter07.IsQRDeflation`). Then either $H_1$ has no two
consecutive nonzero subdiagonal entries and the state becomes $(H_1, Q, \mathrm{true})$, or the
state becomes $(Z^T H_1 Z, QZ, \mathrm{false})$ for a Francis step
$Z = \operatorname{diag}(I_p, Z_{22}, I_q)$ on the unreduced block $H_{22}$ of $H_1$
(`GolubVanLoan.Chapter07.IsQRFrancisPass`). -/
def IsQRPass (tol : ℝ)
    (st st' : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) : Prop :=
  (st.2.2 = true → st' = st) ∧
    (st.2.2 = false → ∃ H₁, IsQRDeflation tol st.1 H₁ ∧
      ((NoTwoSubdiag H₁ ∧ st' = (H₁, st.2.1, true)) ∨
        ∃ (p N : ℕ) (h : p + (N + 3) ≤ n) (Z : Matrix (Fin n) (Fin n) ℝ),
          IsQRFrancisPass p N h H₁ Z ∧ st' = (Zᵀ * H₁ * Z, st.2.1 * Z, false)))

/-- **Algorithm 7.5.2** of [golub2013matrix], the loop body. Let $\mathrm{tol} \in \mathbb{R}$, and
let $(H, Q, \mathrm{done})$ be a state with $H$ upper Hessenberg. Then the exact pass
`GolubVanLoan.Chapter07.qrPass` relates the state to its result by
`GolubVanLoan.Chapter07.IsQRPass`: a finished state is kept, and an unfinished state is deflated
and then either marked as finished or changed by a Francis step on the unreduced block $H_{22}$. -/
theorem qrPass_isQRPass (tol : ℝ)
    {st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool}
    (hH : st.1.IsUpperHessenberg) : IsQRPass tol st (Id.run (qrPass pure tol st)) := by
  obtain ⟨H, Q, d⟩ := st
  cases d with
  | true => exact ⟨fun _ => rfl, fun h => absurd h (by simp)⟩
  | false =>
    refine ⟨fun h => absurd h (by simp), fun _ => ⟨_, qrDeflate_isQRDeflation tol H, ?_⟩⟩
    rcases qrPass_false_spec tol hH Q with h | ⟨p, N, h, Z, hF, hrun⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, N, h, Z, hF, hrun⟩

/-- The invariant of the passes of Algorithm 7.5.2: $Q$ is orthogonal, $H = Q^T (A + E) Q$ is upper
Hessenberg for some $E$ with $\|E\|_F \le (c - 1) \|A\|_F$ and $E = 0$ if $\mathrm{tol} = 0$,
and no two consecutive subdiagonal entries of $H$ are nonzero once done is set. -/
private def QRPassInv (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ st.1.IsUpperHessenberg ∧
    (st.2.2 = true → NoTwoSubdiag st.1) ∧
    ∃ E, st.1 = st.2.1ᵀ * (A + E) * st.2.1 ∧ ‖E‖ ≤ (c - 1) * ‖A‖ ∧ (tol = 0 → E = 0)

/-- One pass of Algorithm 7.5.2 keeps the invariant, with the perturbation factor $c$ multiplied by
$(1 + 2\,\mathrm{tol})^n$ for the deflation, since the Francis step and the off-block updates
are together an exact similarity by $\operatorname{diag}(I_p, Z, I_q)$. -/
private theorem qrPass_inv {tol : ℝ} (htol : 0 ≤ tol) {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hc : 1 ≤ c) {st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool}
    (hst : QRPassInv tol A c st) :
    QRPassInv tol A ((1 + 2 * tol) ^ n * c) (Id.run (qrPass pure tol st)) := by
  obtain ⟨H, Q, d⟩ := st
  obtain ⟨hQ, hH, hdone, E, hHE, hE, hE0⟩ := hst
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  have hpow : 1 ≤ (1 + 2 * tol) ^ n := one_le_pow₀ (by linarith)
  cases d with
  | true =>
    refine ⟨hQ, hH, hdone, E, hHE, hE.trans ?_, hE0⟩
    have : c ≤ (1 + 2 * tol) ^ n * c := le_mul_of_one_le_left (by linarith) hpow
    nlinarith
  | false =>
    obtain ⟨E₁, hH₁E, hE₁, hE₁0, hH₁⟩ := qrDeflate_spec htol hQ hQ A hHE hE hE0 hH
    rcases qrPass_false_spec tol hH Q with ⟨h2, hrun⟩ |
        ⟨p, N, h, Z, ⟨-, -, -, -, ⟨hZ, -⟩, hZH⟩, hrun⟩
    · rw [hrun]
      exact ⟨hQ, hH₁, fun _ => h2, E₁, hH₁E, hE₁, hE₁0⟩
    · rw [hrun]
      refine ⟨mul_mem hQ hZ, hZH, fun h => by simp at h, E₁, ?_, hE₁, hE₁0⟩
      rw [hH₁E, transpose_mul]
      simp only [Matrix.mul_assoc]

/-- The passes of Algorithm 7.5.2 keep the invariant, with the perturbation factor multiplied by
$(1 + 2\,\mathrm{tol})^n$ for each pass. -/
private theorem qrPass_foldl {tol : ℝ} (htol : 0 ≤ tol) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (l : List ℕ) (c : ℝ) (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool),
      1 ≤ c → QRPassInv tol A c st →
      QRPassInv tol A ((1 + 2 * tol) ^ (n * l.length) * c)
        (l.foldl (fun st _ => Id.run (qrPass pure tol st)) st)
  | [], c, st, _, h => by simpa using h
  | a :: l, c, st, hc, h => by
    have hpow : 1 ≤ (1 + 2 * tol) ^ n := one_le_pow₀ (by linarith)
    have := qrPass_foldl htol A l _ _ (one_le_mul_of_one_le_of_one_le hpow hc)
      (qrPass_inv htol hc h)
    rw [List.foldl_cons, show (1 + 2 * tol) ^ (n * (a :: l).length) * c =
      (1 + 2 * tol) ^ (n * l.length) * ((1 + 2 * tol) ^ n * c) by
        rw [List.length_cons, Nat.mul_succ, pow_add]; ring]
    exact this

/-- **Algorithm 7.5.2** of [golub2013matrix] (QR algorithm), exact semantics. Let
$A \in \mathbb{R}^{n \times n}$, $\mathrm{tol} \ge 0$ and $\mathrm{fuel} \in \mathbb{N}$, and
let $(Q, T, \mathrm{done})$ be the exact output of the program with at most fuel passes. Then:
* $Q$ is orthogonal;
* $T = Q^T (A + E) Q$ for some $E$ with $\|E\|_F \le ((1 + 2\,\mathrm{tol})^{n \cdot
  \mathrm{fuel}} - 1) \|A\|_F$, and $E = 0$ if $\mathrm{tol} = 0$;
* $T$ is upper Hessenberg;
* if done is set (the loop ended with $q = n$), then $T$ is upper quasi-triangular, and every
  $2 \times 2$ diagonal block with $t_{ji} \neq 0$, $j = i + 1$, has complex eigenvalues:
  $(t_{ii} - t_{jj})^2 + 4 t_{ij} t_{ji} < 0$. So $T$ is the real Schur form of $A + E$;
* the iteration is the one of the source: there are an orthogonal $Q_0$ with $H_0 = Q_0^T A Q_0$
  upper Hessenberg and states $(H_k, Q_k, \mathrm{done}_k)$ that start at
  $(H_0, Q_0, \mathrm{false})$, each related to the next by a pass
  (`GolubVanLoan.Chapter07.IsQRPass`) for $k < \mathrm{fuel}$, with
  $\mathrm{done}_{\mathrm{fuel}} = \mathrm{done}$ and $(Q, T) = (Q_{\mathrm{fuel}} G, G^T
  H_{\mathrm{fuel}} G)$ for an orthogonal $G$, the final standardization.

**Reading.** The source says that the algorithm computes the real Schur form $Q^T A Q = T$. Each
deflation sets nonzero subdiagonal entries to zero, so even in exact arithmetic $T$ is the real
Schur form of a perturbation $A + E$. Each of the at most $n$ deflations of a pass changes the
matrix by at most $\mathrm{tol} (|h_{ii}| + |h_{i-1,i-1}|) \le 2\,\mathrm{tol}\,\|H\|_F$, and
everything else is an exact orthogonal similarity. The loop of the source need not end; the
program stops after fuel passes, and the flag done says whether the loop ended.

The norm $\|\cdot\|_F$ is the Frobenius norm. -/
theorem algorithm_7_5_2_spec {tol : ℝ} (htol : 0 ≤ tol) (A : Matrix (Fin n) (Fin n) ℝ)
    (fuel : ℕ) {Q T : Matrix (Fin n) (Fin n) ℝ} {done : Bool}
    (h : Id.run (algorithm_7_5_2 pure tol A fuel) = (Q, T, done)) :
    Q ∈ orthogonalGroup (Fin n) ℝ ∧
      (∃ E : Matrix (Fin n) (Fin n) ℝ, T = Qᵀ * (A + E) * Q ∧
        ‖E‖ ≤ ((1 + 2 * tol) ^ (n * fuel) - 1) * ‖A‖ ∧ (tol = 0 → E = 0)) ∧
      T.IsUpperHessenberg ∧
      (done = true → T.IsQuasiUpperTriangular ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 → T j i ≠ 0 →
          (T i i - T j j) ^ 2 + 4 * T i j * T j i < 0) ∧
      ∃ (Q₀ : Matrix (Fin n) (Fin n) ℝ)
        (sts : ℕ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool),
        Q₀ ∈ orthogonalGroup (Fin n) ℝ ∧ (Q₀ᵀ * A * Q₀).IsUpperHessenberg ∧
        sts 0 = (Q₀ᵀ * A * Q₀, Q₀, false) ∧ (∀ k < fuel, IsQRPass tol (sts k) (sts (k + 1))) ∧
        (sts fuel).2.2 = done ∧
        ∃ G ∈ orthogonalGroup (Fin n) ℝ, Q = (sts fuel).2.1 * G ∧ T = Gᵀ * (sts fuel).1 * G := by
  have hrun : Id.run (algorithm_7_5_2 pure tol A fuel) =
      (let r := Id.run (algorithm_7_4_2 pure A)
       let st := Id.run ((List.range fuel).foldlM (fun st _ => qrPass pure tol st)
         (hessenbergPart r.1, Id.run (backwardAccumulation pure r.2), false))
       let HQ := Id.run ((List.finRange n).foldlM (standardizeStep pure) (st.1, st.2.1))
       (HQ.2, HQ.1, st.2.2)) := rfl
  rw [hrun] at h
  dsimp only at h
  rw [List.idRun_foldlM, List.idRun_foldlM, GolubVanLoan.Chapter05.backwardAccumulation_spec]
    at h
  obtain ⟨hQ₀, hH₀E, hH₀⟩ := qrInit A
  have hinit : QRPassInv tol A 1 (hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1,
      householderProduct (Id.run (algorithm_7_4_2 pure A)).2, false) :=
    ⟨hQ₀, hH₀, fun h => by simp at h, 0, by rw [add_zero]; exact hH₀E, by simp,
      fun _ => rfl⟩
  let sts : ℕ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool := fun k =>
    (List.range k).foldl (fun st _ => Id.run (qrPass pure tol st))
      (hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1,
        householderProduct (Id.run (algorithm_7_4_2 pure A)).2, false)
  have hinvk : ∀ k, QRPassInv tol A ((1 + 2 * tol) ^ (n * k)) (sts k) := fun k => by
    have := qrPass_foldl htol A (List.range k) 1 _ le_rfl hinit
    rwa [List.length_range, mul_one] at this
  have hstep : ∀ k, sts (k + 1) = Id.run (qrPass pure tol (sts k)) := fun k => by
    simp only [sts, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hpass := hinvk fuel
  change QRPassInv tol A _ (sts fuel) at hpass
  have hfuel : (List.range fuel).foldl (fun st _ => Id.run (qrPass pure tol st))
      (hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1,
        householderProduct (Id.run (algorithm_7_4_2 pure A)).2, false) = sts fuel := rfl
  rw [hfuel] at h
  generalize hst : sts fuel = st at hpass h
  obtain ⟨hQ, hH, hdone, E, hHE, hE, hE0⟩ := hpass
  have hstd := standardize_foldl (A := A) (E := E) (D := st.2.2 = true) (List.finRange n) st.1
    st.2.1 (fun _ => False) hQ hHE hH fun d => ⟨hdone d, fun _ _ _ h => h.elim⟩
  generalize (List.finRange n).foldl (fun HQ i => Id.run (standardizeStep pure HQ i))
    (st.1, st.2.1) = HQ at hstd h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨hQ', hHE', hH', hD⟩ := hstd
  have hQQ : ∀ X : Matrix (Fin n) (Fin n) ℝ, st.2.1 * (st.2.1ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, (mem_orthogonalGroup_iff (Fin n) ℝ).1 hQ, Matrix.one_mul]
  refine ⟨hQ', ⟨E, hHE', hE, hE0⟩, hH', fun hd =>
    ⟨isQuasiUpperTriangular_of_noTwoSubdiag hH' (hD hd).1,
      fun i j hij hji => (hD hd).2 i j hij (Or.inr (List.mem_finRange i)) hji⟩,
    householderProduct (Id.run (algorithm_7_4_2 pure A)).2, sts, hQ₀, by rw [← hH₀E]; exact hH₀,
    by change (hessenbergPart _, _, false) = _; rw [hH₀E],
    fun k _ => by rw [hstep]; exact qrPass_isQRPass tol (hinvk k).2.1, by rw [hst],
    st.2.1ᵀ * HQ.2, mul_mem (Matrix.transpose_mem_unitaryGroup_iff.2 hQ) hQ', ?_, ?_⟩
  · rw [hst, hQQ]
  · rw [hst, hHE', hHE, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc, hQQ]

end QRSpec

end QRAlgorithmSpec

end GolubVanLoan.Chapter07
