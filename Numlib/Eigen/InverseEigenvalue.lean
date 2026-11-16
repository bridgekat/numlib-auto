/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.QR

/-!
# The resolvent in an eigenbasis and the eigenvector–eigenvalue identity

Let $A$ be a square matrix over a field with an involution, and let $Q$ be unitary with
$Q^H A Q = \operatorname{diag}(d)$. Every entry of the resolvent $(A - \lambda I)^{-1}$ is then a
partial-fraction sum over the rows of $Q$, and every entry of the adjugate of $A - \lambda I$ is the
corresponding polynomial in $\lambda$. For a matrix of order $N + 1$ with indices $0, \dots, N$,
write $A'$ for the trailing principal submatrix, obtained by deleting row $0$ and column $0$;
[golub2013matrix] writes it $A(2{:}n, 2{:}n)$. Cramer's rule gives $((A - \lambda I)^{-1})_{00} =
\det(A' - \lambda I) / \det(A - \lambda I)$. Comparing the two expressions for the $(0, 0)$ entry of
the adjugate at $\lambda = d_i$ gives the **eigenvector–eigenvalue identity**: for a Hermitian $A$
with eigenvalues $\lambda_j$ and $A'$ with eigenvalues $\mu_j$,
$$|Q_{0i}|^2 \prod_{j \neq i} (\lambda_j - \lambda_i) = \prod_j (\mu_j - \lambda_i).$$
Denton, Parke, Tao and Zhang call it by this name; it is equation (8.4.12) of [golub2013matrix]
§8.4.6 read in reverse.

For strictly interlacing data $\lambda_0 > \mu_0 > \lambda_1 > \dots > \mu_{N-1} > \lambda_N$, the
ratios $\prod_j (\mu_j - \lambda_k) / \prod_{j \neq k} (\lambda_j - \lambda_k)$ are positive and sum
to $1$ (Problem P8.4.7 of [golub2013matrix]). So they are the squares of the entries of a unit
vector $d$. This is the basis of the inverse tridiagonal eigenproblem of [golub2013matrix] §8.4.6,
after G. H. Golub, "Some modified matrix eigenvalue problems", SIAM Review 15 (1973): a real
symmetric tridiagonal matrix with eigenvalues $\lambda$ whose trailing principal submatrix has
eigenvalues $\mu$ is obtained by tridiagonalizing $W \Lambda W^T$, for an orthogonal $W$ with first
row $d$.

## Main results

* `Matrix.inv_sub_smul_one_apply_eq_sum`: if $Q^H A Q = \operatorname{diag}(d)$ with $Q$ unitary and
  $\lambda \neq d_i$ for all $i$, then $((A - \lambda I)^{-1})_{jk} = \sum_i Q_{ji}
  \overline{Q_{ki}} / (d_i - \lambda)$; the Hermitian form is
  `Matrix.IsHermitian.inv_sub_apply_eq_sum`.
* `Matrix.adjugate_sub_smul_one_apply_eq_sum`: the polynomial form $\operatorname{adj}(A - \lambda
  I)_{jk} = \sum_i Q_{ji} \overline{Q_{ki}} \prod_{l \neq i} (d_l - \lambda)$, valid for every
  $\lambda$.
* `Matrix.inv_sub_apply_zero_zero_eq_det_div`: $((A - \lambda I)^{-1})_{00} = \det(A' - \lambda I) /
  \det(A - \lambda I)$.
* `Matrix.mul_star_mul_prod_eq_det_submatrix`: $Q_{0i} \overline{Q_{0i}} \prod_{j \neq i} (d_j -
  d_i) = \det(A' - d_i I)$.
* `Matrix.IsHermitian.norm_sq_eigenvector_mul_prod_eq`: the eigenvector–eigenvalue identity.
* `Matrix.prod_sub_div_prod_sub_pos_of_strictInterlace`: the interlacing ratios are positive and sum
  to $1$.
* `Matrix.exists_isTridiagonal_eigenvalues_eq_of_strictInterlace`: for strictly interlacing
  $\lambda$ and $\mu$ there is a real symmetric tridiagonal $T$ with eigenvalues $\lambda$ whose
  trailing principal submatrix has eigenvalues $\mu$.

## Proof outline

The eigenvector–eigenvalue identity comes from the adjugate (`Matrix.adjugate_mul_distrib`,
`Matrix.adjugate_diagonal`). It is an identity of polynomials in $\lambda$, evaluated directly at
$\lambda = \lambda_i$, so no limit and no interpolation argument is needed. The positivity and the
sum rule of the interlacing ratios come from Lagrange interpolation
(`Lagrange.leadingCoeff_eq_sum`). The tridiagonal matrix is built with a unitary that has a
prescribed column, `Matrix.exists_mem_unitaryGroup_mulVec_single_eq` (a scaled Householder
reflector), and the Householder tridiagonalization `Matrix.hessenbergReduce`, whose unitary fixes
$e_0$ (`Matrix.hessenbergQ_apply_zero`).

## Implementation notes

* Indices start at $0$, so the first row and the first column of [golub2013matrix] are row $0$ and
  column $0$ here.
* [golub2013matrix] works with the first *column* of $Q$ in $Q^T \Lambda Q = T$. With
  $T = Q^T \Lambda Q$ the eigenvectors of $T$ are the rows of $Q$, so this column is the first row
  of the eigenvector matrix of $T$. The statements here use the eigenvector matrix of $A$ itself,
  whose first row is `fun i => Q 0 i`.
-/

open Finset Polynomial

namespace Matrix

section Unitary

variable {K : Type*} [Field K] [StarRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $Q$ be unitary and let $M$ be any square matrix. Then $(Q M Q^H)^{-1} = Q M^{-1} Q^H$.

Here $M^{-1}$ is the Lean inverse `Matrix.inv`, which is $0$ for a singular matrix; the identity
holds without invertibility because `Matrix.mul_inv_rev` does and $Q^{-1} = Q^H$. -/
theorem inv_mul_mul_star_of_mem_unitaryGroup {Q : Matrix n n K} (hQ : Q ∈ unitaryGroup n K)
    (M : Matrix n n K) : (Q * M * star Q)⁻¹ = Q * M⁻¹ * star Q := by
  have h1 : Q⁻¹ = star Q := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hQ)
  have h2 : (star Q)⁻¹ = Q := inv_eq_left_inv (mem_unitaryGroup_iff.mp hQ)
  rw [mul_inv_rev, mul_inv_rev, h1, h2, Matrix.mul_assoc]

/-- Let $Q$ be unitary and let $M$ be any square matrix over a field with an involution. Then the
adjugate satisfies
$$\operatorname{adj}(Q M Q^H) = Q \operatorname{adj}(M) Q^H.$$

The proof applies `Matrix.adjugate_mul_distrib` with $\operatorname{adj} Q = \det Q \cdot Q^H$,
$\operatorname{adj} Q^H = \det Q^H \cdot Q$ and $\det Q^H \det Q = 1$. -/
theorem adjugate_mul_mul_star_of_mem_unitaryGroup {Q : Matrix n n K}
    (hQ : Q ∈ unitaryGroup n K) (M : Matrix n n K) :
    adjugate (Q * M * star Q) = Q * adjugate M * star Q := by
  have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hQQ' : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  have hdet : det Q * det (star Q) = 1 := by rw [← det_mul, hQQ', det_one]
  have hadjQ : adjugate Q = det Q • star Q :=
    calc adjugate Q = star Q * Q * adjugate Q := by rw [hQQ, Matrix.one_mul]
      _ = det Q • star Q := by rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul,
          Matrix.mul_one]
  have hadjQ' : adjugate (star Q) = det (star Q) • Q :=
    calc adjugate (star Q) = Q * star Q * adjugate (star Q) := by rw [hQQ', Matrix.one_mul]
      _ = det (star Q) • Q := by rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul,
          Matrix.mul_one]
  rw [adjugate_mul_distrib, adjugate_mul_distrib, hadjQ, hadjQ']
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hdet, one_smul, Matrix.mul_assoc]

variable {A Q : Matrix n n K} {d : n → K}

/-- If $Q$ is unitary and $Q^H A Q = \operatorname{diag}(d)$, then for every scalar $c$
$$A - c I = Q \operatorname{diag}(d_i - c) Q^H.$$
-/
theorem sub_smul_one_eq_mul_diagonal_mul_star (hQ : Q ∈ unitaryGroup n K)
    (hQA : star Q * A * Q = diagonal d) (c : K) :
    A - c • 1 = Q * diagonal (fun i => d i - c) * star Q := by
  have hQQ' : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  have hA : A = Q * diagonal d * star Q := by
    rw [← hQA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul, Matrix.mul_assoc,
      hQQ', Matrix.mul_one]
  have hD : diagonal (fun i => d i - c) = diagonal d - c • 1 := by
    rw [smul_one_eq_diagonal, diagonal_sub]
  rw [hD, Matrix.mul_sub, Matrix.sub_mul, ← hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hQQ']

/-- **The resolvent in an eigenbasis.** Let $Q$ be unitary with $Q^H A Q = \operatorname{diag}(d)$,
and let $c$ be a scalar with $d_i \neq c$ for all $i$. Then for all indices $j$ and $k$
$$((A - c I)^{-1})_{jk} = \sum_i \frac{Q_{ji} \overline{Q_{ki}}}{d_i - c}.$$

At $j = k$ this is the partial-fraction expansion $\sum_i |Q_{ji}|^2 / (d_i - c)$ of equation
(8.4.10) of [golub2013matrix]. The conjugate $\overline{Q_{ki}}$ is `star (Q k i)`. -/
theorem inv_sub_smul_one_apply_eq_sum (hQ : Q ∈ unitaryGroup n K)
    (hQA : star Q * A * Q = diagonal d) {c : K} (hc : ∀ i, d i ≠ c) (j k : n) :
    (A - c • 1)⁻¹ j k = ∑ i, Q j i * star (Q k i) / (d i - c) := by
  have hinv : (diagonal fun i => d i - c)⁻¹ = diagonal fun i => (d i - c)⁻¹ :=
    inv_eq_right_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (sub_ne_zero.mpr (hc i))))
  rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQA, inv_mul_mul_star_of_mem_unitaryGroup hQ,
    hinv, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, star_apply, div_eq_mul_inv]
  ring

/-- **The adjugate in an eigenbasis.** Let $Q$ be unitary with $Q^H A Q = \operatorname{diag}(d)$.
Then for every scalar $c$ and all indices $j$ and $k$
$$\operatorname{adj}(A - c I)_{jk} = \sum_i Q_{ji} \overline{Q_{ki}} \prod_{l \neq i} (d_l -
  c).$$

This is the polynomial form of `Matrix.inv_sub_smul_one_apply_eq_sum`. Unlike that statement, it
also holds when $c$ is one of the $d_i$. -/
theorem adjugate_sub_smul_one_apply_eq_sum (hQ : Q ∈ unitaryGroup n K)
    (hQA : star Q * A * Q = diagonal d) (c : K) (j k : n) :
    adjugate (A - c • 1) j k = ∑ i, Q j i * star (Q k i) * ∏ l ∈ univ.erase i, (d l - c) := by
  rw [sub_smul_one_eq_mul_diagonal_mul_star hQ hQA, adjugate_mul_mul_star_of_mem_unitaryGroup hQ,
    adjugate_diagonal, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_diagonal, star_apply]
  ring

end Unitary

section Cramer

variable {K : Type*} [Field K] {N : ℕ}

/-- For a matrix $A$ of order $N + 1$ and a scalar $c$, the trailing principal submatrix of
$A - c I$ (rows and columns $1, \dots, N$) is $A' - c I$, where $A'$ is the trailing principal
submatrix of $A$. -/
theorem submatrix_succ_sub_smul_one (A : Matrix (Fin (N + 1)) (Fin (N + 1)) K) (c : K) :
    (A - c • 1).submatrix Fin.succ Fin.succ = A.submatrix Fin.succ Fin.succ - c • 1 := by
  ext i j
  simp [Matrix.one_apply, Fin.succ_inj]

/-- **Cramer's rule at the corner.** Let $A$ be a matrix of order $N + 1$ over a field and let $A'$
be its trailing principal submatrix. Then for every scalar $c$
$$((A - c I)^{-1})_{00} = \frac{\det(A' - c I)}{\det(A - c I)}.$$

This is used in [golub2013matrix] §8.4.6. No hypothesis on $c$ is needed: when
$\det(A - c I) = 0$, both sides are $0$, because the Lean inverse of a singular matrix is $0$
(`Matrix.inv_def`) and $x / 0 = 0$. The $(0, 0)$ cofactor is the trailing principal minor
(`Matrix.adjugate_fin_succ_eq_det_submatrix`). -/
theorem inv_sub_apply_zero_zero_eq_det_div (A : Matrix (Fin (N + 1)) (Fin (N + 1)) K) (c : K) :
    (A - c • 1)⁻¹ 0 0 = det (A.submatrix Fin.succ Fin.succ - c • 1) / det (A - c • 1) := by
  rw [inv_def, Matrix.smul_apply, adjugate_fin_succ_eq_det_submatrix, Ring.inverse_eq_inv',
    Fin.succAbove_zero, submatrix_succ_sub_smul_one, smul_eq_mul, div_eq_inv_mul]
  simp

end Cramer

section EigenvectorEigenvalue

variable {K : Type*} [Field K] [StarRing K] {N : ℕ} {A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
  {d : Fin (N + 1) → K}

/-- **The eigenvector–eigenvalue identity, determinant form.** Let $A$ be a matrix of order $N + 1$
over a field with an involution, let $A'$ be its trailing principal submatrix, and let $Q$ be
unitary with $Q^H A Q = \operatorname{diag}(d)$. Then for every index $i$
$$Q_{0i} \overline{Q_{0i}} \prod_{j \neq i} (d_j - d_i) = \det(A' - d_i I).$$

The proof computes the $(0, 0)$ entry of $\operatorname{adj}(A - d_i I)$ in two ways: in the
eigenbasis (`Matrix.adjugate_sub_smul_one_apply_eq_sum`, where every term except the $i$-th has
the factor $d_i - d_i = 0$), and as the trailing principal minor
(`Matrix.adjugate_fin_succ_eq_det_submatrix`). -/
theorem mul_star_mul_prod_eq_det_submatrix (hQ : Q ∈ unitaryGroup (Fin (N + 1)) K)
    (hQA : star Q * A * Q = diagonal d) (i : Fin (N + 1)) :
    Q 0 i * star (Q 0 i) * ∏ j ∈ univ.erase i, (d j - d i) =
      det (A.submatrix Fin.succ Fin.succ - d i • 1) := by
  have h := adjugate_sub_smul_one_apply_eq_sum hQ hQA (d i) 0 0
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, submatrix_succ_sub_smul_one] at h
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul] at h
  rw [h, Finset.sum_eq_single i]
  · intro k _ hk
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hk, Finset.mem_univ i⟩) (sub_self _),
      mul_zero]
  · simp

end EigenvectorEigenvalue

namespace IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Let $M$ be a Hermitian matrix with eigenvalues $\lambda_i$, over $\mathbb{R}$ or $\mathbb{C}$.
Then for every scalar $c$
$$\det(M - c I) = \prod_i (\lambda_i - c).$$

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. The proof evaluates the characteristic
polynomial $\prod_i (X - \lambda_i)$ (`Matrix.IsHermitian.charpoly_eq`) at $c$ and corrects the
sign $(-1)^n$ that comes from $M - c I = -(c I - M)$. -/
theorem det_sub_smul_one_eq_prod {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.IsHermitian) (c : 𝕜) : det (M - c • 1) = ∏ i, ((hM.eigenvalues i : 𝕜) - c) := by
  have h := congrArg (Polynomial.eval c) hM.charpoly_eq
  rw [eval_charpoly, eval_prod] at h
  simp only [eval_sub, eval_X, eval_C] at h
  have hneg : M - c • 1 = -(scalar n c - M) := by
    rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
  rw [hneg, det_neg, h, ← Finset.card_univ, ← Finset.prod_neg]
  simp [neg_sub]

/-- Let $A$ be Hermitian, over $\mathbb{R}$ or $\mathbb{C}$, with eigenvalues $\lambda_i$ and
unitary eigenvector matrix $U$, and let $c$ be a real number that is not an eigenvalue. Then for
all indices $j$ and $k$
$$((A - c I)^{-1})_{jk} = \sum_i \frac{U_{ji} \overline{U_{ki}}}{\lambda_i - c}.$$

This is equation (8.4.10) of [golub2013matrix]. The matrix $U$ is
`Matrix.IsHermitian.eigenvectorUnitary`, and the eigenvalues are
`Matrix.IsHermitian.eigenvalues`. The statement is `Matrix.inv_sub_smul_one_apply_eq_sum` for
this eigenbasis. -/
theorem inv_sub_apply_eq_sum {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, hA.eigenvalues i ≠ c) (j k : n) :
    (A - (c : 𝕜) • 1)⁻¹ j k = ∑ i, (hA.eigenvectorUnitary : Matrix n n 𝕜) j i *
      star ((hA.eigenvectorUnitary : Matrix n n 𝕜) k i) / ((hA.eigenvalues i : 𝕜) - c) := by
  refine inv_sub_smul_one_apply_eq_sum hA.eigenvectorUnitary.2 ?_ (fun i h => hc i ?_) j k
  · exact hA.star_eigenvectorUnitary_mul_mul
  · exact_mod_cast h

/-- **The eigenvector–eigenvalue identity.** Let $A$ be a Hermitian matrix of order $N + 1$, over
$\mathbb{R}$ or $\mathbb{C}$, and let $Q$ be unitary with $Q^H A Q = \operatorname{diag}(l)$ for
real numbers $l_0, \dots, l_N$. Let $\mu_0, \dots, \mu_{N-1}$ be the eigenvalues of the trailing
principal submatrix $A'$. Then for every index $i$
$$|Q_{0i}|^2 \prod_{j \neq i} (l_j - l_i) = \prod_j (\mu_j - l_i).$$

This is equation (8.4.12) of [golub2013matrix] read in reverse; Denton, Parke, Tao and Zhang
call it the eigenvector–eigenvalue identity. The numbers $\mu_j$ are
`Matrix.IsHermitian.eigenvalues` of the Hermitian matrix `A.submatrix Fin.succ Fin.succ`. The
proof is `Matrix.mul_star_mul_prod_eq_det_submatrix` together with
$\det(A' - c I) = \prod_j (\mu_j - c)$ (`Matrix.IsHermitian.det_sub_smul_one_eq_prod`). -/
theorem norm_sq_eigenvector_mul_prod_eq {N : ℕ} {A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜}
    (hA : A.IsHermitian) (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜) {l : Fin (N + 1) → ℝ}
    (hQA : star Q * A * Q = diagonal fun i => (l i : 𝕜)) (i : Fin (N + 1)) :
    ‖Q 0 i‖ ^ 2 * ∏ j ∈ univ.erase i, (l j - l i) =
      ∏ j, ((hA.submatrix Fin.succ).eigenvalues j - l i) := by
  have h := mul_star_mul_prod_eq_det_submatrix hQ hQA i
  rw [(hA.submatrix Fin.succ).det_sub_smul_one_eq_prod, RCLike.star_def, RCLike.mul_conj] at h
  exact_mod_cast h

end IsHermitian

/-- **The interlacing ratios are positive and sum to one.** Let $l_0, \dots, l_N$ and
$\mu_0, \dots, \mu_{N-1}$ be real numbers that interlace strictly,
$$l_0 > \mu_0 > l_1 > \mu_1 > \dots > \mu_{N-1} > l_N,$$
as in (8.4.7) of [golub2013matrix]. Then each ratio
$$r_k = \frac{\prod_j (\mu_j - l_k)}{\prod_{j \neq k} (l_j - l_k)}$$
is positive, and $\sum_k r_k = 1$.

This is Problem P8.4.7 of [golub2013matrix]. The interlacing is stated as $\mu_j < l_j$ and
$l_{j+1} < \mu_j$ for all $j$. For positivity, pair the $j$-th factor of the numerator with the
factor of $l_{j'}$ in the denominator, where $j'$ is the $j$-th index other than $k$
(`Fin.succAbove`); each quotient is a ratio of two positive numbers ($j < k$) or of two negative
numbers ($j \ge k$). The sum is the leading coefficient $1$ of $\prod_j (X - \mu_j)$, by
Lagrange interpolation at the points $l_k$ (`Lagrange.leadingCoeff_eq_sum`). -/
theorem prod_sub_div_prod_sub_pos_of_strictInterlace {N : ℕ} {l : Fin (N + 1) → ℝ}
    {μ : Fin N → ℝ} (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    (∀ k, 0 < (∏ j, (μ j - l k)) / ∏ j ∈ univ.erase k, (l j - l k)) ∧
      ∑ k, (∏ j, (μ j - l k)) / ∏ j ∈ univ.erase k, (l j - l k) = 1 := by
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.mpr fun j => (h₂ j).trans (h₁ j)
  have herase : ∀ k : Fin (N + 1), ∀ f : Fin (N + 1) → ℝ,
      ∏ j ∈ univ.erase k, f j = ∏ j : Fin N, f (k.succAbove j) := fun k f => by
    rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
      Finset.prod_image fun a _ b _ h => Fin.succAbove_right_injective h]
  refine ⟨fun k => ?_, ?_⟩
  · rw [herase, ← Finset.prod_div_distrib]
    refine Finset.prod_pos fun j _ => ?_
    rcases lt_or_ge j.castSucc k with hjk | hjk
    · rw [Fin.succAbove_of_castSucc_lt _ _ hjk]
      have hsk : j.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hjk
      exact div_pos (by linarith [h₂ j, hl.antitone hsk]) (by linarith [hl hjk])
    · rw [Fin.succAbove_of_le_castSucc _ _ hjk]
      exact div_pos_of_neg_of_neg (by linarith [h₁ j, hl.antitone hjk])
        (by linarith [hl (lt_of_le_of_lt hjk Fin.castSucc_lt_succ)])
  · have hP : (∏ j, (X - C (μ j))).leadingCoeff = 1 := (monic_prod_X_sub_C μ univ).leadingCoeff
    have hdeg : ((#(univ : Finset (Fin (N + 1))) : ℕ) : WithBot ℕ) =
        (∏ j, (X - C (μ j))).degree + 1 := by
      rw [degree_eq_natDegree (monic_prod_X_sub_C μ univ).ne_zero,
        natDegree_finsetProd_X_sub_C_eq_card]
      simp
    rw [Lagrange.leadingCoeff_eq_sum (hl.injective.injOn) hdeg] at hP
    rw [← hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    have hnum : ∏ j, (μ j - l k) = (-1) ^ N * ∏ j, (l k - μ j) := by
      have := Finset.prod_neg (s := univ) (fun j => l k - μ j)
      simpa only [neg_sub, card_univ, Fintype.card_fin] using this
    have hden : ∏ j ∈ univ.erase k, (l j - l k) = (-1) ^ N * ∏ j ∈ univ.erase k, (l k - l j) := by
      have := Finset.prod_neg (s := univ.erase k) (fun j => l k - l j)
      simpa only [neg_sub, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
        add_tsub_cancel_right] using this
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

/-- Under strict interlacing, the vector $d$ with entries $d_k = \sqrt{r_k}$, where $r_k$ are the
interlacing ratios of `Matrix.prod_sub_div_prod_sub_pos_of_strictInterlace`, has Euclidean norm
$1$. -/
private theorem norm_sqrt_interlaceRatio {N : ℕ} {l : Fin (N + 1) → ℝ} {μ : Fin N → ℝ}
    (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    ‖(WithLp.toLp 2 (fun k => √((∏ j, (μ j - l k)) / ∏ j ∈ univ.erase k, (l j - l k))) :
      EuclideanSpace ℝ (Fin (N + 1)))‖ = 1 := by
  obtain ⟨hpos, hsum⟩ := prod_sub_div_prod_sub_pos_of_strictInterlace h₁ h₂
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, ← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hpos k).le]

/-- **Golub's inverse tridiagonal eigenproblem.** Let $l_0, \dots, l_N$ and
$\mu_0, \dots, \mu_{N-1}$ be real numbers that interlace strictly,
$l_0 > \mu_0 > l_1 > \dots > \mu_{N-1} > l_N$. Then there is a real symmetric tridiagonal matrix
$T$ of order $N + 1$ with
$$\det(X I - T) = \prod_i (X - l_i), \qquad \det(X I - T') = \prod_j (X - \mu_j),$$
where $T'$ is the trailing principal submatrix of $T$. So $T$ has the eigenvalues $l$, and $T'$
has the eigenvalues $\mu$.

This is the problem of [golub2013matrix] §8.4.6, (8.4.7)–(8.4.9), after G. H. Golub, "Some
modified matrix eigenvalue problems", SIAM Review 15 (1973). The interlacing is stated as
$\mu_j < l_j$ and $l_{j+1} < \mu_j$ for all $j$, and the two conditions on $T$ are
`Matrix.IsSymm` and `Matrix.IsTridiagonal`. The construction follows the source. The vector $d$
with $d_k^2 = \prod_j (\mu_j - l_k) / \prod_{j \neq k} (l_j - l_k)$ is a unit vector
(`Matrix.prod_sub_div_prod_sub_pos_of_strictInterlace`). Take $W$ orthogonal with first row $d$
(`Matrix.exists_mem_unitaryGroup_mulVec_single_eq`) and let $T = Q_1^T (W \Lambda W^T) Q_1$ be
the Householder tridiagonalization, whose $Q_1$ fixes $e_0$ (`Matrix.hessenbergQ_apply_zero`).
Then $Q = Q_1^T W$ diagonalizes $T$ and has first row $d$. The eigenvector–eigenvalue identity
(`Matrix.mul_star_mul_prod_eq_det_submatrix`) gives $\det(T' - l_k I) = \prod_j (\mu_j - l_k)$
at the $N + 1$ distinct points $l_k$, and this determines the characteristic polynomial of $T'$,
which has degree $N$. -/
theorem exists_isTridiagonal_eigenvalues_eq_of_strictInterlace {N : ℕ} {l : Fin (N + 1) → ℝ}
    {μ : Fin N → ℝ} (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    ∃ T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, T.IsSymm ∧ T.IsTridiagonal ∧
      T.charpoly = ∏ i, (X - C (l i)) ∧
        (T.submatrix Fin.succ Fin.succ).charpoly = ∏ j, (X - C (μ j)) := by
  obtain ⟨hpos, -⟩ := prod_sub_div_prod_sub_pos_of_strictInterlace h₁ h₂
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.mpr fun j => (h₂ j).trans (h₁ j)
  obtain ⟨U, hU, hUd⟩ := exists_mem_unitaryGroup_mulVec_single_eq (norm_sqrt_interlaceRatio h₁ h₂) 0
  obtain ⟨W, hW, hWU⟩ : ∃ W, W ∈ unitaryGroup (Fin (N + 1)) ℝ ∧ W = star U :=
    ⟨_, Unitary.star_mem hU, rfl⟩
  have hW0 : ∀ i, W 0 i = √((∏ j, (μ j - l i)) / ∏ j ∈ univ.erase i, (l j - l i)) := fun i => by
    have h := congrFun hUd i
    simp only [mulVec_single_one, col_apply] at h
    rw [hWU, star_apply, star_trivial, h]
  obtain ⟨A, hA⟩ : ∃ A, A = W * diagonal l * star W := ⟨_, rfl⟩
  have hAh : A.IsHermitian := by
    rw [hA, star_eq_conjTranspose]
    exact isHermitian_mul_mul_conjTranspose _ (isHermitian_diagonal l)
  have hQ₁ := hessenbergQ_mem_unitaryGroup A
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = star (hessenbergQ A) * W := ⟨_, rfl⟩
  have hQu : Q ∈ unitaryGroup (Fin (N + 1)) ℝ := hQ ▸ mul_mem (Unitary.star_mem hQ₁) hW
  have hQ₁' : ∀ M, hessenbergQ A * (star (hessenbergQ A) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hQ₁, Matrix.one_mul]
  have hW' : ∀ M, star W * (W * M) = M := fun M => by
    rw [← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hW, Matrix.one_mul]
  have hWA : star W * (A * W) = diagonal l := by
    rw [hA]
    simp only [Matrix.mul_assoc, hW', mem_unitaryGroup_iff'.mp hW, Matrix.mul_one]
  have hQT : star Q * hessenbergReduce A * Q = diagonal l := by
    rw [hessenbergReduce_eq_conj, hQ, star_mul, star_star, ← star_eq_conjTranspose]
    simp only [Matrix.mul_assoc, hQ₁', hWA]
  have hQ0 : ∀ i, Q 0 i = W 0 i := fun i => by
    rw [hQ, Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [star_apply, hessenbergQ_apply_zero, one_apply_eq, star_one, one_mul]
    · intro k _ hk
      rw [star_apply, hessenbergQ_apply_zero, one_apply_ne hk, star_zero, zero_mul]
    · simp
  have hAs : A.IsSymm := by
    have h := hAh
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  refine ⟨hessenbergReduce A, isSymm_hessenbergReduce hAs,
    isTridiagonal_hessenbergReduce_of_isHermitian A hAh, ?_, ?_⟩
  · rw [← charpoly_diagonal, ← hQT, charpoly_mul_comm, ← Matrix.mul_assoc,
      mem_unitaryGroup_iff.mp hQu, Matrix.one_mul]
  have hkey : ∀ k, eval (l k) ((hessenbergReduce A).submatrix Fin.succ Fin.succ).charpoly =
      eval (l k) (∏ j, (X - C (μ j))) := fun k => by
    have hne : ∏ j ∈ univ.erase k, (l j - l k) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hl.injective.ne (ne_of_mem_erase hj))
    have h := mul_star_mul_prod_eq_det_submatrix hQu hQT k
    rw [hQ0, hW0, star_trivial, Real.mul_self_sqrt (hpos k).le, div_mul_cancel₀ _ hne] at h
    have hneg : scalar (Fin N) (l k) - (hessenbergReduce A).submatrix Fin.succ Fin.succ =
        -((hessenbergReduce A).submatrix Fin.succ Fin.succ - l k • 1) := by
      rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
    rw [eval_charpoly, hneg, det_neg, ← h, eval_prod, Fintype.card_fin]
    simp only [eval_sub, eval_X, eval_C]
    rw [show ∏ j, (μ j - l k) = ∏ j, -(l k - μ j) by simp only [neg_sub], Finset.prod_neg,
      card_univ, Fintype.card_fin, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨N, rfl⟩, one_mul]
  have hcard : (#(univ : Finset (Fin (N + 1))) : WithBot ℕ) = N + 1 := by simp
  refine eq_of_degrees_lt_of_eval_index_eq (s := univ) (v := l) hl.injective.injOn ?_ ?_
    fun k _ => hkey k
  · rw [charpoly_degree_eq_dim, Fintype.card_fin, hcard]
    exact_mod_cast Nat.lt_succ_self N
  · rw [degree_eq_natDegree (monic_prod_X_sub_C μ univ).ne_zero,
      natDegree_finsetProd_X_sub_C_eq_card, card_univ, Fintype.card_fin, hcard]
    exact_mod_cast Nat.lt_succ_self N

end Matrix
