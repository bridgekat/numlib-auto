/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.CauchyBinet
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Symmetric indefinite systems: Bunch–Parlett growth and the Stewart–Todd bound

This module proves two numerical facts about symmetric indefinite systems, following
[golub2013matrix], §4.4.4–4.4.5, and [higham2002accuracy], Chapter 11: the bounds on element growth
in the pivoting strategy of Bunch and Parlett (1971), and the uniform bound of Stewart (1989) and
Todd (1990) on weighted least-squares operators, which is behind the analysis of equilibrium
systems.

One step of a block $LDL^T$ factorization eliminates either one pivot ($1 \times 1$) or a
$2 \times 2$ pivot block, and leaves a Schur complement $\tilde A$. Let
$\mu_0 = \max_{i,j} |a_{ij}|$ and $\mu_1 = \max_i |a_{ii}|$, and let $0 < \alpha < 1$. The rule of
Bunch and Parlett takes a $1 \times 1$ pivot when $\mu_1 \ge \alpha \mu_0$, and otherwise the
$2 \times 2$ pivot block of an off-diagonal entry of modulus $\mu_0$. The entries of the Schur
complement then satisfy $|\tilde a_{ij}| \le (1 + \alpha^{-1}) \mu_0$ after a $1 \times 1$ step and
$|\tilde a_{ij}| \le \frac{3 - \alpha}{1 - \alpha} \mu_0$ after a $2 \times 2$ step. The parameter
$\alpha = (1 + \sqrt{17})/8$ makes the growth of two $1 \times 1$ steps equal to that of one
$2 \times 2$ step.

## Main results

* `BunchParlett.abs_schurComplementSingle_le`: the bound
  $|\tilde a_{ij}| \le (1 + \alpha^{-1}) \mu_0$ of [golub2013matrix] (4.4.16) for a $1 \times 1$
  pivot.
* `BunchParlett.abs_schurComplement_two_le`: the $2 \times 2$ pivot block is nonsingular, and
  $|\tilde a_{ij}| \le \frac{3 - \alpha}{1 - \alpha} \mu_0$, [golub2013matrix] (4.4.17).
* `BunchParlett.alpha_eq`: $\alpha = (1 + \sqrt{17})/8$ is the unique $\alpha \in (0, 1)$ with $(1 +
  \alpha^{-1})^2 = \frac{3 - \alpha}{1 - \alpha}$.
* `Matrix.exists_forall_l2_opNorm_weightedLeastSquaresOp_le`: the Stewart–Todd bound
  [golub2013matrix] (4.4.21). For $B$ of full column rank, the weighted least-squares operators
  $(B^T D B)^{-1} B^T D$ are bounded uniformly in the positive diagonal weights $D$.

## Proof outline

The proof of the Stewart–Todd bound uses Cramer's rule and the Cauchy–Binet formula. They write the
operator $(B^T D B)^{-1} B^T D$ as a convex combination of the inverses of the nonsingular
$p \times p$ row submatrices of $B$, and these inverses are finitely many.

## Implementation notes

* The $1 \times 1$ Schur complement is `Matrix.schurComplementSingle`. The $2 \times 2$ Schur
  complement is `Matrix.schurComplement` of the matrix reindexed by `{p, q} ⊕ rest`, with the two
  pivot rows first.
* The hypotheses are the weakest that the arguments use. The $1 \times 1$ bound needs only
  $\alpha \mu_0 \le |a_{pp}|$; the maximal diagonal entry is one such pivot. The $2 \times 2$ bound
  needs only $|a_{pp}|, |a_{qq}| \le \alpha \mu_0$ and $|a_{qp}| = \mu_0$.
* The Cauchy–Binet formula is `Matrix.factorial_mul_det_transpose_mul_diagonal_mul` of
  `Numlib.LinearAlgebra.Matrix.CauchyBinet`. It is stated symmetrized over the orderings of the row
  selections, so that no sorted subsets appear.
* The specifications of the factorizations, `Matrix.IsAasen` and `Matrix.IsBlockLDL`, are in
  `Numlib.LinearAlgebra.Matrix.SymmetricIndefinite`. The equilibrium matrix
  $\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix}$ of [golub2013matrix], §4.4.5, is
  `Matrix.saddleMatrix` of `Numlib.LinearAlgebra.Matrix.SchurComplement`.
-/

open Matrix

/-! ### Element growth of the Bunch–Parlett pivoting strategy -/

namespace BunchParlett

variable {n : Type*}

/-- **The $1 \times 1$ step of Bunch and Parlett** ([golub2013matrix] (4.4.16) and Problem P4.4.6).
Let $A \in \mathbb{R}^{n \times n}$, and let $\alpha > 0$ and $\mu_0 > 0$ with
$|a_{ij}| \le \mu_0$ for all $i$ and $j$. Let the pivot index $p$ satisfy
$\alpha \mu_0 \le |a_{pp}|$. Then every entry of the Schur complement $\tilde a_{ij} = a_{ij} -
a_{ip} a_{pj} / a_{pp}$, for $i, j \neq p$, satisfies
$$|\tilde a_{ij}| \le (1 + \alpha^{-1}) \mu_0.$$

The book takes $p$ with $|a_{pp}| = \mu_1 = \max_i |a_{ii}| \ge \alpha \mu_0$, and writes the
Schur complement of a symmetric matrix as $B - v v^T / a_{pp}$; the statement here does not need
$A$ to be symmetric. The proof is $|a_{ij} - a_{ip} a_{pj} / a_{pp}| \le \mu_0 + \mu_0^2 /
|a_{pp}| \le \mu_0 + \mu_0 / \alpha$. The Schur complement is `Matrix.schurComplementSingle`.
-/
theorem abs_schurComplementSingle_le {A : Matrix n n ℝ} {p : n} {α μ₀ : ℝ} (hα : 0 < α)
    (hμ₀ : 0 < μ₀) (hA : ∀ i j, |A i j| ≤ μ₀) (hp : α * μ₀ ≤ |A p p|)
    (i j : {i : n // i ≠ p}) :
    |A.schurComplementSingle p i j| ≤ (1 + α⁻¹) * μ₀ := by
  rw [schurComplementSingle_apply]
  calc |A i.1 j.1 - A i.1 p * (A p p)⁻¹ * A p j.1|
      ≤ |A i.1 j.1| + |A i.1 p * (A p p)⁻¹ * A p j.1| := abs_sub _ _
    _ = |A i.1 j.1| + |A i.1 p| * |A p j.1| / |A p p| := by
        rw [abs_mul, abs_mul, abs_inv]
        ring
    _ ≤ μ₀ + μ₀ * μ₀ / (α * μ₀) := by
        gcongr
        · exact hA _ _
        · exact hA _ _
        · exact hA _ _
    _ = (1 + α⁻¹) * μ₀ := by
        field_simp

/-- The Schur complement of a $2 \times 2$ pivot block $E$, with the pivot rows $p$ and $q$ first,
has the entries $\tilde a_{ij} = a_{ij} - [a_{ip} \; a_{iq}] \, E^{-1} [a_{pj} \; a_{qj}]^T$,
written out with $E^{-1} = \det(E)^{-1} \operatorname{adj}(E)$. -/
private theorem schurComplement_two_apply (A : Matrix n n ℝ) (p q : n)
    (i j : {i : n // i ≠ p ∧ i ≠ q}) :
    (A.submatrix (Sum.elim ![p, q] Subtype.val) (Sum.elim ![p, q] Subtype.val)).schurComplement
        i j =
      A i j - (A i p * (A q q * A p j - A p q * A q j) + A i q * (A p p * A q j - A q p * A p j))
        / (A p p * A q q - A p q * A q p) := by
  simp only [schurComplement_eq, Matrix.sub_apply, toBlocks₂₂, toBlocks₂₁, toBlocks₁₁,
    toBlocks₁₂, inv_def, adjugate_fin_two, det_fin_two, Ring.inverse_eq_inv', Matrix.mul_apply,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two, of_apply, submatrix_apply, Sum.elim_inl,
    Sum.elim_inr]
  simp only [cons_val_zero, cons_val_one, cons_val_fin_one, Fin.isValue]
  ring

/-- **The $2 \times 2$ step of Bunch and Parlett** ([golub2013matrix] (4.4.17) and Problem P4.4.6).
Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $0 < \alpha < 1$, and let $\mu_0 > 0$ with
$|a_{ij}| \le \mu_0$ for all $i$ and $j$. Let $p$ and $q$ be indices with $|a_{qp}| = \mu_0$,
$|a_{pp}| \le \alpha \mu_0$ and $|a_{qq}| \le \alpha \mu_0$, and let $E = \begin{bmatrix} a_{pp}
& a_{pq} \\ a_{qp} & a_{qq} \end{bmatrix}$. Then $E$ is nonsingular, and every entry of the
Schur complement $\tilde A = B - C E^{-1} C^T$ satisfies
$$|\tilde a_{ij}| \le \frac{3 - \alpha}{1 - \alpha} \, \mu_0, \qquad i, j \notin \{p, q\}.$$

The hypotheses are the case $\mu_1 < \alpha \mu_0$ of the book. The proof shows
$|\det E| \ge \mu_0^2 - \alpha^2 \mu_0^2$ and bounds an entry of $C \operatorname{adj}(E) C^T$
by $2 \mu_0^3 (1 + \alpha)$, so that $|(C E^{-1} C^T)_{ij}| \le 2 \mu_0 / (1 - \alpha)$. The
Schur complement is `Matrix.schurComplement` of the matrix reindexed by `{p, q} ⊕ rest`. -/
theorem abs_schurComplement_two_le {A : Matrix n n ℝ} (hA : A.IsSymm) {p q : n} {α μ₀ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hμ₀ : 0 < μ₀) (hAμ : ∀ i j, |A i j| ≤ μ₀) (hqp : |A q p| = μ₀)
    (hpp : |A p p| ≤ α * μ₀) (hqq : |A q q| ≤ α * μ₀) :
    IsUnit (A.submatrix ![p, q] ![p, q]) ∧
      ∀ i j : {i : n // i ≠ p ∧ i ≠ q},
        |(A.submatrix (Sum.elim ![p, q] Subtype.val)
          (Sum.elim ![p, q] Subtype.val)).schurComplement i j| ≤ (3 - α) / (1 - α) * μ₀ := by
  have hpq : A p q = A q p := by
    have := congrFun (congrFun hA q) p
    simpa [transpose_apply] using this
  have hαμ : 0 ≤ α * μ₀ := by positivity
  -- the determinant of the pivot block is bounded away from zero
  have hdet : μ₀ ^ 2 * (1 - α ^ 2) ≤ |A p p * A q q - A p q * A q p| := by
    have h1 : |A p p * A q q| ≤ (α * μ₀) ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul hpp hqq (abs_nonneg _) hαμ
    have h2 : |A p q * A q p| = μ₀ ^ 2 := by rw [abs_mul, hpq, hqp, sq]
    have h3 := abs_sub_abs_le_abs_sub (A p q * A q p) (A p p * A q q)
    rw [abs_sub_comm] at h3
    nlinarith
  have hdet₀ : 0 < μ₀ ^ 2 * (1 - α ^ 2) := by
    have : α ^ 2 < 1 := by nlinarith
    have : 0 < μ₀ ^ 2 := by positivity
    nlinarith
  have hD : A p p * A q q - A p q * A q p ≠ 0 := fun h => by
    rw [h, abs_zero] at hdet
    linarith
  refine ⟨?_, fun i j => ?_⟩
  · rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_fin_two]
    simpa using hD
  rw [schurComplement_two_apply]
  have hN : |A i p * (A q q * A p j - A p q * A q j) + A i q * (A p p * A q j - A q p * A p j)|
      ≤ 2 * μ₀ ^ 3 * (1 + α) := by
    have e1 : |A q q * A p j - A p q * A q j| ≤ α * μ₀ * μ₀ + μ₀ * μ₀ := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul hqq (hAμ _ _) (abs_nonneg _) hαμ
      · exact mul_le_mul (hAμ _ _) (hAμ _ _) (abs_nonneg _) hμ₀.le
    have e2 : |A p p * A q j - A q p * A p j| ≤ α * μ₀ * μ₀ + μ₀ * μ₀ := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul hpp (hAμ _ _) (abs_nonneg _) hαμ
      · exact mul_le_mul (hAμ _ _) (hAμ _ _) (abs_nonneg _) hμ₀.le
    calc _ ≤ |A i p * (A q q * A p j - A p q * A q j)| +
          |A i q * (A p p * A q j - A q p * A p j)| := abs_add_le _ _
      _ ≤ μ₀ * (α * μ₀ * μ₀ + μ₀ * μ₀) + μ₀ * (α * μ₀ * μ₀ + μ₀ * μ₀) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hAμ _ _) e1 (abs_nonneg _) hμ₀.le)
            (mul_le_mul (hAμ _ _) e2 (abs_nonneg _) hμ₀.le)
      _ = 2 * μ₀ ^ 3 * (1 + α) := by ring
  have hq : |(A i p * (A q q * A p j - A p q * A q j) + A i q * (A p p * A q j - A q p * A p j))
      / (A p p * A q q - A p q * A q p)| ≤ 2 * μ₀ / (1 - α) := by
    rw [abs_div]
    calc _ ≤ 2 * μ₀ ^ 3 * (1 + α) / (μ₀ ^ 2 * (1 - α ^ 2)) :=
          div_le_div₀ (by positivity) hN hdet₀ hdet
      _ = 2 * μ₀ / (1 - α) := by
          rw [div_eq_div_iff hdet₀.ne' (by linarith)]
          ring
  calc _ ≤ |A i j| + |(A i p * (A q q * A p j - A p q * A q j) +
        A i q * (A p p * A q j - A q p * A p j)) / (A p p * A q q - A p q * A q p)| := abs_sub _ _
    _ ≤ μ₀ + 2 * μ₀ / (1 - α) := add_le_add (hAμ _ _) hq
    _ = (3 - α) / (1 - α) * μ₀ := by
        have : 1 - α ≠ 0 := by linarith
        field_simp
        ring

/-- **The parameter of Bunch and Parlett** ([golub2013matrix], §4.4.4). The number
$\alpha = (1 + \sqrt{17})/8$ is the unique $\alpha$ with $0 < \alpha < 1$ and
$$(1 + \alpha^{-1})^2 = \frac{3 - \alpha}{1 - \alpha}.$$
The book chooses $\alpha$ by "equating the growth factor of two $s = 1$ steps with that of one
$s = 2$ step".

After clearing denominators the equation is $(1 + \alpha)^2 (1 - \alpha) = \alpha^2 (3 -
\alpha)$. The cubic terms cancel, and it becomes $4\alpha^2 - \alpha - 1 = 0$. -/
theorem alpha_eq :
    {α : ℝ | 0 < α ∧ α < 1 ∧ (1 + α⁻¹) ^ 2 = (3 - α) / (1 - α)} = {(1 + √17) / 8} := by
  have h17 : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17' : 0 ≤ √17 := Real.sqrt_nonneg _
  -- the equation is the quadratic `4α² − α − 1 = 0` on `(0, 1)`
  have key : ∀ α : ℝ, 0 < α → α < 1 →
      ((1 + α⁻¹) ^ 2 = (3 - α) / (1 - α) ↔ 4 * α ^ 2 - α - 1 = 0) := by
    intro α h0 h1
    have ha : α ≠ 0 := h0.ne'
    have hb : 1 - α ≠ 0 := by linarith
    have e : (1 + α⁻¹) ^ 2 * (1 - α) - (3 - α) = -(4 * α ^ 2 - α - 1) / α ^ 2 := by
      field_simp
      ring
    rw [eq_div_iff hb, ← sub_eq_zero, e, div_eq_zero_iff, neg_eq_zero,
      or_iff_left (pow_ne_zero 2 ha)]
  ext α
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, h⟩
    have hq := (key α h0 h1).1 h
    have hsq : (8 * α - 1) ^ 2 = √17 ^ 2 := by rw [h17]; linear_combination 16 * hq
    have hnn : 0 ≤ 8 * α - 1 := by nlinarith
    have := (sq_eq_sq₀ hnn h17').1 hsq
    linarith
  · rintro rfl
    have hlt : √17 < 7 := by nlinarith
    refine ⟨by positivity, by linarith, (key _ (by positivity) (by linarith)).2 ?_⟩
    linear_combination h17 / 16

end BunchParlett

namespace Matrix

/-! ### The Stewart–Todd bound -/

/-- A weighted form of Cramer's rule: for a square real matrix $A$ and a vector $v$, $\det A \cdot
(\operatorname{Cramer}(A, v))_k = (\det A)^2 (A^{-1} v)_k$; for a singular $A$ both sides
vanish. -/
private theorem det_mul_cramer_apply {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℝ)
    (v : p → ℝ) (k : p) : A.det * cramer A v k = A.det ^ 2 * (A⁻¹ *ᵥ v) k := by
  by_cases hA : A.det = 0
  · rw [hA]
    ring
  · rw [inv_def, Ring.inverse_eq_inv', smul_mulVec, ← cramer_eq_adjugate_mulVec, Pi.smul_apply,
      smul_eq_mul]
    field_simp

open scoped Matrix.Norms.L2Operator in
/-- **The Stewart–Todd bound** ([golub2013matrix] (4.4.21); Stewart 1989, O'Leary 1990, Todd 1990).
Let $B \in \mathbb{R}^{n \times p}$ have linearly independent columns. Then there is a number
$\psi$ such that for every diagonal matrix $D = \operatorname{diag}(d)$ with $d_i > 0$ for every
$i$,
$$\|(B^T D B)^{-1} B^T D\|_2 \le \psi.$$

The norm is the operator norm induced by the Euclidean norm, and the operator is
`Matrix.weightedLeastSquaresOp (Matrix.diagonal d) B`. By Cramer's rule and the Cauchy–Binet
formula, $(B^T D B)^{-1} B^T D b = \sum_r \lambda_r B_r^{-1} b_r$. This is a convex combination
over the row selections $r$ with nonsingular $B_r$, with the weights $\lambda_r$ proportional to
$(\prod_i d_{r_i}) \det(B_r)^2$ (Dikin; Ben-Tal and Teboulle). So
$\psi = \sqrt{p} \sum_r \|B_r^{-1}\|_2$ works. -/
theorem exists_forall_l2_opNorm_weightedLeastSquaresOp_le {n p : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [DecidableEq p] {B : Matrix n p ℝ}
    (hB : LinearIndependent ℝ Bᵀ) :
    ∃ ψ : ℝ, ∀ d : n → ℝ, (∀ i, 0 < d i) →
      ‖weightedLeastSquaresOp (diagonal d) B‖ ≤ ψ := by
  classical
  refine ⟨√(Fintype.card p : ℝ) * ∑ r : p → n, ‖(B.submatrix r id)⁻¹‖, fun d hd => ?_⟩
  set M := Bᵀ * diagonal d * B with hM
  have hW : weightedLeastSquaresOp (diagonal d) B = M⁻¹ * Bᵀ * diagonal d := by
    rw [weightedLeastSquaresOp_def, conjTranspose_eq_transpose_of_trivial]
  -- `Bᵀ D B` is positive definite
  have hinj := mulVec_injective_of_linearIndependent_transpose hB
  have hMpd : M.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hM, transpose_mul, transpose_mul,
        transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    · have hBx : B *ᵥ x ≠ 0 := fun h => hx (hinj (by rw [h, mulVec_zero]))
      rw [star_trivial, hM, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hBx
      simp only [dotProduct, mulVec_diagonal]
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · have := hd j
        nlinarith [mul_self_nonneg ((B *ᵥ x) j)]
      · have := hd i
        have := mul_self_pos.2 hi
        nlinarith
  have hdet : 0 < M.det := hMpd.det_pos
  -- Cauchy–Binet for `det M`
  have hfac : (0 : ℝ) < (Fintype.card p).factorial := by exact_mod_cast Nat.factorial_pos _
  set D := ((Fintype.card p).factorial : ℝ) * M.det with hD
  have hD0 : 0 < D := mul_pos hfac hdet
  have hDsum : D = ∑ r : p → n, (∏ i, d (r i)) * (B.submatrix r id).det ^ 2 := by
    rw [hD, factorial_mul_det_transpose_mul_diagonal_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  set lam : (p → n) → ℝ := fun r => (∏ i, d (r i)) * (B.submatrix r id).det ^ 2 / D with hlam
  have hlam0 : ∀ r, 0 ≤ lam r := fun r =>
    div_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => (hd _).le) (sq_nonneg _)) hD0.le
  have hlam1 : ∑ r, lam r = 1 := by
    rw [hlam, ← Finset.sum_div, ← hDsum, div_self hD0.ne']
  have hlamle : ∀ r, lam r ≤ 1 := fun r =>
    hlam1 ▸ Finset.single_le_sum (fun r _ => hlam0 r) (Finset.mem_univ r)
  refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (by positivity) fun b => ?_
  -- the solution as a convex combination of basic solutions
  set y : (p → n) → p → ℝ := fun r => (B.submatrix r id)⁻¹ *ᵥ fun i => WithLp.ofLp b (r i)
  have hx : WithLp.ofLp (toEuclideanLin (weightedLeastSquaresOp (diagonal d) B) b) =
      ∑ r, lam r • y r := by
    funext k
    have hWb : weightedLeastSquaresOp (diagonal d) B *ᵥ WithLp.ofLp b =
        M⁻¹ *ᵥ ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b) := by
      rw [hW, Matrix.mul_assoc, ← mulVec_mulVec]
    rw [ofLp_toEuclideanLin, hWb, inv_def, Ring.inverse_eq_inv', smul_mulVec,
      ← cramer_eq_adjugate_mulVec, Pi.smul_apply, smul_eq_mul, cramer_apply,
      Finset.sum_apply]
    -- the numerator by Cauchy–Binet
    have hupd : M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b) =
        Bᵀ * diagonal d * B.updateCol k (WithLp.ofLp b) := by
      ext i j
      rw [updateCol_apply, Matrix.mul_apply]
      split_ifs with hj
      · subst hj
        simp [mulVec, dotProduct]
      · simp [hM, Matrix.mul_apply, hj]
    have hnum : ((Fintype.card p).factorial : ℝ) *
        (M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b)).det =
        ∑ r : p → n, (∏ i, d (r i)) * (B.submatrix r id).det ^ 2 * y r k := by
      rw [hupd, factorial_mul_det_transpose_mul_diagonal_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      have : (B.updateCol k (WithLp.ofLp b)).submatrix r id =
          (B.submatrix r id).updateCol k fun i => WithLp.ofLp b (r i) := by
        ext i j
        simp [updateCol_apply]
      rw [this, ← cramer_apply, mul_assoc, det_mul_cramer_apply]
      ring
    have e : (M.det)⁻¹ * (M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b)).det =
        (((Fintype.card p).factorial : ℝ) *
          (M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b)).det) / D := by
      rw [hD]
      field_simp
    rw [e, hnum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hlam]
    ring
  -- the norm estimate
  have hbr : ∀ r : p → n, ‖(WithLp.toLp 2 fun i => WithLp.ofLp b (r i) :
      EuclideanSpace ℝ p)‖ ≤ √(Fintype.card p : ℝ) * ‖b‖ := fun r => by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(WithLp.toLp 2 fun i => WithLp.ofLp b (r i) : EuclideanSpace ℝ p) i‖ ^ 2
        ≤ ∑ _i : p, ‖b‖ ^ 2 := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le b (r i)) 2
      _ = (Fintype.card p : ℝ) * ‖b‖ ^ 2 := by simp
  have hy : ∀ r, ‖(WithLp.toLp 2 (y r) : EuclideanSpace ℝ p)‖ ≤
      ‖(B.submatrix r id)⁻¹‖ * (√(Fintype.card p : ℝ) * ‖b‖) := fun r => by
    rw [← toEuclideanLin_toLp]
    exact (norm_toEuclideanLin_apply_le _ _).trans
      (mul_le_mul_of_nonneg_left (hbr r) (norm_nonneg _))
  calc ‖toEuclideanLin (weightedLeastSquaresOp (diagonal d) B) b‖
      = ‖(WithLp.toLp 2 (∑ r, lam r • y r) : EuclideanSpace ℝ p)‖ := by
        rw [← hx]
    _ ≤ ∑ r, lam r * ‖(WithLp.toLp 2 (y r) : EuclideanSpace ℝ p)‖ := by
        rw [WithLp.toLp_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hlam0 r)]
    _ ≤ ∑ r, ‖(B.submatrix r id)⁻¹‖ * (√(Fintype.card p : ℝ) * ‖b‖) :=
        Finset.sum_le_sum fun r _ => (mul_le_mul (hlamle r) (hy r) (norm_nonneg _)
          zero_le_one).trans_eq (one_mul _)
    _ = √(Fintype.card p : ℝ) * (∑ r : p → n, ‖(B.submatrix r id)⁻¹‖) * ‖b‖ := by
        rw [← Finset.sum_mul]
        ring

end Matrix
