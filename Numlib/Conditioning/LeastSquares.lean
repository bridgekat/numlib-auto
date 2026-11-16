/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Conditioning.LinearSystem

/-!
# Perturbation theory for least-squares problems

Let $A \in \mathbb{K}^{m \times n}$ with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $A^+$ be
its pseudoinverse. If $A$ has linearly independent columns, $x = A^+ b$ is the least-squares
solution of $Ax = b$ and $r = b - Ax$ is its residual. If $A$ has linearly independent rows,
$x = A^+ b$ is the solution of $Ax = b$ of minimal norm. This module shows how these solutions and
the residual move when $A$ and $b$ are perturbed to $\hat A = A + \delta A$ and $b + \delta b$. It
proves exact identities for the changes, such as $$\hat x - x = \hat A^+ (\delta b - \delta A \,
x) + (\hat A^H \hat A)^{-1} \delta A^H r,$$ and derives from them the bounds of Theorems 5.3.1 and
5.6.1 of [golub2013matrix] in a rigorous form, without the $O(\varepsilon^2)$ terms of the source.
It also bounds the error of the method of normal equations, (5.3.4) of [golub2013matrix], and
computes the derivatives of $t \mapsto (A + tE)^+ (b + tf)$ that the first-order proofs of the
source use. The presentation follows [golub2013matrix], §5.3 and §5.6, and [higham2002accuracy],
Theorem 20.1.

## Main results

* `Matrix.leastSquares_sub_eq`, `Matrix.leastSquares_residual_sub_eq`: the exact identities $\hat
  x - x = \hat A^+ (\delta b - \delta A \, x) + (\hat A^H \hat A)^{-1} \delta A^H r$ and $\hat r -
  r = (I - \hat A \hat A^+)(\delta b - \delta A \, x) - (\hat A^+)^H \delta A^H r$.
* `Matrix.norm_leastSquares_sub_le`, `Matrix.norm_leastSquares_residual_sub_le`: Theorem 5.3.1 of
  [golub2013matrix] in rigorous form, with $\sigma_{\min}(A) - \|\delta A\|_2$ in place of the
  $\sigma_{\min}(A)$ of the source and no $O(\varepsilon^2)$ term.
* `Matrix.norm_normalEquations_sub_le`: the accuracy of the method of normal equations, (5.3.4) of
  [golub2013matrix].
* `Matrix.mul_pinv_of_linearIndependent`: for linearly independent rows, $A A^+ = I$, so the
  minimal-norm solution solves the system (`Matrix.toEuclideanLin_pinv_of_linearIndependent`).
* `Matrix.minNorm_sub_eq`, `Matrix.norm_minNorm_sub_le`: Theorem 5.6.1 of [golub2013matrix] in
  rigorous form.
* `Matrix.hasDerivAt_pinv_mulVec_line`, `Matrix.hasDerivAt_minNorm_line`: the derivatives (5.3.15)
  and (5.6.2) of [golub2013matrix] of $t \mapsto (A + tE)^+ (b + tf)$ at $t = 0$, over $\mathbb{R}$.

## Implementation notes

* The source proves Theorems 5.3.1 and 5.6.1 by differentiating $t \mapsto x(t)$ at $0$, and states
  them up to $O(\varepsilon^2)$. This module proves the exact identities instead. The bounds follow
  from the norms of the pseudoinverse and of the inverse Gram matrix of $\hat A$
  (`Matrix.l2_opNorm_pinv_eq_inv_iInf_colSingularValues`,
  `Matrix.l2_opNorm_inv_conjTranspose_mul_self`), together with Weyl's bound $\sigma_{\min}(A +
  \delta A) \ge \sigma_{\min}(A) - \|\delta A\|_2$
  (`Matrix.sub_l2_opNorm_le_iInf_colSingularValues_add`), which also shows that $A + \delta A$ keeps
  independent columns.
* $\sigma_{\min}(A)$ is `⨅ i, A.colSingularValues i`, the infimum of the singular values indexed by
  the columns, which is the least stretch $\min_{\|v\| = 1} \|Av\|$ of $A$.
* Vectors are elements of `EuclideanSpace`, matrices act through `Matrix.toEuclideanLin`, and matrix
  norms are the spectral norms of the scoped `Matrix.Norms.L2Operator` instance. The condition
  number $\kappa_2(A) = \|A\|_2 \|A^+\|_2$ of a rectangular matrix is `Matrix.pinvCondNumberLp 2 A`.
* The derivatives are stated over $\mathbb{R}$. Over $\mathbb{C}$ the conjugate transpose makes the
  map not holomorphic in a complex parameter. Along the line $A + tE$ the columns (or rows) stay
  independent for small $t$ (`Matrix.eventually_linearIndependent_transpose_add_smul`,
  `Matrix.eventually_linearIndependent_add_smul`); the other stability facts of full rank are in
  `Numlib.Analysis.Matrix.SingularValues`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The full-rank least-squares problem -/

section FullColumnRank

variable {A δA : Matrix m n 𝕜} {b δb r r' : EuclideanSpace 𝕜 m} {x x' : EuclideanSpace 𝕜 n}

/-- If $x = A^+ b$, then the residual is orthogonal to the columns of $A$: $A^H (b - Ax) = 0$. -/
private theorem toEuclideanLin_conjTranspose_residual (hx : x = toEuclideanLin A.pinv b) :
    toEuclideanLin Aᴴ (b - toEuclideanLin A x) = 0 := by
  rw [hx, map_sub, ← toEuclideanLin_mul_apply, normalEquations_pinv, sub_self]

/-- If $A$ has linearly independent columns, then $A^+ A z = z$ for every $z$. -/
private theorem toEuclideanLin_pinv_apply_toEuclideanLin (hA : LinearIndependent 𝕜 Aᵀ)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A.pinv (toEuclideanLin A z) = z := by
  rw [← toEuclideanLin_mul_apply, pinv_mul_self_of_linearIndependent hA, toEuclideanLin_one,
    LinearMap.id_apply]

/-- **The exact perturbation identity of the least-squares solution.** Let
$A, \delta A \in \mathbb{K}^{m \times n}$, and suppose that $\hat A = A + \delta A$ has linearly
independent columns. Let $x = A^+ b$, $\hat x = \hat A^+ (b + \delta b)$ and $r = b - Ax$. Then
$$\hat x - x = \hat A^+ (\delta b - \delta A \, x) + (\hat A^H \hat A)^{-1} \delta A^H r.$$

No hypothesis on the columns of $A$ is needed. The proof uses $\hat A^+ \hat A = I$, which gives
$\hat x - x = \hat A^+ (b + \delta b - \hat A x) = \hat A^+ (r + \delta b - \delta A \, x)$, and
$\hat A^+ r = (\hat A^H \hat A)^{-1} \hat A^H r = (\hat A^H \hat A)^{-1} \delta A^H r$, because
$A^H r = 0$. -/
theorem leastSquares_sub_eq (hA' : LinearIndependent 𝕜 (A + δA)ᵀ)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) :
    x' - x = toEuclideanLin (A + δA).pinv (δb - toEuclideanLin δA x) +
      toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r := by
  have hAr : toEuclideanLin Aᴴ r = 0 := hr ▸ toEuclideanLin_conjTranspose_residual hx
  have hPr : toEuclideanLin (A + δA).pinv r =
      toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r := by
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA', toEuclideanLin_mul_apply,
      toEuclideanLin_mul_apply, conjTranspose_add, map_add, LinearMap.add_apply, hAr, zero_add]
  have hAx : toEuclideanLin (A + δA) x = toEuclideanLin A x + toEuclideanLin δA x := by
    rw [map_add, LinearMap.add_apply]
  calc x' - x = toEuclideanLin (A + δA).pinv (b + δb) -
        toEuclideanLin (A + δA).pinv (toEuclideanLin (A + δA) x) := by
        rw [hx', toEuclideanLin_pinv_apply_toEuclideanLin hA']
    _ = toEuclideanLin (A + δA).pinv (r + (δb - toEuclideanLin δA x)) := by
        rw [← map_sub, hAx, hr]
        congr 1
        abel
    _ = _ := by rw [map_add, hPr, add_comm]

/-- **The exact perturbation identity of the least-squares residual.** Under the hypotheses of
`Matrix.leastSquares_sub_eq`, let $\hat r = (b + \delta b) - \hat A \hat x$. Then $$\hat r - r =
(I - \hat A \hat A^+)(\delta b - \delta A \, x) - (\hat A^+)^H \delta A^H r.$$

The proof applies $\hat A$ to the identity for $\hat x - x$, and uses
$\hat A (\hat A^H \hat A)^{-1} = (\hat A^+)^H$. -/
theorem leastSquares_residual_sub_eq (hA' : LinearIndependent 𝕜 (A + δA)ᵀ)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') :
    r' - r = toEuclideanLin (1 - (A + δA) * (A + δA).pinv) (δb - toEuclideanLin δA x) -
      toEuclideanLin ((A + δA).pinvᴴ * δAᴴ) r := by
  have hd := leastSquares_sub_eq hA' hx hx' hr
  set u := δb - toEuclideanLin δA x with hu
  have hx'' : x' = x + (toEuclideanLin (A + δA).pinv u +
      toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r) := by
    rw [← hd]
    abel
  have hPH : (A + δA) * ((A + δA)ᴴ * (A + δA))⁻¹ = (A + δA).pinvᴴ := by
    have hH : (((A + δA)ᴴ * (A + δA))⁻¹)ᴴ = ((A + δA)ᴴ * (A + δA))⁻¹ :=
      (isHermitian_conjTranspose_mul_self (A + δA)).inv
    rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA', conjTranspose_mul,
      conjTranspose_conjTranspose, hH]
  have hAQ : toEuclideanLin (A + δA)
      (toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r) =
        toEuclideanLin ((A + δA).pinvᴴ * δAᴴ) r := by
    rw [toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply (A + δA), hPH,
      ← toEuclideanLin_mul_apply]
  have hbx : b + δb - toEuclideanLin (A + δA) x - r = u := by
    rw [hr, hu, map_add, LinearMap.add_apply]
    abel
  have hre : ∀ z w, b + δb - (toEuclideanLin (A + δA) x + (z + w)) - r =
      (b + δb - toEuclideanLin (A + δA) x - r) - z - w := fun z w => by abel
  rw [hr', hx'', LinearMap.map_add, LinearMap.map_add, hAQ, hre, hbx,
    show toEuclideanLin (1 - (A + δA) * (A + δA).pinv) =
      toEuclideanLin 1 - toEuclideanLin ((A + δA) * (A + δA).pinv) from map_sub _ _ _,
    LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply,
    toEuclideanLin_mul_apply (A + δA) (A + δA).pinv]

/-- **Theorem 5.3.1** of [golub2013matrix], the bound on the solution, in rigorous form. Let
$A, \delta A \in \mathbb{K}^{m \times n}$, let $\sigma = \sigma_{\min}(A)$, and suppose that
$\|\delta A\|_2 < \sigma$ (so $A$ has linearly independent columns). Let $x = A^+ b$,
$\hat x = (A + \delta A)^+ (b + \delta b)$ and $r = b - Ax$. Then $A + \delta A$ has linearly
independent columns, and $$\|\hat x - x\| \le \frac{\|\delta b\| + \|\delta A\|_2
\|x\|}{\sigma - \|\delta A\|_2} + \frac{\|\delta A\|_2 \|r\|}{(\sigma - \|\delta A\|_2)^2}.$$

The bound (5.3.11) of the source is the relative form of this bound, with $\sigma$ in place of
$\sigma - \|\delta A\|_2$ and up to $O(\varepsilon^2)$. The proof combines
`Matrix.leastSquares_sub_eq` with $\|\hat A^+\|_2 = 1 / \sigma_{\min}(\hat A)$, $\|(\hat A^H
\hat A)^{-1}\|_2 = 1 / \sigma_{\min}(\hat A)^2$ and $\sigma_{\min}(\hat A) \ge \sigma - \|\delta
A\|_2$. Here $\sigma_{\min}(A)$ is `⨅ i, A.colSingularValues i`. -/
theorem norm_leastSquares_sub_le (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) :
    LinearIndependent 𝕜 (A + δA)ᵀ ∧
      ‖x' - x‖ ≤ (‖δb‖ + ‖δA‖ * ‖x‖) / ((⨅ i, A.colSingularValues i) - ‖δA‖) +
        ‖δA‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) ^ 2 := by
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues hδA
  set σ := ⨅ i, A.colSingularValues i with hσ
  have hσ' := sub_l2_opNorm_le_iInf_colSingularValues_add A δA
  have hd : 0 < σ - ‖δA‖ := sub_pos.2 hδA
  have hA' := linearIndependent_transpose_add_of_l2_opNorm_lt hδA
  refine ⟨hA', ?_⟩
  rw [leastSquares_sub_eq hA' hx hx' hr]
  have hP : ‖(A + δA).pinv‖ ≤ (σ - ‖δA‖)⁻¹ := by
    rw [l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA']
    exact inv_anti₀ hd hσ'
  have hG : ‖((A + δA)ᴴ * (A + δA))⁻¹‖ ≤ (σ - ‖δA‖)⁻¹ ^ 2 := by
    rw [l2_opNorm_inv_conjTranspose_mul_self hA']
    exact pow_le_pow_left₀ (inv_nonneg.2 (hd.trans_le hσ').le) (inv_anti₀ hd hσ') 2
  have hu : ‖δb - toEuclideanLin δA x‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le _ _))
  have hQ : ‖((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ‖ ≤ (σ - ‖δA‖)⁻¹ ^ 2 * ‖δA‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  calc ‖toEuclideanLin (A + δA).pinv (δb - toEuclideanLin δA x) +
        toEuclideanLin (((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ) r‖
      ≤ ‖(A + δA).pinv‖ * ‖δb - toEuclideanLin δA x‖ +
          ‖((A + δA)ᴴ * (A + δA))⁻¹ * δAᴴ‖ * ‖r‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_toEuclideanLin_apply_le _ _)
          (norm_toEuclideanLin_apply_le _ _))
    _ ≤ (σ - ‖δA‖)⁻¹ * (‖δb‖ + ‖δA‖ * ‖x‖) + (σ - ‖δA‖)⁻¹ ^ 2 * ‖δA‖ * ‖r‖ :=
        add_le_add (mul_le_mul hP hu (norm_nonneg _) (inv_nonneg.2 hd.le))
          (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    _ = _ := by
        rw [div_eq_inv_mul, div_eq_inv_mul, inv_pow]
        ring

/-- **Theorem 5.3.1** of [golub2013matrix], the bound on the residual, in rigorous form. Under the
hypotheses of `Matrix.norm_leastSquares_sub_le`, let $\hat r = (b + \delta b) - (A + \delta A)
\hat x$. Then $$\|\hat r - r\| \le \|\delta b\| + \|\delta A\|_2 \|x\| + \frac{\|\delta A\|_2
\|r\|}{\sigma - \|\delta A\|_2}.$$

The bound (5.3.12) of the source is the relative form of this bound. The proof combines
`Matrix.leastSquares_residual_sub_eq` with $\|I - \hat A \hat A^+\|_2 \le 1$ and
$\|(\hat A^+)^H\|_2 = \|\hat A^+\|_2$. -/
theorem norm_leastSquares_residual_sub_le (hδA : ‖δA‖ < ⨅ i, A.colSingularValues i)
    (hx : x = toEuclideanLin A.pinv b) (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb))
    (hr : r = b - toEuclideanLin A x) (hr' : r' = (b + δb) - toEuclideanLin (A + δA) x') :
    ‖r' - r‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ + ‖δA‖ * ‖r‖ / ((⨅ i, A.colSingularValues i) - ‖δA‖) := by
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues hδA
  set σ := ⨅ i, A.colSingularValues i with hσ
  have hσ' := sub_l2_opNorm_le_iInf_colSingularValues_add A δA
  have hd : 0 < σ - ‖δA‖ := sub_pos.2 hδA
  have hA' := linearIndependent_transpose_add_of_l2_opNorm_lt hδA
  rw [leastSquares_residual_sub_eq hA' hx hx' hr hr']
  have hP : ‖(A + δA).pinvᴴ‖ ≤ (σ - ‖δA‖)⁻¹ := by
    rw [l2_opNorm_conjTranspose, l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA']
    exact inv_anti₀ hd hσ'
  have hu : ‖δb - toEuclideanLin δA x‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le _ _))
  have hQ : ‖(A + δA).pinvᴴ * δAᴴ‖ ≤ (σ - ‖δA‖)⁻¹ * ‖δA‖ := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose δA]
    exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  calc ‖toEuclideanLin (1 - (A + δA) * (A + δA).pinv) (δb - toEuclideanLin δA x) -
        toEuclideanLin ((A + δA).pinvᴴ * δAᴴ) r‖
      ≤ ‖1 - (A + δA) * (A + δA).pinv‖ * ‖δb - toEuclideanLin δA x‖ +
          ‖(A + δA).pinvᴴ * δAᴴ‖ * ‖r‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_toEuclideanLin_apply_le _ _)
          (norm_toEuclideanLin_apply_le _ _))
    _ ≤ 1 * (‖δb‖ + ‖δA‖ * ‖x‖) + (σ - ‖δA‖)⁻¹ * ‖δA‖ * ‖r‖ :=
        add_le_add (mul_le_mul (l2_opNorm_one_sub_mul_pinv_le_one _) hu (norm_nonneg _)
          zero_le_one) (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    _ = _ := by
        rw [div_eq_inv_mul]
        ring

open scoped ComplexOrder in
/-- **The accuracy of the method of normal equations**, (5.3.4) of [golub2013matrix]. Let
$A \in \mathbb{K}^{m \times n}$ have linearly independent columns, let $x = A^+ b$ with
$x \neq 0$, and let $\hat x$ solve the perturbed normal equations $(A^H A + E) \hat x = A^H b$.
If $\|E\|_2 \le \eta \|A^H A\|_2$ and $\eta \kappa_2(A)^2 < 1$, then $$\frac{\|\hat x -
x\|}{\|x\|} \le \frac{\eta \kappa_2(A)^2}{1 - \eta \kappa_2(A)^2}.$$

Here $\kappa_2(A) = \|A\|_2 \|A^+\|_2$ is the condition number of a rectangular matrix,
`Matrix.pinvCondNumberLp 2 A`. The proof applies the linear-system bound
`relative_error_le_norm_inverse` to $A^H A$, whose condition number is $\kappa_2(A)^2$
(`Matrix.pinvCondNumberLp_two_conjTranspose_mul_self`). The estimate "$\approx u \kappa_2(A)^2$"
of the source is this bound with $\eta = c u$ from the backward error of the Cholesky
factorization. -/
theorem norm_normalEquations_sub_le (hA : LinearIndependent 𝕜 Aᵀ) {E : Matrix n n 𝕜}
    {x y : EuclideanSpace 𝕜 n} (hx : x = toEuclideanLin A.pinv b)
    (hy : toEuclideanLin (Aᴴ * A + E) y = toEuclideanLin Aᴴ b) {η : ℝ}
    (hE : ‖E‖ ≤ η * ‖Aᴴ * A‖) (hη : η * pinvCondNumberLp 2 A ^ 2 < 1) (hx0 : x ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ η * pinvCondNumberLp 2 A ^ 2 / (1 - η * pinvCondNumberLp 2 A ^ 2) := by
  classical
  have hn : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    exact hx0 (by ext i; exact isEmptyElim i)
  set G := Aᴴ * A with hG
  have hGu : IsUnit G := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hu : IsUnit (toEuclideanCLM (n := n) (𝕜 := 𝕜) G) := hGu.map _
  set L := ContinuousLinearEquiv.unitsEquiv 𝕜 (EuclideanSpace 𝕜 n) hu.unit with hL
  have hLc : (L : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) G := rfl
  have hLs : (L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) G⁻¹ := by
    have h1 : (L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) = ↑hu.unit⁻¹ := rfl
    rw [h1, ← Ring.inverse_unit, hu.unit_spec, toEuclideanCLM_nonsing_inv hGu]
  have hκ : ‖G⁻¹‖ * ‖G‖ = pinvCondNumberLp 2 A ^ 2 := by
    rw [← pinvCondNumberLp_two_conjTranspose_mul_self hA, pinvCondNumberLp, pinv_eq_inv hGu,
      lpOpNorm_two, lpOpNorm_two, mul_comm]
  have hxb : L x = toEuclideanLin Aᴴ b := by
    rw [← normalEquations_pinv, hx]
    rfl
  have hyb : ((L : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) +
      toEuclideanCLM (n := n) (𝕜 := 𝕜) E) y =
      toEuclideanLin Aᴴ b + 0 := by
    rw [add_zero, ← hy, map_add, LinearMap.add_apply]
    rfl
  have hsmall : ‖(L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ *
      ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) E‖ ≤ η * pinvCondNumberLp 2 A ^ 2 := by
    rw [hLs, l2_opNorm_toEuclideanCLM, l2_opNorm_toEuclideanCLM, ← hκ]
    have := mul_le_mul_of_nonneg_left hE (norm_nonneg G⁻¹)
    linarith
  have h := relative_error_le_norm_inverse L (toEuclideanCLM (n := n) (𝕜 := 𝕜) E) hxb hyb
    (hsmall.trans_lt hη) hx0
  rw [norm_zero, zero_div, zero_add] at h
  refine h.trans ?_
  set t := ‖(L.symm : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ *
    ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) E‖ with ht
  have ht0 : 0 ≤ t := by positivity
  rw [← mul_div_right_comm, ← ht]
  exact div_le_div₀ (by linarith) hsmall (by linarith) (by linarith)

end FullColumnRank

/-! ### The minimal-norm solution of an underdetermined system -/

section FullRowRank

variable {A δA : Matrix m n 𝕜} {b δb : EuclideanSpace 𝕜 m} {x x' : EuclideanSpace 𝕜 n}

open scoped ComplexOrder in
/-- If $A \in \mathbb{K}^{m \times n}$ has linearly independent rows, then the pseudoinverse is a
right inverse: $A A^+ = I$.

This is the dual of `Matrix.pinv_mul_self_of_linearIndependent`, through
$A^+ = A^H (A A^H)^{-1}$. -/
theorem mul_pinv_of_linearIndependent (hA : LinearIndependent 𝕜 A) : A * A.pinv = 1 := by
  rw [pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
      (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit)]

/-- If $A \in \mathbb{K}^{m \times n}$ has linearly independent rows, then the minimal-norm solution
solves the system: $A (A^+ b) = b$. -/
theorem toEuclideanLin_pinv_of_linearIndependent (hA : LinearIndependent 𝕜 A) :
    toEuclideanLin A (toEuclideanLin A.pinv b) = b := by
  rw [← toEuclideanLin_mul_apply, mul_pinv_of_linearIndependent hA, toEuclideanLin_one,
    LinearMap.id_apply]

/-- For every matrix $A$, $A^+ A = A^H (A^H)^+$, so $I - A^+ A$ is the orthogonal projection onto
the orthogonal complement of the range of $A^H$. -/
private theorem pinv_mul_self_eq_conjTranspose_mul_pinv (A : Matrix m n 𝕜) :
    A.pinv * A = Aᴴ * Aᴴ.pinv := by
  rw [pinv_conjTranspose, ← conjTranspose_mul, A.isHermitian_pinv_mul.eq]

/-- **The exact perturbation identity of the minimal-norm solution.** Let
$A, \delta A \in \mathbb{K}^{m \times n}$, and suppose that $A$ has linearly independent rows.
Let $\hat A = A + \delta A$, $x = A^+ b$ and $\hat x = \hat A^+ (b + \delta b)$. Then $$\hat x -
x = \hat A^+ (\delta b - \delta A \, x) + (I - \hat A^+ \hat A) \, \delta A^H (A A^H)^{-1} b.$$

The sign of the second term is $+$, as in the derivative (5.6.2) of [golub2013matrix]. The proof
sets $y = (A A^H)^{-1} b$. Then $x = A^H y$ solves $Ax = b$, so $\hat A^+ (\delta b - \delta A
\, x) = \hat x - \hat A^+ \hat A x$, and $(I - \hat A^+ \hat A) \hat A^H = 0$ turns $\hat A^+
\hat A x - x = -(I - \hat A^+ \hat A)(\hat A^H - \delta A^H) y$ into
$(I - \hat A^+ \hat A) \, \delta A^H y$. -/
theorem minNorm_sub_eq (hA : LinearIndependent 𝕜 A) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    x' - x = toEuclideanLin (A + δA).pinv (δb - toEuclideanLin δA x) +
      toEuclideanLin ((1 - (A + δA).pinv * (A + δA)) * δAᴴ * (A * Aᴴ)⁻¹) b := by
  set y := toEuclideanLin (A * Aᴴ)⁻¹ b with hy
  have hxy : x = toEuclideanLin Aᴴ y := by
    rw [hx, pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA, toEuclideanLin_mul_apply]
  have hAx : toEuclideanLin A x = b := by
    rw [hx]
    exact toEuclideanLin_pinv_of_linearIndependent hA
  have hPA : toEuclideanLin (1 - (A + δA).pinv * (A + δA)) (toEuclideanLin (A + δA)ᴴ y) = 0 := by
    rw [← toEuclideanLin_mul_apply, Matrix.sub_mul, Matrix.one_mul,
      pinv_mul_self_mul_conjTranspose, sub_self, map_zero, LinearMap.zero_apply]
  have hδ : toEuclideanLin δAᴴ y = toEuclideanLin (A + δA)ᴴ y - x := by
    rw [hxy, conjTranspose_add, map_add, LinearMap.add_apply]
    abel
  have hsecond : toEuclideanLin ((1 - (A + δA).pinv * (A + δA)) * δAᴴ * (A * Aᴴ)⁻¹) b =
      toEuclideanLin (A + δA).pinv (toEuclideanLin (A + δA) x) - x := by
    rw [toEuclideanLin_mul_apply, ← hy, toEuclideanLin_mul_apply, hδ, LinearMap.map_sub, hPA,
      zero_sub, show toEuclideanLin (1 - (A + δA).pinv * (A + δA)) =
        toEuclideanLin 1 - toEuclideanLin ((A + δA).pinv * (A + δA)) from map_sub _ _ _,
      LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, toEuclideanLin_mul_apply]
    abel
  have hres : b + δb - toEuclideanLin (A + δA) x = δb - toEuclideanLin δA x := by
    rw [map_add, LinearMap.add_apply, hAx]
    abel
  rw [hsecond, hx', ← hres, LinearMap.map_sub]
  abel

omit [DecidableEq n] in
/-- If $m \ge 1$ and the least singular value $\sigma_{\min}(A^H)$ is positive, then
$\|y\| \le \|A^H y\| / \sigma_{\min}(A^H)$ for every $y \in \mathbb{K}^m$. -/
private theorem norm_le_of_iInf_colSingularValues_conjTranspose [Nonempty m]
    (h : 0 < ⨅ i, Aᴴ.colSingularValues i) (y : EuclideanSpace 𝕜 m) :
    ‖y‖ ≤ ‖toEuclideanLin Aᴴ y‖ / ⨅ i, Aᴴ.colSingularValues i := by
  rw [le_div_iff₀ h, mul_comm]
  exact Aᴴ.iInf_colSingularValues_mul_norm_le y

/-- **Theorem 5.6.1** of [golub2013matrix], in rigorous form. Let
$A, \delta A \in \mathbb{K}^{m \times n}$, suppose that $A$ has linearly independent rows, let
$\sigma = \sigma_{\min}(A^H)$ (the least singular value $\sigma_m$ of $A$), and suppose that
$\|\delta A\|_2 < \sigma$. Let $b \neq 0$, $x = A^+ b$,
$\hat x = (A + \delta A)^+ (b + \delta b)$, $\varepsilon_A = \|\delta A\|_2 / \|A\|_2$ and
$\varepsilon_b = \|\delta b\| / \|b\|$. Then $A + \delta A$ has linearly independent rows, and
$$\frac{\|\hat x - x\|}{\|x\|} \le \frac{\|A\|_2}{\sigma - \|\delta A\|_2} (\varepsilon_A +
\varepsilon_b) + \begin{cases} \kappa_2(A) \, \varepsilon_A & \text{if } m < n, \\ 0 &
\text{otherwise.} \end{cases}$$

Here $\kappa_2(A) = \|A\|_2 \|A^+\|_2$ is `Matrix.pinvCondNumberLp 2 A`, and $\sigma$ is
`⨅ i, Aᴴ.colSingularValues i`. The first-order form of this bound is the bound $\kappa_2(A)
(\varepsilon_A \min\{2, n - m + 1\} + \varepsilon_b) + O(\varepsilon^2)$ of the source. The
proof combines `Matrix.minNorm_sub_eq` with $\|\hat A^+\|_2 \le 1 / (\sigma - \|\delta A\|_2)$,
$\|I - \hat A^+ \hat A\|_2 \le 1$ (and $= 0$ for a square $A$),
$\|(A A^H)^{-1} b\| \le \|x\| / \sigma$ and $\|b\| \le \|A\|_2 \|x\|$. -/
theorem norm_minNorm_sub_le (hA : LinearIndependent 𝕜 A) (hδA : ‖δA‖ < ⨅ i, Aᴴ.colSingularValues i)
    (hb : b ≠ 0) (hx : x = toEuclideanLin A.pinv b)
    (hx' : x' = toEuclideanLin (A + δA).pinv (b + δb)) :
    LinearIndependent 𝕜 (A + δA) ∧
      ‖x' - x‖ / ‖x‖ ≤ ‖A‖ / ((⨅ i, Aᴴ.colSingularValues i) - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) +
        if Fintype.card m < Fintype.card n then pinvCondNumberLp 2 A * (‖δA‖ / ‖A‖) else 0 := by
  have hδA' : ‖δAᴴ‖ < ⨅ i, Aᴴ.colSingularValues i := by rwa [l2_opNorm_conjTranspose]
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues hδA'
  set σ := ⨅ i, Aᴴ.colSingularValues i with hσ
  have hA'r := linearIndependent_add_of_l2_opNorm_lt hδA
  refine ⟨hA'r, ?_⟩
  have hd : 0 < σ - ‖δA‖ := sub_pos.2 hδA
  have hσ0 : 0 < σ := (norm_nonneg _).trans_lt hδA
  -- `x ≠ 0` and `A ≠ 0`
  have hAx : toEuclideanLin A x = b := by
    rw [hx]
    exact toEuclideanLin_pinv_of_linearIndependent hA
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hAx
    exact hb hAx.symm
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hbA : ‖b‖ ≤ ‖A‖ * ‖x‖ := hAx ▸ norm_toEuclideanLin_apply_le A x
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hAn : 0 < ‖A‖ := by
    by_contra h0
    have : ‖A‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [this, zero_mul] at hbA
    linarith
  -- the pieces of the identity
  have hσ' : σ - ‖δA‖ ≤ ⨅ i, (A + δA)ᴴ.colSingularValues i := by
    rw [conjTranspose_add, ← l2_opNorm_conjTranspose δA]
    exact sub_l2_opNorm_le_iInf_colSingularValues_add Aᴴ δAᴴ
  have hc' : LinearIndependent 𝕜 (A + δA)ᴴᵀ := by
    rw [conjTranspose_add]
    exact linearIndependent_transpose_add_of_l2_opNorm_lt hδA'
  have hP : ‖(A + δA).pinv‖ ≤ (σ - ‖δA‖)⁻¹ := by
    rw [← l2_opNorm_conjTranspose, ← pinv_conjTranspose,
      l2_opNorm_pinv_eq_inv_iInf_colSingularValues hc']
    exact inv_anti₀ hd hσ'
  set y := toEuclideanLin (A * Aᴴ)⁻¹ b with hy
  have hxy : x = toEuclideanLin Aᴴ y := by
    rw [hx, pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA, toEuclideanLin_mul_apply]
  have hyx : ‖y‖ ≤ ‖x‖ / σ := by
    rw [hxy]
    exact norm_le_of_iInf_colSingularValues_conjTranspose hσ0 y
  -- the projection term
  set c : ℝ := if Fintype.card m < Fintype.card n then 1 else 0 with hc
  have hproj : ‖1 - (A + δA).pinv * (A + δA)‖ ≤ c := by
    rw [pinv_mul_self_eq_conjTranspose_mul_pinv, hc]
    split_ifs with hmn
    · exact l2_opNorm_one_sub_mul_pinv_le_one _
    · -- a square matrix with independent rows: the range of `Âᴴ` is everything
      have hle : Fintype.card m ≤ Fintype.card n := by
        simpa using hA'r.fintype_card_le_finrank
      have heq : Fintype.card m = Fintype.card n := le_antisymm hle (not_lt.1 hmn)
      have hinj : Function.Injective (toEuclideanLin (A + δA)ᴴ) := by
        intro v w hvw
        have := mulVec_injective_iff.2 hc' (show (A + δA)ᴴ *ᵥ WithLp.ofLp v =
          (A + δA)ᴴ *ᵥ WithLp.ofLp w from congrArg WithLp.ofLp hvw)
        exact WithLp.ofLp_injective 2 this
      have htop : LinearMap.range (toEuclideanLin (A + δA)ᴴ) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by
          rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace,
            finrank_euclideanSpace, heq])
      have hz : 1 - (A + δA)ᴴ * (A + δA)ᴴ.pinv = 0 := by
        refine toEuclideanLin.injective ?_
        rw [toEuclideanLin_one_sub_mul_pinv, map_zero]
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ LinearMap.range (toEuclideanLin (A + δA)ᴴ) := htop ▸ Submodule.mem_top
        rw [ContinuousLinearMap.coe_coe, LinearMap.zero_apply,
          Submodule.starProjection_orthogonal_val,
          Submodule.starProjection_eq_self_iff.2 hv, sub_self]
      rw [hz, norm_zero]
  have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> norm_num
  have hκ : pinvCondNumberLp 2 A = ‖A‖ / σ := by
    rw [pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two, ← l2_opNorm_conjTranspose A.pinv,
      ← pinv_conjTranspose, l2_opNorm_pinv_eq_inv_iInf_colSingularValues
        (linearIndependent_transpose_of_iInf_colSingularValues_pos hσ0), div_eq_mul_inv]
  -- the bound on `‖x̂ - x‖`
  have hu : ‖δb - toEuclideanLin δA x‖ ≤ ‖δb‖ + ‖δA‖ * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_toEuclideanLin_apply_le _ _))
  have hmain : ‖x' - x‖ ≤ (σ - ‖δA‖)⁻¹ * (‖δb‖ + ‖δA‖ * ‖x‖) + c * ‖δA‖ * (‖x‖ / σ) := by
    rw [minNorm_sub_eq hA hx hx']
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_toEuclideanLin_apply_le _ _).trans (mul_le_mul hP hu (norm_nonneg _)
        (inv_nonneg.2 hd.le))
    · rw [toEuclideanLin_mul_apply, ← hy, toEuclideanLin_mul_apply]
      have h1 : ‖toEuclideanLin δAᴴ y‖ ≤ ‖δA‖ * (‖x‖ / σ) := by
        refine (norm_toEuclideanLin_apply_le _ _).trans ?_
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_left hyx (norm_nonneg _)
      calc _ ≤ ‖1 - (A + δA).pinv * (A + δA)‖ * ‖toEuclideanLin δAᴴ y‖ :=
            norm_toEuclideanLin_apply_le _ _
        _ ≤ c * (‖δA‖ * (‖x‖ / σ)) := mul_le_mul hproj h1 (norm_nonneg _) hc0
        _ = c * ‖δA‖ * (‖x‖ / σ) := by ring
  rw [div_le_iff₀ hxn]
  refine hmain.trans ?_
  have hδb : ‖δb‖ ≤ ‖δb‖ / ‖b‖ * (‖A‖ * ‖x‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hbn]
    exact mul_le_mul_of_nonneg_left hbA (norm_nonneg _)
  have e1 : (σ - ‖δA‖)⁻¹ * (‖δb‖ + ‖δA‖ * ‖x‖) ≤
      ‖A‖ / (σ - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) * ‖x‖ := by
    have hAn' := hAn.ne'
    have hbn' := hbn.ne'
    have hd' := hd.ne'
    rw [show ‖A‖ / (σ - ‖δA‖) * (‖δA‖ / ‖A‖ + ‖δb‖ / ‖b‖) * ‖x‖ =
      (σ - ‖δA‖)⁻¹ * (‖δb‖ / ‖b‖ * (‖A‖ * ‖x‖) + ‖δA‖ * ‖x‖) by field_simp; ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hd.le)
  have e2 : c * ‖δA‖ * (‖x‖ / σ) =
      (if Fintype.card m < Fintype.card n then pinvCondNumberLp 2 A * (‖δA‖ / ‖A‖) else 0) *
        ‖x‖ := by
    rw [hc, hκ]
    split_ifs
    · rw [div_mul_div_comm, mul_comm σ ‖A‖, mul_div_mul_left _ _ hAn.ne']
      ring
    · simp
  rw [add_mul, e2]
  linarith

end FullRowRank

/-! ### The derivatives along a line -/

section Derivative

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A quadratic $t \mapsto c_0 + t c_1 + t^2 c_2$ in a real parameter has the derivative $c_1$ at
$t = 0$. -/
private theorem hasDerivAt_quadratic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c₀ c₁ c₂ : F) : HasDerivAt (fun t : ℝ => c₀ + t • c₁ + t ^ 2 • c₂) c₁ 0 := by
  have h1 := (hasDerivAt_id (0 : ℝ)).smul_const c₁
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).smul_const c₂
  convert ((hasDerivAt_const (0 : ℝ) c₀).add h1).add h2 using 1
  · rfl
  · simp

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Gram matrix along a line is quadratic in the parameter: $(A + tE)^H (A + tE) = A^H A + t
(E^H A + A^H E) + t^2 E^H E$. -/
private theorem conjTranspose_mul_self_line (A E : Matrix m n ℝ) (t : ℝ) :
    (A + t • E)ᴴ * (A + t • E) = Aᴴ * A + t • (Eᴴ * A + Aᴴ * E) + t ^ 2 • (Eᴴ * E) := by
  simp only [conjTranspose_add, conjTranspose_smul, star_trivial, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

/-- **The derivative of the least-squares solution along a line**, (5.3.15) of [golub2013matrix].
Let $A \in \mathbb{R}^{m \times n}$ have linearly independent columns, and let
$E \in \mathbb{R}^{m \times n}$ and $b, f \in \mathbb{R}^m$. Let $x = A^+ b$ and $r = b - Ax$.
Then the map $t \mapsto (A + tE)^+ (b + tf)$ has at $t = 0$ the derivative $$A^+ (f - E x) +
(A^H A)^{-1} E^H r.$$

The source writes $A^+ = (A^H A)^{-1} A^H$. Near $0$ the columns of $A + tE$ stay independent
(`Matrix.eventually_linearIndependent_transpose_add_smul`), so the map is
$t \mapsto G(t)^{-1} h(t)$ with the quadratics $G(t) = (A + tE)^H (A + tE)$ and
$h(t) = (A + tE)^H (b + tf)$, and the derivative of the inverse is $-G^{-1} G' G^{-1}$
(`hasFDerivAt_ringInverse`). The theorem is stated over $\mathbb{R}$, because over $\mathbb{C}$
the conjugate transpose makes the map not holomorphic in a complex parameter. -/
theorem hasDerivAt_pinv_mulVec_line {A : Matrix m n ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (E : Matrix m n ℝ) (b f : EuclideanSpace ℝ m) :
    HasDerivAt (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f))
      (toEuclideanLin A.pinv (f - toEuclideanLin E (toEuclideanLin A.pinv b)) +
        toEuclideanLin ((Aᴴ * A)⁻¹ * Eᴴ) (b - toEuclideanLin A (toEuclideanLin A.pinv b)))
      0 := by
  nth_rw 1 [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA]
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Subsingleton (EuclideanSpace ℝ n) := ⟨fun a b => by ext i; exact isEmptyElim i⟩
    convert hasDerivAt_const (0 : ℝ) (0 : EuclideanSpace ℝ n) using 1
  set x₀ := toEuclideanLin A.pinv b with hx₀
  set G : ℝ → EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    fun t => toEuclideanCLM (n := n) (𝕜 := ℝ) ((A + t • E)ᴴ * (A + t • E)) with hGdef
  set h : ℝ → EuclideanSpace ℝ n := fun t => toEuclideanLin (A + t • E)ᴴ (b + t • f) with hhdef
  have hGd : HasDerivAt G (toEuclideanCLM (n := n) (𝕜 := ℝ) (Eᴴ * A + Aᴴ * E)) 0 := by
    convert hasDerivAt_quadratic (toEuclideanCLM (n := n) (𝕜 := ℝ) (Aᴴ * A))
      (toEuclideanCLM (n := n) (𝕜 := ℝ) (Eᴴ * A + Aᴴ * E))
      (toEuclideanCLM (n := n) (𝕜 := ℝ) (Eᴴ * E)) using 1
    funext t
    simp only [hGdef]
    rw [conjTranspose_mul_self_line, map_add, map_add, map_smul, map_smul]
  have hhd : HasDerivAt h (toEuclideanLin Eᴴ b + toEuclideanLin Aᴴ f) 0 := by
    convert hasDerivAt_quadratic (toEuclideanLin Aᴴ b)
      (toEuclideanLin Eᴴ b + toEuclideanLin Aᴴ f) (toEuclideanLin Eᴴ f) using 1
    funext t
    simp only [hhdef, conjTranspose_add, conjTranspose_smul, star_trivial, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply]
    module
  have hGu : IsUnit (Aᴴ * A) := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hu := hGu.map (toEuclideanCLM (n := n) (𝕜 := ℝ))
  have hG0 : G 0 = hu.unit := by
    rw [hu.unit_spec, hGdef]
    simp
  have hinv' : ((hu.unit⁻¹ : (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)ˣ) :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) =
        toEuclideanCLM (n := n) (𝕜 := ℝ) (Aᴴ * A)⁻¹ := by
    rw [toEuclideanCLM_nonsing_inv hGu, ← Ring.inverse_unit, hu.unit_spec]
  have hinvD : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) ↑hu.unit⁻¹ ↑hu.unit⁻¹) (G 0) := by
    rw [hG0]
    exact hasFDerivAt_ringInverse hu.unit
  have hcomp := hinvD.comp_hasDerivAt (0 : ℝ) hGd
  have hres := hcomp.clm_apply hhd
  -- near `0` the map is `G(t)⁻¹ h(t)`
  have hev : (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f)) =ᶠ[nhds 0]
      fun t => (Ring.inverse ∘ G) t (h t) := by
    filter_upwards [eventually_linearIndependent_transpose_add_smul hA E] with t hAt
    replace hAt : LinearIndependent ℝ (A + t • E)ᵀ := hAt
    have hGt := (posDef_conjTranspose_mul_self_of_linearIndependent hAt).isUnit
    simp only [Function.comp_apply, hGdef]
    rw [← toEuclideanCLM_nonsing_inv hGt,
      pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hAt, toEuclideanLin_mul_apply]
    rfl
  convert hres.congr_of_eventuallyEq hev using 1
  -- the value of the derivative
  have hh0 : h 0 = toEuclideanLin Aᴴ b := by simp [hhdef]
  have hx₀' : toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin Aᴴ b) = x₀ := by
    rw [hx₀, pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA, toEuclideanLin_mul_apply]
  rw [Function.comp_apply, hG0, Ring.inverse_unit, hinv', hh0]
  change _ = -toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin (Eᴴ * A + Aᴴ * E)
      (toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin Aᴴ b))) +
    toEuclideanLin (Aᴴ * A)⁻¹ (toEuclideanLin Eᴴ b + toEuclideanLin Aᴴ f)
  rw [hx₀', toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, ← LinearMap.map_add,
    ← LinearMap.map_neg, ← LinearMap.map_add]
  congr 1
  rw [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    LinearMap.map_sub, LinearMap.map_sub]
  abel

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The Gram matrix of the rows along a line is quadratic in the parameter: $(A + tE)(A + tE)^H = A
A^H + t (E A^H + A E^H) + t^2 E E^H$. -/
private theorem mul_conjTranspose_self_line (A E : Matrix m n ℝ) (t : ℝ) :
    (A + t • E) * (A + t • E)ᴴ = A * Aᴴ + t • (E * Aᴴ + A * Eᴴ) + t ^ 2 • (E * Eᴴ) := by
  simp only [conjTranspose_add, conjTranspose_smul, star_trivial, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  module

/-- If $A \in \mathbb{R}^{m \times n}$ has linearly independent rows, let $M(t) = A + tE$ and
$H(t) = M(t) M(t)^H$. Then $t \mapsto M(t)^H H(t)^{-1} (b + tf)$ has at $t = 0$ the derivative
$(I - A^H (A A^H)^{-1} A) E^H (A A^H)^{-1} b + A^H (A A^H)^{-1} (f - E A^H (A A^H)^{-1} b)$. -/
private theorem hasDerivAt_conjTranspose_mul_inv_line {A : Matrix m n ℝ}
    (hA : LinearIndependent ℝ A)
    (E : Matrix m n ℝ) (b f : EuclideanSpace ℝ m) :
    HasDerivAt (fun t : ℝ =>
        toEuclideanLin ((A + t • E)ᴴ * ((A + t • E) * (A + t • E)ᴴ)⁻¹) (b + t • f))
      (toEuclideanLin ((1 - Aᴴ * (A * Aᴴ)⁻¹ * A) * Eᴴ * (A * Aᴴ)⁻¹) b +
        toEuclideanLin (Aᴴ * (A * Aᴴ)⁻¹)
          (f - toEuclideanLin E (toEuclideanLin (Aᴴ * (A * Aᴴ)⁻¹) b))) 0 := by
  rcases isEmpty_or_nonempty m with hm | hm
  · have : Subsingleton (EuclideanSpace ℝ m) := ⟨fun a b => by ext i; exact isEmptyElim i⟩
    obtain rfl : b = 0 := Subsingleton.elim _ _
    obtain rfl : f = 0 := Subsingleton.elim _ _
    simp only [smul_zero, add_zero, map_zero, sub_zero]
    exact hasDerivAt_const _ _
  set H : ℝ → EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m :=
    fun t => toEuclideanCLM (n := m) (𝕜 := ℝ) ((A + t • E) * (A + t • E)ᴴ) with hHdef
  set T : ℝ → EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ n :=
    fun t => LinearMap.toContinuousLinearMap (toEuclideanLin (A + t • E)ᴴ) with hTdef
  have hHd : HasDerivAt H (toEuclideanCLM (n := m) (𝕜 := ℝ) (E * Aᴴ + A * Eᴴ)) 0 := by
    convert hasDerivAt_quadratic (toEuclideanCLM (n := m) (𝕜 := ℝ) (A * Aᴴ))
      (toEuclideanCLM (n := m) (𝕜 := ℝ) (E * Aᴴ + A * Eᴴ))
      (toEuclideanCLM (n := m) (𝕜 := ℝ) (E * Eᴴ)) using 1
    funext t
    simp only [hHdef]
    rw [mul_conjTranspose_self_line, map_add, map_add, map_smul, map_smul]
  have hTd : HasDerivAt T (LinearMap.toContinuousLinearMap (toEuclideanLin Eᴴ)) 0 := by
    convert hasDerivAt_quadratic (LinearMap.toContinuousLinearMap (toEuclideanLin Aᴴ))
      (LinearMap.toContinuousLinearMap (toEuclideanLin Eᴴ)) 0 using 1
    funext t
    simp only [hTdef, conjTranspose_add, conjTranspose_smul, star_trivial, map_add, map_smul,
      smul_zero, add_zero]
  have hbd : HasDerivAt (fun t : ℝ => b + t • f) f 0 := by
    convert hasDerivAt_quadratic b f 0 using 1
    funext t
    simp
  have hGu : IsUnit (A * Aᴴ) := (posDef_self_mul_conjTranspose_of_linearIndependent hA).isUnit
  have hu := hGu.map (toEuclideanCLM (n := m) (𝕜 := ℝ))
  have hH0 : H 0 = hu.unit := by
    rw [hu.unit_spec, hHdef]
    simp
  have hinv' : ((hu.unit⁻¹ : (EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m)ˣ) :
      EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m) =
        toEuclideanCLM (n := m) (𝕜 := ℝ) (A * Aᴴ)⁻¹ := by
    rw [toEuclideanCLM_nonsing_inv hGu, ← Ring.inverse_unit, hu.unit_spec]
  have hinvD : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ
      (EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m) ↑hu.unit⁻¹ ↑hu.unit⁻¹) (H 0) := by
    rw [hH0]
    exact hasFDerivAt_ringInverse hu.unit
  have hw := (hinvD.comp_hasDerivAt (0 : ℝ) hHd).clm_apply hbd
  have hres := hTd.clm_apply hw
  -- near `0` the rows stay independent
  have hev : (fun t : ℝ =>
      toEuclideanLin ((A + t • E)ᴴ * ((A + t • E) * (A + t • E)ᴴ)⁻¹) (b + t • f)) =ᶠ[nhds 0]
      fun t => T t ((Ring.inverse ∘ H) t (b + t • f)) := by
    filter_upwards [eventually_linearIndependent_add_smul hA E] with t hAt
    replace hAt : LinearIndependent ℝ (A + t • E) := hAt
    have hHt := (posDef_self_mul_conjTranspose_of_linearIndependent hAt).isUnit
    simp only [Function.comp_apply, hHdef, hTdef]
    rw [← toEuclideanCLM_nonsing_inv hHt, toEuclideanLin_mul_apply]
    rfl
  convert hres.congr_of_eventuallyEq hev using 1
  rw [Function.comp_apply, hH0, Ring.inverse_unit, hinv']
  change _ = toEuclideanLin Eᴴ (toEuclideanLin (A * Aᴴ)⁻¹ (b + (0 : ℝ) • f)) +
    toEuclideanLin (A + (0 : ℝ) • E)ᴴ (-toEuclideanLin (A * Aᴴ)⁻¹
      (toEuclideanLin (E * Aᴴ + A * Eᴴ) (toEuclideanLin (A * Aᴴ)⁻¹ (b + (0 : ℝ) • f))) +
      toEuclideanLin (A * Aᴴ)⁻¹ f)
  simp only [zero_smul, add_zero, toEuclideanLin_mul_apply, map_sub, map_add, map_neg,
    LinearMap.sub_apply, LinearMap.add_apply, toEuclideanLin_one, LinearMap.id_apply]
  abel

/-- **The derivative of the minimal-norm solution along a line**, (5.6.2) of [golub2013matrix]. Let
$A \in \mathbb{R}^{m \times n}$ have linearly independent rows, and let
$E \in \mathbb{R}^{m \times n}$ and $b, f \in \mathbb{R}^m$. Let $x = A^+ b$. Then the map
$t \mapsto (A + tE)^+ (b + tf)$ has at $t = 0$ the derivative $$(I - A^+ A) E^H (A A^H)^{-1} b +
A^+ (f - E x).$$

The source writes $A^+ = A^H (A A^H)^{-1}$. Near $0$ the rows of $A + tE$ stay independent
(`Matrix.eventually_linearIndependent_add_smul`), and the map is
$t \mapsto M(t)^H H(t)^{-1} (b + tf)$ with $M(t) = A + tE$ and the quadratic
$H(t) = M(t) M(t)^H$. The product rule and the derivative $-H^{-1} H' H^{-1}$ of the inverse
give the formula. The theorem is stated over $\mathbb{R}$, as
`Matrix.hasDerivAt_pinv_mulVec_line` is. -/
theorem hasDerivAt_minNorm_line {A : Matrix m n ℝ} (hA : LinearIndependent ℝ A)
    (E : Matrix m n ℝ) (b f : EuclideanSpace ℝ m) :
    HasDerivAt (fun t : ℝ => toEuclideanLin (A + t • E).pinv (b + t • f))
      (toEuclideanLin ((1 - A.pinv * A) * Eᴴ * (A * Aᴴ)⁻¹) b +
        toEuclideanLin A.pinv (f - toEuclideanLin E (toEuclideanLin A.pinv b))) 0 := by
  have h := hasDerivAt_conjTranspose_mul_inv_line hA E b f
  rw [← pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_linearIndependent_add_smul hA E] with t hAt
  replace hAt : LinearIndependent ℝ (A + t • E) := hAt
  rw [pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hAt]

end Derivative

end Matrix
