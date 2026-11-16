/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Normed
import Numlib.Preconditioner.ApproximateInverse
import Numlib.Projection.OneDimensional
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 10.5: Approximate inverse preconditioners

This module formalizes Section 10.5 of [saad2003iterative]. Instead of factoring
$A \in \mathbb{R}^{n \times n}$, an approximate inverse preconditioner minimizes the Frobenius
objective $F(M) = \|I - AM\|_F^2$ over sparse matrices $M$ and uses $M$ itself as the
preconditioner. The objective is the squared norm of the residual $R = I - AM$ for the Frobenius
inner product $\langle X, Y \rangle = \operatorname{tr}(Y^T X)$ of (10.48), it splits into $n$
independent least-squares problems, one per column (10.46), and its gradient is $-2 A^T R$
(Proposition 10.9). A residual of norm less than $1$ makes $M$ nonsingular (Proposition 10.10 and
(10.54)). An accurate approximate inverse must contain the large entries of $A^{-1}$ in its pattern
(Proposition 10.11 and Corollary 10.12). The self-preconditioned minimal-residual iteration
converges quadratically (Propositions 10.13 and 10.14, (10.61), (10.63)), and in the bordering
algorithm the pivots stay positive (Lemma 10.15).

The section has little matrix content beyond the Frobenius geometry. Proposition 10.10 is the
Neumann series in a normed ring, Proposition 10.11 and Corollary 10.12 are a Hölder bound on
$M = A^{-1} - A^{-1} R$, and Proposition 10.14 is the observation that a minimizer over the step
length is at least as good as the step length $1$, whose residual is $R^2$. One minimal-residual
step on a single column is the one-dimensional projection step of `Numlib.Projection.OneDimensional`
for the matrix $C = AM$: self-preconditioned minimal residual for $Am = e_j$ is plain minimal
residual for $Cy = e_j$. The general Hilbert-space statements come from
`Numlib.Preconditioner.ApproximateInverse`.

## Main definitions

* Section 10.5, `SaadSparse.Chapter10.frobeniusEquiv`: the linear isometry that reads a matrix as
  the vector of its entries.
* Equation (10.48), `SaadSparse.Chapter10.frobeniusInner`: the Frobenius inner product $\langle X, Y
  \rangle = \operatorname{tr}(Y^T X)$.

## Main results

* Equations (10.43) and (10.48), `SaadSparse.Chapter10.frobeniusInner_self`:
  $\langle X, X \rangle = \|X\|_F^2$.
* Equation (10.46), `SaadSparse.Chapter10.equation_10_46`:
  $\|I - AM\|_F^2 = \sum_j \|e_j - A m_j\|_2^2$.
* Proposition 10.9, `SaadSparse.Chapter10.proposition_10_9`: the derivative of $F$ at $M$ is the
  Frobenius inner product against $-2 A^T (I - AM)$.
* Proposition 10.10, `SaadSparse.Chapter10.proposition_10_10`: if $\|I - AM\|_F < 1$, then $M$ is
  nonsingular.
* Equation (10.54), `SaadSparse.Chapter10.equation_10_54`: the same with the scaled residual
  $I - D_1 A M D_2$.
* Proposition 10.11, `SaadSparse.Chapter10.proposition_10_11`: a small column residual forces
  $m_{ij} \neq 0$ where $(A^{-1})_{ij}$ is large.
* Corollary 10.12, `SaadSparse.Chapter10.corollary_10_12`: for a $\tau$-equimodular inverse, the
  pattern of $M$ contains the pattern of $A^{-1}$.
* Proposition 10.13, `SaadSparse.Chapter10.proposition_10_13`: the residual identity of one
  self-preconditioned minimal-residual step.
* Equation (10.61), `SaadSparse.Chapter10.equation_10_61`: the residual of the global
  self-preconditioned step is $(1 - \alpha) R + \alpha R^2$.
* Equation (10.63), `SaadSparse.Chapter10.equation_10_63`: the preconditioned matrix obeys
  $B' = B + \alpha B (I - B)$.
* Section 10.5, `SaadSparse.Chapter10.isSymm_mul_selfPreconditionedStep`: the step preserves the
  symmetry of $B = AM$.
* Proposition 10.14, `SaadSparse.Chapter10.proposition_10_14`: the new residual satisfies
  $\|R'\|_F \le \|R\|_F^2$.
* Lemma 10.15, `SaadSparse.Chapter10.lemma_10_15`: the pivot of the bordering algorithm is positive.

## Conventions

* Matrix norms in this module are Frobenius norms: Mathlib's Frobenius norm on `Matrix`, under
  `open scoped Matrix.Norms.Frobenius`. Vector norms are Euclidean.
* The column $m_j$ of $M$ is `Mᵀ j`, and $e_j$ is `Pi.single j 1`.

## Implementation notes

* Mathlib has the Frobenius norm on matrices but no inner product space structure. The isometry
  `SaadSparse.Chapter10.frobeniusEquiv` onto `EuclideanSpace ℝ (Fin n × Fin n)` supplies it, and
  through it the general statements of `Numlib.Preconditioner.ApproximateInverse` become statements
  about matrices. Proposition 10.9 is obtained this way.

## Deviations from the source

* **Lemma 10.15** (reading). The pivot $\delta_{k+1}$ of (10.70) is read as the diagonal entry of
  $L A L^T$, and the positivity is proved for every nonsingular $L$. See
  `SaadSparse.Chapter10.lemma_10_15`.

## Not formalized

* **Sections 10.5.1–10.5.5** (the dropping strategies). They carry no statement of their own.
* **Sections 10.5.7–10.5.8** (the factored approximate inverses). They carry no statement of their
  own.
-/

open Matrix Projection
open scoped Matrix.Norms.Frobenius SaadSparse

namespace SaadSparse.Chapter10

variable {n : ℕ}

/-! ### The Frobenius inner product, (10.43)–(10.48) -/

private theorem norm_toLp_eq (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖(WithLp.toLp 2 fun p : Fin n × Fin n => M p.1 p.2 : EuclideanSpace ℝ (Fin n × Fin n))‖
      = ‖M‖ := by
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, Fintype.sum_prod_type, Real.sqrt_eq_rpow]
  norm_num

/-- **Section 10.5** of [saad2003iterative], the Frobenius norm as a Euclidean norm. Reading a
matrix $M \in \mathbb{R}^{n \times n}$ as the vector $(m_{ij})_{(i, j)}$ of its $n^2$ entries is
a linear isometry from the matrices with the Frobenius norm onto $\mathbb{R}^{n \times n}$ with
the Euclidean norm.

Mathlib has the Frobenius norm but no inner product space structure on `Matrix`, and this
identification supplies one. The target is `EuclideanSpace ℝ (Fin n × Fin n)`. -/
noncomputable def frobeniusEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin n) where
  toFun M := WithLp.toLp 2 fun p => M p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := Matrix.of fun i j => WithLp.ofLp x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' := norm_toLp_eq

/-- `SaadSparse.Chapter10.frobeniusEquiv` maps a matrix $M$ to the vector $(m_{ij})_{(i, j)}$ of its
entries. -/
@[simp]
theorem frobeniusEquiv_apply (M : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusEquiv n M = WithLp.toLp 2 fun p => M p.1 p.2 := rfl

/-- **Equation (10.48)** of [saad2003iterative]. For $X, Y \in \mathbb{R}^{n \times n}$, the
**Frobenius inner product** is
$$\langle X, Y \rangle = \operatorname{tr}(Y^T X).$$
Its norm is the Frobenius norm (`SaadSparse.Chapter10.frobeniusInner_self`). -/
def frobeniusInner (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ := Matrix.trace (Yᵀ * X)

/-- The Frobenius inner product entry by entry: $\langle X, Y \rangle = \sum_i \sum_j x_{ij}
y_{ij}$. -/
theorem frobeniusInner_eq_sum (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusInner X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp only [frobeniusInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The Frobenius inner product $\langle X, Y \rangle$ is the Euclidean inner product of the images
of $X$ and $Y$ under `SaadSparse.Chapter10.frobeniusEquiv`. -/
theorem inner_frobeniusEquiv (X Y : Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (frobeniusEquiv n X) (frobeniusEquiv n Y) = frobeniusInner X Y := by
  rw [frobeniusInner_eq_sum]
  simp only [frobeniusEquiv_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **Equations (10.43) and (10.48)** of [saad2003iterative]. For $X \in \mathbb{R}^{n \times n}$,
$$\langle X, X \rangle = \|X\|_F^2.$$
So the objective $F(M) = \|I - AM\|_F^2$ is the squared norm of the residual for the Frobenius
inner product. -/
theorem frobeniusInner_self (X : Matrix (Fin n) (Fin n) ℝ) : frobeniusInner X X = ‖X‖ ^ 2 := by
  rw [← inner_frobeniusEquiv, real_inner_self_eq_norm_sq, (frobeniusEquiv n).norm_map]

/-- The squared Frobenius norm entry by entry: $\|X\|_F^2 = \sum_i \sum_j x_{ij}^2$. -/
theorem norm_sq_eq_sum (X : Matrix (Fin n) (Fin n) ℝ) : ‖X‖ ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  rw [← frobeniusInner_self, frobeniusInner_eq_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (sq _).symm

/-- **Equation (10.46)** of [saad2003iterative]. For $A, M \in \mathbb{R}^{n \times n}$ with columns
$m_1, \dots, m_n$ of $M$,
$$\|I - AM\|_F^2 = \sum_j \|e_j - A m_j\|_2^2.$$
So the objective splits into $n$ independent least-squares problems, one per column, and the
computation of an approximate inverse is parallel over the columns. -/
theorem equation_10_46 (A M : Matrix (Fin n) (Fin n) ℝ) :
    ‖1 - A * M‖ ^ 2 =
      ∑ j, ‖(WithLp.toLp 2 (Pi.single j (1 : ℝ) - A *ᵥ Mᵀ j) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [norm_sq_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Pi.single_apply, eq_comm]

/-! ### Proposition 10.9: the gradient of the Frobenius objective -/

/-- Moving a left factor across the Frobenius inner product transposes it: $\langle X, AY \rangle =
\langle A^T X, Y \rangle$. -/
private theorem frobeniusInner_mul_left (A X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusInner X (A * Y) = frobeniusInner (Aᵀ * X) Y := by
  change Matrix.trace ((A * Y)ᵀ * X) = Matrix.trace (Yᵀ * (Aᵀ * X))
  rw [Matrix.transpose_mul, Matrix.mul_assoc]

/-- For $X \in \mathbb{R}^{n \times n}$, the continuous linear functional
$Y \mapsto \langle X, Y \rangle$ given by the Frobenius inner product. -/
noncomputable def frobeniusInnerL (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (innerSL ℝ (frobeniusEquiv n X)).comp (frobeniusEquiv n).toLinearIsometry.toContinuousLinearMap

/-- `SaadSparse.Chapter10.frobeniusInnerL X` maps $Y$ to the Frobenius inner product
$\langle X, Y \rangle$. -/
@[simp]
theorem frobeniusInnerL_apply (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusInnerL X Y = frobeniusInner X Y :=
  inner_frobeniusEquiv X Y

/-- **Proposition 10.9** of [saad2003iterative]. Let $A, M \in \mathbb{R}^{n \times n}$ and let
$R = I - AM$. The function $F(Z) = \|I - AZ\|_F^2$ has at $M$ the Fréchet derivative
$$F'(M) Z = \langle -2 A^T R, Z \rangle.$$
So the array representation of the gradient of $F$ at $M$ is $G = -2 A^T R$. -/
theorem proposition_10_9 (A M : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt (fun Z : Matrix (Fin n) (Fin n) ℝ => ‖1 - A * Z‖ ^ 2)
      ((-2 : ℝ) • frobeniusInnerL (Aᵀ * (1 - A * M))) M := by
  have h := Preconditioner.hasFDerivAt_normSq_sub_apply
    (((frobeniusEquiv n).toLinearIsometry.toContinuousLinearMap).comp
      (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) A)) (frobeniusEquiv n 1) M
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)).congr_fderiv
    (ContinuousLinearMap.ext fun E => ?_)
  · rw [← (frobeniusEquiv n).norm_map (1 - A * Z), map_sub]
    rfl
  · change (-2 : ℝ) * inner ℝ (frobeniusEquiv n 1 - frobeniusEquiv n (A * M))
        (frobeniusEquiv n (A * E))
      = (-2 : ℝ) * frobeniusInnerL (Aᵀ * (1 - A * M)) E
    rw [frobeniusInnerL_apply, ← map_sub, inner_frobeniusEquiv, frobeniusInner_mul_left]

/-! ### Proposition 10.10: nonsingularity from a small residual -/

/-- **Proposition 10.10** of [saad2003iterative]. Let $A, M \in \mathbb{R}^{n \times n}$ with
$$\|I - AM\|_F < 1.$$
Then $M$ is nonsingular.

The book allows any consistent matrix norm; the formal statement uses the Frobenius norm. The
proof is the Neumann series: $AM$ is nonsingular, and hence so is $M$. -/
theorem proposition_10_10 {A M : Matrix (Fin n) (Fin n) ℝ} (h : ‖1 - A * M‖ < 1) : IsUnit M := by
  have hAM := Preconditioner.isUnit_of_norm_one_sub_mul_lt_one h
  rw [Matrix.isUnit_iff_isUnit_det] at hAM ⊢
  rw [Matrix.det_mul] at hAM
  exact isUnit_of_mul_isUnit_right hAM

/-- **Equation (10.54)** of [saad2003iterative]. Let $A, M, D_1, D_2 \in \mathbb{R}^{n \times n}$
with $D_1$ and $D_2$ nonsingular, and let
$$\|I - D_1 A M D_2\|_F < 1.$$
Then $M$ is nonsingular.

In the book, $D_1$ and $D_2$ are diagonal scalings that improve the conditioning. -/
theorem equation_10_54 {A M D₁ D₂ : Matrix (Fin n) (Fin n) ℝ} (hD₁ : IsUnit D₁) (hD₂ : IsUnit D₂)
    (h : ‖1 - D₁ * (A * M) * D₂‖ < 1) : IsUnit M := by
  have hAM := Preconditioner.isUnit_of_norm_one_sub_units_mul_lt_one
    (d₁ := hD₁.unit) (d₂ := hD₂.unit) (by rwa [IsUnit.unit_spec, IsUnit.unit_spec])
  rw [Matrix.isUnit_iff_isUnit_det] at hAM ⊢
  rw [Matrix.det_mul] at hAM
  exact isUnit_of_mul_isUnit_right hAM

/-! ### Proposition 10.11 and Corollary 10.12: the sparsity of an approximate inverse -/

/-- **Proposition 10.11** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, let $M \in \mathbb{R}^{n \times n}$ have the columns $m_1, \dots, m_n$, and let
$\tau_1, \dots, \tau_n \in \mathbb{R}$ bound the column residuals in the $\ell^1$ norm,
$\|e_j - A m_j\|_1 \le \tau_j$ for every $j$. If for some $i, j$
$$\tau_j \max_k |(A^{-1})_{ik}| < |(A^{-1})_{ij}|,$$
then $m_{ij} \neq 0$. So an accurate approximate inverse must contain the large entries of
$A^{-1}$ in its pattern.

The nonsingularity of $A$ is stated as `IsUnit A.det`. -/
theorem proposition_10_11 {A M : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) {τ : Fin n → ℝ}
    (hτ : ∀ j, ∑ i, |(Pi.single j (1 : ℝ) : Fin n → ℝ) i - (A *ᵥ Mᵀ j) i| ≤ τ j) {i j : Fin n}
    (hlt : τ j * (⨆ k, |A⁻¹ i k|) < |A⁻¹ i j|) : M i j ≠ 0 := by
  refine Preconditioner.apply_ne_zero_of_abs_lt (Matrix.nonsing_inv_mul A hA) ?_ hlt
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) (hτ j)
  congr 1
  simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Pi.single_apply, eq_comm]

/-- **Corollary 10.12** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
let $M \in \mathbb{R}^{n \times n}$ have the columns $m_1, \dots, m_n$, and let
$\tau \in \mathbb{R}$ with $\|e_j - A m_j\|_1 \le \tau$ for every $j$. Assume that the nonzero
entries of $A^{-1}$ are $\tau$-equimodular: every $(i, j)$ with $(A^{-1})_{ij} \neq 0$ satisfies
$$\tau \max_{l, k} |(A^{-1})_{lk}| < |(A^{-1})_{ij}|.$$
Then $(A^{-1})_{ij} \neq 0$ implies $m_{ij} \neq 0$: the pattern of $M$ contains the pattern of
$A^{-1}$.

So an approximate inverse of a matrix whose inverse is dense with entries of comparable size
must itself be dense. This is the practical limit of the approach. -/
theorem corollary_10_12 {A M : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) {τ : ℝ}
    (hτ : ∀ j, ∑ i, |(Pi.single j (1 : ℝ) : Fin n → ℝ) i - (A *ᵥ Mᵀ j) i| ≤ τ)
    (hequi : ∀ i j : Fin n, A⁻¹ i j ≠ 0 → τ * (⨆ (l : Fin n) (k : Fin n), |A⁻¹ l k|) < |A⁻¹ i j|)
    {i j : Fin n} (h : A⁻¹ i j ≠ 0) : M i j ≠ 0 := by
  have hτ0 : 0 ≤ τ :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hτ j)
  have hbdd : BddAbove (Set.range fun k => |A⁻¹ i k|) := Set.Finite.bddAbove (Set.finite_range _)
  have hbdd' : BddAbove (Set.range fun l => ⨆ k, |A⁻¹ l k|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hle : (⨆ k, |A⁻¹ i k|) ≤ ⨆ (l : Fin n) (k : Fin n), |A⁻¹ l k| := le_ciSup hbdd' i
  exact proposition_10_11 (τ := fun _ => τ) hA hτ
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hτ0) (hequi i j h))

/-! ### Propositions 10.13 and 10.14: quadratic convergence of self-preconditioned MR -/

/-- **Proposition 10.13** of [saad2003iterative], first part, the identity (10.58). Let
$A, M \in \mathbb{R}^{n \times n}$, let $C = AM$, let $b, x \in \mathbb{R}^n$ and let
$r = b - Cx$. Let $x'$ be the result of one minimal-residual step for $Cy = b$ from $x$, and let
$r' = b - Cx'$. Then
$$\|r'\|_2^2 = \|r\|_2^2 \left(1 - \frac{(Cr, r)^2}{\|r\|_2^2 \, \|Cr\|_2^2}\right),$$
that is, $\|r'\|_2 = \|r\|_2 \sin \angle(r, Cr)$. If $r = 0$ or $Cr = 0$, the quotient is $0$.

The self-preconditioned minimal-residual step for $Am = b$ with search direction $Mr$ is the
plain minimal-residual step for $Cy = b$ with $m = My$, so the one-step identity of
`Numlib.Projection.OneDimensional` applies to $C$. The minimal-residual step is
`Projection.minResStep`. The book derives from the identity the bound (10.59),
$\|r'\|_2 \le \|(I - AM) r\|_2$; this bound is not part of the formal statement. The second part
of the proposition, (10.60), is `SaadSparse.Chapter10.proposition_10_14`. -/
theorem proposition_10_13 (A M : Matrix (Fin n) (Fin n) ℝ) (b x : EuclideanSpace ℝ (Fin n)) :
    ‖b - ((A * M) ⬝ minResStep (Matrix.toEuclideanLin (A * M)) b x)‖ ^ 2 =
      ‖b - ((A * M) ⬝ x)‖ ^ 2 *
        (1 - ‖inner ℝ ((A * M) ⬝ (b - ((A * M) ⬝ x))) (b - ((A * M) ⬝ x))‖ ^ 2 /
          (‖b - ((A * M) ⬝ x)‖ ^ 2 * ‖(A * M) ⬝ (b - ((A * M) ⬝ x))‖ ^ 2)) :=
  Projection.norm_residual_minResStep_sq_eq x

/-- **Equation (10.61)** of [saad2003iterative]. Let $A, M \in \mathbb{R}^{n \times n}$, let
$\alpha \in \mathbb{R}$ and let $R = I - AM$. The global self-preconditioned minimal-residual
step $M' = M + \alpha M R$ has the residual
$$I - AM' = (1 - \alpha) R + \alpha R^2.$$
So after $k$ steps the residual $R_k$ is a polynomial of degree $2^k$ in $R_0$. -/
theorem equation_10_61 (A M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    1 - A * (M + α • (M * (1 - A * M))) = (1 - α) • (1 - A * M) + α • (1 - A * M) ^ 2 :=
  Preconditioner.residual_selfPreconditionedStep A M α

/-- **Equation (10.63)** of [saad2003iterative]. Let $A, M \in \mathbb{R}^{n \times n}$, let
$\alpha \in \mathbb{R}$, and let $B = AM$. The global self-preconditioned step
$M' = M + \alpha M (I - AM)$ gives the preconditioned matrix
$$B' = AM' = B + \alpha B (I - B).$$
So $B_k$ stays a polynomial in $B_0$. -/
theorem equation_10_63 (A M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    A * (M + α • (M * (1 - A * M))) = A * M + α • (A * M * (1 - A * M)) :=
  Preconditioner.mul_selfPreconditionedStep A M α

/-- **Section 10.5** of [saad2003iterative], the consequence that the book draws from (10.63). Let
$A, M \in \mathbb{R}^{n \times n}$ and $\alpha \in \mathbb{R}$. If $B = AM$ is symmetric, then
$AM'$ is symmetric for the global self-preconditioned step $M' = M + \alpha M (I - AM)$.

So a symmetric $B_0 = A M_0$, for example from $M_0 = \alpha_0 A^T$, keeps every $B_k$
symmetric. -/
theorem isSymm_mul_selfPreconditionedStep {A M : Matrix (Fin n) (Fin n) ℝ} (α : ℝ)
    (hB : (A * M).IsSymm) : (A * (M + α • (M * (1 - A * M)))).IsSymm := by
  have h1 : (A * M * (1 - A * M))ᵀ = A * M * (1 - A * M) := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hB, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [equation_10_63]
  change (A * M + α • (A * M * (1 - A * M)))ᵀ = A * M + α • (A * M * (1 - A * M))
  rw [Matrix.transpose_add, Matrix.transpose_smul, hB, h1]

/-- **Proposition 10.14** of [saad2003iterative], with (10.60). Let
$A, M \in \mathbb{R}^{n \times n}$, let $R = I - AM$, and let $\alpha \in \mathbb{R}$ minimize
the residual of the global self-preconditioned step: for every $t \in \mathbb{R}$,
$$\|I - A(M + \alpha M R)\|_F \le \|I - A(M + t M R)\|_F.$$
Then
$$\|I - A(M + \alpha M R)\|_F \le \|R\|_F^2.$$
So the global self-preconditioned minimal-residual iteration without dropping converges
quadratically when it converges.

The hypothesis is what a minimal-residual choice of the step length gives. The proof compares
with the step length $t = 1$, whose residual is $R^2$ by (10.61), and uses
$\|R^2\|_F \le \|R\|_F^2$. -/
theorem proposition_10_14 {A M : Matrix (Fin n) (Fin n) ℝ} {α : ℝ}
    (hmin : ∀ t : ℝ, ‖1 - A * (M + α • (M * (1 - A * M)))‖
      ≤ ‖1 - A * (M + t • (M * (1 - A * M)))‖) :
    ‖1 - A * (M + α • (M * (1 - A * M)))‖ ≤ ‖1 - A * M‖ ^ 2 :=
  Preconditioner.norm_le_norm_sq_of_isMinOn fun t => by
    simpa only [equation_10_61] using hmin t

/-! ### Lemma 10.15: the bordering algorithm -/

/-- **Lemma 10.15** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, let $L \in \mathbb{R}^{n \times n}$ be nonsingular, and let $k$ be an index.
Then
$$(L A L^T)_{kk} > 0.$$

**Reading.** The book states that in the bordering algorithm for a symmetric positive definite
$A$ the scalar $\delta_{k+1}$ of (10.70) is positive, however inaccurately the auxiliary systems
(10.67)–(10.68) are solved. The formal statement reads $\delta_{k+1}$ as the $(k+1, k+1)$ entry
of $L A L^T$, where $L$ is the unit lower triangular matrix that the algorithm builds, and
proves the positivity for every nonsingular $L$.

The index $k$ is $0$-based, so the entry $(k, k)$ is the book's entry $(k+1, k+1)$. The entry is
the value of the quadratic form of $A$ at the nonzero vector $L^T e_k$, so it is positive by
positive definiteness alone. -/
theorem lemma_10_15 {A L : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hL : IsUnit L)
    (k : Fin n) : 0 < (L * A * Lᵀ) k k := by
  have hinj : Function.Injective L.vecMul := Matrix.vecMul_injective_iff_isUnit.2 hL
  have h := hA.mul_mul_conjTranspose_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.diag_pos

end SaadSparse.Chapter10
