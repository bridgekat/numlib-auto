/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section05

/-!
# Golub and Van Loan, Section 7.6: Invariant subspace computations

This module formalizes §7.6 of [golub2013matrix], which computes eigenvectors and invariant
subspaces of a matrix $A \in \mathbb{R}^{n \times n}$ from an approximate eigenvalue or from a Schur
decomposition $Q^T A Q = T$. It covers inverse iteration (7.6.1), its convergence and its stopping
criterion (7.6.2) (§7.6.1); the invariant subspace spanned by the leading columns of $Q$ when the
diagonal blocks of $T$ have disjoint spectra, the $2 \times 2$ swap, and the reordering of a
triangular Schur form by Algorithm 7.6.1 (§7.6.2); block diagonalization of $T$ by the matrices
$Y_{ij}$, the column recurrences (7.6.4)–(7.6.5) of the Sylvester equation $FZ - ZG = C$, the
Bartels–Stewart algorithm (Algorithm 7.6.2), Algorithm 7.6.3, the bound (7.6.6) through the
separation, and the condition number of $Y_{ij}$ (§7.6.3); eigenvectors and the eigenvalue condition
from the Schur form (§7.6.4); and the number of Jordan blocks of each size from the dimensions of
the null spaces of the powers of $N = C - \lambda I$ (§7.6.5).

The proofs specialize the backbone: inverse iteration is the power method `Krylov.inverseIterate` of
`Numlib.Eigen.PowerMethod`, the separation is `Matrix.sep` of
`Numlib.LinearAlgebra.Matrix.Sylvester`, and the Jordan form is `Matrix.jordanForm` of
`Numlib.LinearAlgebra.Matrix.Jordan`. The invariant subspace result is
`GolubVanLoan.Chapter07.span_leading_schurVectors_eq` of §7.3. The algorithms call Algorithm 3.1.2
(back substitution) and the Givens rotations of §5.1.

## Main definitions

* Equation (7.6.1), `GolubVanLoan.Chapter07.inverseIteration`: inverse iteration with shift $\mu$,
  which returns the vectors $q^{(k)}$ and the Rayleigh quotients $\lambda^{(k)}$.
* Algorithm 7.6.1, `GolubVanLoan.Chapter07.algorithm_7_6_1`: reordering of a triangular real Schur
  form by Givens rotations so that the diagonal entries in a set $\Delta$ come first.
* Algorithm 7.6.2, `GolubVanLoan.Chapter07.algorithm_7_6_2`: the Bartels–Stewart algorithm for
  $FZ - ZG = C$ with $F$ and $G$ upper triangular.
* Algorithm 7.6.3, `GolubVanLoan.Chapter07.algorithm_7_6_3`: block diagonalization of a Schur form
  $T = Q^T A Q$, which overwrites $Q$ with $QY$.

## Main results

* Equation (7.6.1), `GolubVanLoan.Chapter07.equation_7_6_1`: if the shift $\mu$ is closer to the
  eigenvalue $\lambda_j$ than to every other eigenvalue, then the direction of $q^{(k)}$ converges
  to an eigenvector for $\lambda_j$ and $\lambda^{(k)} \to \lambda_j$.
* Equation (7.6.2), `GolubVanLoan.Chapter07.equation_7_6_2`: with $r = (A - \mu I) q$, the pair
  $(\mu, q)$ is an exact eigenpair of $A - r q^T$, and $\|r q^T\|_\infty \le \sqrt{n} \|r\|_\infty$.
* §7.6.2, `GolubVanLoan.Chapter07.invariantSubspace_leading_unique`: if $\lambda(T_{11}) \cap
  \lambda(T_{22}) = \emptyset$, the first $p$ columns of $Q$ span the unique invariant subspace of
  $A$ for $\lambda(T_{11})$.
* §7.6.2, `GolubVanLoan.Chapter07.swap_two_by_two`: a Givens rotation that zeroes the second entry
  of $(t_{12}, \lambda_2 - \lambda_1)$ swaps the diagonal entries $\lambda_1$ and $\lambda_2$ of a
  $2 \times 2$ upper triangular matrix.
* Algorithm 7.6.1, `GolubVanLoan.Chapter07.algorithm_7_6_1_spec`: after $n$ passes the output is an
  orthogonal similarity of $T$, upper triangular, with the diagonal entries in $\Delta$ first.
* §7.6.3, `GolubVanLoan.Chapter07.blockDiagonalization_update`: $Y_{ij} = I + Z$ has inverse
  $I - Z$, and $Y_{ij}^{-1} T Y_{ij} = T + TZ - ZT$.
* Equations (7.6.4)–(7.6.5), `GolubVanLoan.Chapter07.equation_7_6_5`: the columns of $FZ - ZG$ for
  an upper Hessenberg $G$, in the triangular case and in the case of a $2 \times 2$ diagonal block.
* Algorithm 7.6.2, `GolubVanLoan.Chapter07.algorithm_7_6_2_spec`: in exact arithmetic the output is
  the unique solution of $FZ - ZG = C$.
* Algorithm 7.6.3, `GolubVanLoan.Chapter07.algorithm_7_6_3_spec`: in exact arithmetic the output is
  $QY$ with $Y$ block unit upper triangular and $Y^{-1} T Y$ block diagonal.
* Equation (7.6.6), `GolubVanLoan.Chapter07.equation_7_6_6`: $\operatorname{sep}(T_{ii}, T_{jj})$ is
  at most the distance between the spectra, and a solution of $T_{ii} Z - Z T_{jj} = -T_{ij}$ has
  $\|Z\|_F \le \|T_{ij}\|_F / \operatorname{sep}(T_{ii}, T_{jj})$.
* §7.6.3, `GolubVanLoan.Chapter07.kappaF_blockUnit`: $\kappa_F(Y_{ij}) = n_i + n_j + \|Z\|_F^2$.
* §7.6.4, `GolubVanLoan.Chapter07.schur_eigenvectors`: right and left eigenvectors of $A$ from the
  Schur form, and the eigenvalue condition $\sqrt{(1 + w^T w)(1 + z^T z)}$.
* §7.6.5, `GolubVanLoan.Chapter07.jordan_block_count`: $\dim \operatorname{null}(N^{k+1}) - \dim
  \operatorname{null}(N^k)$ is the number of Jordan blocks for $\lambda$ of size at least $k + 1$.

## Proof outline

Each step of Algorithm 7.6.1 is the $2 \times 2$ swap in the plane $(k, k+1)$, so a pass acts on the
diagonal as one pass of a bubble sort, and $n$ passes sort it. Algorithm 7.6.3 builds $Y$ as the
product of the $Y_{ij}$ in the order of the loop. After the pair $(i, j)$ the block $(i, j)$ of
$Y^{-1} T Y$ is zero, by the Sylvester equation that Algorithm 7.6.2 solves, and it stays zero.

## Conventions

* Matrices are real, `Matrix (Fin n) (Fin n) ℝ`, where the source is real. The unique invariant
  subspace (§7.6.2) and the bound (7.6.6) are stated over `ℂ`, and inverse iteration over any
  `RCLike` field.
* Indices are 0-based: the source's $t_{kk}$, $k = 1, \dots, n$, is `T (k - 1) (k - 1)` with
  `k - 1 : Fin n`.
* The $\infty$-norm of a matrix is the operator norm of the scope `Matrix.Norms.Operator`, and the
  $\infty$-norm of a vector is the sup norm of `Fin n → ℝ`. The Frobenius norm is the norm of the
  scope `Matrix.Norms.Frobenius`.

## Implementation notes

* The algorithms are programs generic in a monad `M` and a rounding hook `rnd : ℝ → M ℝ`, as in the
  algorithm conventions of `NumlibSurface.GolubVanLoan`. Each has its exact semantics (`M := Id`,
  `rnd := pure`); the source analyses none of their rounding errors precisely, and no rounding
  theorem is stated.
* Algorithm 7.6.1 calls Algorithm 5.1.3 (`GolubVanLoan.Chapter05.algorithm_5_1_3`) and the Givens
  updates `GolubVanLoan.Chapter05.givensApplyLeft` and `GolubVanLoan.Chapter05.givensApplyRight`.
  Its `while` loop is at most `fuel` passes with a `done` flag.
* Algorithm 7.6.2 calls the back substitution Algorithm 3.1.2
  (`GolubVanLoan.Chapter03.algorithm_3_1_2`).
* Algorithm 7.6.3 represents the partitioning (7.6.3) by a block index `b : Fin n → Fin q`, which
  the specification assumes monotone. It extracts the diagonal blocks for Algorithm 7.6.2 and
  updates $T$ and $Q$ in place on index lists.

## Deviations from the source

* **Equation (7.6.1)** (reading). The source describes the convergence of inverse iteration
  informally; the statement fixes a precise form, in which $A$ need not be diagonalizable. See
  `GolubVanLoan.Chapter07.equation_7_6_1`.
* **Equation (7.6.1)** (generalization). Inverse iteration is defined over any `RCLike` field, not
  only over $\mathbb{R}$. See `GolubVanLoan.Chapter07.inverseIteration`.
* **Equation (7.6.2)** (reading). The source leaves the factor $\sqrt{n}$ in the bound on the
  perturbation implicit; the statement makes it explicit. See
  `GolubVanLoan.Chapter07.equation_7_6_2`.
* **§7.6.2, unique invariant subspace** (generalization). The source has a real orthogonal $Q$; the
  statement has a complex unitary $Q$, of which the real case is an instance. See
  `GolubVanLoan.Chapter07.invariantSubspace_leading_unique`.
* **Algorithm 7.6.1** (reading). The test $\{t_{11}, \dots, t_{pp}\} = \Delta$ is read with
  multiplicities: the diagonal entries in $\Delta$ come first. See
  `GolubVanLoan.Chapter07.algorithm_7_6_1_spec`.
* **Algorithm 7.6.3** (reading). The source applies Algorithm 7.6.2, which it states for triangular
  matrices only, to the blocks of a quasi-triangular $T$; the specification assumes $T$ upper
  triangular. See `GolubVanLoan.Chapter07.algorithm_7_6_3_spec`.
* **§7.6.3, condition of $Y_{ij}$** (correction). The source prints
  $\kappa_F(Y_{ij}) = n_i^2 + n_j^2 + \|Z\|_F^2$; the value is $n_i + n_j + \|Z\|_F^2$, because
  $\|I_k\|_F^2 = k$. See `GolubVanLoan.Chapter07.kappaF_blockUnit`.
* **§7.6.4** (generalization). The identities hold without the hypothesis $\lambda \notin
  \lambda(T_{11}) \cup \lambda(T_{33})$, which the source needs only to solve for $w$ and $z$. See
  `GolubVanLoan.Chapter07.schur_eigenvectors`.

## Not formalized

* **The quasi-triangular case of Algorithm 7.6.3.** It needs the $2p \times 2p$ systems (7.6.5),
  which the source does not write as an algorithm.
* **The SVD heuristic for why one step of inverse iteration suffices.**
* **The stability claims of §7.6.2.**
* **The relative error of the Sylvester solve after (7.6.6).** The source states it with $\approx$
  and gives no derivation.
* **The algorithm of Bavely and Stewart.**
* **The $7 \times 7$ example of a Jordan structure in §7.6.5.**
* **The flop counts.** Operation counts are out of scope for the library.
-/

open Matrix Filter Topology

namespace GolubVanLoan.Chapter07

open Chapter05 (selCols selCols_mul_apply_get selCols_mul_apply_of_notMem
  mul_selCols_transpose_apply_get mul_selCols_transpose_apply_of_notMem selCols_transpose_mul_apply
  mul_selCols_apply)

variable {n : ℕ}

/-! ### §7.6.1 Selected eigenvectors via inverse iteration -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Equation (7.6.1)** of [golub2013matrix] (inverse iteration). Let
$A \in \mathbb{K}^{n \times n}$ with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let
$\mu \in \mathbb{K}$ and $q^{(0)} \in \mathbb{K}^n$. Inverse iteration computes, for
$k = 1, 2, \dots$,
$$(A - \mu I) z^{(k)} = q^{(k-1)}, \qquad q^{(k)} = z^{(k)} / \|z^{(k)}\|_2, \qquad
  \lambda^{(k)} = q^{(k)H} A q^{(k)},$$
and returns the pair $(q^{(k)}, \lambda^{(k)})$; at $k = 0$ it returns
$(q^{(0)}, q^{(0)H} A q^{(0)})$.

**Generalization.** The source states inverse iteration over $\mathbb{R}$; the definition is
over any `RCLike` field.

The solve is $z^{(k)} = (A - \mu I)^{-1} q^{(k-1)}$ with the matrix inverse, which is $0$ when
$A - \mu I$ is singular; then $z^{(k)} = q^{(k)} = 0$. The source calls inverse iteration the
power method applied to $(A - \mu I)^{-1}$: for a unit $q^{(0)}$ and nonsingular $A - \mu I$ the
vectors are the backbone's `Krylov.inverseIterate`
(`GolubVanLoan.Chapter07.inverseIteration_fst`). -/
noncomputable def inverseIteration (A : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜)
    (q₀ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n) × 𝕜
  | 0 => (q₀, inner 𝕜 q₀ (toEuclideanLin A q₀))
  | k + 1 =>
    let z := toEuclideanLin (A - μ • 1)⁻¹ (inverseIteration A μ q₀ k).1
    let q := (‖z‖ : 𝕜)⁻¹ • z
    (q, inner 𝕜 q (toEuclideanLin A q))

/-- The eigenvalue estimate $\lambda^{(k)}$ of inverse iteration is the Rayleigh quotient
$q^{(k)H} A q^{(k)}$ of its vector $q^{(k)}$, for every $k$. -/
theorem inverseIteration_snd (A : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜)
    (q₀ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    (inverseIteration A μ q₀ k).2 =
      inner 𝕜 (inverseIteration A μ q₀ k).1 (toEuclideanLin A (inverseIteration A μ q₀ k).1) := by
  cases k <;> rfl

/-- For nonsingular $A - \mu I$, the operator of $A - \mu I$ on `EuclideanSpace` is a unit whose
ring inverse is the operator of $(A - \mu I)^{-1}$. -/
private theorem ringInverse_toEuclideanLin_sub {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜}
    (hA : IsUnit (A - μ • 1)) :
    IsUnit (toEuclideanLin A - μ • (1 : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)))) ∧
      Ring.inverse (toEuclideanLin A - μ • (1 : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)))) =
        toEuclideanLin (A - μ • 1)⁻¹ := by
  have hT : toEuclideanLin (A - μ • 1) =
      toEuclideanLin A - μ • (1 : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n))) := by
    rw [map_sub, map_smul, toLpLin_one]
    rfl
  have hdet : IsUnit (A - μ • 1).det := (isUnit_iff_isUnit_det _).1 hA
  have h1 : toEuclideanLin (A - μ • 1)⁻¹ * toEuclideanLin (A - μ • 1) = 1 := by
    rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, Matrix.nonsing_inv_mul _ hdet, toLpLin_one]
    rfl
  have h2 : toEuclideanLin (A - μ • 1) * toEuclideanLin (A - μ • 1)⁻¹ = 1 := by
    rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, Matrix.mul_nonsing_inv _ hdet, toLpLin_one]
    rfl
  rw [← hT]
  have hu : IsUnit (toEuclideanLin (A - μ • 1)) := ⟨⟨_, _, h2, h1⟩, rfl⟩
  refine ⟨hu, ?_⟩
  calc Ring.inverse (toEuclideanLin (A - μ • 1))
      = Ring.inverse (toEuclideanLin (A - μ • 1)) *
          (toEuclideanLin (A - μ • 1) * toEuclideanLin (A - μ • 1)⁻¹) := by rw [h2, mul_one]
    _ = toEuclideanLin (A - μ • 1)⁻¹ := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- Let $A - \mu I$ be nonsingular and $\|q^{(0)}\|_2 = 1$. Then the vectors $q^{(k)}$ of inverse
iteration (7.6.1) are the backbone's `Krylov.inverseIterate`, the power method on
$(A - \mu I)^{-1}$. -/
theorem inverseIteration_fst {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜} (hA : IsUnit (A - μ • 1))
    {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    (inverseIteration A μ q₀ k).1 = Krylov.inverseIterate (toEuclideanLin A) μ q₀ k := by
  rw [Krylov.inverseIterate_eq_powerIterate, (ringInverse_toEuclideanLin_sub hA).2]
  refine Krylov.eq_powerIterate_of_recurrence _ q₀
    (y := fun j => (inverseIteration A μ q₀ j).1) ?_ (fun _ => rfl) k
  change q₀ = _
  rw [hq₀, RCLike.ofReal_one, inv_one, one_smul]

/-- **Equation (7.6.1)** of [golub2013matrix], convergence of inverse iteration. Let
$A \in \mathbb{K}^{n \times n}$ with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$\mu, \lambda_j \in \mathbb{K}$ with $A - \mu I$ nonsingular. Let $u \neq 0$ satisfy
$Au = \lambda_j u$, let $w$ lie in the sum of the generalized eigenspaces of $A$ for the
eigenvalues $\nu \neq \lambda_j$, and let $q^{(0)} = u + w$ with $\|q^{(0)}\|_2 = 1$. Suppose
that $|\lambda_j - \mu| < |\nu - \mu|$ for every eigenvalue $\nu \neq \lambda_j$ of $A$. Then
the iterates $(q^{(k)}, \lambda^{(k)})$ of (7.6.1) satisfy
$$\Bigl(\frac{\lambda_j - \mu}{|\lambda_j - \mu|}\Bigr)^k q^{(k)} \to \frac{u}{\|u\|_2}
  \quad\text{and}\quad \lambda^{(k)} \to \lambda_j \qquad (k \to \infty).$$

**Reading.** The source argues informally: it writes $q^{(0)} = \sum_i \beta_i x_i$ in
eigenvectors with $\beta_j \neq 0$, and says that if $\mu$ is much closer to $\lambda_j$ than to
the other eigenvalues, then $q^{(k)}$ is rich in the direction of $x_j$. The statement makes
this precise as the convergence of the direction of $q^{(k)}$ and of $\lambda^{(k)}$, and it
lets the component $w$ lie in generalized eigenspaces, so that $A$ need not be diagonalizable.

The proof specializes `Krylov.tendsto_smul_inverseIterate` and
`Krylov.tendsto_inner_inverseIterate`. -/
theorem equation_7_6_1 {A : Matrix (Fin n) (Fin n) 𝕜} {μ l : 𝕜} (hA : IsUnit (A - μ • 1))
    {u w q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (hu : toEuclideanLin A u = l • u)
    (hu0 : u ≠ 0)
    (hw : w ∈ ⨆ ν, ⨆ _ : ν ≠ l, Module.End.maxGenEigenspace (toEuclideanLin A) ν)
    (hdom : ∀ ν, ν ≠ l → Module.End.HasEigenvalue (toEuclideanLin A) ν → ‖l - μ‖ < ‖ν - μ‖)
    (hq : q₀ = u + w) :
    Tendsto (fun k => (((l - μ) / (‖l - μ‖ : 𝕜)) ^ k) • (inverseIteration A μ q₀ k).1) atTop
        (𝓝 ((‖u‖ : 𝕜)⁻¹ • u)) ∧
      Tendsto (fun k => (inverseIteration A μ q₀ k).2) atTop (𝓝 l) := by
  have hσ := (ringInverse_toEuclideanLin_sub hA).1
  refine ⟨?_, ?_⟩
  · simp_rw [inverseIteration_fst hA hq₀]
    exact Krylov.tendsto_smul_inverseIterate hσ hu hu0 hw hdom hq
  · simp_rw [inverseIteration_snd, inverseIteration_fst hA hq₀]
    exact Krylov.tendsto_inner_inverseIterate (LinearMap.continuous_of_finiteDimensional _) hσ hu
      hu0 hw hdom hq

end RCLike

section LInfty

open scoped Matrix.Norms.Operator

/-- **Equation (7.6.2)** of [golub2013matrix] and the sentence after it. Let
$A \in \mathbb{R}^{n \times n}$, $\mu \in \mathbb{R}$ and $q \in \mathbb{R}^n$ with
$\|q\|_2 = 1$. Put $r = (A - \mu I) q$ and $E = -r q^T$. Then
$$(A + E) q = \mu q, \qquad \|E\|_\infty = \|r\|_\infty \|q\|_1 \le \sqrt{n} \, \|r\|_\infty.$$
Hence the stopping test $\|r\|_\infty \le c u \|A\|_\infty$ of (7.6.2) makes $(\mu, q)$ an exact
eigenpair of a matrix $A + E$ with $\|E\|_\infty \le \sqrt{n} \, c u \|A\|_\infty$.

**Reading.** The source leaves the factor $\sqrt{n}$ in the bound on $E$ implicit; the statement
makes it explicit.

The matrix norm is the $\infty$-operator norm of the scope `Matrix.Norms.Operator`, $\|q\|_1$ is
written $\sum_i |q_i|$, and $r q^T$ is `Matrix.vecMulVec r q`. -/
theorem equation_7_6_2 {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} {q : Fin n → ℝ}
    (hq : ‖WithLp.toLp 2 q‖ = 1) :
    (A + -vecMulVec ((A - μ • 1) *ᵥ q) q) *ᵥ q = μ • q ∧
      ‖-vecMulVec ((A - μ • 1) *ᵥ q) q‖ = ‖(A - μ • 1) *ᵥ q‖ * ∑ i, |q i| ∧
      ‖-vecMulVec ((A - μ • 1) *ᵥ q) q‖ ≤ √n * ‖(A - μ • 1) *ᵥ q‖ := by
  set r := (A - μ • 1) *ᵥ q
  have hqq : q ⬝ᵥ q = 1 := by
    have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 q)
    rw [hq, one_pow] at h
    rw [dotProduct, h]
    simp [sq]
  have hnorm : ‖-vecMulVec r q‖ = ‖r‖ * ∑ i, |q i| := by
    have e : ∀ i, ∑ j, ‖vecMulVec r q i j‖₊ = ‖r i‖₊ * ∑ j, ‖q j‖₊ := fun i => by
      simp only [vecMulVec_apply, nnnorm_mul, Finset.mul_sum]
    have hr : ‖r‖ = ((Finset.univ.sup fun b => ‖r b‖₊ : NNReal) : ℝ) := Pi.norm_def r
    rw [norm_neg, linfty_opNorm_def, hr]
    simp_rw [e]
    rw [← NNReal.finset_sup_mul, NNReal.coe_mul, NNReal.coe_sum]
    simp [Real.norm_eq_abs]
  have hl1 : ∑ i, |q i| ≤ √n := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) fun i => |q i|
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at hcs
    have hsq : ∑ i, q i ^ 2 = 1 := by rw [← hqq]; simp [dotProduct, sq]
    rw [hsq, mul_one] at hcs
    exact Real.le_sqrt_of_sq_le hcs
  refine ⟨?_, hnorm, ?_⟩
  · rw [add_mulVec, neg_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hqq, one_smul]
    simp only [r, sub_mulVec, smul_mulVec, one_mulVec]
    abel
  · rw [hnorm, mul_comm]
    exact mul_le_mul_of_nonneg_right hl1 (norm_nonneg _)

end LInfty

/-! ### §7.6.2 Orthogonal bases for selected invariant subspaces -/

/-- **§7.6.2** of [golub2013matrix], the unique invariant subspace. Let
$A, Q \in \mathbb{C}^{(p+q) \times (p+q)}$ with $Q$ unitary, and suppose that
$$Q^H A Q = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}$$
with $T_{11} \in \mathbb{C}^{p \times p}$, $T_{22} \in \mathbb{C}^{q \times q}$ and
$\lambda(T_{11}) \cap \lambda(T_{22}) = \emptyset$. Let $S_1$ be the span of the first $p$
columns of $Q$. Then $S_1$ is the sum of the generalized eigenspaces of $A$ for the eigenvalues
in $\lambda(T_{11})$. Moreover, every $A$-invariant subspace $S$ of dimension $p$ that contains
no eigenvector of $A$ for an eigenvalue outside $\lambda(T_{11})$ equals $S_1$. This is the
unique invariant subspace associated with $\lambda(T_{11})$, as in §7.1.4 of the source.

**Generalization.** The source has a real orthogonal $Q$; the statement has a complex unitary
$Q$, and the real case is an instance.

The block form is stated through `Matrix.reindex` along `finSumFinEquiv` and
`Matrix.fromBlocks`. The proof is `GolubVanLoan.Chapter07.span_leading_schurVectors_eq`. -/
theorem invariantSubspace_leading_unique {p q : ℕ} {A Q : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin (p + q)) ℂ) {T₁₁ : Matrix (Fin p) (Fin p) ℂ}
    {T₁₂ : Matrix (Fin p) (Fin q) ℂ} {T₂₂ : Matrix (Fin q) (Fin q) ℂ}
    (hT : (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
      fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdisj : spectrum ℂ T₁₁ ∩ spectrum ℂ T₂₂ = ∅) :
    Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) =
        ⨆ μ ∈ spectrum ℂ T₁₁, Module.End.maxGenEigenspace (toLin' A) μ ∧
      ∀ S ∈ Module.End.invtSubmodule (toLin' A), Module.finrank ℂ S = p →
        (∀ μ ∉ spectrum ℂ T₁₁, ∀ x ∈ S, A *ᵥ x = μ • x → x = 0) →
        S = Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) :=
  span_leading_schurVectors_eq hQ hT (Set.disjoint_iff_inter_eq_empty.2 hdisj)

/-- **§7.6.2** of [golub2013matrix], the $2 \times 2$ swap. Let $\lambda_1, \lambda_2, t_{12}, c, s
\in \mathbb{R}$ with $c^2 + s^2 = 1$, and put
$$T_F = \begin{bmatrix} \lambda_1 & t_{12} \\ 0 & \lambda_2 \end{bmatrix}, \qquad
  x = \begin{bmatrix} t_{12} \\ \lambda_2 - \lambda_1 \end{bmatrix}, \qquad
  Q_D = \begin{bmatrix} c & s \\ -s & c \end{bmatrix}.$$
If the second entry of $Q_D^T x$ is zero, as for the output of
$\mathtt{givens}(t_{12}, \lambda_2 - \lambda_1)$, then $T_F x = \lambda_2 x$ and
$$Q_D^T T_F Q_D = \begin{bmatrix} \lambda_2 & t_{12} \\ 0 & \lambda_1 \end{bmatrix}.$$

The source writes the $(1, 2)$ entry of the result as $\pm t_{12}$; with this sign convention
for $Q_D$ it is $t_{12}$. The second entry of a vector is index `1`. -/
theorem swap_two_by_two {l₁ l₂ t c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hQx : ((!![c, s; -s, c])ᵀ *ᵥ ![t, l₂ - l₁]) 1 = 0) :
    !![l₁, t; 0, l₂] *ᵥ ![t, l₂ - l₁] = l₂ • ![t, l₂ - l₁] ∧
      (!![c, s; -s, c])ᵀ * !![l₁, t; 0, l₂] * !![c, s; -s, c] = !![l₂, t; 0, l₁] := by
  have h : s * t + c * (l₂ - l₁) = 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using hQx
  constructor
  · ext i
    fin_cases i
    · simp only [mulVec, dotProduct, Fin.sum_univ_two]
      simp
      ring
    · simp only [mulVec, dotProduct, Fin.sum_univ_two]
      simp
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-c) * h + l₂ * hcs
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-s) * h + t * hcs
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-s) * h
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination c * h + l₁ * hcs

/-! ### §7.6.2 Algorithm 7.6.1: reordering the Schur form -/

section Reorder

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The test of the `while` loop of Algorithm 7.6.1, $\{t_{11}, \dots, t_{pp}\} = \Delta$, read with
multiplicities: $T$ satisfies it if every diagonal entry above a diagonal entry in $\Delta$ is
also in $\Delta$, that is, the diagonal entries in $\Delta$ come first. -/
def IsDeltaLeading (Δ : Finset ℝ) (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ k j : Fin n, j ≤ k → T k k ∈ Δ → T j j ∈ Δ

/-- The `while` test of Algorithm 7.6.1 is decidable, through the decidable comparisons of real
numbers. -/
noncomputable instance instDecidableIsDeltaLeading (Δ : Finset ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : Decidable (IsDeltaLeading Δ T) := by
  unfold IsDeltaLeading
  infer_instance

/-- One step $k$ of the inner loop of Algorithm 7.6.1 on the pair $(Q, T)$, with $k$ 0-based. If
$k + 1 < n$, $t_{kk} \notin \Delta$ and $t_{k+1,k+1} \in \Delta$ (exact comparisons), the step
computes $[c, s] = \mathtt{givens}(t_{k,k+1}, \mathrm{fl}(t_{k+1,k+1} - t_{kk}))$ by Algorithm 5.1.3
and puts $G = \begin{bmatrix} c & s \\ -s & c \end{bmatrix}$. It then replaces rows $k, k+1$ of $T$
in the columns $j \ge k$ by their product with $G^T$ on the left, columns $k, k+1$ of $T$ in the
rows $i \le k + 1$ by their product with $G$ on the right, and columns $k, k+1$ of $Q$ by their
product with $G$ on the right. These are the source's
$$T(k{:}k{+}1, k{:}n) = G^T \, T(k{:}k{+}1, k{:}n), \qquad
  T(1{:}k{+}1, k{:}k{+}1) = T(1{:}k{+}1, k{:}k{+}1) \, G, \qquad
  Q(1{:}n, k{:}k{+}1) = Q(1{:}n, k{:}k{+}1) \, G,$$
computed by `GolubVanLoan.Chapter05.givensApplyLeft` and `GolubVanLoan.Chapter05.givensApplyRight`
on lists of indices. Otherwise the step returns $(Q, T)$ unchanged. -/
noncomputable def schurSwapStep (Δ : Finset ℝ)
    (QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if hk : k + 1 < n then
    if QT.2 ⟨k, by omega⟩ ⟨k, by omega⟩ ∉ Δ ∧ QT.2 ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ ∈ Δ then do
      let d ← rnd (QT.2 ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ - QT.2 ⟨k, by omega⟩ ⟨k, by omega⟩)
      let cs ← Chapter05.algorithm_5_1_3 rnd (QT.2 ⟨k, by omega⟩ ⟨k + 1, hk⟩) d
      let T ← Chapter05.givensApplyLeft rnd ⟨k, by omega⟩ ⟨k + 1, hk⟩ cs.1 cs.2
        (Chapter05.indexFrom n k) QT.2
      let T ← Chapter05.givensApplyRight rnd ⟨k, by omega⟩ ⟨k + 1, hk⟩ cs.1 cs.2
        ((List.finRange n).filter fun i => (i : ℕ) ≤ k + 1) T
      let Q ← Chapter05.givensApplyRight rnd ⟨k, by omega⟩ ⟨k + 1, hk⟩ cs.1 cs.2
        (List.finRange n) QT.1
      pure (Q, T)
    else pure QT
  else pure QT

/-- One pass of the `while` loop of Algorithm 7.6.1 on the state $((Q, T), \mathit{done})$. If
$\mathit{done}$ is set, the pass does nothing. If $T$ satisfies the test
`GolubVanLoan.Chapter07.IsDeltaLeading`, it sets $\mathit{done}$. Otherwise it runs the inner
loop, the fold of `GolubVanLoan.Chapter07.schurSwapStep` over $k = 0, \dots, n-2$. -/
noncomputable def schurReorderPass (Δ : Finset ℝ)
    (st : (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) × Bool) :
    M ((Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) × Bool) :=
  if st.2 then pure st
  else if IsDeltaLeading Δ st.1.2 then pure (st.1, true)
  else do
    let QT ← (List.range (n - 1)).foldlM (schurSwapStep rnd Δ) st.1
    pure (QT, false)

/-- **Algorithm 7.6.1** of [golub2013matrix] (reordering the real Schur form, no $2 \times 2$
bumps). Given an orthogonal matrix $Q \in \mathbb{R}^{n \times n}$, an upper triangular matrix
$T = Q^T A Q$, and a subset $\Delta = \{\lambda_1, \dots, \lambda_p\}$ of $\lambda(A)$, the
algorithm computes an orthogonal matrix $Q_D$ such that $Q_D^T T Q_D = S$ is upper triangular
and $\{s_{11}, \dots, s_{pp}\} = \Delta$. The matrices $Q$ and $T$ are overwritten by $Q Q_D$
and $S$.
```
while {t₁₁, …, t_pp} ≠ Δ
    for k = 1:n-1
        if t_kk ∉ Δ and t_{k+1,k+1} ∈ Δ
            [c, s] = givens(T(k, k+1), T(k+1, k+1) - T(k, k))
            T(k:k+1, k:n) = [c s; -s c]ᵀ T(k:k+1, k:n)
            T(1:k+1, k:k+1) = T(1:k+1, k:k+1) [c s; -s c]
            Q(1:n, k:k+1) = Q(1:n, k:k+1) [c s; -s c]
        end
    end
end
```
The program returns the pair $(Q, T)$. It has no hypothesis on its inputs.

**Reading.** The `while` test $\{t_{11}, \dots, t_{pp}\} = \Delta$ is read with multiplicities,
as `GolubVanLoan.Chapter07.IsDeltaLeading`: the diagonal entries in $\Delta$ come first.

The `while` loop is at most `fuel` passes with a `done` flag, and a pass is
`GolubVanLoan.Chapter07.schurReorderPass`. The difference $t_{k+1,k+1} - t_{kk}$ and every
operation of the rotations are rounded by `rnd`. -/
noncomputable def algorithm_7_6_1 (Q T : Matrix (Fin n) (Fin n) ℝ) (Δ : Finset ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let st ← (List.range fuel).foldlM (fun st _ => schurReorderPass rnd Δ st) ((Q, T), false)
  pure st.1

end Reorder

section ReorderDiag

/-!
### The diagonal of Algorithm 7.6.1 as a bubble sort

The private declarations below describe the effect of Algorithm 7.6.1 on the diagonal: one step
exchanges two neighbouring entries, and after $j$ passes the last $\min(j, f)$ diagonal entries are
outside $\Delta$, where $f$ is the number of diagonal entries outside $\Delta$.
-/

variable (Δ : Finset ℝ)

/-- The effect of one step of Algorithm 7.6.1 on the diagonal: entries $k$ and $k + 1$ are exchanged
when the first is outside $\Delta$ and the second is in $\Delta$. -/
private noncomputable def diagSwapStep (d : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  if hk : k + 1 < n then
    if d ⟨k, by omega⟩ ∉ Δ ∧ d ⟨k + 1, hk⟩ ∈ Δ then d ∘ Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩
    else d
  else d

/-- The number of diagonal entries outside $\Delta$. -/
private noncomputable def outCount (d : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i => d i ∉ Δ).card

/-- The last $t$ diagonal entries lie outside $\Delta$. -/
private def TailOut (t : ℕ) (d : Fin n → ℝ) : Prop := ∀ i : Fin n, n ≤ (i : ℕ) + t → d i ∉ Δ

/-- The diagonal entries in $\Delta$ come first. -/
private def Leading (d : Fin n → ℝ) : Prop := ∀ k j : Fin n, j ≤ k → d k ∈ Δ → d j ∈ Δ

private theorem foldl_diagSwapStep_perm (l : List ℕ) (d : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), l.foldl (diagSwapStep Δ) d = d ∘ σ := by
  induction l generalizing d with
  | nil => exact ⟨1, rfl⟩
  | cons a l ih =>
    have h1 : ∃ σ : Equiv.Perm (Fin n), diagSwapStep Δ d a = d ∘ σ := by
      unfold diagSwapStep
      split_ifs
      · exact ⟨Equiv.swap _ _, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
    obtain ⟨σ₁, h₁⟩ := h1
    obtain ⟨σ₂, h₂⟩ := ih (diagSwapStep Δ d a)
    refine ⟨σ₂.trans σ₁, ?_⟩
    rw [List.foldl_cons, h₂, h₁]
    rfl

private theorem outCount_comp_perm (d : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    outCount Δ (d ∘ σ) = outCount Δ d := by
  unfold outCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (σ.subtypeEquiv fun _ => Iff.rfl)

private theorem card_filter_le_add (t : ℕ) :
    (Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + t).card = min t n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < n - t)
  rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < n - t) =
      Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := i.2
    omega
  rw [e] at h
  omega

private theorem outCount_le (d : Fin n → ℝ) : outCount Δ d ≤ n := by
  unfold outCount
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem leading_diagSwapStep {d : Fin n → ℝ} (hd : Leading Δ d) (k : ℕ) :
    diagSwapStep Δ d k = d := by
  unfold diagSwapStep
  split_ifs with hk h
  · exact absurd (hd _ _ (by rw [Fin.le_def]; simp) h.2) h.1
  · rfl
  · rfl

private theorem leading_foldl {d : Fin n → ℝ} (hd : Leading Δ d) (l : List ℕ) :
    l.foldl (diagSwapStep Δ) d = d := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, leading_diagSwapStep Δ hd, ih]

/-- If the entries in $\Delta$ come first and $t \le f$, then the last $t$ entries are outside
$\Delta$. -/
private theorem tailOut_of_leading {d : Fin n → ℝ} (hd : Leading Δ d) {t : ℕ}
    (ht : t ≤ outCount Δ d) : TailOut Δ t d := by
  intro i hi hin
  have hsub : (Finset.univ.filter fun j : Fin n => (j : ℕ) < i + 1) ⊆
      Finset.univ.filter fun j => d j ∈ Δ := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hd i j (by rw [Fin.le_def]; omega) hin
  have h1 := Finset.card_le_card hsub
  rw [Fin.card_filter_val_lt] at h1
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun j => d j ∈ Δ)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  unfold outCount at ht
  have := i.2
  omega

/-- If the last $f$ entries are outside $\Delta$, then the entries in $\Delta$ are exactly the first
$n - f$. -/
private theorem mem_iff_of_tailOut {d : Fin n → ℝ} (hd : TailOut Δ (outCount Δ d) d)
    (k : Fin n) : d k ∈ Δ ↔ (k : ℕ) + outCount Δ d < n := by
  constructor
  · intro hk
    by_contra h
    exact hd k (by omega) hk
  · intro hk
    by_contra hkΔ
    have hsub : insert k (Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + outCount Δ d) ⊆
        Finset.univ.filter fun i => d i ∉ Δ := by
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa using hkΔ
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hd j hj
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp; omega), card_filter_le_add,
      min_eq_left (outCount_le Δ d)] at h1
    unfold outCount at h1
    omega

private theorem leading_of_tailOut {d : Fin n → ℝ} (hd : TailOut Δ (outCount Δ d) d) :
    Leading Δ d := by
  intro k j hjk hk
  rw [mem_iff_of_tailOut Δ hd] at hk ⊢
  rw [Fin.le_def] at hjk
  omega

/-- If more than $t$ entries are outside $\Delta$, then some entry above the last $t$ is outside
$\Delta$. -/
private theorem exists_out_of_tailOut {d : Fin n → ℝ} {t : ℕ}
    (ht : t < outCount Δ d) : ∃ i : Fin n, (i : ℕ) + t < n ∧ d i ∉ Δ := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ.filter fun i : Fin n => d i ∉ Δ) ⊆
      Finset.univ.filter fun i : Fin n => n ≤ (i : ℕ) + t := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra h'
    exact hi (h i (by omega))
  have h1 := Finset.card_le_card hsub
  rw [card_filter_le_add] at h1
  unfold outCount at ht
  omega

/-- One pass of the bubble sort: if $t < f$ and the last $t$ diagonal entries are outside $\Delta$,
then after one pass the last $t + 1$ are. -/
private theorem tailOut_pass {d : Fin n → ℝ} {t : ℕ} (hd : TailOut Δ t d)
    (ht : t < outCount Δ d) :
    TailOut Δ (t + 1) ((List.range (n - 1)).foldl (diagSwapStep Δ) d) := by
  have inv : ∀ k : ℕ, TailOut Δ t ((List.range k).foldl (diagSwapStep Δ) d) ∧
      ∀ m : Fin n, (m : ℕ) = min k (n - t - 1) →
        (∃ i : Fin n, i ≤ m ∧ (List.range k).foldl (diagSwapStep Δ) d i ∉ Δ) →
          (List.range k).foldl (diagSwapStep Δ) d m ∉ Δ := by
    intro k
    induction k with
    | zero =>
      refine ⟨hd, fun m hm ⟨i, him, hi⟩ => ?_⟩
      have : i = m := Fin.ext (by rw [Fin.le_def] at him; simp at hm; omega)
      rwa [← this]
    | succ k ih =>
      obtain ⟨ihA, ihB⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set e := (List.range k).foldl (diagSwapStep Δ) d
      unfold diagSwapStep
      split_ifs with hk hc
      · -- a swap at `k`: then `k + 1` is above the tail
        have hkt : k + 1 + t < n := by
          by_contra h
          exact ihA ⟨k + 1, hk⟩ (by simp; omega) hc.2
        refine ⟨fun i hi => ?_, fun m hm _ => ?_⟩
        · have h1 : i ≠ ⟨k, by omega⟩ := fun h => by rw [h] at hi; simp at hi; omega
          have h2 : i ≠ ⟨k + 1, hk⟩ := fun h => by rw [h] at hi; simp at hi; omega
          simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
          exact ihA i hi
        · have : m = ⟨k + 1, hk⟩ := Fin.ext (by simp at hm ⊢; omega)
          subst this
          simp only [Function.comp_apply, Equiv.swap_apply_right]
          exact hc.1
      · refine ⟨ihA, fun m hm ⟨i, him, hi⟩ => ?_⟩
        by_cases hkt : k < n - t - 1
        · have hm' : (m : ℕ) = k + 1 := by rw [hm]; omega
          by_cases hi' : i = m
          · rwa [← hi']
          · have him' : (i : ℕ) ≤ k := by
              rw [Fin.le_def] at him
              have := Fin.val_ne_iff.2 hi'
              omega
            have hek : e ⟨k, by omega⟩ ∉ Δ :=
              ihB ⟨k, by omega⟩ (by simp; omega) ⟨i, by rw [Fin.le_def]; simpa using him', hi⟩
            have : m = ⟨k + 1, hk⟩ := Fin.ext hm'
            subst this
            exact fun h => hc ⟨hek, h⟩
        · exact ihB m (by rw [hm]; omega) ⟨i, him, hi⟩
      · exact ⟨ihA, fun m hm hex => ihB m (by rw [hm]; omega) hex⟩
  obtain ⟨hA, hB⟩ := inv (n - 1)
  obtain ⟨σ, hσ⟩ := foldl_diagSwapStep_perm Δ (List.range (n - 1)) d
  obtain ⟨i, hi, hiΔ⟩ := exists_out_of_tailOut Δ
    (d := (List.range (n - 1)).foldl (diagSwapStep Δ) d) (t := t)
    (by rw [hσ, outCount_comp_perm]; exact ht)
  intro j hj
  by_cases hjt : n ≤ (j : ℕ) + t
  · exact hA j hjt
  · exact hB j (by omega) ⟨i, by rw [Fin.le_def]; omega, hiΔ⟩

end ReorderDiag

section ReorderSpec

/-- For $T$ upper triangular and a rotation $(c, s)$ with
$s t_{i,i+1} + c (t_{i+1,i+1} - t_{ii}) = 0$, the matrix
$G(i, i+1, \theta)^T T G(i, i+1, \theta)$ is upper triangular with the diagonal entries $i$ and
$i + 1$ of $T$ exchanged. -/
private theorem conj_givensRotation_swap {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsUpperTriangular)
    {i i' : Fin n} (hii' : (i' : ℕ) = i + 1) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (h : s * T i i' + c * (T i' i' - T i i) = 0) :
    ((Chapter05.givensRotation i i' c s)ᵀ * T *
        Chapter05.givensRotation i i' c s).IsUpperTriangular ∧
      ∀ r, ((Chapter05.givensRotation i i' c s)ᵀ * T * Chapter05.givensRotation i i' c s) r r =
        T (Equiv.swap i i' r) (Equiv.swap i i' r) := by
  have hne : i ≠ i' := fun e => by rw [e] at hii'; omega
  have z : ∀ x y : Fin n, (y : ℕ) < x → T x y = 0 := fun x y hxy => hT (show y < x from hxy)
  have hz : T i' i = 0 := z _ _ (by omega)
  have hne' : i' ≠ i := Ne.symm hne
  unfold Chapter05.givensRotation
  refine ⟨fun p q hpq => ?_, fun r => ?_⟩
  · change q < p at hpq
    rw [Fin.lt_def] at hpq
    simp only [mul_planeRotation_apply hne, transpose_planeRotation_mul_apply hne]
    by_cases hqi : q = i
    · subst hqi
      by_cases hpi' : p = i'
      · subst hpi'
        simp only [ite_true, hne', ite_false]
        linear_combination (-s) * h + (c * c) * hz
      · have hpq' : p ≠ q := fun e => by rw [e] at hpq; omega
        simp only [ite_true, hpq', hpi', ite_false,
          z _ _ hpq, z _ _ (show (i' : ℕ) < p by have := Fin.val_ne_iff.2 hpi'; omega)]
        ring
    · by_cases hqi' : q = i'
      · subst hqi'
        have hpi : p ≠ i := fun e => by rw [e] at hpq; omega
        have hpi' : p ≠ q := fun e => by rw [e] at hpq; omega
        simp only [hqi, ite_true, hpi, hpi', ite_false,
          z _ _ (show (i : ℕ) < p by omega), z _ _ hpq]
        ring
      · simp only [hqi, hqi', ite_false]
        by_cases hpi : p = i
        · subst hpi
          simp only [ite_true, z _ _ hpq, z _ _ (show (q : ℕ) < i' by omega)]
          ring
        · by_cases hpi' : p = i'
          · subst hpi'
            have : (q : ℕ) < i := by have := Fin.val_ne_iff.2 hqi; omega
            simp only [hpi, ite_true, ite_false, z _ _ this, z _ _ hpq]
            ring
          · simp only [hpi, hpi', ite_false]
            exact z _ _ hpq
  · simp only [mul_planeRotation_apply hne, transpose_planeRotation_mul_apply hne]
    by_cases hri : r = i
    · subst hri
      simp only [Equiv.swap_apply_left, ite_true, hz]
      linear_combination T i' i' * hcs - c * h
    · by_cases hri' : r = i'
      · subst hri'
        simp only [Equiv.swap_apply_right, hri, ite_true, ite_false, hz]
        linear_combination T i i * hcs + c * h
      · simp only [Equiv.swap_apply_of_ne_of_ne hri hri', hri, hri', ite_false]

/-- In exact arithmetic one step of Algorithm 7.6.1 maps $(Q, T)$, with $T$ upper triangular, to
$(QG, G^T T G)$ for an orthogonal $G$, upper triangular, with the diagonal moved by one step of
the bubble sort. -/
private theorem schurSwapStep_pure (Δ : Finset ℝ)
    (QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (hT : QT.2.IsUpperTriangular)
    (k : ℕ) :
    ∃ G ∈ orthogonalGroup (Fin n) ℝ, (Id.run (schurSwapStep pure Δ QT k)).1 = QT.1 * G ∧
      (Id.run (schurSwapStep pure Δ QT k)).2 = Gᵀ * QT.2 * G ∧
      (Id.run (schurSwapStep pure Δ QT k)).2.IsUpperTriangular ∧
      (fun r => (Id.run (schurSwapStep pure Δ QT k)).2 r r) =
        diagSwapStep Δ (fun r => QT.2 r r) k := by
  have hid : Id.run (schurSwapStep pure Δ QT k) = QT → ∃ G ∈ orthogonalGroup (Fin n) ℝ,
      (Id.run (schurSwapStep pure Δ QT k)).1 = QT.1 * G ∧
      (Id.run (schurSwapStep pure Δ QT k)).2 = Gᵀ * QT.2 * G ∧
      (Id.run (schurSwapStep pure Δ QT k)).2.IsUpperTriangular ∧
      (fun r => (Id.run (schurSwapStep pure Δ QT k)).2 r r) = (fun r => QT.2 r r) := fun h =>
    ⟨1, one_mem _, by rw [h, Matrix.mul_one], by rw [h]; simp, by rw [h]; exact hT, by rw [h]⟩
  by_cases hk : k + 1 < n
  swap
  · have h := hid (by unfold schurSwapStep; rw [dite_eq_right_iff.2 fun h => absurd h hk]; rfl)
    unfold diagSwapStep
    rwa [dite_eq_right_iff.2 fun h => absurd h hk]
  set i : Fin n := ⟨k, by omega⟩ with hi_def
  set i' : Fin n := ⟨k + 1, hk⟩ with hi'_def
  by_cases hc : QT.2 i i ∉ Δ ∧ QT.2 i' i' ∈ Δ
  swap
  · have hrun : Id.run (schurSwapStep pure Δ QT k) = QT := by
      unfold schurSwapStep
      split_ifs
      rfl
    have hd : diagSwapStep Δ (fun r => QT.2 r r) k = fun r => QT.2 r r := by
      unfold diagSwapStep
      split_ifs
      rfl
    rw [hd]
    exact hid hrun
  have hne : i ≠ i' := fun e => by simp [i, i', Fin.ext_iff] at e
  have z : ∀ x y : Fin n, (y : ℕ) < x → QT.2 x y = 0 := fun x y hxy => hT (show y < x from hxy)
  obtain ⟨hcs, hsc, -⟩ := Chapter05.algorithm_5_1_3_spec (QT.2 i i') (QT.2 i' i' - QT.2 i i)
  set c := (Id.run (Chapter05.algorithm_5_1_3 pure (QT.2 i i') (QT.2 i' i' - QT.2 i i))).1
  set s := (Id.run (Chapter05.algorithm_5_1_3 pure (QT.2 i i') (QT.2 i' i' - QT.2 i i))).2
  have hrun : Id.run (schurSwapStep pure Δ QT k) =
      (Id.run (Chapter05.givensApplyRight pure i i' c s (List.finRange n) QT.1),
        Id.run (Chapter05.givensApplyRight pure i i' c s
          ((List.finRange n).filter fun r => (r : ℕ) ≤ k + 1)
          (Id.run (Chapter05.givensApplyLeft pure i i' c s (Chapter05.indexFrom n k) QT.2)))) := by
    unfold schurSwapStep
    split_ifs
    rfl
  have hT1 : Id.run (Chapter05.givensApplyLeft pure i i' c s (Chapter05.indexFrom n k) QT.2) =
      (Chapter05.givensRotation i i' c s)ᵀ * QT.2 :=
    givensApplyLeft_eq_mul hne c s (Chapter05.nodup_indexFrom n k) fun q hq => by
      have hq' : (q : ℕ) < k := by rw [Chapter05.mem_indexFrom] at hq; omega
      exact ⟨z _ _ (show (q : ℕ) < i by simp [i]; omega), z _ _ (show (q : ℕ) < i' by
        simp [i']; omega)⟩
  have hT2 : Id.run (Chapter05.givensApplyRight pure i i' c s
      ((List.finRange n).filter fun r => (r : ℕ) ≤ k + 1)
      ((Chapter05.givensRotation i i' c s)ᵀ * QT.2)) =
      (Chapter05.givensRotation i i' c s)ᵀ * QT.2 * Chapter05.givensRotation i i' c s :=
    givensApplyRight_eq_mul hne c s ((List.nodup_finRange n).filter _) fun r hr => by
      have hr' : k + 1 < (r : ℕ) := by
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hr
        omega
      have hri : r ≠ i := fun e => by rw [e] at hr'; simp [i] at hr'
      have hri' : r ≠ i' := fun e => by rw [e] at hr'; simp [i'] at hr'
      unfold Chapter05.givensRotation
      simp only [transpose_planeRotation_mul_apply hne, hri, hri', ite_false]
      exact ⟨z _ _ (show (i : ℕ) < r by simp [i]; omega), z _ _ (show (i' : ℕ) < r by
        simp [i']; omega)⟩
  have hswap := conj_givensRotation_swap hT (i := i) (i' := i') rfl hcs hsc
  refine ⟨Chapter05.givensRotation i i' c s, Chapter05.givensRotation_mem_orthogonalGroup hne hcs,
    ?_, ?_, ?_, ?_⟩
  · rw [hrun, Chapter05.givensApplyRight_spec_of_forall_mem hne c s (List.nodup_finRange n)
      (List.mem_finRange)]
  · rw [hrun, hT1, hT2]
  · rw [hrun, hT1, hT2]
    exact hswap.1
  · rw [hrun, hT1, hT2]
    funext r
    dsimp only
    rw [hswap.2 r]
    unfold diagSwapStep
    split_ifs
    rfl

end ReorderSpec

section ReorderSpec2

/-- In exact arithmetic a sequence of steps of Algorithm 7.6.1 is an orthogonal similarity that
keeps $T$ upper triangular and moves its diagonal by the corresponding steps of the bubble sort. -/
private theorem foldlM_schurSwapStep_pure (Δ : Finset ℝ) (l : List ℕ)
    (QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (hT : QT.2.IsUpperTriangular) :
    ∃ G ∈ orthogonalGroup (Fin n) ℝ,
      (Id.run (l.foldlM (schurSwapStep pure Δ) QT)).1 = QT.1 * G ∧
      (Id.run (l.foldlM (schurSwapStep pure Δ) QT)).2 = Gᵀ * QT.2 * G ∧
      (Id.run (l.foldlM (schurSwapStep pure Δ) QT)).2.IsUpperTriangular ∧
      (fun r => (Id.run (l.foldlM (schurSwapStep pure Δ) QT)).2 r r) =
        l.foldl (diagSwapStep Δ) (fun r => QT.2 r r) := by
  induction l generalizing QT with
  | nil => exact ⟨1, one_mem _, by simp, by simp, hT, rfl⟩
  | cons a l ih =>
    obtain ⟨G₁, hG₁, h1, h2, h3, h4⟩ := schurSwapStep_pure Δ QT hT a
    obtain ⟨G₂, hG₂, h1', h2', h3', h4'⟩ := ih (Id.run (schurSwapStep pure Δ QT a)) h3
    refine ⟨G₁ * G₂, mul_mem hG₁ hG₂, ?_, ?_, h3', ?_⟩
    · change (Id.run (l.foldlM (schurSwapStep pure Δ) (Id.run (schurSwapStep pure Δ QT a)))).1 = _
      rw [h1', h1, Matrix.mul_assoc]
    · change (Id.run (l.foldlM (schurSwapStep pure Δ) (Id.run (schurSwapStep pure Δ QT a)))).2 = _
      rw [h2', h2, transpose_mul]
      simp only [Matrix.mul_assoc]
    · change (fun r => (Id.run (l.foldlM (schurSwapStep pure Δ)
        (Id.run (schurSwapStep pure Δ QT a)))).2 r r) = _
      rw [h4', h4, List.foldl_cons]

/-- The state of Algorithm 7.6.1 after $j$ passes of its `while` loop, in exact arithmetic. -/
private noncomputable def reorderState (Δ : Finset ℝ) (Q T : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) :
    (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) × Bool :=
  Id.run ((List.range j).foldlM (fun st _ => schurReorderPass pure Δ st) ((Q, T), false))

/-- The invariant of the `while` loop of Algorithm 7.6.1 after $j$ passes: an orthogonal similarity
with an upper triangular result whose diagonal is a permutation of the diagonal of $T$, with its
last $\min(j, f)$ entries outside $\Delta$, and with `done` set only when the entries in
$\Delta$ come first. -/
private theorem reorderState_inv (Δ : Finset ℝ) (Q T : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.IsUpperTriangular) (j : ℕ) :
    ∃ G ∈ orthogonalGroup (Fin n) ℝ, (reorderState Δ Q T j).1.1 = Q * G ∧
      (reorderState Δ Q T j).1.2 = Gᵀ * T * G ∧
      (reorderState Δ Q T j).1.2.IsUpperTriangular ∧
      (∃ σ : Equiv.Perm (Fin n), (fun r => (reorderState Δ Q T j).1.2 r r) =
        (fun r => T r r) ∘ σ) ∧
      TailOut Δ (min j (outCount Δ fun r => T r r)) (fun r => (reorderState Δ Q T j).1.2 r r) ∧
      ((reorderState Δ Q T j).2 = true → Leading Δ fun r => (reorderState Δ Q T j).1.2 r r) := by
  induction j with
  | zero =>
    exact ⟨1, one_mem _, by simp [reorderState], by simp [reorderState], hT, ⟨1, rfl⟩,
      fun i hi => by simp at hi; omega, fun h => absurd h (by simp [reorderState])⟩
  | succ j ih =>
    obtain ⟨G, hG, h1, h2, h3, ⟨σ, hσ⟩, h5, h6⟩ := ih
    have hstep : reorderState Δ Q T (j + 1) =
        Id.run (schurReorderPass pure Δ (reorderState Δ Q T j)) := by
      unfold reorderState
      rw [List.range_succ, List.foldlM_append]
      rfl
    set st := reorderState Δ Q T j
    have hf : outCount Δ (fun r => st.1.2 r r) = outCount Δ fun r => T r r := by
      rw [hσ, outCount_comp_perm]
    rw [hstep]
    unfold schurReorderPass
    by_cases hd : st.2 = true
    · rw [ite_eq_left hd]
      refine ⟨G, hG, h1, h2, h3, ⟨σ, hσ⟩, ?_, fun _ => h6 hd⟩
      exact tailOut_of_leading Δ (h6 hd) (by rw [hf]; exact min_le_right _ _)
    · rw [ite_eq_right hd]
      by_cases hl : IsDeltaLeading Δ st.1.2
      · rw [ite_eq_left hl]
        exact ⟨G, hG, h1, h2, h3, ⟨σ, hσ⟩,
          tailOut_of_leading Δ hl (by rw [hf]; exact min_le_right _ _), fun _ => hl⟩
      · rw [ite_eq_right hl]
        obtain ⟨G', hG', h1', h2', h3', h4'⟩ := foldlM_schurSwapStep_pure Δ (List.range (n - 1))
          st.1 h3
        obtain ⟨τ, hτ⟩ := foldl_diagSwapStep_perm Δ (List.range (n - 1)) fun r => st.1.2 r r
        refine ⟨G * G', mul_mem hG hG', ?_, ?_, h3', ⟨τ.trans σ, ?_⟩, ?_, fun h => ?_⟩
        · change (Id.run ((List.range (n - 1)).foldlM (schurSwapStep pure Δ) st.1)).1 = _
          rw [h1', h1, Matrix.mul_assoc]
        · change (Id.run ((List.range (n - 1)).foldlM (schurSwapStep pure Δ) st.1)).2 = _
          rw [h2', h2, transpose_mul]
          simp only [Matrix.mul_assoc]
        · change (fun r => (Id.run ((List.range (n - 1)).foldlM (schurSwapStep pure Δ)
            st.1)).2 r r) = _
          rw [h4', hτ, hσ]
          rfl
        · change TailOut Δ _ (fun r => (Id.run ((List.range (n - 1)).foldlM
            (schurSwapStep pure Δ) st.1)).2 r r)
          rw [h4']
          by_cases hjf : j < outCount Δ fun r => T r r
          · rw [min_eq_left (by omega)]
            rw [min_eq_left hjf.le] at h5
            exact tailOut_pass Δ h5 (by rw [hf]; exact hjf)
          · rw [min_eq_right (by omega)]
            rw [min_eq_right (by omega), ← hf] at h5
            rw [leading_foldl Δ (leading_of_tailOut Δ h5), ← hf]
            exact h5
        · exact absurd h (by simp)

/-- **Algorithm 7.6.1** of [golub2013matrix], exact semantics. Let
$A, Q, T \in \mathbb{R}^{n \times n}$ with $Q$ orthogonal and $T = Q^T A Q$ upper triangular,
let $\Delta$ be a finite set of real numbers, and let $\mathit{fuel} \ge n$. Let $p$ be the
number of indices $i$ with $t_{ii} \in \Delta$. Then the output $(Q', S)$ of Algorithm 7.6.1 in
exact arithmetic satisfies:
* $Q' = Q Q_D$ and $S = Q_D^T T Q_D$ for an orthogonal $Q_D$;
* $Q'$ is orthogonal and $S = Q'^T A Q'$;
* $S$ is upper triangular, and its diagonal is a permutation of the diagonal of $T$;
* $s_{kk} \in \Delta$ if and only if $k < p$ (0-based), which is
  $\{s_{11}, \dots, s_{pp}\} = \Delta$ with multiplicities.

**Reading.** The source's condition $\{s_{11}, \dots, s_{pp}\} = \Delta$ is read with
multiplicities, as above.

The statement does not need $\Delta \subseteq \lambda(A)$. Each swap is
`GolubVanLoan.Chapter07.swap_two_by_two` in the plane $(k, k+1)$. A pass acts on the diagonal as
one pass of a bubble sort, in which every entry outside $\Delta$ sinks past the entries in
$\Delta$ below it, and $n$ passes sort the diagonal. -/
theorem algorithm_7_6_1_spec {A Q T : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hTA : T = Qᵀ * A * Q) (hT : T.IsUpperTriangular)
    (Δ : Finset ℝ) {fuel : ℕ} (hfuel : n ≤ fuel) :
    ∃ QD ∈ orthogonalGroup (Fin n) ℝ,
      (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).1 = Q * QD ∧
      (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).2 = QDᵀ * T * QD ∧
      (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).1 ∈ orthogonalGroup (Fin n) ℝ ∧
      (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).2 =
        (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).1ᵀ * A *
          (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).1 ∧
      (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).2.IsUpperTriangular ∧
      (∃ σ : Equiv.Perm (Fin n),
        ∀ k, (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).2 k k = T (σ k) (σ k)) ∧
      ∀ k : Fin n, (Id.run (algorithm_7_6_1 pure Q T Δ fuel)).2 k k ∈ Δ ↔
        (k : ℕ) < (Finset.univ.filter fun i => T i i ∈ Δ).card := by
  have hrun : Id.run (algorithm_7_6_1 pure Q T Δ fuel) = (reorderState Δ Q T fuel).1 := rfl
  rw [hrun]
  obtain ⟨G, hG, h1, h2, h3, ⟨σ, hσ⟩, h5, -⟩ := reorderState_inv Δ Q T hT fuel
  have hf : outCount Δ (fun r => (reorderState Δ Q T fuel).1.2 r r) =
      outCount Δ fun r => T r r := by
    rw [hσ, outCount_comp_perm]
  have hfn := outCount_le Δ fun r => T r r
  rw [min_eq_right (by omega), ← hf] at h5
  refine ⟨G, hG, h1, h2, by rw [h1]; exact mul_mem hQ hG, ?_, h3,
    ⟨σ, fun k => congrFun hσ k⟩, fun k => ?_⟩
  · rw [h2, h1, hTA, transpose_mul]
    simp only [Matrix.mul_assoc]
  · rw [mem_iff_of_tailOut Δ h5 k, hf]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => T i i ∈ Δ)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have e : outCount Δ (fun r => T r r) = (Finset.univ.filter fun i => T i i ∉ Δ).card := rfl
    rw [e]
    omega

end ReorderSpec2

/-! ### §7.6.3 Block diagonalization -/

/-- **§7.6.3** of [golub2013matrix], the updates by $Y_{ij}$. Let
$T, Z \in \mathbb{R}^{n \times n}$, where $T$ is block upper triangular for a partitioning into
blocks $1, \dots, q$. Let $i < j$ be two blocks, and let $Z$ be zero outside the block position
$(i, j)$; this is the source's $E_i Z_{ij} E_j^T$. Then $Y_{ij} = I + Z$ satisfies
$$Y_{ij}^{-1} = I - Z, \qquad Y_{ij}^{-1} T Y_{ij} = T + TZ - ZT.$$
Read blockwise, $\bar T = Y_{ij}^{-1} T Y_{ij}$ agrees with $T$ except $\bar T_{ij} = T_{ii}
Z_{ij} - Z_{ij} T_{jj} + T_{ij}$, $\bar T_{ik} = T_{ik} - Z_{ij} T_{jk}$ for $k > j$, and
$\bar T_{kj} = T_{ki} Z_{ij} + T_{kj}$ for $k < i$.

The partitioning is a block index `b : Fin n → Fin q`, and "block upper triangular" is
`Matrix.BlockTriangular b`. The cross term $Z T Z$ vanishes because $T_{ji} = 0$. -/
theorem blockDiagonalization_update {q : ℕ} {b : Fin n → Fin q} {T Z : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.BlockTriangular b) {i j : Fin q} (hij : i < j)
    (hZ : ∀ r c, Z r c ≠ 0 → b r = i ∧ b c = j) :
    (1 + Z)⁻¹ = 1 - Z ∧ (1 + Z)⁻¹ * T * (1 + Z) = T + T * Z - Z * T := by
  have hZZ : Z * Z = 0 := by
    ext r c
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hij.ne ((hZ s c h2).1.symm.trans (hZ r s h1).2)
  have hZTZ : Z * T * Z = 0 := by
    ext r c
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h2 : Z t c = 0
    · rw [h2, mul_zero]
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h1 : Z r s = 0
    · rw [h1, zero_mul, zero_mul]
    have hs := (hZ r s h1).2
    have ht := (hZ t c h2).1
    rw [hT (show b t < b s by rw [hs, ht]; exact hij), mul_zero, zero_mul]
  have hinv : (1 + Z)⁻¹ = 1 - Z := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hZZ]
    abel
  refine ⟨hinv, ?_⟩
  rw [hinv]
  calc (1 - Z) * T * (1 + Z) = T + T * Z - Z * T - Z * T * Z := by noncomm_ring
    _ = T + T * Z - Z * T := by rw [hZTZ, sub_zero]

/-- **Equations (7.6.4) and (7.6.5)** of [golub2013matrix], the column recurrences of the Sylvester
equation. Let $F \in \mathbb{R}^{p \times p}$, let $G \in \mathbb{R}^{r \times r}$ be upper
Hessenberg (for example upper quasi-triangular), and let $Z \in \mathbb{R}^{p \times r}$ with
columns $z_1, \dots, z_r$. Then:
* for every $k$, column $k$ of $FZ - ZG$ is $F z_k - \sum_i g_{ik} z_i$;
* if $g_{k+1,k} = 0$, or $k$ is the last column, then column $k$ of $FZ - ZG$ is
  $(F - g_{kk} I) z_k - \sum_{i<k} g_{ik} z_i$, the triangular recurrence (7.6.4);
* if $m = k + 1$ is a column and $g_{m+1,m} = 0$, or $m$ is the last column, then column $k$ of
  $FZ - ZG$ is $(F - g_{kk} I) z_k - g_{mk} z_m - \sum_{i<k} g_{ik} z_i$ and column $m$ is
  $(F - g_{mm} I) z_m - g_{km} z_k - \sum_{i<k} g_{im} z_i$; these are the rows of the
  $2p \times 2p$ system (7.6.5).

Hence $FZ - ZG = C$ holds exactly when these columns equal the columns of $C$. The source uses
the third part when $g_{k+1,k} \neq 0$, but the identity holds without this condition. Upper
Hessenberg is `Matrix.IsUpperHessenberg`. -/
theorem equation_7_6_5 {p r : ℕ} (F : Matrix (Fin p) (Fin p) ℝ) {G : Matrix (Fin r) (Fin r) ℝ}
    (hG : G.IsUpperHessenberg) (Z : Matrix (Fin p) (Fin r) ℝ) :
    (∀ k, (F * Z - Z * G).col k = F *ᵥ Z.col k - ∑ i, G i k • Z.col i) ∧
    (∀ k : Fin r, (∀ m : Fin r, (m : ℕ) = k + 1 → G m k = 0) →
      (F * Z - Z * G).col k = (F - G k k • 1) *ᵥ Z.col k - ∑ i ∈ Finset.Iio k, G i k • Z.col i) ∧
    (∀ k m : Fin r, (m : ℕ) = k + 1 → (∀ m' : Fin r, (m' : ℕ) = m + 1 → G m' m = 0) →
      (F * Z - Z * G).col k =
          (F - G k k • 1) *ᵥ Z.col k - G m k • Z.col m - ∑ i ∈ Finset.Iio k, G i k • Z.col i ∧
        (F * Z - Z * G).col m =
          (F - G m m • 1) *ᵥ Z.col m - G k m • Z.col k - ∑ i ∈ Finset.Iio k, G i m • Z.col i) := by
  rw [isUpperHessenberg_iff_fin] at hG
  have h1 : ∀ k, (F * Z - Z * G).col k = F *ᵥ Z.col k - ∑ i, G i k • Z.col i := by
    intro k
    ext r'
    simp only [col_apply, Matrix.sub_apply, Matrix.mul_apply, Pi.sub_apply, mulVec, dotProduct,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsub : ∀ k : Fin r, (F - G k k • 1) *ᵥ Z.col k = F *ᵥ Z.col k - G k k • Z.col k := by
    intro k
    rw [sub_mulVec, smul_mulVec, one_mulVec]
  refine ⟨h1, fun k hk => ?_, fun k m hm hm' => ⟨?_, ?_⟩⟩
  · rw [h1, hsub, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic k)) fun i _ hi => ?_,
      ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    · abel
    · simp only [Finset.mem_Iic, not_le] at hi
      rcases Nat.lt_or_ge ((k : ℕ) + 1) i with h | h
      · rw [hG i k h, zero_smul]
      · rw [hk i (by rw [Fin.lt_def] at hi; omega), zero_smul]
  · have hkm : k < m := by rw [Fin.lt_def]; omega
    have hsupp : ∀ i ∉ insert m (Finset.Iic k), G i k • Z.col i = 0 := fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_Iic, not_or, not_le] at hi
      rw [hG i k (by
        have h1 := hi.1
        have h2 := Fin.lt_def.1 hi.2
        have : (i : ℕ) ≠ m := fun h => h1 (Fin.ext h)
        omega), zero_smul]
    rw [h1, hsub, ← Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hsupp i hi,
      Finset.sum_insert (by simp [Finset.mem_Iic, not_le.2 hkm]), ← Finset.Iio_insert,
      Finset.sum_insert Finset.notMem_Iio_self]
    abel
  · have hkm : k < m := by rw [Fin.lt_def]; omega
    have hsupp : ∀ i ∉ insert m (Finset.Iic k), G i m • Z.col i = 0 := fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_Iic, not_or, not_le] at hi
      have h1 := hi.1
      have h2 := Fin.lt_def.1 hi.2
      have : (i : ℕ) ≠ m := fun h => h1 (Fin.ext h)
      rcases Nat.lt_or_ge ((m : ℕ) + 1) i with h | h
      · rw [hG i m h, zero_smul]
      · rw [hm' i (by omega), zero_smul]
    rw [h1, hsub, ← Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hsupp i hi,
      Finset.sum_insert (by simp [Finset.mem_Iic, not_le.2 hkm]), ← Finset.Iio_insert,
      Finset.sum_insert Finset.notMem_Iio_self]
    abel

/-! ### §7.6.3 Algorithms 7.6.2 and 7.6.3 -/

section BartelsStewart

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 7.6.2** of [golub2013matrix] (Bartels–Stewart algorithm). Given
$C \in \mathbb{R}^{p \times r}$ and upper triangular matrices $F \in \mathbb{R}^{p \times p}$
and $G \in \mathbb{R}^{r \times r}$ that satisfy $\lambda(F) \cap \lambda(G) = \emptyset$, the
algorithm overwrites $C$ with the solution of the equation $FZ - ZG = C$.
```
for k = 1:r
    C(1:p, k) = C(1:p, k) + C(1:p, 1:k-1) · G(1:k-1, k)
    Solve (F - G(k,k) I) z = C(1:p, k) for z.
    C(1:p, k) = z
end
```
Entry $i$ of the updated column is $\mathrm{fl}(c_{ik} + \sum_{j<k} c_{ij} g_{jk})$, accumulated
from $c_{ik}$ in increasing order of $j$ by `FloatingPoint.dotAccum`. The triangular solve is
the back substitution Algorithm 3.1.2 (`GolubVanLoan.Chapter03.algorithm_3_1_2`) on the matrix
$F$ with diagonal entries $\mathrm{fl}(f_{ii} - g_{kk})$. The program has no hypothesis on its
inputs. -/
noncomputable def algorithm_7_6_2 {p r : ℕ} (F : Matrix (Fin p) (Fin p) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ) (C : Matrix (Fin p) (Fin r) ℝ) : M (Matrix (Fin p) (Fin r) ℝ) :=
  (List.finRange r).foldlM (fun (C : Matrix (Fin p) (Fin r) ℝ) k => do
    let b ← (List.finRange p).foldlM (fun (b : Fin p → ℝ) i => do
      let x ← FloatingPoint.dotAccum rnd ((List.finRange r).filter (· < k)) (C i)
        (fun j => G j k) (C i k)
      pure (Function.update b i x)) (fun i => C i k)
    let d ← (List.finRange p).foldlM (fun (d : Fin p → ℝ) i => do
      let x ← rnd (F i i - G k k)
      pure (Function.update d i x)) 0
    let z ← Chapter03.algorithm_3_1_2 rnd (of fun i j => if i = j then d i else F i j) b
    pure (C.updateCol k z)) C

end BartelsStewart

section BartelsStewartSpec

variable {p r : ℕ}

/-- The sum over the listed indices $j < k$ is the sum over `Finset.Iio k`. -/
private theorem sum_map_filter_lt (k : Fin r) (f : Fin r → ℝ) :
    (((List.finRange r).filter (· < k)).map f).sum = ∑ j ∈ Finset.Iio k, f j := by
  rw [← List.sum_toFinset _ ((List.nodup_finRange r).filter _)]
  congr 1
  ext j
  simp

/-- The exact column step of Algorithm 7.6.2: column $k$ of $C$ is replaced by the back substitution
solution $z$ of
$$(F - g_{kk} I) z = c_k + \sum_{j<k} g_{jk} c_j,$$
where $c_j$ are the current columns of $C$. The solution is `Matrix.backSubst`. -/
noncomputable def bartelsStewartStep (F : Matrix (Fin p) (Fin p) ℝ) (G : Matrix (Fin r) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin r) ℝ) (k : Fin r) : Matrix (Fin p) (Fin r) ℝ :=
  C.updateCol k ((F - G k k • 1).backSubst (C.col k + ∑ j ∈ Finset.Iio k, G j k • C.col j))

/-- In exact arithmetic, Algorithm 7.6.2 is the fold of `GolubVanLoan.Chapter07.bartelsStewartStep`
over the columns $k = 0, \dots, r - 1$. -/
theorem algorithm_7_6_2_pure (F : Matrix (Fin p) (Fin p) ℝ) (G : Matrix (Fin r) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin r) ℝ) :
    algorithm_7_6_2 (M := Id) pure F G C =
      pure ((List.finRange r).foldl (bartelsStewartStep F G) C) := by
  have h3 : ∀ (U : Matrix (Fin p) (Fin p) ℝ) (b : Fin p → ℝ),
      Chapter03.algorithm_3_1_2 (M := Id) pure U b = pure (U.backSubst b) :=
    fun U b => Chapter03.algorithm_3_1_2_eq_backSubst U b
  unfold algorithm_7_6_2
  rw [← List.foldlM_pure]
  congr 1
  funext C k
  simp only [FloatingPoint.dotAccum_pure, LawfulMonad.pure_bind, List.foldlM_pure, h3,
    List.foldl_update_eq_ite, List.mem_finRange, ↓reduceIte]
  unfold bartelsStewartStep
  congr 3
  · ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h, one_apply_ne h]
  · funext i
    simp only [Pi.add_apply, col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_map_filter_lt]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

/-- A column of `Matrix.updateCol`. -/
private theorem col_updateCol {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k j : Fin n)
    (c : Fin m → ℝ) : (A.updateCol k c).col j = if j = k then c else A.col j := by
  ext i
  by_cases h : j = k
  · subst h; simp
  · simp [h]

/-- The invariant of Algorithm 7.6.2 after its first $k$ columns: these columns solve the triangular
recurrences (7.6.4), and the other columns are still those of $C$. -/
private theorem bartelsStewart_take {F : Matrix (Fin p) (Fin p) ℝ} {G : Matrix (Fin r) (Fin r) ℝ}
    (hF : F.IsUpperTriangular) (hFG : ∀ i j, F i i ≠ G j j) (C : Matrix (Fin p) (Fin r) ℝ) :
    ∀ k ≤ r, (∀ j : Fin r, k ≤ (j : ℕ) →
        (((List.finRange r).take k).foldl (bartelsStewartStep F G) C).col j = C.col j) ∧
      ∀ j : Fin r, (j : ℕ) < k →
        (F - G j j • 1) *ᵥ (((List.finRange r).take k).foldl (bartelsStewartStep F G) C).col j =
          C.col j + ∑ i ∈ Finset.Iio j,
            G i j • (((List.finRange r).take k).foldl (bartelsStewartStep F G) C).col i := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ _ => by simp, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hk' : k < (List.finRange r).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hk', List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.getElem_finRange]
    set Z := ((List.finRange r).take k).foldl (bartelsStewartStep F G) C
    set kk : Fin r := Fin.cast (List.length_finRange) ⟨k, hk'⟩
    have hkk : (kk : ℕ) = k := rfl
    have hU : (F - G kk kk • 1).IsUpperTriangular := fun i j hij => by
      rw [Matrix.sub_apply, hF hij, Matrix.smul_apply,
        one_apply_ne (show i ≠ j from ne_of_gt (show j < i from hij)), smul_zero, sub_zero]
    have hd : ∀ i, (F - G kk kk • 1) i i ≠ 0 := fun i => by
      rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, sub_ne_zero]
      exact hFG i kk
    unfold bartelsStewartStep
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [col_updateCol, ite_eq_right (fun h => by rw [h] at hj; omega)]
      exact ih1 j (by omega)
    · have hcol : ∀ i : Fin r, (i : ℕ) < k → (Z.updateCol kk ((F - G kk kk • 1).backSubst
          (Z.col kk + ∑ j ∈ Finset.Iio kk, G j kk • Z.col j))).col i = Z.col i := fun i hi => by
        rw [col_updateCol, ite_eq_right (fun h => by rw [h] at hi; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
      · rw [hcol j hjk, ih2 j hjk]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hcol i (by have := Finset.mem_Iio.1 hi; rw [Fin.lt_def] at this; omega)]
      · have hjkk : j = kk := Fin.ext hjk
        subst hjkk
        rw [col_updateCol, ite_eq_left rfl, mulVec_backSubst _ hU hd]
        congr 1
        · exact ih1 _ le_rfl
        · refine Finset.sum_congr rfl fun i hi => ?_
          exact congrArg _ (hcol i (by
            have := Finset.mem_Iio.1 hi; rw [Fin.lt_def] at this; omega)).symm

/-- **Algorithm 7.6.2** of [golub2013matrix], exact semantics. Let $F \in \mathbb{R}^{p \times p}$
and $G \in \mathbb{R}^{r \times r}$ be upper triangular with $f_{ii} \neq g_{jj}$ for all $i$
and $j$, and let $C \in \mathbb{R}^{p \times r}$. Then the output $Z$ of Algorithm 7.6.2 in
exact arithmetic satisfies $FZ - ZG = C$, and every $Z'$ with $FZ' - Z'G = C$ equals $Z$.

The spectrum of a triangular matrix is its diagonal, so the hypothesis $f_{ii} \neq g_{jj}$ is
the source's $\lambda(F) \cap \lambda(G) = \emptyset$. Each column $z_k$ is the back
substitution solution of $(F - g_{kk} I) z_k = c_k + \sum_{j<k} g_{jk} z_j$, which is (7.6.4). -/
theorem algorithm_7_6_2_spec {F : Matrix (Fin p) (Fin p) ℝ} {G : Matrix (Fin r) (Fin r) ℝ}
    (hF : F.IsUpperTriangular) (hG : G.IsUpperTriangular) (hFG : ∀ i j, F i i ≠ G j j)
    (C : Matrix (Fin p) (Fin r) ℝ) :
    F * Id.run (algorithm_7_6_2 pure F G C) - Id.run (algorithm_7_6_2 pure F G C) * G = C ∧
      ∀ Z : Matrix (Fin p) (Fin r) ℝ, F * Z - Z * G = C →
        Z = Id.run (algorithm_7_6_2 pure F G C) := by
  have hGH : G.IsUpperHessenberg := fun i j ⟨k, hjk, hki⟩ => hG (hjk.trans hki)
  have hcol : ∀ (Z : Matrix (Fin p) (Fin r) ℝ) (k : Fin r), (F * Z - Z * G).col k =
      (F - G k k • 1) *ᵥ Z.col k - ∑ i ∈ Finset.Iio k, G i k • Z.col i :=
    fun Z k => (equation_7_6_5 F hGH Z).2.1 k fun m hm => hG (show k < m by rw [Fin.lt_def]; omega)
  rw [algorithm_7_6_2_pure]
  obtain ⟨-, h2⟩ := bartelsStewart_take hF hFG C r le_rfl
  rw [List.take_of_length_le (by simp)] at h2
  change F * (List.finRange r).foldl (bartelsStewartStep F G) C -
      (List.finRange r).foldl (bartelsStewartStep F G) C * G = C ∧ ∀ Z : Matrix (Fin p) (Fin r) ℝ,
    F * Z - Z * G = C → Z = (List.finRange r).foldl (bartelsStewartStep F G) C
  set Z := (List.finRange r).foldl (bartelsStewartStep F G) C
  have hZ : F * Z - Z * G = C := by
    ext i k
    have h := congrFun (hcol Z k) i
    rw [h2 k k.2, add_sub_cancel_right] at h
    exact h
  refine ⟨hZ, fun Z' hZ' => ?_⟩
  have hD : F * (Z' - Z) - (Z' - Z) * G = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, show F * Z' - F * Z - (Z' * G - Z * G) =
      (F * Z' - Z' * G) - (F * Z - Z * G) by abel, hZ', hZ, sub_self]
  have hind : ∀ k : ℕ, ∀ j : Fin r, (j : ℕ) < k → (Z' - Z).col j = 0 := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
      · exact ih j hjk
      · have hU : (F - G j j • 1).IsUpperTriangular := fun a c hac => by
          rw [Matrix.sub_apply, hF hac, Matrix.smul_apply,
            one_apply_ne (show a ≠ c from ne_of_gt (show c < a from hac)), smul_zero, sub_zero]
        have hd : ∀ a, (F - G j j • 1) a a ≠ 0 := fun a => by
          rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, sub_ne_zero]
          exact hFG a j
        have h := hcol (Z' - Z) j
        rw [hD, Finset.sum_eq_zero fun i hi => by
          rw [ih i (by have := Finset.mem_Iio.1 hi; rw [Fin.lt_def] at this; omega), smul_zero],
          sub_zero] at h
        have h0 : (F - G j j • 1) *ᵥ (Z' - Z).col j = 0 := by
          rw [← h]; ext; simp
        rw [← backSubst_eq_of_mulVec_eq _ hU hd h0,
          backSubst_eq_of_mulVec_eq _ hU hd (mulVec_zero _)]
  have : Z' - Z = 0 := by
    ext i j
    exact congrFun (hind (j + 1) j (Nat.lt_succ_self _)) i
  exact sub_eq_zero.1 this

end BartelsStewartSpec

section BlockDiag

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {q : ℕ}

/-- The rows (and columns) of block $i$ of the partitioning (7.6.3), given by a block index
`b : Fin n → Fin q`, in increasing order. -/
def blockIndices (b : Fin n → Fin q) (i : Fin q) : List (Fin n) :=
  (List.finRange n).filter fun r => b r = i

/-- The update $T_{ik} \leftarrow T_{ik} - Z T_{jk}$ of Algorithm 7.6.3, on index lists. Let `li`
and `lj` list the rows of blocks $i$ and $j$. For each column $c$ in `cols` and each position
$a$ of `li`,
$$T(\ell_i[a], c) \leftarrow \mathrm{fl}\Bigl(T(\ell_i[a], c) - \mathrm{fl}\Bigl(\sum_e Z(a, e)
  \, T(\ell_j[e], c)\Bigr)\Bigr),$$
where the sum is accumulated by Algorithm 1.1.1. -/
def blockSubMul (li lj : List (Fin n)) (Z : Matrix (Fin li.length) (Fin lj.length) ℝ)
    (cols : List (Fin n)) (T : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  cols.foldlM (fun (T : Matrix (Fin n) (Fin n) ℝ) c => do
    let x ← (List.finRange li.length).foldlM (fun (x : Fin n → ℝ) a => do
      let s ← FloatingPoint.dotAccum rnd (List.finRange lj.length) (Z a) (fun e => x (lj.get e)) 0
      let y ← rnd (x (li.get a) - s)
      pure (Function.update x (li.get a) y)) (fun r => T r c)
    pure (T.updateCol c x)) T

/-- The update $Q_{kj} \leftarrow Q_{ki} Z + Q_{kj}$ of Algorithm 7.6.3 for all block rows $k$, on
index lists. Let `li` and `lj` list the columns of blocks $i$ and $j$. For each row $r$ and each
position $e$ of `lj`,
$$Q(r, \ell_j[e]) \leftarrow \mathrm{fl}\Bigl(\mathrm{fl}\Bigl(\sum_a Q(r, \ell_i[a]) \, Z(a,
  e)\Bigr) + Q(r, \ell_j[e])\Bigr).$$
-/
def blockAddMul (li lj : List (Fin n)) (Z : Matrix (Fin li.length) (Fin lj.length) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (Q : Matrix (Fin n) (Fin n) ℝ) r => do
    let x ← (List.finRange lj.length).foldlM (fun (x : Fin n → ℝ) e => do
      let s ← FloatingPoint.dotAccum rnd (List.finRange li.length) (fun a => x (li.get a))
        (fun a => Z a e) 0
      let y ← rnd (s + x (lj.get e))
      pure (Function.update x (lj.get e) y)) (Q r)
    pure (Q.updateRow r x)) Q

/-- The body of Algorithm 7.6.3 for the pair of blocks $i < j$. It solves
$T_{ii} Z - Z T_{jj} = -T_{ij}$ by Algorithm 7.6.2 on the extracted blocks (the negation is
exact), then updates $T_{ik} \leftarrow T_{ik} - Z T_{jk}$ for $k > j$ by
`GolubVanLoan.Chapter07.blockSubMul` and $Q_{kj} \leftarrow Q_{ki} Z + Q_{kj}$ by
`GolubVanLoan.Chapter07.blockAddMul`. As in the source, it does not write the block $T_{ij}$,
which is now zero. -/
noncomputable def blockDiagStep (b : Fin n → Fin q)
    (QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (i j : Fin q) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let Z ← algorithm_7_6_2 rnd
    (QT.2.submatrix (blockIndices b i).get (blockIndices b i).get)
    (QT.2.submatrix (blockIndices b j).get (blockIndices b j).get)
    (-QT.2.submatrix (blockIndices b i).get (blockIndices b j).get)
  let T ← blockSubMul rnd (blockIndices b i) (blockIndices b j) Z
    ((List.finRange n).filter fun c => j < b c) QT.2
  let Q ← blockAddMul rnd (blockIndices b i) (blockIndices b j) Z QT.1
  pure (Q, T)

/-- **Algorithm 7.6.3** of [golub2013matrix] (block diagonalization). Given an orthogonal matrix
$Q \in \mathbb{R}^{n \times n}$, an upper quasi-triangular matrix $T = Q^T A Q$, and the
partitioning (7.6.3), the algorithm overwrites $Q$ with $QY$ where $Y^{-1} T Y =
\operatorname{diag}(T_{11}, \dots, T_{qq})$.
```
for j = 2:q
    for i = 1:j-1
        Solve T_ii Z - Z T_jj = -T_ij for Z using the Bartels-Stewart algorithm.
        for k = j+1:q
            T_ik = T_ik - Z T_jk
        end
        for k = 1:q
            Q_kj = Q_ki Z + Q_kj
        end
    end
end
```
The program returns the pair $(Q, T)$. It has no hypothesis on its inputs.

The partitioning is a block index `b : Fin n → Fin q`, which the specification assumes monotone.
The body of the loop is `GolubVanLoan.Chapter07.blockDiagStep`. -/
noncomputable def algorithm_7_6_3 (Q T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → Fin q) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange q).foldlM (fun QT (j : Fin q) =>
    (List.finRange (j : ℕ)).foldlM (fun QT (i : Fin j) =>
      blockDiagStep rnd b QT ⟨i, i.2.trans j.2⟩ j) QT) (Q, T)

end BlockDiag

section BlockDiagSpec

variable {q : ℕ}

/-- A loop that rewrites each column from its own old values only is a simultaneous update. -/
private theorem foldl_apply_of_colLocal (f : Matrix (Fin n) (Fin n) ℝ → Fin n →
    Matrix (Fin n) (Fin n) ℝ) (l : List (Fin n)) (hl : l.Nodup)
    (hf₁ : ∀ T c r c', c' ≠ c → f T c r c' = T r c')
    (hf₂ : ∀ T T' c, (∀ r, T r c = T' r c) → ∀ r, f T c r c = f T' c r c)
    (T₀ : Matrix (Fin n) (Fin n) ℝ) (r c : Fin n) :
    l.foldl f T₀ r c = if c ∈ l then f T₀ c r c else T₀ r c := by
  induction l generalizing T₀ with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons, ih hl.2]
    by_cases hca : c = a
    · subst hca
      simp [hl.1]
    · rw [hf₁ T₀ a r c hca]
      by_cases hcl : c ∈ l
      · simp only [hcl, ite_true, List.mem_cons, or_true]
        exact hf₂ _ _ c (fun r' => hf₁ T₀ a r' c hca) r
      · simp [hcl, hca]

/-- A loop that rewrites whole rows, each from its own old values only, is a simultaneous update. -/
private theorem foldl_apply_of_rowLocal (f : Matrix (Fin n) (Fin n) ℝ → Fin n →
    Matrix (Fin n) (Fin n) ℝ) (l : List (Fin n)) (hl : l.Nodup)
    (hf₁ : ∀ Q r r' c, r' ≠ r → f Q r r' c = Q r' c)
    (hf₂ : ∀ Q Q' r, Q r = Q' r → f Q r r = f Q' r r)
    (Q₀ : Matrix (Fin n) (Fin n) ℝ) (r c : Fin n) :
    l.foldl f Q₀ r c = if r ∈ l then f Q₀ r r c else Q₀ r c := by
  have hf : f = fun Q a => Function.update Q a (f Q a a) :=
    funext₂ fun Q a => Function.eq_update_iff.2 ⟨rfl, fun r' hr' => funext (hf₁ Q a r' · hr')⟩
  have e : l.foldl f Q₀ =
      l.foldl (fun (Q : Fin n → Fin n → ℝ) a => Function.update Q a (f Q a a)) Q₀ :=
    congrArg (fun F => l.foldl F Q₀) hf
  rw [e]
  exact (congrFun (congrFun (List.foldl_update_of_nodup hl (fun a (Q : Fin n → Fin n → ℝ) =>
    f Q a a) (fun a _ Q Q' _ h => hf₂ Q Q' a h) Q₀) r) c).trans (by split_ifs <;> rfl)


/-- A loop that writes the entries `key a` of a vector, each from its own old value and from entries
outside a set $S$ that it never writes, is a simultaneous update. -/
private theorem foldl_update_of_local {α : Type} (f : (Fin n → ℝ) → α → Fin n → ℝ)
    (key : α → Fin n) (S : Fin n → Prop) (L : List α) (hL : (L.map key).Nodup)
    (hS : ∀ a ∈ L, S (key a)) (hf₁ : ∀ y a s, s ≠ key a → f y a s = y s)
    (hf₂ : ∀ a ∈ L, ∀ y y' : Fin n → ℝ, (∀ s, ¬ S s → y s = y' s) → y (key a) = y' (key a) →
      f y a (key a) = f y' a (key a)) (y₀ : Fin n → ℝ) :
    (∀ a ∈ L, L.foldl f y₀ (key a) = f y₀ a (key a)) ∧
      ∀ s, s ∉ L.map key → L.foldl f y₀ s = y₀ s := by
  have hf : f = fun y a => Function.update y (key a) (f y a (key a)) :=
    funext₂ fun y a => Function.eq_update_iff.2 ⟨rfl, hf₁ y a⟩
  have hpw : L.Pairwise fun a b => key a ≠ key b ∧ ∀ y y' : Fin n → ℝ,
      (∀ k, k ≠ key a → y k = y' k) → f y b (key b) = f y' b (key b) := by
    rw [List.Nodup, List.pairwise_map] at hL
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ⟨hab, fun y y' hy => ?_⟩) hL
    exact hf₂ b hb y y' (fun s hs => hy s fun e => hs (e ▸ hS a ha)) (hy _ (Ne.symm hab))
  have e : L.foldl f y₀ = L.foldl (fun y a => Function.update y (key a) (f y a (key a))) y₀ :=
    congrArg (fun F => L.foldl F y₀) hf
  rw [e]
  exact ⟨fun a ha => List.foldl_update_apply_of_pairwise key (fun a y => f y a (key a)) hpw y₀ ha,
    fun s hs => List.foldl_update_apply_of_forall_ne key _
      (fun a ha (e : key a = s) => hs (e ▸ List.mem_map_of_mem ha)) y₀⟩

/-- For duplicate-free and disjoint blocks `li` and `lj`, `blockSubMul` replaces the columns in
`cols` of $T$ by those of $T - E_i Z E_j^T T$ and keeps the others, in exact arithmetic. -/
private theorem blockSubMul_pure {li lj : List (Fin n)} (hli : li.Nodup)
    (hdisj : ∀ r ∈ lj, r ∉ li) (Z : Matrix (Fin li.length) (Fin lj.length) ℝ)
    {cols : List (Fin n)} (hcols : cols.Nodup) (T : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (blockSubMul pure li lj Z cols T) = of fun r c => if c ∈ cols then
      T r c - (selCols li * Z * (selCols lj)ᵀ * T) r c else T r c := by
  unfold blockSubMul
  simp only [FloatingPoint.dotAccum_pure, LawfulMonad.pure_bind, List.foldlM_pure, zero_add]
  ext r c
  rw [of_apply]
  refine (foldl_apply_of_colLocal _ cols hcols (fun T c r c' h => updateCol_ne h)
    (fun T T' c h r => ?_) T r c).trans ?_
  · simp only [updateCol_self]
    rw [show (fun r => T r c) = fun r => T' r c from funext h]
  split_ifs with hc
  swap
  · rfl
  rw [updateCol_self]
  have hmap : (List.finRange li.length).map li.get = li := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hf₂ : ∀ a ∈ List.finRange li.length, ∀ y y' : Fin n → ℝ, (∀ s, ¬ s ∈ li → y s = y' s) →
      y (li.get a) = y' (li.get a) →
      Function.update y (li.get a) (y (li.get a) - ((List.finRange lj.length).map fun e =>
          Z a e * y (lj.get e)).sum) (li.get a) =
        Function.update y' (li.get a) (y' (li.get a) - ((List.finRange lj.length).map fun e =>
          Z a e * y' (lj.get e)).sum) (li.get a) := by
    intro a _ y y' hy hya
    simp only [Function.update_self]
    rw [hya]
    congr 2
    exact List.map_congr_left fun e _ => by rw [hy _ (hdisj _ (List.get_mem lj e))]
  obtain ⟨h1, h2⟩ := foldl_update_of_local _ li.get (· ∈ li) (List.finRange li.length)
    (by rw [hmap]; exact hli) (fun a _ => List.get_mem li a)
    (fun y a s hs => Function.update_of_ne hs _ _) hf₂ (fun r => T r c)
  by_cases hr : r ∈ li
  · obtain ⟨a, rfl⟩ := List.mem_iff_get.1 hr
    rw [h1 a (List.mem_finRange a), Function.update_self, Matrix.mul_assoc, Matrix.mul_assoc,
      selCols_mul_apply_get hli, Matrix.mul_apply, Fin.sum_univ_def]
    congr 2
    exact List.map_congr_left fun e _ => by rw [selCols_transpose_mul_apply]
  · rw [h2 r (by rwa [hmap]), Matrix.mul_assoc, Matrix.mul_assoc,
      selCols_mul_apply_of_notMem _ hr, sub_zero]

/-- For duplicate-free and disjoint blocks `li` and `lj`, `blockAddMul` returns
$Q (I + E_i Z E_j^T)$, in exact arithmetic. -/
private theorem blockAddMul_pure {li lj : List (Fin n)} (hlj : lj.Nodup)
    (hdisj : ∀ r ∈ li, r ∉ lj) (Z : Matrix (Fin li.length) (Fin lj.length) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (blockAddMul pure li lj Z Q) = Q * (1 + selCols li * Z * (selCols lj)ᵀ) := by
  unfold blockAddMul
  simp only [FloatingPoint.dotAccum_pure, LawfulMonad.pure_bind, List.foldlM_pure, zero_add]
  ext r c
  refine (foldl_apply_of_rowLocal _ (List.finRange n) (List.nodup_finRange n)
    (fun Q r r' c h => by rw [updateRow_ne h]) (fun Q Q' r h => ?_) Q r c).trans ?_
  · simp only [updateRow_self]
    rw [h]
  rw [ite_eq_left (List.mem_finRange r), updateRow_self]
  have hmap : (List.finRange lj.length).map lj.get = lj := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have hf₂ : ∀ e ∈ List.finRange lj.length, ∀ y y' : Fin n → ℝ, (∀ s, ¬ s ∈ lj → y s = y' s) →
      y (lj.get e) = y' (lj.get e) →
      Function.update y (lj.get e) (((List.finRange li.length).map fun a =>
          y (li.get a) * Z a e).sum + y (lj.get e)) (lj.get e) =
        Function.update y' (lj.get e) (((List.finRange li.length).map fun a =>
          y' (li.get a) * Z a e).sum + y' (lj.get e)) (lj.get e) := by
    intro e _ y y' hy hye
    simp only [Function.update_self]
    rw [hye]
    congr 2
    exact List.map_congr_left fun a _ => by rw [hy _ (hdisj _ (List.get_mem li a))]
  obtain ⟨h1, h2⟩ := foldl_update_of_local _ lj.get (· ∈ lj) (List.finRange lj.length)
    (by rw [hmap]; exact hlj) (fun e _ => List.get_mem lj e)
    (fun y e s hs => Function.update_of_ne hs _ _) hf₂ (Q r)
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  simp only [← Matrix.mul_assoc]
  by_cases hc : c ∈ lj
  · obtain ⟨e, rfl⟩ := List.mem_iff_get.1 hc
    rw [h1 e (List.mem_finRange e), Function.update_self, mul_selCols_transpose_apply_get hlj,
      Matrix.mul_apply, Fin.sum_univ_def, add_comm]
    congr 2
    exact List.map_congr_left fun a _ => by rw [mul_selCols_apply]
  · rw [h2 c (by rwa [hmap]), mul_selCols_transpose_apply_of_notMem _ _ hc, add_zero]

private theorem blockIndices_nodup (b : Fin n → Fin q) (i : Fin q) : (blockIndices b i).Nodup :=
  (List.nodup_finRange n).filter _

private theorem mem_blockIndices {b : Fin n → Fin q} {i : Fin q} {r : Fin n} :
    r ∈ blockIndices b i ↔ b r = i := by
  simp [blockIndices]

private theorem blockIndices_get (b : Fin n → Fin q) (i : Fin q)
    (a : Fin (blockIndices b i).length) : b ((blockIndices b i).get a) = i :=
  mem_blockIndices.1 (List.get_mem _ _)

private theorem blockIndices_strictMono (b : Fin n → Fin q) (i : Fin q) :
    StrictMono (blockIndices b i).get :=
  ((List.sortedLT_finRange n).pairwise.filter _).sortedLT.strictMono_get

/-- The solution $Z$ of $T_{ii} Z - Z T_{jj} = -T_{ij}$ that Algorithm 7.6.2 computes in exact
arithmetic. -/
private noncomputable def blockZ (b : Fin n → Fin q) (T : Matrix (Fin n) (Fin n) ℝ) (i j : Fin q) :
    Matrix (Fin (blockIndices b i).length) (Fin (blockIndices b j).length) ℝ :=
  Id.run (algorithm_7_6_2 pure (T.submatrix (blockIndices b i).get (blockIndices b i).get)
    (T.submatrix (blockIndices b j).get (blockIndices b j).get)
    (-T.submatrix (blockIndices b i).get (blockIndices b j).get))

/-- The matrix $E_i Z_{ij} E_j^T$: the solution `blockZ` placed in the block position $(i, j)$. -/
private noncomputable def blockZf (b : Fin n → Fin q) (T : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin q) : Matrix (Fin n) (Fin n) ℝ :=
  selCols (blockIndices b i) * blockZ b T i j * (selCols (blockIndices b j))ᵀ

/-- In exact arithmetic the body of Algorithm 7.6.3 for blocks $i \neq j$ sets
$Q \leftarrow Q (I + E_i Z E_j^T)$ and $T \leftarrow T - E_i Z E_j^T T$ in the columns of the
blocks after $j$. -/
private theorem blockDiagStep_pure (b : Fin n → Fin q)
    (QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) {i j : Fin q} (hij : i ≠ j) :
    Id.run (blockDiagStep pure b QT i j) =
      (QT.1 * (1 + blockZf b QT.2 i j), of fun r c => if j < b c then
        QT.2 r c - (blockZf b QT.2 i j * QT.2) r c else QT.2 r c) := by
  have hdisj : ∀ r ∈ blockIndices b j, r ∉ blockIndices b i := fun r hj hi =>
    hij ((mem_blockIndices.1 hi).symm.trans (mem_blockIndices.1 hj))
  have hdisj' : ∀ r ∈ blockIndices b i, r ∉ blockIndices b j := fun r hi hj => hdisj r hj hi
  change (Id.run (blockAddMul pure (blockIndices b i) (blockIndices b j) (blockZ b QT.2 i j)
      QT.1), Id.run (blockSubMul pure (blockIndices b i) (blockIndices b j) (blockZ b QT.2 i j)
      ((List.finRange n).filter fun c => j < b c) QT.2)) = _
  rw [blockAddMul_pure (blockIndices_nodup b j) hdisj',
    blockSubMul_pure (blockIndices_nodup b i) hdisj _
      ((List.nodup_finRange n).filter _)]
  ext r c
  · rfl
  · simp only [of_apply, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    rfl

end BlockDiagSpec

section BlockDiagInv

variable {q : ℕ}

/-- The invariant of Algorithm 7.6.3 for a set $P$ of processed block pairs: $Q = Q_0 Y$ for a
nonsingular block unit upper triangular $Y$, and $W = Y^{-1} T_0 Y$ is block upper triangular
with the diagonal blocks of $T_0$, zero in the processed blocks, and equal to the current $T$ in
the other blocks above the diagonal, while the current $T$ keeps the diagonal blocks of $T_0$. -/
private def BlockDiagInv (b : Fin n → Fin q) (Q₀ T₀ : Matrix (Fin n) (Fin n) ℝ)
    (P : Fin q → Fin q → Prop) (QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  ∃ Y : Matrix (Fin n) (Fin n) ℝ, IsUnit Y ∧ (∀ r c, b c < b r → Y r c = 0) ∧
    (∀ r c, b r = b c → Y r c = (1 : Matrix (Fin n) (Fin n) ℝ) r c) ∧ QT.1 = Q₀ * Y ∧
    (Y⁻¹ * T₀ * Y).BlockTriangular b ∧
    (∀ r c, b r = b c → (Y⁻¹ * T₀ * Y) r c = T₀ r c) ∧
    (∀ r c, b r < b c → P (b r) (b c) → (Y⁻¹ * T₀ * Y) r c = 0) ∧
    (∀ r c, b r < b c → ¬ P (b r) (b c) → (Y⁻¹ * T₀ * Y) r c = QT.2 r c) ∧
    (∀ r c, b r = b c → QT.2 r c = T₀ r c)

private theorem BlockDiagInv.congr {b : Fin n → Fin q} {Q₀ T₀ : Matrix (Fin n) (Fin n) ℝ}
    {P P' : Fin q → Fin q → Prop} (hPP : ∀ x y, x < y → (P x y ↔ P' x y))
    {QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ} (h : BlockDiagInv b Q₀ T₀ P QT) :
    BlockDiagInv b Q₀ T₀ P' QT := by
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨Y, h1, h2, h3, h4, h5, h6, fun r c hrc hP => h7 r c hrc ((hPP _ _ hrc).2 hP),
    fun r c hrc hP => h8 r c hrc fun h => hP ((hPP _ _ hrc).1 h), h9⟩

/-- One step of Algorithm 7.6.3 for the pair $(i, j)$ keeps the invariant, with $(i, j)$ added to
the processed pairs; the blocks $(k, j)$ with $k < i$ need no update because $W_{ki} = 0$
already. -/
private theorem BlockDiagInv.step {b : Fin n → Fin q} {Q₀ T₀ : Matrix (Fin n) (Fin n) ℝ}
    (hT₀ : T₀.IsUpperTriangular) (hdiag : ∀ r c, b r ≠ b c → T₀ r r ≠ T₀ c c)
    {P : Fin q → Fin q → Prop} {QT : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    (h : BlockDiagInv b Q₀ T₀ P QT) {i j : Fin q} (hij : i < j) (hPij : ¬ P i j)
    (hPi : ∀ k, k < i → P k i) (hPj : ∀ k, j < k → ¬ P j k ∧ ¬ P i k) :
    BlockDiagInv b Q₀ T₀ (fun x y => P x y ∨ (x = i ∧ y = j))
      (Id.run (blockDiagStep pure b QT i j)) := by
  obtain ⟨Y, hYu, hY1, hY2, hQ, hWt, hWd, hWp, hWu, hTd⟩ := h
  set W := Y⁻¹ * T₀ * Y with hW_def
  have hli := blockIndices_nodup b i
  have hlj := blockIndices_nodup b j
  have hbi : ∀ a, b ((blockIndices b i).get a) = i := blockIndices_get b i
  have hbj : ∀ e, b ((blockIndices b j).get e) = j := blockIndices_get b j
  set Z := blockZ b QT.2 i j
  set Zf := blockZf b QT.2 i j with hZf_def
  -- the Sylvester equation for the extracted blocks
  have hF : (QT.2.submatrix (blockIndices b i).get (blockIndices b i).get).IsUpperTriangular :=
    fun a a' haa => by
      change QT.2 ((blockIndices b i).get a) ((blockIndices b i).get a') = 0
      rw [hTd _ _ (by rw [hbi, hbi])]
      exact hT₀ (blockIndices_strictMono b i haa)
  have hG : (QT.2.submatrix (blockIndices b j).get (blockIndices b j).get).IsUpperTriangular :=
    fun e e' hee => by
      change QT.2 ((blockIndices b j).get e) ((blockIndices b j).get e') = 0
      rw [hTd _ _ (by rw [hbj, hbj])]
      exact hT₀ (blockIndices_strictMono b j hee)
  have hFG : ∀ a e, QT.2.submatrix (blockIndices b i).get (blockIndices b i).get a a ≠
      QT.2.submatrix (blockIndices b j).get (blockIndices b j).get e e := by
    intro a e
    simp only [submatrix_apply]
    rw [hTd _ _ rfl, hTd _ _ rfl]
    exact hdiag _ _ (by rw [hbi, hbj]; exact hij.ne)
  have hsyl : QT.2.submatrix (blockIndices b i).get (blockIndices b i).get * Z -
      Z * QT.2.submatrix (blockIndices b j).get (blockIndices b j).get =
        -QT.2.submatrix (blockIndices b i).get (blockIndices b j).get :=
    (algorithm_7_6_2_spec hF hG hFG _).1
  -- entries of the products with `Zf`
  have hZL : ∀ (A : Matrix (Fin n) (Fin n) ℝ) a c, (Zf * A) ((blockIndices b i).get a) c =
      ∑ e, Z a e * A ((blockIndices b j).get e) c := by
    intro A a c
    rw [hZf_def, blockZf, Matrix.mul_assoc, Matrix.mul_assoc, selCols_mul_apply_get hli,
      Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => by rw [selCols_transpose_mul_apply]
  have hZL0 : ∀ (A : Matrix (Fin n) (Fin n) ℝ) r c, b r ≠ i → (Zf * A) r c = 0 := by
    intro A r c hr
    rw [hZf_def, blockZf, Matrix.mul_assoc, Matrix.mul_assoc]
    exact selCols_mul_apply_of_notMem _ (fun h => hr (mem_blockIndices.1 h)) c
  have hZR : ∀ (A : Matrix (Fin n) (Fin n) ℝ) r e, (A * Zf) r ((blockIndices b j).get e) =
      ∑ a, A r ((blockIndices b i).get a) * Z a e := by
    intro A r e
    rw [hZf_def, blockZf]
    simp only [← Matrix.mul_assoc]
    rw [mul_selCols_transpose_apply_get hlj, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_selCols_apply]
  have hZR0 : ∀ (A : Matrix (Fin n) (Fin n) ℝ) r c, b c ≠ j → (A * Zf) r c = 0 := by
    intro A r c hc
    rw [hZf_def, blockZf]
    simp only [← Matrix.mul_assoc]
    exact mul_selCols_transpose_apply_of_notMem _ _ fun h => hc (mem_blockIndices.1 h)
  have hsupp : ∀ r c, Zf r c ≠ 0 → b r = i ∧ b c = j := by
    intro r c hrc
    refine ⟨?_, ?_⟩
    · by_contra hr
      have := hZL0 1 r c hr
      rw [Matrix.mul_one] at this
      exact hrc this
    · by_contra hc
      have := hZR0 1 r c hc
      rw [Matrix.one_mul] at this
      exact hrc this
  have hWZf : ∀ (A : Matrix (Fin n) (Fin n) ℝ) r c,
      (b c = j → ∀ a, A r ((blockIndices b i).get a) = 0) → (A * Zf) r c = 0 := by
    intro A r c hA
    by_cases hc : b c = j
    · obtain ⟨e, rfl⟩ := List.mem_iff_get.1 (mem_blockIndices.2 hc)
      rw [hZR]
      exact Finset.sum_eq_zero fun a _ => by rw [hA hc a, zero_mul]
    · exact hZR0 A r c hc
  have hZfW : ∀ (A : Matrix (Fin n) (Fin n) ℝ) r c,
      (b r = i → ∀ e, A ((blockIndices b j).get e) c = 0) → (Zf * A) r c = 0 := by
    intro A r c hA
    by_cases hr : b r = i
    · obtain ⟨a, rfl⟩ := List.mem_iff_get.1 (mem_blockIndices.2 hr)
      rw [hZL]
      exact Finset.sum_eq_zero fun e _ => by rw [hA hr e, mul_zero]
    · exact hZL0 A r c hr
  -- the similarity by `I + Zf`
  obtain ⟨-, hconj⟩ := blockDiagonalization_update hWt hij hsupp
  have hZZ : Zf * Zf = 0 := by
    ext r c
    rw [Matrix.zero_apply]
    refine hZfW Zf r c fun _ e => ?_
    by_contra hne
    exact hij.ne ((hsupp _ _ hne).1.symm.trans (hbj e))
  have hunit : IsUnit (1 + Zf) := by
    have h1 : (1 + Zf) * (1 - Zf) = 1 - Zf * Zf := by noncomm_ring
    rw [hZZ, sub_zero] at h1
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hW'e : ∀ r c, ((Y * (1 + Zf))⁻¹ * T₀ * (Y * (1 + Zf))) r c =
      W r c + (W * Zf) r c - (Zf * W) r c := by
    have hW' : (Y * (1 + Zf))⁻¹ * T₀ * (Y * (1 + Zf)) = W + W * Zf - Zf * W := by
      rw [← hconj, Matrix.mul_inv_rev, hW_def]
      simp only [Matrix.mul_assoc]
    intro r c
    rw [hW', Matrix.sub_apply, Matrix.add_apply]
  -- `W r (li a) = 0` in the block row of a processed or lower block
  have hWrow : ∀ r, b r ≠ i → ∀ a, W r ((blockIndices b i).get a) = 0 := by
    intro r hri a
    rcases lt_or_gt_of_ne hri with hlt | hgt
    · exact hWp _ _ (by rw [hbi]; exact hlt) (by rw [hbi]; exact hPi _ hlt)
    · exact hWt (by rw [hbi]; exact hgt)
  rw [blockDiagStep_pure b QT hij.ne]
  refine ⟨Y * (1 + Zf), hYu.mul hunit, fun r c hrc => ?_, fun r c hrc => ?_, ?_, fun r c hrc => ?_,
    fun r c hrc => ?_, fun r c hrc hP => ?_, fun r c hrc hP => ?_, fun r c hrc => ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hY1 r c hrc, zero_add]
    exact hWZf Y r c fun hc a => hY1 _ _ (by rw [hbi]; exact hij.trans (hc ▸ hrc))
  · rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hY2 r c hrc,
      hWZf Y r c fun hc a => hY1 _ _ (by rw [hbi, hrc, hc]; exact hij), add_zero]
  · change QT.1 * (1 + Zf) = Q₀ * (Y * (1 + Zf))
    rw [hQ, Matrix.mul_assoc]
  · change b c < b r at hrc
    rw [hW'e, hWt hrc, hWZf W r c fun hc a => hWt (by rw [hbi]; exact hij.trans (hc ▸ hrc)),
      hZfW W r c fun hr e => hWt (by rw [hbj]; exact (hr ▸ hrc).trans hij)]
    simp
  · rw [hW'e, hWd r c hrc, hWZf W r c fun hc a => hWt (by rw [hbi, hrc, hc]; exact hij),
      hZfW W r c fun hr e => hWt (by rw [hbj, ← hrc, hr]; exact hij)]
    simp
  · rcases hP with hP | ⟨hri, hcj⟩
    · have hnot : ¬ (b r = i ∧ b c = j) := fun h => hPij (h.1 ▸ h.2 ▸ hP)
      rw [hW'e, hWp r c hrc hP,
        hWZf W r c fun hc => hWrow r fun hr => hnot ⟨hr, hc⟩]
      rw [hZfW W r c fun hr e => ?_]
      · simp
      · have hcj : b c ≠ j := fun hc => hnot ⟨hr, hc⟩
        rcases lt_or_gt_of_ne hcj with hlt | hgt
        · exact hWt (by rw [hbj]; exact hlt)
        · exact absurd (hr ▸ hP) (hPj _ hgt).2
    · obtain ⟨a, rfl⟩ := List.mem_iff_get.1 (mem_blockIndices.2 hri)
      obtain ⟨e, rfl⟩ := List.mem_iff_get.1 (mem_blockIndices.2 hcj)
      have hs := congrFun (congrFun hsyl a) e
      simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, submatrix_apply] at hs
      rw [hW'e, hZR W, hZL W, hWu _ _ hrc (by rw [hri, hcj]; exact hPij)]
      have e1 : ∑ a', W ((blockIndices b i).get a) ((blockIndices b i).get a') * Z a' e =
          ∑ a', QT.2 ((blockIndices b i).get a) ((blockIndices b i).get a') * Z a' e :=
        Finset.sum_congr rfl fun a' _ => by
          rw [hWd _ _ (by rw [hbi, hbi]), hTd _ _ (by rw [hbi, hbi])]
      have e2 : ∑ e', Z a e' * W ((blockIndices b j).get e') ((blockIndices b j).get e) =
          ∑ e', Z a e' * QT.2 ((blockIndices b j).get e') ((blockIndices b j).get e) :=
        Finset.sum_congr rfl fun e' _ => by
          rw [hWd _ _ (by rw [hbj, hbj]), hTd _ _ (by rw [hbj, hbj])]
      rw [e1, e2]
      linarith
  · have hP1 : ¬ P (b r) (b c) := fun h => hP (Or.inl h)
    have hP2 : ¬ (b r = i ∧ b c = j) := fun h => hP (Or.inr h)
    dsimp only
    rw [hW'e, hWu r c hrc hP1, hWZf W r c fun hc => hWrow r fun hr => hP2 ⟨hr, hc⟩, of_apply]
    · by_cases hr : b r = i
      · have hcj : b c ≠ j := fun hc => hP2 ⟨hr, hc⟩
        obtain ⟨a, rfl⟩ := List.mem_iff_get.1 (mem_blockIndices.2 hr)
        split_ifs with hjc
        · rw [hZL W, hZL QT.2, add_zero]
          congr 1
          exact Finset.sum_congr rfl fun e _ => by
            rw [hWu _ _ (by rw [hbj]; exact hjc) (by rw [hbj]; exact (hPj _ hjc).1)]
        · rw [hZfW W _ c fun _ e => hWt (by
            rw [hbj]; exact lt_of_le_of_ne (not_lt.1 hjc) hcj)]
          ring
      · rw [hZfW W r c fun h => absurd h hr, hZL0 QT.2 r c hr]
        split_ifs <;> ring
  · dsimp only
    rw [of_apply]
    split_ifs with hjc
    · rw [hZL0 QT.2 r c fun hr => absurd (show j < i by rw [← hr, hrc]; exact hjc)
        (not_lt.2 hij.le), sub_zero, hTd r c hrc]
    · exact hTd r c hrc

end BlockDiagInv

section BlockDiagLoop

variable {q : ℕ}

private theorem id_run_foldlM_append_singleton {α β : Type} (f : β → α → Id β) (l : List α)
    (a : α) (x : β) :
    Id.run ((l ++ [a]).foldlM f x) = Id.run (f (Id.run (l.foldlM f x)) a) := by
  rw [List.foldlM_append]
  rfl

/-- After the steps $i = 0, \dots, m - 1$ of the inner loop of Algorithm 7.6.3 for block column $j$,
the processed pairs are those of the earlier block columns and the pairs $(i, j)$ with $i < m$. -/
private theorem blockDiagInv_inner {b : Fin n → Fin q} {Q₀ T₀ : Matrix (Fin n) (Fin n) ℝ}
    (hT₀ : T₀.IsUpperTriangular) (hdiag : ∀ r c, b r ≠ b c → T₀ r r ≠ T₀ c c) (j : Fin q)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (h : BlockDiagInv b Q₀ T₀ (fun x y => x < y ∧ (y : ℕ) < j) st) :
    ∀ m ≤ (j : ℕ), BlockDiagInv b Q₀ T₀
      (fun x y => x < y ∧ ((y : ℕ) < j ∨ (y = j ∧ (x : ℕ) < m)))
      (Id.run (((List.finRange (j : ℕ)).take m).foldlM
        (fun QT (i : Fin j) => blockDiagStep pure b QT ⟨i, i.2.trans j.2⟩ j) st)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine h.congr fun x y _ => ?_
    simp
  | succ m ih =>
    intro hm
    have hlen : m < (List.finRange (j : ℕ)).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hlen, id_run_foldlM_append_singleton,
      List.getElem_finRange]
    refine (BlockDiagInv.step hT₀ hdiag (ih (by omega)) (i := ⟨m, by omega⟩) (j := j)
      (by rw [Fin.lt_def]; simp; omega) ?_ ?_ ?_).congr ?_
    · simp
    · intro k hk
      rw [Fin.lt_def] at hk
      simp only [Fin.lt_def] at hk ⊢
      omega
    · intro k hk
      rw [Fin.lt_def] at hk
      simp only [Fin.lt_def, Fin.ext_iff, not_and, not_or]
      omega
    · intro x y _
      simp only [Fin.lt_def, Fin.ext_iff]
      omega

/-- After the whole inner loop of Algorithm 7.6.3 for block column $j$, the processed pairs are all
pairs $(i, j')$ with $i < j' \le j$. -/
private theorem blockDiagInv_inner_full {b : Fin n → Fin q} {Q₀ T₀ : Matrix (Fin n) (Fin n) ℝ}
    (hT₀ : T₀.IsUpperTriangular) (hdiag : ∀ r c, b r ≠ b c → T₀ r r ≠ T₀ c c) (j : Fin q)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (h : BlockDiagInv b Q₀ T₀ (fun x y => x < y ∧ (y : ℕ) < j) st) :
    BlockDiagInv b Q₀ T₀ (fun x y => x < y ∧ (y : ℕ) ≤ j)
      (Id.run ((List.finRange (j : ℕ)).foldlM
        (fun QT (i : Fin j) => blockDiagStep pure b QT ⟨i, i.2.trans j.2⟩ j) st)) := by
  have h' := blockDiagInv_inner hT₀ hdiag j st h j le_rfl
  rw [List.take_of_length_le (by simp)] at h'
  refine h'.congr fun x y hxy => ?_
  simp only [Fin.lt_def, Fin.ext_iff] at hxy ⊢
  omega

/-- After the outer loop of Algorithm 7.6.3 for the block columns $j < k$, the processed pairs are
all pairs $i < j < k$. -/
private theorem blockDiagInv_outer {b : Fin n → Fin q} (hb : Monotone b)
    {Q₀ T₀ : Matrix (Fin n) (Fin n) ℝ} (hT₀ : T₀.IsUpperTriangular)
    (hdiag : ∀ r c, b r ≠ b c → T₀ r r ≠ T₀ c c) :
    ∀ k ≤ q, BlockDiagInv b Q₀ T₀ (fun x y => x < y ∧ (y : ℕ) < k)
      (Id.run (((List.finRange q).take k).foldlM (fun QT (j : Fin q) =>
        (List.finRange (j : ℕ)).foldlM (fun QT (i : Fin j) =>
          blockDiagStep pure b QT ⟨i, i.2.trans j.2⟩ j) QT) (Q₀, T₀))) := by
  intro k
  induction k with
  | zero =>
    intro _
    have hW : (1 : Matrix (Fin n) (Fin n) ℝ)⁻¹ * T₀ * 1 = T₀ := by simp
    refine ⟨1, isUnit_one, fun r c hrc => one_apply_ne fun h => (h ▸ hrc).false,
      fun r c _ => rfl, (Matrix.mul_one _).symm, ?_, fun r c _ => by rw [hW], fun r c _ h => ?_,
      fun r c _ _ => by rw [hW]; rfl, fun r c _ => rfl⟩
    · rw [hW]
      exact fun r c hrc => hT₀ (hb.reflect_lt hrc)
    · simp at h
  | succ k ih =>
    intro hk
    have hlen : k < (List.finRange q).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hlen, id_run_foldlM_append_singleton,
      List.getElem_finRange]
    refine (blockDiagInv_inner_full hT₀ hdiag _ _ ((ih (by omega)).congr fun x y _ => ?_)).congr
      fun x y _ => ?_
    · simp
    · simp only [Fin.val_cast]
      omega

/-- **Algorithm 7.6.3** of [golub2013matrix], exact semantics. Let
$A, Q, T \in \mathbb{R}^{n \times n}$ with $Q$ orthogonal and $T = Q^T A Q$ upper triangular.
Let the partitioning (7.6.3) be given by a monotone block index $b$, and suppose that diagonal
entries of $T$ in different blocks are distinct. Then there is a nonsingular
$Y \in \mathbb{R}^{n \times n}$ that is block unit upper triangular (zero below the diagonal
blocks and the identity on them) such that the output $Q'$ of Algorithm 7.6.3 in exact
arithmetic is $QY$, and
$$Y^{-1} T Y = \operatorname{diag}(T_{11}, \dots, T_{qq}), \qquad
  (QY)^{-1} A (QY) = \operatorname{diag}(T_{11}, \dots, T_{qq}).$$

**Reading.** The source states the algorithm for an upper quasi-triangular $T$, but Algorithm
7.6.2, which it calls, is stated for triangular matrices only. The quasi-triangular case needs
the $2p \times 2p$ systems (7.6.5), which the source does not write as an algorithm. The
specification assumes $T$ upper triangular.

For triangular $T$, distinct diagonal entries in different blocks mean that the diagonal blocks
have pairwise disjoint spectra. The block diagonal matrix is written as $T$ with the entries
outside the diagonal blocks set to zero. The theorem is a constructive form of Theorem 7.1.6
(`GolubVanLoan.Chapter07.theorem_7_1_6`). In the proof, $Y$ is the product of the $Y_{ij}$ in
the order of the loop; after the pair $(i, j)$ the block $(i, j)$ of $Y^{-1} T Y$ is zero, by
`GolubVanLoan.Chapter07.algorithm_7_6_2_spec` and
`GolubVanLoan.Chapter07.blockDiagonalization_update`, and it stays zero. -/
theorem algorithm_7_6_3_spec {A Q T : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hTA : T = Qᵀ * A * Q) (hT : T.IsUpperTriangular)
    {b : Fin n → Fin q} (hb : Monotone b) (hdiag : ∀ r c, b r ≠ b c → T r r ≠ T c c) :
    ∃ Y : Matrix (Fin n) (Fin n) ℝ, IsUnit Y ∧ (∀ r c, b c < b r → Y r c = 0) ∧
      (∀ r c, b r = b c → Y r c = (1 : Matrix (Fin n) (Fin n) ℝ) r c) ∧
      (Id.run (algorithm_7_6_3 pure Q T b)).1 = Q * Y ∧
      Y⁻¹ * T * Y = (of fun r c => if b r = b c then T r c else 0) ∧
      (Q * Y)⁻¹ * A * (Q * Y) = of fun r c => if b r = b c then T r c else 0 := by
  have h := blockDiagInv_outer hb (Q₀ := Q) hT hdiag q le_rfl
  rw [List.take_of_length_le (by simp)] at h
  obtain ⟨Y, hYu, hY1, hY2, hQY, hWt, hWd, hWp, -, -⟩ := h
  have hblk : Y⁻¹ * T * Y = of fun r c => if b r = b c then T r c else 0 := by
    ext r c
    rw [of_apply]
    split_ifs with hrc
    · exact hWd r c hrc
    · rcases lt_or_gt_of_ne hrc with hlt | hgt
      · exact hWp r c hlt ⟨hlt, (b c).2⟩
      · exact hWt hgt
  refine ⟨Y, hYu, hY1, hY2, hQY, hblk, ?_⟩
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hQQ, ← hblk, hTA]
  simp only [Matrix.mul_assoc]

end BlockDiagLoop

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Equation (7.6.6)** of [golub2013matrix] and the bound after it. Let
$T_{ii} \in \mathbb{C}^{p \times p}$, $T_{jj} \in \mathbb{C}^{q \times q}$ and
$T_{ij} \in \mathbb{C}^{p \times q}$. Then
$$\operatorname{sep}(T_{ii}, T_{jj}) \le |\mu - \nu| \qquad \text{for all } \mu \in
  \lambda(T_{ii}), \ \nu \in \lambda(T_{jj}).$$
If moreover $\operatorname{sep}(T_{ii}, T_{jj}) > 0$, then every solution $Z$ of (7.6.6),
$T_{ii} Z - Z T_{jj} = -T_{ij}$, satisfies
$$\|Z\|_F \le \frac{\|T_{ij}\|_F}{\operatorname{sep}(T_{ii}, T_{jj})}.$$

The separation $\operatorname{sep}(A, B) = \min_{\|X\|_F = 1} \|AX - XB\|_F$ of (7.2.5) is
`Matrix.sep`. The proof specializes `Matrix.sep_le_norm_sub` and
`Matrix.frobenius_norm_le_div_sep`. -/
theorem equation_7_6_6 {p q : ℕ} (Tii : Matrix (Fin p) (Fin p) ℂ) (Tjj : Matrix (Fin q) (Fin q) ℂ)
    (Tij : Matrix (Fin p) (Fin q) ℂ) :
    (∀ μ ∈ spectrum ℂ Tii, ∀ ν ∈ spectrum ℂ Tjj, sep Tii Tjj ≤ ‖μ - ν‖) ∧
      (0 < sep Tii Tjj → ∀ Z : Matrix (Fin p) (Fin q) ℂ, Tii * Z - Z * Tjj = -Tij →
        ‖Z‖ ≤ ‖Tij‖ / sep Tii Tjj) := by
  refine ⟨fun μ hμ ν hν => sep_le_norm_sub hμ hν, fun hs Z hZ => ?_⟩
  have h := frobenius_norm_le_div_sep hs Z
  rwa [hZ, norm_neg] at h

/-- For $Z \in \mathbb{R}^{a \times b}$, the matrix $Y = \begin{bmatrix} I_a & Z \\ 0 & I_b
\end{bmatrix}$ has $\|Y\|_F^2 = a + b + \|Z\|_F^2$. -/
private theorem frobenius_norm_sq_fromBlocks_one {a b : ℕ} (Z : Matrix (Fin a) (Fin b) ℝ) :
    ‖(fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)‖ ^ 2 = a + b + ‖Z‖ ^ 2 := by
  have hone : ∀ m : ℕ, ∑ i : Fin m, ∑ j : Fin m, ‖(1 : Matrix (Fin m) (Fin m) ℝ) i j‖ ^ 2 = m := by
    intro m
    simp [Matrix.one_apply]
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Finset.sum_add_distrib, hone]
  simp [Matrix.zero_apply]
  ring

/-- **§7.6.3** of [golub2013matrix], the condition of $Y_{ij}$. Let
$Z \in \mathbb{R}^{n_i \times n_j}$ and $Y = \begin{bmatrix} I_{n_i} & Z \\ 0 & I_{n_j}
\end{bmatrix}$. Then
$$\kappa_F(Y) = \|Y\|_F \, \|Y^{-1}\|_F = n_i + n_j + \|Z\|_F^2.$$

**Correction.** The source prints $\kappa_F(Y_{ij}) = n_i^2 + n_j^2 + \|Z\|_F^2$. This is false
because $\|I_k\|_F^2 = k$, not $k^2$: for $n_i = n_j = 2$ and $Z = 0$, $Y = I_4$ has
$\kappa_F(Y) = 4$, but the printed value is $8$.

The proof uses $Y^{-1} = \begin{bmatrix} I & -Z \\ 0 & I \end{bmatrix}$, which has the same
Frobenius norm as $Y$. -/
theorem kappaF_blockUnit {a b : ℕ} (Z : Matrix (Fin a) (Fin b) ℝ) :
    ‖(fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)‖ *
        ‖(fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)⁻¹‖ = a + b + ‖Z‖ ^ 2 := by
  have hinv : (fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ)⁻¹ =
      fromBlocks 1 (-Z) 0 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  have h1 := frobenius_norm_sq_fromBlocks_one Z
  have h2 := frobenius_norm_sq_fromBlocks_one (-Z)
  rw [norm_neg] at h2
  rw [hinv, ← Real.sqrt_sq (norm_nonneg (fromBlocks 1 Z 0 1 : Matrix (Fin a ⊕ Fin b) _ ℝ)),
    ← Real.sqrt_sq (norm_nonneg (fromBlocks 1 (-Z) 0 1 : Matrix (Fin a ⊕ Fin b) _ ℝ)), h1, h2,
    Real.mul_self_sqrt (by positivity)]

end Frobenius

/-! ### §7.6.4 Eigenvectors and eigenvalue condition from the Schur form -/

/-- **§7.6.4** of [golub2013matrix], eigenvectors from the real Schur form. Let
$A, Q \in \mathbb{R}^{(p+1+q) \times (p+1+q)}$ with $Q$ orthogonal and
$$Q^T A Q = \begin{bmatrix} T_{11} & u & T_{13} \\ 0 & \lambda & v^T \\ 0 & 0 & T_{33}
  \end{bmatrix},$$
with $T_{11} \in \mathbb{R}^{p \times p}$, $T_{33} \in \mathbb{R}^{q \times q}$,
$u \in \mathbb{R}^p$, $v \in \mathbb{R}^q$ and $\lambda \in \mathbb{R}$. Let
$w \in \mathbb{R}^p$ and $z \in \mathbb{R}^q$ satisfy $(T_{11} - \lambda I) w = -u$ and
$(T_{33} - \lambda I)^T z = -v$, and put
$$x = Q \begin{bmatrix} w \\ 1 \\ 0 \end{bmatrix}, \qquad y = Q \begin{bmatrix} 0 \\ 1 \\ z
  \end{bmatrix}.$$
Then $Ax = \lambda x$ and $y^T A = \lambda y^T$, with $y^T x = 1$, $x^T x = 1 + w^T w$ and
$y^T y = 1 + z^T z$. Hence the condition $1/s(\lambda)$ of $\lambda$ (§7.2.2) is
$$\frac{1}{s(\lambda)} = \frac{\|x\|_2 \, \|y\|_2}{|y^T x|} = \sqrt{(1 + w^T w)(1 + z^T z)}.$$

**Generalization.** The source assumes $\lambda \notin \lambda(T_{11}) \cup \lambda(T_{33})$, so
that $w$ and $z$ exist and are unique. The identities hold for any solutions $w$ and $z$, and
the statement does not need this hypothesis.

The index type is `(Fin p ⊕ Unit) ⊕ Fin q`, and the block matrix is built with
`Matrix.fromBlocks`, `Matrix.fromRows`, `Matrix.replicateCol` and `Matrix.replicateRow`. -/
theorem schur_eigenvectors {p q : ℕ}
    {A Q : Matrix ((Fin p ⊕ Unit) ⊕ Fin q) ((Fin p ⊕ Unit) ⊕ Fin q) ℝ}
    (hQ : Q ∈ orthogonalGroup ((Fin p ⊕ Unit) ⊕ Fin q) ℝ) {T₁₁ : Matrix (Fin p) (Fin p) ℝ}
    {u : Fin p → ℝ} {T₁₃ : Matrix (Fin p) (Fin q) ℝ} {l : ℝ} {v : Fin q → ℝ}
    {T₃₃ : Matrix (Fin q) (Fin q) ℝ}
    (hT : Qᵀ * A * Q = fromBlocks (fromBlocks T₁₁ (replicateCol Unit u) 0 (of fun _ _ => l))
      (fromRows T₁₃ (replicateRow Unit v)) 0 T₃₃)
    {w : Fin p → ℝ} {z : Fin q → ℝ} (hw : (T₁₁ - l • 1) *ᵥ w = -u)
    (hz : (T₃₃ - l • 1)ᵀ *ᵥ z = -v) {x y : (Fin p ⊕ Unit) ⊕ Fin q → ℝ}
    (hx : x = Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0)
    (hy : y = Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) :
    A *ᵥ x = l • x ∧ y ᵥ* A = l • y ∧ y ⬝ᵥ x = 1 ∧ x ⬝ᵥ x = 1 + w ⬝ᵥ w ∧
      y ⬝ᵥ y = 1 + z ⬝ᵥ z ∧ √(x ⬝ᵥ x) * √(y ⬝ᵥ y) / |y ⬝ᵥ x| = √((1 + w ⬝ᵥ w) * (1 + z ⬝ᵥ z)) := by
  subst hx hy
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hQQ' : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hAQ : A * Q = Q * (Qᵀ * A * Q) := by
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQA : Aᵀ * Q = Q * (Qᵀ * A * Q)ᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hdot : ∀ a b : (Fin p ⊕ Unit) ⊕ Fin q → ℝ, (Q *ᵥ a) ⬝ᵥ (Q *ᵥ b) = a ⬝ᵥ b := by
    intro a b
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hQQ', vecMul_one]
  have hw' : T₁₁ *ᵥ w = -u + l • w := by
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hw
    exact sub_eq_iff_eq_add.1 hw
  have hz' : z ᵥ* T₃₃ = -v + l • z := by
    rw [mulVec_transpose, vecMul_sub, vecMul_smul, vecMul_one] at hz
    exact sub_eq_iff_eq_add.1 hz
  have hc1 : replicateCol Unit u *ᵥ (fun _ => (1 : ℝ)) = u := by
    ext i
    simp [mulVec, dotProduct, replicateCol_apply]
  have hc2 : (of fun _ _ => l : Matrix Unit Unit ℝ) *ᵥ (fun _ => (1 : ℝ)) = fun _ => l := by
    ext i
    simp [mulVec, dotProduct]
  have hr1 : (fun _ => (1 : ℝ)) ᵥ* replicateRow Unit v = v := by
    ext i
    simp [vecMul, dotProduct, replicateRow_apply]
  have hr2 : (fun _ => (1 : ℝ)) ᵥ* (of fun _ _ => l : Matrix Unit Unit ℝ) = fun _ => l := by
    ext i
    simp [vecMul, dotProduct]
  have hTx : (Qᵀ * A * Q) *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0 =
      l • Sum.elim (Sum.elim w fun _ => 1) 0 := by
    rw [hT]
    ext ((i | ⟨⟩) | i)
    · simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, add_zero,
        hw', hc1, Sum.elim_inl, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp [fromBlocks_mulVec, hc2]
    · simp [fromBlocks_mulVec]
  have hTy : (Qᵀ * A * Q)ᵀ *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z =
      l • Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z := by
    rw [mulVec_transpose, hT]
    ext ((i | ⟨⟩) | i)
    · simp [vecMul_fromBlocks]
    · simp [vecMul_fromBlocks, hr2]
    · simp only [vecMul_fromBlocks, vecMul_fromRows, Sum.elim_comp_inl, Sum.elim_comp_inr,
        zero_vecMul, zero_add, hz', hr1, Sum.elim_inr, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
  have h1 : A *ᵥ (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) =
      l • (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) := by
    rw [mulVec_mulVec, hAQ, ← mulVec_mulVec, hTx, mulVec_smul]
  have h2 : (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) ᵥ* A =
      l • (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) := by
    rw [← mulVec_transpose, mulVec_mulVec, hQA, ← mulVec_mulVec, hTy, mulVec_smul]
  have h3 : (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) ⬝ᵥ
      (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) = 1 := by
    rw [hdot]
    simp [dotProduct, Fintype.sum_sum_type]
  have h4 : (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) ⬝ᵥ
      (Q *ᵥ Sum.elim (Sum.elim w fun _ => 1) 0) = 1 + w ⬝ᵥ w := by
    rw [hdot]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero, Finset.univ_unique, Finset.sum_singleton,
      mul_one]
    ring
  have h5 : (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) ⬝ᵥ
      (Q *ᵥ Sum.elim (Sum.elim (0 : Fin p → ℝ) fun _ => 1) z) = 1 + z ⬝ᵥ z := by
    rw [hdot]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Finset.univ_unique, Finset.sum_singleton,
      mul_one]
  have hw0 : 0 ≤ 1 + w ⬝ᵥ w :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rw [h3, h4, h5, abs_one, div_one, Real.sqrt_mul hw0]

/-! ### §7.6.5 Ascertaining Jordan block structures -/

/-- **§7.6.5** of [golub2013matrix], Jordan block counts from null spaces. Let
$C, N \in \mathbb{C}^{n \times n}$ and $\lambda \in \mathbb{C}$ with $C = \lambda I + N$. Let
$X^{-1} C X = J$ be a Jordan decomposition, with $X$ nonsingular and $J$ the Jordan form with
blocks of sizes $e_1, \dots, e_q$ and eigenvalues $\mu_1, \dots, \mu_q$. Put
$p_k = \dim \operatorname{null}(N^k)$. Then for every $k \ge 0$,
$$p_{k+1} - p_k = \#\{\, i : \mu_i = \lambda \text{ and } e_i \ge k + 1 \,\},$$
the number of Jordan blocks for $\lambda$ of size at least $k + 1$. In particular these numbers
do not depend on the choice of the Jordan decomposition.

The Jordan form is `Matrix.jordanForm e μ` with upper bidiagonal blocks, laid out along `Fin n`
by the bijection `σ` through `Matrix.reindex`. The subtraction is in $\mathbb{N}$, which is
exact because $p_k \le p_{k+1}$. The proof specializes `Matrix.card_filter_le_jordanBlocks_eq`. -/
theorem jordan_block_count {C N X : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hC : C = c • 1 + N)
    {q : ℕ} {e : Fin q → ℕ} {μ : Fin q → ℂ} (σ : ((i : Fin q) × Fin (e i)) ≃ Fin n)
    (hX : IsUnit X) (h : X⁻¹ * C * X = reindex σ σ (jordanForm e μ)) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (N ^ (k + 1)).mulVecLin) -
        Module.finrank ℂ (LinearMap.ker (N ^ k).mulVecLin) =
      (Finset.univ.filter fun i => μ i = c ∧ k + 1 ≤ e i).card := by
  have hs : IsSimilar C (reindex σ σ (jordanForm e μ)) := ⟨X, hX, h.symm⟩
  have hN : N = C - c • 1 := by rw [hC]; abel
  have key : ∀ m, Module.finrank ℂ (LinearMap.ker (N ^ m).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker ((jordanForm e μ - c • 1) ^ m).mulVecLin) := by
    intro m
    have hr : (reindex σ σ (jordanForm e μ) - c • 1) ^ m =
        reindex σ σ ((jordanForm e μ - c • 1) ^ m) := by
      have := map_pow (reindexAlgEquiv ℂ ℂ σ) (jordanForm e μ - c • 1) m
      rw [map_sub, map_smul, map_one] at this
      simpa using this.symm
    rw [hN, ((hs.sub_smul_one c).pow m).finrank_ker_mulVecLin_eq, hr,
      finrank_ker_mulVecLin_reindex]
  rw [key, key]
  exact card_filter_le_jordanBlocks_eq e μ c k

end GolubVanLoan.Chapter07
