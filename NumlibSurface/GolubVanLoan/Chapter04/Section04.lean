/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Star.Real
import Numlib.Direct.SymmetricIndefinite
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.SymmetricIndefinite
import NumlibSurface.GolubVanLoan.Chapter04.Section02

/-!
# Golub and Van Loan, Section 4.4: Symmetric indefinite systems

This module formalizes §4.4 of [golub2013matrix], the factorizations of a symmetric matrix
$A \in \mathbb{R}^{n \times n}$ that need not be definite. Aasen's method computes $PAP^T = LTL^T$
with $P$ a permutation, $L$ unit lower triangular and $T$ symmetric tridiagonal, (4.4.1). The
diagonal pivoting methods compute $PAP^T = LDL^T$ with $D$ a direct sum of $1 \times 1$ and
$2 \times 2$ pivot blocks, (4.4.2). Each factorization reduces $Ax = b$ to three simpler systems.
The section has no numbered theorem and no numbered algorithm.

The module states the existence of both factorizations with their solve chains, the Parlett–Reid
update of §4.4.1, the Hessenberg relation (4.4.5) behind Aasen's method, and Aasen's method without
pivoting (4.4.14) as a program with its exact correctness. For the diagonal pivoting methods it
states the pivot step (4.4.15), the growth bounds (4.4.16)–(4.4.17) of the Bunch–Parlett strategy,
its parameter $\alpha = (1 + \sqrt{17})/8$, and the true bound on its multipliers. For the
equilibrium systems $\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix}$ of §4.4.5 it states
nonsingularity (4.4.18), a Cholesky-based factorization, the formula (4.4.20) for $y$, and the bound
(4.4.21). The proofs specialize `Numlib.LinearAlgebra.Matrix.SymmetricIndefinite`,
`Numlib.LinearAlgebra.Matrix.SchurComplement` and `Numlib.Direct.SymmetricIndefinite`, and use the
Cholesky factor of §4.2.

## Main definitions

* (4.4.14), `GolubVanLoan.Chapter04.aasenNoPivot`: Aasen's method without pivoting, with its parts
  `GolubVanLoan.Chapter04.aasenH` and `GolubVanLoan.Chapter04.aasenColumn`.

## Main results

* (4.4.1), `GolubVanLoan.Chapter04.equation_4_4_1`: every symmetric $A$ has an Aasen factorization
  $PAP^T = LTL^T$ with $|\ell_{ij}| \le 1$.
* (4.4.2), `GolubVanLoan.Chapter04.equation_4_4_2`: every symmetric $A$ has a block factorization
  $PAP^T = LDL^T$.
* (4.4.2), `GolubVanLoan.Chapter04.equation_4_4_2_multipliers`: the factorization can be chosen with
  $|\ell_{ij}| \le \max(1/\alpha, 1/(1 - \alpha))$.
* §4.4, `GolubVanLoan.Chapter04.aasen_solve` and `GolubVanLoan.Chapter04.blockLDL_solve`: the solve
  chains of (4.4.1) and (4.4.2).
* §4.4.1, `GolubVanLoan.Chapter04.parlettReid_update`: $(I - we_1^T) B (I - we_1^T)^T = B - wu^T -
  uw^T$.
* (4.4.5), `GolubVanLoan.Chapter04.equation_4_4_5`: $H = TL^T$ is upper Hessenberg and $A = LH$.
* (4.4.14), `GolubVanLoan.Chapter04.equation_4_4_14`: Aasen's method without pivoting computes an
  Aasen factorization.
* (4.4.15), `GolubVanLoan.Chapter04.equation_4_4_15`: the block factorization with a nonsingular
  pivot block $E$.
* §4.4.3, `GolubVanLoan.Chapter04.exists_nonsingular_pivot`: a nonzero symmetric matrix has a
  nonsingular pivot of order one or two.
* (4.4.16), `GolubVanLoan.Chapter04.equation_4_4_16`: the growth bound $(1 + \alpha^{-1}) \mu_0$ for
  a $1 \times 1$ pivot.
* (4.4.17), `GolubVanLoan.Chapter04.equation_4_4_17`: the growth bound
  $\frac{3 - \alpha}{1 - \alpha} \mu_0$ for a $2 \times 2$ pivot.
* §4.4.3, `GolubVanLoan.Chapter04.bunchParlett_alpha`: $\alpha = (1 + \sqrt{17})/8$ equates the two
  growth factors.
* §4.4.5, `GolubVanLoan.Chapter04.equilibrium_factorization`: the factorization of the equilibrium
  matrix through Cholesky factors.
* (4.4.18), `GolubVanLoan.Chapter04.equation_4_4_18`: the equilibrium matrix is nonsingular.
* (4.4.20), `GolubVanLoan.Chapter04.equation_4_4_20`: $y = (B^T C^{-1} B)^{-1} B^T C^{-1} f$ when
  $g = 0$.
* (4.4.21), `GolubVanLoan.Chapter04.equation_4_4_21`: $\|(B^T C^{-1} B)^{-1} B^T C^{-1}\|_2$ is
  bounded independently of the positive diagonal $C$.

## Conventions

* Matrices are real, `A : Matrix (Fin n) (Fin n) ℝ`, and indices are 0-based.
* A permutation $P$ is a permutation `σ : Equiv.Perm (Fin n)`, and $PAP^T$ is `A.submatrix σ σ`.
* The Aasen factorization $A = LTL^T$ is `Matrix.IsAasen A L T`: $L$ is unit lower triangular with
  first column $e_1$, and $T$ is symmetric tridiagonal.
* The block factorization $A = LDL^T$ is `Matrix.IsBlockLDL A L D`: $L$ is unit lower triangular,
  $D$ is a direct sum of $1 \times 1$ and $2 \times 2$ pivot blocks, and $L$ is the identity on each
  $2 \times 2$ diagonal block.
* The equilibrium matrix $\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix}$ is `fromBlocks C B Bᵀ 0`,
  which is the saddle-point matrix `Matrix.saddleMatrix C B 0` of the backbone.
* "$B$ has full column rank" is `Function.Injective B.mulVec`.

## Implementation notes

* Aasen's method (4.4.14) is the only form of the method in the source. It is a display, not a
  numbered algorithm, so it is the program `GolubVanLoan.Chapter04.aasenNoPivot`, and its exact
  specification carries the number of the display.
* The program follows the algorithm conventions of `NumlibSurface.GolubVanLoan`. Every product, sum,
  difference and quotient passes through the rounding hook. The inner products
  $L(j, 1{:}j-1) \cdot h(1{:}j-1)$ are running differences from the entry of $A$. The state holds
  the arrays $\alpha$, $\beta$ and $L$ of the source, indexed by `ℕ`.
* The exact specification is read off the run in the exact model through a loop invariant: after
  step $j$, the columns up to $j$ satisfy the recurrences (4.4.10)–(4.4.13), which is what $A = LH$
  with $H = TL^T$ requires of them.
* The growth bounds (4.4.16)–(4.4.17), the parameter $\alpha = (1 + \sqrt{17})/8$ and the bound
  (4.4.21) of Stewart and Todd are restatements of results of `Numlib.Direct.SymmetricIndefinite`.

## Deviations from the source

* **Correction.** The first component of the Aasen recurrence uses the boundary rule in (4.4.14).
  See `GolubVanLoan.Chapter04.aasenH`, `GolubVanLoan.Chapter04.hval`.
* **Reading.** The rounded Aasen column updates use running subtractions. See
  `GolubVanLoan.Chapter04.aasenColumn`.
* **Reading.** The Aasen recurrence totalizes division at a zero subdiagonal pivot. See
  `GolubVanLoan.Chapter04.aasenNoPivot`, `GolubVanLoan.Chapter04.ColDone`.
* **Reading.** The no-pivot factorization assumes nonzero entries only where the program divides.
  See `GolubVanLoan.Chapter04.equation_4_4_14`.
* **Generalization.** The one-by-one growth bound needs only a positive entry bound and an
  admissible pivot. See `GolubVanLoan.Chapter04.equation_4_4_16`.
* **Generalization.** The two-by-two growth bound allows threshold equality at the selected diagonal
  entries. See `GolubVanLoan.Chapter04.equation_4_4_17`.
* **Scope.** The parameter theorem characterizes equality of the two factors. See
  `GolubVanLoan.Chapter04.bunchParlett_alpha`.
* **Scope.** The theorem for (4.4.5) gives the matrix identity and its Hessenberg support. See
  `GolubVanLoan.Chapter04.equation_4_4_5`.
* **(4.4.2)** (correction). The source says that $P$ is chosen so that $|\ell_{ij}| \le 1$. This is
  false for the Bunch–Parlett strategy of the section. The library proves
  $|\ell_{ij}| \le \max(1/\alpha, 1/(1 - \alpha))$. See
  `GolubVanLoan.Chapter04.equation_4_4_2_multipliers`.
* **(4.4.10)** (typo). The loop starts at $k = 1$, which needs an undefined $\beta_0$. The program
  follows (4.4.14), whose loop starts at $k = 2$. See `GolubVanLoan.Chapter04.aasenNoPivot`.
* **(4.4.15)** (generalization). The pivot block $E$ need not be symmetric for the displayed
  factorization. See `GolubVanLoan.Chapter04.equation_4_4_15`.
* **(4.4.20)** (generalization). The source assumes that $C$ is diagonal. The library assumes only
  that $C$ is symmetric positive definite. See `GolubVanLoan.Chapter04.equation_4_4_20`.

## Not formalized

* **The derivation steps (4.4.3)–(4.4.4) and (4.4.6)–(4.4.13).** Their content is
  `GolubVanLoan.Chapter04.equation_4_4_14`.
* **The Bunch–Kaufman strategy.**
* **The stability claims of §4.4.4.**
-/

open FloatingPoint Finset Matrix

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### (4.4.1)–(4.4.2) and their solve chains -/

/-- **Equation (4.4.1)** of [golub2013matrix] (Aasen's factorization). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then there are a permutation matrix $P$, a unit
lower triangular $L$ with $L(:, 1) = e_1$ and a symmetric tridiagonal $T$ such that
$$PAP^T = LTL^T, \qquad |\ell_{ij}| \le 1 \text{ for all } i, j.$$

The source says that $P$ is a permutation chosen such that $|\ell_{ij}| \le 1$. The
factorization is `Matrix.IsAasen (A.submatrix σ σ) L T`. -/
theorem equation_4_4_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L T : Matrix (Fin n) (Fin n) ℝ),
      IsAasen (A.submatrix σ σ) L T ∧ ∀ i j, |L i j| ≤ 1 :=
  exists_perm_isAasen hA

/-- **Equation (4.4.2)** of [golub2013matrix] (the diagonal pivoting factorization). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then there are a permutation matrix $P$, a unit
lower triangular $L$ and a matrix $D$ that is a direct sum of $1 \times 1$ and $2 \times 2$
pivot blocks such that
$$PAP^T = LDL^T,$$
with $L$ the identity on each $2 \times 2$ diagonal block.

**Correction.** The source also says that $P$ can be chosen so that $|\ell_{ij}| \le 1$. This is
false for the pivot strategy of the section, and the theorem omits it. The true bound is
`GolubVanLoan.Chapter04.equation_4_4_2_multipliers`.

The factorization is `Matrix.IsBlockLDL (A.submatrix σ σ) L D`. -/
theorem equation_4_4_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) ℝ),
      IsBlockLDL (A.submatrix σ σ) L D :=
  exists_perm_isBlockLDL hA

/-- **Equation (4.4.2)** of [golub2013matrix], the bound on the multipliers. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and let $0 < \alpha < 1$. Then there are a
permutation matrix $P$, a unit lower triangular $L$ and a direct sum $D$ of $1 \times 1$ and
$2 \times 2$ pivot blocks with $PAP^T = LDL^T$ and
$$|\ell_{ij}| \le \max\left( \frac{1}{\alpha}, \frac{1}{1 - \alpha} \right) \quad \text{for all
  } i, j.$$

**Correction.** The source prints the bound $|\ell_{ij}| \le 1$. It is false for the
Bunch–Parlett strategy of §4.4.3: at $\alpha = (1 + \sqrt{17})/8$, the matrix $\begin{bmatrix} 1
& 3/2 \\ 3/2 & 0 \end{bmatrix}$ takes a $1 \times 1$ pivot with multiplier $3/2$. At this
$\alpha$ the true bound is about $2.78$.

The factorization comes from the Bunch–Parlett strategy with parameter $\alpha$. A $1 \times 1$
pivot $e$ has $|e| \ge \alpha \mu_0$, so its multipliers are at most $1/\alpha$; a $2 \times 2$
pivot $E$ has $|\det E| \ge (1 - \alpha^2) \mu_0^2$, so its multipliers are at most
$1/(1 - \alpha)$. Here $\mu_0 = \max_{i,j} |a_{ij}|$. -/
theorem equation_4_4_2_multipliers {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) ℝ),
      IsBlockLDL (A.submatrix σ σ) L D ∧ ∀ i j, |L i j| ≤ max α⁻¹ (1 - α)⁻¹ :=
  exists_perm_isBlockLDL_abs_le hA hα0 hα1

/-- **Section 4.4** of [golub2013matrix], the solve chain of (4.4.1). Let
$A, L, T \in \mathbb{R}^{n \times n}$ and let $P$ be a permutation matrix with $PAP^T = LTL^T$
an Aasen factorization. If $b, z, w, y \in \mathbb{R}^n$ satisfy
$$Lz = Pb, \qquad Tw = z, \qquad L^T y = w,$$
then $x = P^T y$ satisfies $Ax = b$.

The vector $Pb$ is `b ∘ σ`, and $P^T y$ is `y ∘ σ.symm`. -/
theorem aasen_solve {A L T : Matrix (Fin n) (Fin n) ℝ} {σ : Equiv.Perm (Fin n)}
    (h : IsAasen (A.submatrix σ σ) L T) {b z w y : Fin n → ℝ} (hz : L *ᵥ z = b ∘ σ)
    (hw : T *ᵥ w = z) (hy : Lᵀ *ᵥ y = w) : A *ᵥ (y ∘ σ.symm) = b :=
  h.solve hz hw hy

/-- **Section 4.4** of [golub2013matrix], the solve chain of (4.4.2). Let
$A, L, D \in \mathbb{R}^{n \times n}$ and let $P$ be a permutation matrix with $PAP^T = LDL^T$ a
block factorization as in (4.4.2). If $b, z, w, y \in \mathbb{R}^n$ satisfy
$$Lz = Pb, \qquad Dw = z, \qquad L^T y = w,$$
then $x = P^T y$ satisfies $Ax = b$.

The vector $Pb$ is `b ∘ σ`, and $P^T y$ is `y ∘ σ.symm`. -/
theorem blockLDL_solve {A L D : Matrix (Fin n) (Fin n) ℝ} {σ : Equiv.Perm (Fin n)}
    (h : IsBlockLDL (A.submatrix σ σ) L D) {b z w y : Fin n → ℝ} (hz : L *ᵥ z = b ∘ σ)
    (hw : D *ᵥ w = z) (hy : Lᵀ *ᵥ y = w) : A *ᵥ (y ∘ σ.symm) = b :=
  h.solve hz hw hy

/-! ### §4.4.1 The Parlett–Reid algorithm -/

/-- **Section 4.4.1** of [golub2013matrix], the update in the Parlett–Reid algorithm (4.4.3). Let
$B \in \mathbb{R}^{(m+1) \times (m+1)}$ be symmetric and $w \in \mathbb{R}^{m+1}$, and set
$u = Be_1 - (b_{11}/2) w$. Then
$$B_+ = (I - we_1^T) B (I - we_1^T)^T = B - wu^T - uw^T.$$

The vector $e_1$ is `Pi.single 0 1` on `Fin (m + 1)`. -/
theorem parlettReid_update {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hB : B.IsSymm)
    (w : Fin (m + 1) → ℝ) :
    (1 - vecMulVec w (Pi.single 0 1)) * B * (1 - vecMulVec w (Pi.single 0 1))ᵀ =
      B - vecMulVec w (B *ᵥ Pi.single 0 1 - (B 0 0 / 2) • w) -
        vecMulVec (B *ᵥ Pi.single 0 1 - (B 0 0 / 2) • w) w := by
  have hvec : ∀ j, ((Pi.single 0 1 : Fin (m + 1) → ℝ) ᵥ* B) j = B 0 j := fun j => by
    simp [vecMul, dotProduct, Pi.single_apply]
  have hcol : ∀ i, (B *ᵥ (Pi.single 0 1 : Fin (m + 1) → ℝ)) i = B i 0 := fun i => by
    simp [mulVec, dotProduct, Pi.single_apply]
  have hdot : ((Pi.single 0 1 : Fin (m + 1) → ℝ) ᵥ* B) ⬝ᵥ (Pi.single 0 1) = B 0 0 := by
    simp [dotProduct, Pi.single_apply, hvec]
  have hX : ∀ i, (vecMulVec w ((Pi.single 0 1 : Fin (m + 1) → ℝ) ᵥ* B) *ᵥ
      (Pi.single 0 1 : Fin (m + 1) → ℝ)) i = w i * B 0 0 := fun i => by
    rw [vecMulVec_mulVec, hdot]
    simp
  simp only [transpose_sub, transpose_one, transpose_vecMulVec, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, vecMulVec_mul, mul_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvec,
    hcol, Matrix.sub_mulVec, hX]
  rw [← hB.apply 0 j]
  ring

/-! ### §4.4.2 The method of Aasen -/

/-- **Equation (4.4.5)** of [golub2013matrix]. Let $A = LTL^T$ be an Aasen factorization of
$A \in \mathbb{R}^{n \times n}$, without pivoting. Then $H = TL^T$ is upper Hessenberg and
$A = LH$.

So $A(:, j) = LH(:, j) = \sum_{k \le j+1} L(:, k) h_k$. Aasen's method computes $L$ column by
column from this relation.

**Reading.** Lean states the Hessenberg property and the matrix identity underlying the source's
column expansion. The display also writes out the truncated column sum up to $j+1$.
-/
theorem equation_4_4_5 {A L T : Matrix (Fin n) (Fin n) ℝ} (h : IsAasen A L T) :
    (T * Lᵀ).IsUpperHessenberg ∧ A = L * (T * Lᵀ) :=
  ⟨h.isUpperHessenberg_mul_transpose, h.eq_mul_mul_transpose⟩

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The column $h(1{:}j)$ of $H = TL^T$ in step $j$ of Aasen's method (4.4.14) of [golub2013matrix],
computed from the state $(\alpha, \beta, L)$. With 0-based indices,
$$h_0 = \beta_0 \ell_{j1}, \qquad h_k = \beta_{k-1} \ell_{j,k-1} + \alpha_k \ell_{jk} + \beta_k
  \ell_{j,k+1} \quad (0 < k < j),$$
which is (4.4.10), and $h_j = a_{jj} - L(j, 0{:}j-1) \cdot h(0{:}j-1)$, which is (4.4.11), as a
running difference. Every product and sum is rounded.

**Correction.** The first component uses the separately displayed boundary rule. In the earlier
(4.4.10), the interior loop incorrectly begins at one and uses an undefined $\beta_0$. The final
algorithm (4.4.14) correctly starts that loop at two.
-/
def aasenH {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ))
    (j : Fin n) : M (ℕ → ℝ) := do
  let h ← (List.range j).foldlM (fun (h : ℕ → ℝ) (k : ℕ) => do
    let hk ← (if k = 0 then rnd (s.2.1 0 * s.2.2 j 1) else do
      let a ← rnd (s.2.1 (k - 1) * s.2.2 j (k - 1))
      let b ← rnd (s.1 k * s.2.2 j k)
      let c ← rnd (s.2.1 k * s.2.2 j (k + 1))
      let ab ← rnd (a + b)
      rnd (ab + c) : M ℝ)
    pure (Function.update h k hk)) 0
  let hj ← (List.range j).foldlM (fun (t : ℝ) (k : ℕ) => do
    let p ← rnd (s.2.2 j k * h k)
    rnd (t - p)) (A j j)
  pure (Function.update h j hj)

/-- Step $j$ of Aasen's method (4.4.14) of [golub2013matrix] up to the new column of $L$. The
program returns the diagonal entry $\alpha_j = h_j - \beta_{j-1} \ell_{j,j-1}$ and the vector
$v(j{+}1{:}n) = A(j{+}1{:}n, j) - L(j{+}1{:}n, 1{:}j) \cdot h(1{:}j)$ of (4.4.7), a running
difference from the entries $A(i, j)$. At $j = 1$ it returns $\alpha_1 = a_{11}$ and
$v(2{:}n) = A(2{:}n, 1)$ without rounding.

**Reading.** The dot-product differences are evaluated as rounded running subtractions. At the first
step the program copies the diagonal and full column, of which only the entries below the diagonal
are used as $v$.
-/
def aasenColumn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ)) (j : Fin n) : M (ℝ × (ℕ → ℝ)) :=
  if (j : ℕ) = 0 then pure (A j j, fun i : ℕ => if h : i < n then A ⟨i, h⟩ j else 0) else do
    let h ← aasenH rnd A s j
    let q ← rnd (s.2.1 (j - 1) * s.2.2 j (j - 1))
    let αj ← rnd (h j - q)
    let v ← ((List.finRange n).filter (j < ·)).foldlM (fun (v : ℕ → ℝ) (i : Fin n) => do
      let vi ← (List.range (j + 1)).foldlM (fun (t : ℝ) (k : ℕ) => do
        let p ← rnd (s.2.2 i k * h k)
        rnd (t - p)) (A i j)
      pure (Function.update v i vi)) 0
    pure (αj, v)

/-- **Equation (4.4.14)** of [golub2013matrix] (Aasen's method without pivoting), in the operation
order of the source:
```
L = I_n
for j = 1:n
    if j = 1
        α₁ = a₁₁;  v(2:n) = A(2:n, 1)
    else
        h₁ = β₁ ℓ_{j2}
        for k = 2:j−1
            h_k = β_{k−1} ℓ_{j,k−1} + α_k ℓ_{jk} + β_k ℓ_{j,k+1}
        end
        h_j = a_jj − L(j, 1:j−1) · h(1:j−1)
        α_j = h_j − β_{j−1} ℓ_{j,j−1}
        v(j+1:n) = A(j+1:n, j) − L(j+1:n, 1:j) · h(1:j)
    end
    if j ≤ n−1:  β_j = v(j+1)
    if j ≤ n−2:  L(j+2:n, j+1) = v(j+2:n)/v(j+1)
end
```

**Typo.** The source prints the loop of (4.4.10) from $k = 1$, which needs an undefined
$\beta_0$. The program follows (4.4.14), whose loop starts at $k = 2$.

The state $(\alpha, \beta, L)$ holds the diagonal and the subdiagonal of $T$ and the unit lower
triangular $L$, as arrays indexed by `ℕ`; the entries outside $0 \le i, k < n$ are never read.
The indices are 0-based. The column $h(1{:}j)$ is `GolubVanLoan.Chapter04.aasenH`, and
$\alpha_j$ and $v$ are `GolubVanLoan.Chapter04.aasenColumn`. Every product, sum, difference and
quotient is rounded; the copies $\alpha_1 = a_{11}$, $v = A(:, 1)$ and $\beta_j = v(j+1)$ are
exact.

**Reading.** The recurrence is evaluated with Lean's totalized division when a divisor is zero. The
exact factorization theorem requires every divisor used by this recurrence to be nonzero.
-/
noncomputable def aasenNoPivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    M ((ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ)) :=
  (List.finRange n).foldlM (fun (s : (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ)) (j : Fin n) => do
    let r ← aasenColumn rnd A s j
    let L ← ((List.finRange n).filter (fun i : Fin n => (j : ℕ) + 2 ≤ i)).foldlM
      (fun (L : ℕ → ℕ → ℝ) (i : Fin n) => do
        let l ← rnd (r.2 i / r.2 (j + 1))
        pure (Function.update L i (Function.update (L i) (j + 1) l))) s.2.2
    pure (Function.update s.1 j r.1,
      if (j : ℕ) + 1 < n then Function.update s.2.1 j (r.2 (j + 1)) else s.2.1, L))
    (0, 0, fun i k => if i = k then 1 else 0)

end Programs

/-! ### Exact semantics of (4.4.14) -/

/-- The state of Aasen's method: the diagonal, the subdiagonal and the lower factor, indexed by `ℕ`.
-/
private abbrev St := (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ)

/-- The entries $h_k = H(k, j)$, $k < j$, computed exactly by (4.4.10) and (4.4.14).

**Correction.** The first component uses the separately displayed boundary rule. In the earlier
(4.4.10), the interior loop incorrectly begins at one and uses an undefined $\beta_0$. The final
algorithm (4.4.14) correctly starts that loop at two.
-/
private def hval (s : St) (j k : ℕ) : ℝ :=
  if k = 0 then s.2.1 0 * s.2.2 j 1 else
    s.2.1 (k - 1) * s.2.2 j (k - 1) + s.1 k * s.2.2 j k + s.2.1 k * s.2.2 j (k + 1)

/-- The diagonal entry $h_j$ of (4.4.11), computed exactly. -/
private def hdiag (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : ℝ :=
  A j j - ∑ k ∈ Finset.range j, s.2.2 j k * hval s j k

/-- The column $h(0{:}j)$ of $H = TL^T$, computed exactly. -/
private def hfull (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : ℕ → ℝ :=
  Function.update (hval s j) j (hdiag A s j)

/-- The vector $v$ of (4.4.7), computed exactly. -/
private def vval (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j i : Fin n) : ℝ :=
  if (j : ℕ) = 0 then A i j else
    A i j - ∑ k ∈ Finset.range (j + 1), s.2.2 i k * hfull A s j k

/-- The diagonal entry $\alpha_j$ of (4.4.12), computed exactly. -/
private def αval (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then A j j else hdiag A s j - s.2.1 (j - 1) * s.2.2 j (j - 1)

/-- Column $j$ of the state is finished: $\alpha_j$, $\beta_j$ and the new column $j + 1$ of $L$
have their exact values under the output recurrences in (4.4.14).

**Reading.** The recurrence is evaluated with Lean's totalized division when a divisor is zero. The
exact factorization theorem requires every divisor used by this recurrence to be nonzero.
-/
private def ColDone (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : Prop :=
  s.1 j = αval A s j ∧
    (∀ h : (j : ℕ) + 1 < n, s.2.1 j = vval A s j ⟨j + 1, h⟩) ∧
    ∀ (h : (j : ℕ) + 1 < n) (i : Fin n), (j : ℕ) + 2 ≤ i →
      s.2.2 i (j + 1) = vval A s j i / vval A s j ⟨j + 1, h⟩

/-- Two states agree on all entries that the formulas for the columns up to $m$ read. -/
private def Agree (m : ℕ) (s s' : St) : Prop :=
  (∀ k < m, s'.1 k = s.1 k ∧ s'.2.1 k = s.2.1 k) ∧ ∀ r c, c ≤ m → s'.2.2 r c = s.2.2 r c

private theorem hval_congr {m : ℕ} {s s' : St} (h : Agree m s s') {j k : ℕ} (hj : j ≤ m)
    (hk : k < j) : hval s' j k = hval s j k := by
  obtain ⟨h1, h2⟩ := h
  unfold hval
  split_ifs with hk0
  · rw [(h1 0 (by omega)).2, h2 j 1 (by omega)]
  · rw [(h1 (k - 1) (by omega)).2, (h1 k (by omega)).1, (h1 k (by omega)).2,
      h2 j (k - 1) (by omega), h2 j k (by omega), h2 j (k + 1) (by omega)]

private theorem hdiag_congr (A : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} {s s' : St}
    (h : Agree m s s') {j : Fin n} (hj : (j : ℕ) ≤ m) : hdiag A s' j = hdiag A s j := by
  unfold hdiag
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [h.2 j k (by omega), hval_congr h hj hk']

private theorem hfull_congr (A : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} {s s' : St}
    (h : Agree m s s') {j : Fin n} (hj : (j : ℕ) ≤ m) {k : ℕ} (hk : k ≤ j) :
    hfull A s' j k = hfull A s j k := by
  unfold hfull
  rcases eq_or_lt_of_le hk with rfl | hk
  · rw [Function.update_self, Function.update_self, hdiag_congr A h hj]
  · rw [Function.update_of_ne (ne_of_lt hk), Function.update_of_ne (ne_of_lt hk),
      hval_congr h hj hk]

private theorem vval_congr (A : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} {s s' : St}
    (h : Agree m s s') {j : Fin n} (hj : (j : ℕ) ≤ m) (i : Fin n) :
    vval A s' j i = vval A s j i := by
  unfold vval
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [h.2 i k (by omega), hfull_congr A h hj (by omega)]

private theorem αval_congr (A : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} {s s' : St}
    (h : Agree m s s') {j : Fin n} (hj : (j : ℕ) ≤ m) : αval A s' j = αval A s j := by
  unfold αval
  split_ifs with hj0
  · rfl
  · rw [hdiag_congr A h hj, (h.1 (j - 1) (by omega)).2, h.2 j (j - 1) (by omega)]

/-- A finished column stays finished in a state that agrees with the original state on the columns
up to it. -/
private theorem ColDone.congr (A : Matrix (Fin n) (Fin n) ℝ) {s s' : St} {j : Fin n}
    (hc : ColDone A s j) (h : Agree (j + 1) s s') : ColDone A s' j := by
  have h' : Agree j s s' := ⟨fun k hk => h.1 k (by omega), fun r c hc => h.2 r c (by omega)⟩
  obtain ⟨e1, e2, e3⟩ := hc
  refine ⟨?_, fun hn => ?_, fun hn i hi => ?_⟩
  · rw [(h.1 j (by omega)).1, αval_congr A h' le_rfl]
    exact e1
  · rw [(h.1 j (by omega)).2, vval_congr A h' le_rfl]
    exact e2 hn
  · rw [h.2 i (j + 1) le_rfl, vval_congr A h' le_rfl, vval_congr A h' le_rfl]
    exact e3 hn i hi

/-- The loop invariant of Aasen's method after $c$ columns: $L$ is unit lower triangular, its
columns $0$ and those after $c$ are those of the identity, and the columns before $c$ are
finished. -/
private def Inv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ) (s : St) : Prop :=
  (∀ r k, r ≤ k → s.2.2 r k = if r = k then 1 else 0) ∧
    (∀ r k, (k = 0 ∨ c < k) → s.2.2 r k = if r = k then 1 else 0) ∧
    ∀ j : Fin n, (j : ℕ) < c → ColDone A s j


/-- The sum of a list over `List.range j` is the sum over `Finset.range j`. -/
private theorem list_sum_range (g : ℕ → ℝ) (j : ℕ) :
    ((List.range j).map g).sum = ∑ k ∈ Finset.range j, g k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A loop that writes entry $k$ from a value $F(k)$ that does not depend on the state leaves $F(k)$
at entry $k$, for $k$ in a duplicate-free list. -/
private theorem foldl_update_const (F : ℕ → ℝ) (l : List ℕ) (hl : l.Nodup) (g : ℕ → ℝ) {k : ℕ}
    (hk : k ∈ l) : l.foldl (fun h k => Function.update h k (F k)) g k = F k :=
  List.foldl_update_apply_of_pairwise (fun k : ℕ => k) (fun k _ => F k)
    (hl.imp fun hab => ⟨hab, fun _ _ _ => rfl⟩) g hk

/-- In exact arithmetic, `GolubVanLoan.Chapter04.aasenH` computes the column $h(0{:}j)$. -/
private theorem aasenH_exact (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) :
    ∀ h ∈ (aasenH (M := SetM) pure A s j).run, ∀ k ≤ (j : ℕ), h k = hfull A s j k := by
  intro h hh k hk
  simp only [aasenH, pure_bind, ite_pure, List.foldlM_pure, SetM.mem_run_pure] at hh
  subst hh
  have hF : ∀ k' < (j : ℕ), List.foldl (fun h k => Function.update h k
      (if k = 0 then s.2.1 0 * s.2.2 j 1 else s.2.1 (k - 1) * s.2.2 j (k - 1) + s.1 k * s.2.2 j k +
        s.2.1 k * s.2.2 j (k + 1))) 0 (List.range j) k' = hval s j k' := fun k' hk' =>
    foldl_update_const _ _ (List.nodup_range) _ (List.mem_range.2 hk')
  rcases eq_or_lt_of_le hk with rfl | hk
  · rw [Function.update_self, hfull, Function.update_self, List.foldl_sub_eq_sub_sum_map,
      list_sum_range, hdiag]
    congr 1
    exact Finset.sum_congr rfl fun k' hk' => by rw [hF k' (Finset.mem_range.1 hk')]
  · rw [Function.update_of_ne (ne_of_lt hk), hfull, Function.update_of_ne (ne_of_lt hk), hF k hk]

/-- In exact arithmetic, `GolubVanLoan.Chapter04.aasenColumn` computes $\alpha_j$ and $v$. -/
private theorem aasenColumn_exact (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) :
    ∀ r ∈ (aasenColumn (M := SetM) pure A s j).run,
      r.1 = αval A s j ∧ ∀ i : Fin n, j < i → r.2 i = vval A s j i := by
  intro r hr
  unfold aasenColumn at hr
  split_ifs at hr with hj0
  · rw [SetM.mem_run_pure] at hr
    subst hr
    refine ⟨by rw [αval, ite_eq_left hj0], fun i _ => ?_⟩
    rw [vval, ite_eq_left hj0]
    simp
  · simp only [SetM.mem_run_bind, pure_bind, List.foldlM_pure, SetM.mem_run_pure] at hr
    obtain ⟨h, hh, rfl⟩ := hr
    have hH := aasenH_exact A s j h hh
    refine ⟨?_, fun i hi => ?_⟩
    · rw [αval, ite_eq_right hj0, hH j le_rfl, hfull, Function.update_self]
    · have := List.foldl_update_apply_of_pairwise (fun i : Fin n => (i : ℕ)) (fun i _ =>
          List.foldl (fun t k => t - s.2.2 i k * h k) (A i j) (List.range (j + 1)))
          (l := (List.finRange n).filter (j < ·))
          (((List.nodup_finRange n).filter _).imp fun hab =>
            ⟨fun e => hab (Fin.ext e), fun _ _ _ => rfl⟩) 0 (a := i) (by simpa using hi)
      dsimp only
      rw [this, vval, ite_eq_right hj0, List.foldl_sub_eq_sub_sum_map, list_sum_range]
      congr 1
      exact Finset.sum_congr rfl fun k hk => by
        rw [hH k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]


/-- The exact run of Aasen's method is one of its runs in the exact rounding model. -/
private theorem aasenNoPivot_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (aasenNoPivot pure A) ∈ (aasenNoPivot (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [aasenNoPivot, aasenColumn, aasenH, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

/-- The exact run of Aasen's method satisfies the loop invariant after all $n$ columns. -/
private theorem aasenNoPivot_inv (A : Matrix (Fin n) (Fin n) ℝ) :
    Inv A n (Id.run (aasenNoPivot pure A)) := by
  have hmem := aasenNoPivot_mem_exact A
  rw [aasenNoPivot, RoundingModel.round_exact] at hmem
  refine SetM.forall_mem_run_foldlM_finRange (Inv A)
    ⟨fun r k _ => rfl, fun r k _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    (fun j s hs s' hs' => ?_) _ hmem
  obtain ⟨hS1, hS2, hdone⟩ := hs
  simp only [SetM.mem_run_bind, pure_bind, List.foldlM_pure, SetM.mem_run_pure] at hs'
  obtain ⟨r, hr, rfl⟩ := hs'
  obtain ⟨hr1, hr2⟩ := aasenColumn_exact A s j r hr
  -- the new column of `L`
  have hL₁ := fun (i : Fin n) (hi : i ∈ (List.finRange n).filter
      (fun i : Fin n => (j : ℕ) + 2 ≤ i)) => List.foldl_update_apply_of_pairwise
    (fun i : Fin n => (i : ℕ))
    (fun i (L : ℕ → ℕ → ℝ) => Function.update (L i) (j + 1) (r.2 i / r.2 (j + 1)))
    (((List.nodup_finRange n).filter _).imp fun hab =>
      ⟨fun e => hab (Fin.ext e), fun g g' hg => by rw [hg _ (Ne.symm fun e => hab (Fin.ext e))]⟩)
    s.2.2 hi
  have hL₂ := fun (t : ℕ) (ht : ∀ i ∈ (List.finRange n).filter
      (fun i : Fin n => (j : ℕ) + 2 ≤ i), (i : ℕ) ≠ t) => List.foldl_update_apply_of_forall_ne
    (fun i : Fin n => (i : ℕ))
    (fun i (L : ℕ → ℕ → ℝ) => Function.update (L i) (j + 1) (r.2 i / r.2 (j + 1))) ht s.2.2
  set L' := List.foldl (fun (L : ℕ → ℕ → ℝ) (i : Fin n) =>
    Function.update L i (Function.update (L i) (j + 1) (r.2 i / r.2 (j + 1)))) s.2.2
    ((List.finRange n).filter (fun i : Fin n => (j : ℕ) + 2 ≤ i)) with hL'
  have hLnew : ∀ (i : Fin n), (j : ℕ) + 2 ≤ i → L' i (j + 1) = r.2 i / r.2 (j + 1) := by
    intro i hi
    rw [hL₁ i (by simpa using hi), Function.update_self]
  have hLold : ∀ (a c : ℕ), (c ≠ (j : ℕ) + 1 ∨ a < (j : ℕ) + 2) → L' a c = s.2.2 a c := by
    intro a c hc
    by_cases ha : ∃ i ∈ (List.finRange n).filter (fun i : Fin n => (j : ℕ) + 2 ≤ i),
        (i : ℕ) = a
    · obtain ⟨i, hi, rfl⟩ := ha
      have hi' : (j : ℕ) + 2 ≤ i := by simpa using hi
      rw [hL₁ i hi, Function.update_of_ne (by omega)]
    · push Not at ha
      rw [hL₂ a ha]
  have hagree : Agree j s (Function.update s.1 j r.1,
      if (j : ℕ) + 1 < n then Function.update s.2.1 j (r.2 (j + 1)) else s.2.1, L') := by
    refine ⟨fun k hk => ⟨?_, ?_⟩, fun a c hc => hLold a c (by omega)⟩
    · exact Function.update_of_ne (by omega) _ _
    · dsimp only
      split_ifs
      · exact Function.update_of_ne (by omega) _ _
      · rfl
  refine ⟨fun a c hac => ?_, fun a c hc => ?_, fun m hm => ?_⟩
  · change L' a c = _
    rw [hLold a c (by omega)]
    exact hS1 a c hac
  · change L' a c = _
    rw [hLold a c (by omega)]
    exact hS2 a c (by omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | hm
    · exact (hdone m hm).congr A ⟨fun k hk => hagree.1 k (by omega),
        fun a c hc => hagree.2 a c (by omega)⟩
    · have hmj : m = j := Fin.ext hm
      subst hmj
      refine ⟨?_, fun hn => ?_, fun hn i hi => ?_⟩
      · change Function.update s.1 m r.1 m = _
        rw [αval_congr A hagree le_rfl, Function.update_self, hr1]
      · change (if (m : ℕ) + 1 < n then Function.update s.2.1 m (r.2 (m + 1)) else s.2.1) m = _
        rw [vval_congr A hagree le_rfl, ite_eq_left hn, Function.update_self]
        exact hr2 ⟨m + 1, hn⟩ (Fin.lt_def.2 (Nat.lt_succ_self _))
      · change L' i (m + 1) = _
        rw [hLnew i hi, vval_congr A hagree le_rfl, vval_congr A hagree le_rfl,
          ← hr2 i (Fin.lt_def.2 (by omega)), ← hr2 ⟨m + 1, hn⟩ (Fin.lt_def.2 (Nat.lt_succ_self _))]

/-- **Equation (4.4.14)** of [golub2013matrix], exact correctness of Aasen's method without
pivoting. Let $A \in \mathbb{R}^{(N+1) \times (N+1)}$ be symmetric, and let $(\alpha, \beta, L)$
be the output of `GolubVanLoan.Chapter04.aasenNoPivot` on $A$ in exact arithmetic. If
$\beta_j \neq 0$ for $j = 1, \dots, N - 1$, then
$$A = LTL^T, \qquad T = \begin{bmatrix} \alpha_1 & \beta_1 & & \\ \beta_1 & \alpha_2 & \ddots &
  \\ & \ddots & \ddots & \beta_N \\ & & \beta_N & \alpha_{N+1} \end{bmatrix},$$
with $L$ unit lower triangular and $L(:, 1) = e_1$.

The numbers $\beta_1, \dots, \beta_{N-1}$ are the numbers $v(j+1)$ that the method uses as
divisors; with 0-based indices the hypothesis is on $\beta_j$ for $j + 1 < N$. The source
obtains the method by combining the equations of its derivation. The loop invariant is that
derivation, (4.4.5)–(4.4.13): the columns up to $j$ of $A = LH$, with $H = TL^T$ upper
Hessenberg, hold with $h(1{:}j)$ the column $j$ of $H$. The conclusion is `Matrix.IsAasen` with
$T$ = `Matrix.tridiagonalOf β α β`.

**Reading.** The program's exact factorization theorem explicitly assumes nonzero $v(j+1)$ for the
iterations that divide by it. The final subdiagonal entry can be zero because it is never used as a
divisor.
-/
theorem equation_4_4_14 {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hA : A.IsSymm)
    (hβ : ∀ j : ℕ, j + 1 < N → (Id.run (aasenNoPivot pure A)).2.1 j ≠ 0) :
    IsAasen A (of fun i k : Fin (N + 1) => (Id.run (aasenNoPivot pure A)).2.2 i k)
      (tridiagonalOf (fun i : Fin N => (Id.run (aasenNoPivot pure A)).2.1 i)
        (fun i => (Id.run (aasenNoPivot pure A)).1 i)
        (fun i : Fin N => (Id.run (aasenNoPivot pure A)).2.1 i)) := by
  obtain ⟨hS1, hS2, hcol⟩ := aasenNoPivot_inv A
  set s := Id.run (aasenNoPivot pure A)
  have hup : ∀ r k : ℕ, r < k → s.2.2 r k = 0 := fun r k h => by
    rw [hS1 r k h.le, ite_eq_right h.ne]
  have hone : ∀ r, s.2.2 r r = 1 := fun r => by rw [hS1 r r le_rfl, ite_eq_left rfl]
  have hzero : ∀ r : ℕ, r ≠ 0 → s.2.2 r 0 = 0 := fun r hr => by
    rw [hS2 r 0 (Or.inl rfl), ite_eq_right hr]
  set Lm : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := of fun i k => s.2.2 i k with hLm
  set T := tridiagonalOf (fun i : Fin N => s.2.1 i) (fun i => s.1 i) (fun i : Fin N => s.2.1 i)
    with hT
  have hLu : Lm.IsUnitLowerTriangular :=
    ⟨fun i k hik => hup i k (OrderDual.toDual_lt_toDual.1 hik), fun i => hone i⟩
  have hTs : T.IsSymm := by rw [IsSymm, hT, tridiagonalOf_transpose]
  refine ⟨hLu, fun i h hi => hzero i (fun e => hi (Fin.ext e)), hTs,
    isTridiagonal_tridiagonalOf _ _ _, ?_⟩
  -- the column `m` of `H = T Lᵀ`, entry `k`
  set Hn : ℕ → ℕ → ℝ := fun m k =>
    (if 0 < k then s.2.1 (k - 1) * s.2.2 m (k - 1) else 0) + s.1 k * s.2.2 m k +
      (if k < N then s.2.1 k * s.2.2 m (k + 1) else 0) with hHn
  have hH : ∀ k m : Fin (N + 1), (T * Lmᵀ) k m = Hn m k := by
    intro k m
    have := tridiagonalOf_mulVec (fun i : Fin N => s.2.1 i) (fun i => s.1 i)
      (fun i : Fin N => s.2.1 i) (fun c => s.2.2 m c) k
    change (T *ᵥ fun c => s.2.2 m c) k = _
    rw [this, hHn]
    simp only
    split_ifs <;> rfl
  -- the entries of the column `m` of `H`
  have hHlow : ∀ m k : ℕ, m ≤ N → k < m → Hn m k = hval s m k := by
    intro m k hm hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hHn, hval, hzero m (by omega), show 0 < N by omega]
    · simp only [hHn, hval, ite_eq_left hk0, ite_eq_left (show k < N by omega),
        ite_eq_right (show k ≠ 0 by omega)]
  have hHdiag : ∀ m : Fin (N + 1), Hn m m = hdiag A s m := by
    intro m
    obtain ⟨e1, -, -⟩ := hcol m m.isLt
    simp only [hHn]
    rw [e1, αval, hone, hup m (m + 1) (by omega)]
    by_cases h0 : (m : ℕ) = 0
    · rw [ite_eq_left h0, ite_eq_right (by omega)]
      simp [hdiag, h0]
    · rw [ite_eq_right h0, ite_eq_left (Nat.pos_of_ne_zero h0)]
      split_ifs <;> ring
  have hHsub : ∀ m : ℕ, m < N → Hn m (m + 1) = s.2.1 m := by
    intro m hm
    simp only [hHn]
    rw [ite_eq_left (by omega), Nat.add_sub_cancel, hone, hup m (m + 1) (by omega)]
    split_ifs
    · rw [hup m (m + 1 + 1) (by omega)]
      ring
    · ring
  have hHzero : ∀ m k : ℕ, m + 2 ≤ k → Hn m k = 0 := by
    intro m k hk
    simp only [hHn]
    rw [hup m (k - 1) (by omega), hup m k (by omega), hup m (k + 1) (by omega)]
    simp
  -- the lower triangle of `L T Lᵀ`
  have hlow : ∀ i m : Fin (N + 1), m ≤ i → (Lm * T * Lmᵀ) i m = A i m := by
    intro i m hmi
    have hmi' := Fin.le_def.1 hmi
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [hH]
    simp only [hLm, of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => s.2.2 i k * Hn m k) (N + 1),
      ← Finset.sum_range_add_sum_Ico _ (show (m : ℕ) + 1 ≤ N + 1 by omega)]
    have hsplit : ∑ k ∈ Finset.range ((m : ℕ) + 1), s.2.2 i k * Hn m k =
        ∑ k ∈ Finset.range ((m : ℕ) + 1), s.2.2 i k * hfull A s m k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
      · rw [hfull, Function.update_of_ne (ne_of_lt hk'), hHlow m k (by omega) hk']
      · rw [hfull, Function.update_self, hHdiag]
    have htail : ∑ k ∈ Finset.Ico ((m : ℕ) + 1) (N + 1), s.2.2 i k * Hn m k =
        if (m : ℕ) < N then s.2.2 i (m + 1) * s.2.1 m else 0 := by
      split_ifs with hmN
      · rw [Finset.sum_eq_single_of_mem ((m : ℕ) + 1) (by simp; omega) fun k hk hk' => by
          rw [hHzero m k (by simp at hk; omega), mul_zero], hHsub m hmN]
      · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    rw [hsplit, htail]
    rcases eq_or_lt_of_le hmi with hmi | hmi
    · -- the diagonal
      subst hmi
      rw [Finset.sum_range_succ, hfull, Function.update_self, hone, one_mul]
      have : ∑ k ∈ Finset.range m, s.2.2 m k * Function.update (hval s m) m (hdiag A s m) k =
          ∑ k ∈ Finset.range m, s.2.2 m k * hval s m k :=
        Finset.sum_congr rfl fun k hk => by
          rw [Function.update_of_ne (ne_of_lt (Finset.mem_range.1 hk))]
      rw [this, hdiag]
      split_ifs
      · rw [hup m (m + 1) (by omega), zero_mul]
        ring
      · ring
    · -- below the diagonal
      have hmi'' := Fin.lt_def.1 hmi
      have hmN : (m : ℕ) < N := by have := i.isLt; omega
      rw [ite_eq_left hmN]
      obtain ⟨-, e2, e3⟩ := hcol m m.isLt
      have hv : vval A s m i =
          A i m - ∑ k ∈ Finset.range ((m : ℕ) + 1), s.2.2 i k * hfull A s m k := by
        unfold vval
        split_ifs with h0
        · rw [h0, Finset.sum_range_one, hzero i (by omega), zero_mul, sub_zero]
        · rfl
      have hprod : s.2.2 i (m + 1) * s.2.1 m = vval A s m i := by
        rw [e2 (by omega)]
        rcases Nat.lt_or_ge (i : ℕ) (m + 2) with hi | hi
        · have hi1 : i = ⟨m + 1, by omega⟩ := Fin.ext (by simp only; omega)
          rw [hi1, hone, one_mul]
        · have hβm := hβ m (by have := i.isLt; omega)
          rw [e2 (by omega)] at hβm
          rw [e3 (by omega) i hi, div_mul_cancel₀ _ hβm]
      rw [hprod, hv]
      ring
  have hsymm : (Lm * T * Lmᵀ).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, hTs.eq, Matrix.mul_assoc]
  ext i m
  rcases le_total m i with h | h
  · exact hlow i m h
  · rw [← hsymm.apply i m, hlow m i h, hA.apply]


/-! ### §4.4.3 Diagonal pivoting methods -/

/-- **Equation (4.4.15)** of [golub2013matrix], with the displayed block factorization. Let
$E \in \mathbb{R}^{s \times s}$ be nonsingular, $C \in \mathbb{R}^{m \times s}$ and
$B \in \mathbb{R}^{m \times m}$. Then
$$\begin{bmatrix} E & C^T \\ C & B \end{bmatrix} = \begin{bmatrix} I_s & 0 \\ CE^{-1} & I_m
  \end{bmatrix} \begin{bmatrix} E & 0 \\ 0 & B - CE^{-1}C^T \end{bmatrix} \begin{bmatrix} I_s &
  E^{-1}C^T \\ 0 & I_m \end{bmatrix}.$$

**Generalization.** The source writes this for $P_1 A P_1^T = \begin{bmatrix} E & C^T \\ C & B
\end{bmatrix}$ with $A$ symmetric, $s = 1$ or $2$ and $m = n - s$. The factorization holds for
every nonsingular pivot block $E$, symmetric or not.

The matrix $\tilde A = B - CE^{-1}C^T$ is the reduced matrix of (4.4.15). The existence of a
nonsingular pivot block is `GolubVanLoan.Chapter04.exists_nonsingular_pivot`. -/
theorem equation_4_4_15 {s m : ℕ} {E : Matrix (Fin s) (Fin s) ℝ} (hE : IsUnit E)
    (C : Matrix (Fin m) (Fin s) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    fromBlocks E Cᵀ C B =
      fromBlocks 1 0 (C * E⁻¹) 1 * fromBlocks E 0 0 (B - C * E⁻¹ * Cᵀ) *
        fromBlocks 1 (E⁻¹ * Cᵀ) 0 1 := by
  have hinv : E * E⁻¹ = 1 := mul_nonsing_inv E ((isUnit_iff_isUnit_det E).1 hE)
  have hinv' : E⁻¹ * E = 1 := nonsing_inv_mul E ((isUnit_iff_isUnit_det E).1 hE)
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, ← Matrix.mul_assoc, hinv]
  rw [Matrix.mul_assoc C E⁻¹ E, hinv', Matrix.mul_one, add_sub_cancel]

/-- **Section 4.4.3** of [golub2013matrix], the choice of the pivot in (4.4.15). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and nonzero. Then $A$ has a nonsingular principal
pivot of order one or two: either $a_{ii} \neq 0$ for some $i$, or there are $i \neq j$ with
$a_{ii} a_{jj} - a_{ij} a_{ji} \neq 0$.

The source says that if $A$ is nonzero, then it is always possible to choose $P_1$ and $s$ so
that $E$ is nonsingular. This is Problem P4.4.1 of the source. -/
theorem exists_nonsingular_pivot {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hA0 : A ≠ 0) :
    (∃ i, A i i ≠ 0) ∨ ∃ i j, i ≠ j ∧ A i i * A j j - A i j * A j i ≠ 0 :=
  exists_principal_pivot_ne_zero hA hA0

/-- **Equation (4.4.16)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, let
$\alpha > 0$ and $\mu_0 > 0$ with $|a_{ij}| \le \mu_0$ for all $i, j$, and let $p$ be an index
with $\alpha \mu_0 \le |a_{pp}|$. Then the reduced matrix $\tilde A$ of the $1 \times 1$ pivot
$a_{pp}$, with entries $\tilde a_{ij} = a_{ij} - a_{ip} a_{pj} / a_{pp}$ for $i, j \neq p$,
satisfies
$$|\tilde a_{ij}| \le (1 + \alpha^{-1}) \mu_0$$
for all indices $i, j \neq p$.

For a symmetric $A$, the matrix $\tilde A$ is the matrix $B - vv^T / a_{pp}$ of (4.4.15) with
$s = 1$; the theorem does not need the symmetry. In the Bunch–Parlett strategy,
$\mu_0 = \max |a_{ij}|$ and $\mu_1 = \max |a_{ii}|$; when $\mu_1 \ge \alpha \mu_0$, the maximal
diagonal entry is such a pivot. The source says that the bound is easy to verify from (4.4.15)
for $s = 1$. The reduced matrix is `Matrix.schurComplementSingle A p`.

**Generalization.** Lean permits any matrix, any positive uniform entry bound $\mu_0$, and any
positive $\alpha$ for which the chosen diagonal entry meets the threshold. The source uses symmetric
matrices, $0 < \alpha < 1$, and actual maximum entry and diagonal magnitudes.
-/
theorem equation_4_4_16 {A : Matrix (Fin n) (Fin n) ℝ} {p : Fin n} {α μ₀ : ℝ} (hα : 0 < α)
    (hμ₀ : 0 < μ₀) (hA : ∀ i j, |A i j| ≤ μ₀) (hp : α * μ₀ ≤ |A p p|)
    (i j : {i : Fin n // i ≠ p}) :
    |A.schurComplementSingle p i j| ≤ (1 + α⁻¹) * μ₀ :=
  BunchParlett.abs_schurComplementSingle_le hα hμ₀ hA hp i j

/-- **Equation (4.4.17)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric,
let $0 < \alpha < 1$ and $\mu_0 > 0$ with $|a_{ij}| \le \mu_0$ for all $i, j$, and let $p, q$ be
indices with $|a_{qp}| = \mu_0$, $|a_{pp}| \le \alpha \mu_0$ and $|a_{qq}| \le \alpha \mu_0$.
Then the $2 \times 2$ pivot block $E = A(\{p, q\}, \{p, q\})$ is nonsingular, and the reduced
matrix $\tilde A = B - CE^{-1}C^T$ satisfies
$$|\tilde a_{ij}| \le \frac{3 - \alpha}{1 - \alpha} \mu_0$$
for all indices $i, j \notin \{p, q\}$.

In the Bunch–Parlett strategy, the bounds on $a_{pp}$ and $a_{qq}$ follow from
$\mu_1 < \alpha \mu_0$. The reduced matrix is `Matrix.schurComplement` of $A$ reindexed along
`Sum.elim ![p, q] Subtype.val`, that is, along the pivot pair followed by the other indices.

**Generalization.** Only the two chosen diagonal entries need satisfy their upper bounds, which can
be attained. The source uses the strict inequality for the largest diagonal entry to select the
two-by-two branch.
-/
theorem equation_4_4_17 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    {α μ₀ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (hμ₀ : 0 < μ₀) (hAμ : ∀ i j, |A i j| ≤ μ₀)
    (hqp : |A q p| = μ₀) (hpp : |A p p| ≤ α * μ₀) (hqq : |A q q| ≤ α * μ₀) :
    IsUnit (A.submatrix ![p, q] ![p, q]) ∧
      ∀ i j : {i : Fin n // i ≠ p ∧ i ≠ q},
        |(A.submatrix (Sum.elim ![p, q] Subtype.val)
          (Sum.elim ![p, q] Subtype.val)).schurComplement i j| ≤ (3 - α) / (1 - α) * μ₀ :=
  BunchParlett.abs_schurComplement_two_le hA hα₀ hα₁ hμ₀ hAμ hqp hpp hqq

/-- **Section 4.4.3** of [golub2013matrix], the Bunch–Parlett parameter. The number
$\alpha = (1 + \sqrt{17})/8$ is the unique $\alpha \in (0, 1)$ with
$$(1 + \alpha^{-1})^2 = \frac{3 - \alpha}{1 - \alpha}.$$

The left side is the growth factor of two $s = 1$ steps and the right side that of one $s = 2$
step. By equating them, Bunch and Parlett conclude that this $\alpha$ is optimum from the
standpoint of minimizing the bound on element growth.

**Reading.** Lean characterizes the unique intersection of the two growth factors. The source also
identifies it as the minimizer of the worst growth factor.
-/
theorem bunchParlett_alpha :
    {α : ℝ | 0 < α ∧ α < 1 ∧ (1 + α⁻¹) ^ 2 = (3 - α) / (1 - α)} = {(1 + √17) / 8} :=
  BunchParlett.alpha_eq

/-! ### §4.4.5 Equilibrium systems -/

/-- For $C \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times p}$, the equilibrium matrix
$\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix}$ is the saddle-point matrix
`Matrix.saddleMatrix C B 0` of the backbone. -/
theorem fromBlocks_transpose_zero_eq_saddleMatrix {p : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : fromBlocks C B Bᵀ 0 = C.saddleMatrix B 0 := by
  rw [saddleMatrix, conjTranspose_eq_transpose_of_trivial]

/-- **Section 4.4.5** of [golub2013matrix], the factorization of the equilibrium matrix through
Cholesky factors. Let $C \in \mathbb{R}^{n \times n}$ be symmetric positive definite with
Cholesky factor $G$, let $B \in \mathbb{R}^{n \times p}$ have full column rank, and let
$K \in \mathbb{R}^{n \times p}$ satisfy $GK = B$. Then $K^T K = B^T C^{-1} B$, this matrix is
symmetric positive definite, and with $H$ its Cholesky factor,
$$\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix} = \begin{bmatrix} G & 0 \\ K^T & H
  \end{bmatrix} \begin{bmatrix} G^T & K \\ 0 & -H^T \end{bmatrix}.$$

The source describes the computation in three steps: compute the Cholesky factorization
$C = GG^T$, solve $GK = B$ for $K$, and compute the Cholesky factorization
$HH^T = K^T K = B^T C^{-1} B$. The Cholesky factors are `Matrix.cholesky C` and
`Matrix.cholesky (Kᵀ * K)` (Theorem 4.2.7). -/
theorem equilibrium_factorization {p : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin p) ℝ} (hC : C.PosDef) (hB : Function.Injective B.mulVec)
    {K : Matrix (Fin n) (Fin p) ℝ} (hK : cholesky C * K = B) :
    Kᵀ * K = Bᵀ * C⁻¹ * B ∧ (Kᵀ * K).PosDef ∧
      fromBlocks C B Bᵀ 0 = fromBlocks (cholesky C) 0 Kᵀ (cholesky (Kᵀ * K)) *
        fromBlocks (cholesky C)ᵀ K 0 (-(cholesky (Kᵀ * K))ᵀ) := by
  obtain ⟨-, -, -, hCG⟩ := theorem_4_2_7 hC
  have hGdet : IsUnit (cholesky C).det := by
    have hCd : IsUnit C.det := (isUnit_iff_isUnit_det C).1 hC.isUnit
    rw [hCG, det_mul] at hCd
    exact isUnit_of_mul_isUnit_left hCd
  have hKe : K = (cholesky C)⁻¹ * B := by
    rw [← hK, ← Matrix.mul_assoc, nonsing_inv_mul _ hGdet, Matrix.one_mul]
  have hKK : Kᵀ * K = Bᵀ * C⁻¹ * B := by
    conv_rhs => rw [hCG, Matrix.mul_inv_rev, ← transpose_nonsing_inv]
    rw [hKe, transpose_mul]
    simp only [Matrix.mul_assoc]
  have hKinj : Function.Injective K.mulVec := fun x y hxy =>
    hB (by rw [← hK, ← mulVec_mulVec, ← mulVec_mulVec, hxy])
  have hpos : (Kᵀ * K).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self K hKinj
  refine ⟨hKK, hpos, ?_⟩
  have h := saddleMatrix_zero_eq_mul (A := C) (G := cholesky C) (B := B) (K := K)
    (H := cholesky (Kᵀ * K)) (by rw [conjTranspose_eq_transpose_of_trivial]; exact hCG) hK
    (by
      rw [conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial]
      exact cholesky_mul_transpose hpos)
  rw [fromBlocks_transpose_zero_eq_saddleMatrix, h]
  simp only [conjTranspose_eq_transpose_of_trivial]

/-- **Equation (4.4.18)** of [golub2013matrix]. Let $C \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and let $B \in \mathbb{R}^{n \times p}$ have full column rank. Then the
symmetric indefinite matrix
$$A = \begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix}$$
is nonsingular. -/
theorem equation_4_4_18 {p : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ}
    (hC : C.PosDef) (hB : Function.Injective B.mulVec) : IsUnit (fromBlocks C B Bᵀ 0) := by
  rw [fromBlocks_transpose_zero_eq_saddleMatrix]
  exact isUnit_saddleMatrix_zero hC hB

/-- **Equation (4.4.20)** of [golub2013matrix]. Let $C \in \mathbb{R}^{n \times n}$ be symmetric
positive definite and let $B \in \mathbb{R}^{n \times p}$ have full column rank. If
$x, f \in \mathbb{R}^n$ and $y \in \mathbb{R}^p$ satisfy the equilibrium system (4.4.19) with
$g = 0$,
$$\begin{bmatrix} C & B \\ B^T & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} =
  \begin{bmatrix} f \\ 0 \end{bmatrix},$$
then
$$y = (B^T C^{-1} B)^{-1} B^T C^{-1} f.$$

**Generalization.** The source assumes that $C$ is diagonal. The theorem needs only that $C$ is
symmetric positive definite. -/
theorem equation_4_4_20 {p : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ}
    (hC : C.PosDef) (hB : Function.Injective B.mulVec) {x f : Fin n → ℝ} {y : Fin p → ℝ}
    (h : fromBlocks C B Bᵀ 0 *ᵥ Sum.elim x y = Sum.elim f 0) :
    y = (Bᵀ * C⁻¹ * B)⁻¹ *ᵥ ((Bᵀ * C⁻¹) *ᵥ f) := by
  rw [fromBlocks_transpose_zero_eq_saddleMatrix] at h
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    saddleMatrix_zero_mulVec_snd_eq hC hB h

open scoped Matrix.Norms.L2Operator in
/-- **Equation (4.4.21)** of [golub2013matrix] (the bound of Stewart and Todd). Let
$B \in \mathbb{R}^{n \times p}$ have full column rank. Then there is a number $\psi_B$ such that
$$\|(B^T C^{-1} B)^{-1} B^T C^{-1}\|_2 \le \psi_B$$
for every positive diagonal matrix $C = \operatorname{diag}(c)$.

The source says that the upper bound $\psi_B$ is independent of $C$. The norm is the scoped
operator norm of `Matrix.Norms.L2Operator`. The proof specializes the bound of the backbone on
the weighted least-squares operators at the weights $C^{-1}$. -/
theorem equation_4_4_21 {p : ℕ} {B : Matrix (Fin n) (Fin p) ℝ}
    (hB : Function.Injective B.mulVec) :
    ∃ ψ : ℝ, ∀ c : Fin n → ℝ, (∀ i, 0 < c i) →
      ‖(Bᵀ * (diagonal c)⁻¹ * B)⁻¹ * Bᵀ * (diagonal c)⁻¹‖ ≤ ψ := by
  obtain ⟨ψ, hψ⟩ := exists_forall_l2_opNorm_weightedLeastSquaresOp_le (mulVec_injective_iff.1 hB)
  refine ⟨ψ, fun c hc => ?_⟩
  have hinv : (diagonal c)⁻¹ = diagonal fun i => (c i)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hc i).ne')
  simpa only [hinv, weightedLeastSquaresOp_def, conjTranspose_eq_transpose_of_trivial] using
    hψ (fun i => (c i)⁻¹) fun i => inv_pos.2 (hc i)

end GolubVanLoan.Chapter04
