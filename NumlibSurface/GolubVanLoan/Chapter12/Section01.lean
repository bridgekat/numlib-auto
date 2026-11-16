/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.SineCosineTransform
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.Displacement
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter03.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section01

/-!
# Golub and Van Loan, Section 12.1: Linear systems with displacement structure

This module formalizes §12.1 of [golub2013matrix]. For square matrices $F$ and $G$, the
$\{F, G\}$-displacement of $A \in \mathbb{R}^{n \times n}$ is $FA - AG$, and the
$\{F, G\}$-displacement rank $\operatorname{rank}_{F,G}(A)$ is the rank of this matrix. A matrix of
displacement rank $r$ has generators $R, S \in \mathbb{R}^{n \times r}$ with $FA - AG = RS^T$, and
the generators determine $A$ when the Sylvester operator $X \mapsto FX - XG$ is injective. For
$F = \Omega = \operatorname{diag}(\omega)$ and $G = \Lambda = \operatorname{diag}(\nu)$ these are
the Cauchy-like matrices. The module proves the generator update of Theorem 12.1.1 for one step of
Gaussian elimination, and the correctness of the fast LU factorizations Algorithm 12.1.1 (`LUdisp`)
and Algorithm 12.1.2 (`LUdispPiv`, with partial pivoting), which work on the generators only. It
then treats Toeplitz-like, Hankel-like and Toeplitz-plus-Hankel-like matrices (12.1.7)–(12.1.11),
their conversion to Cauchy-like form by diagonalization of $F$ and $G$ (§12.1.8), and the orthogonal
eigensystems (12.1.12)–(12.1.13) of the corner matrices $Y_{0,0}$ and $Y_{1,1}$, which the sine and
cosine transforms give.

The proofs specialize `Numlib.LinearAlgebra.Matrix.Displacement`, which is built on the Sylvester
operator `Matrix.sylvesterMap` of `Numlib.LinearAlgebra.Matrix.Sylvester`, and
`Numlib.Analysis.Fourier.SineCosineTransform`. The existence of the LU factorization comes from
Theorem 3.2.1 (`GolubVanLoan.Chapter03.theorem_3_2_1`), and the spectra of Sylvester operators from
Lemma 7.1.5 (`GolubVanLoan.Chapter07.lemma_7_1_5`).

## Main definitions

* §12.1.2, `GolubVanLoan.Chapter12.IsCauchyLike`: $A$ is Cauchy-like if
  $\Omega A - A \Lambda = RS^T$ with generators of full column rank.
* Algorithm 12.1.1, `GolubVanLoan.Chapter12.algorithm_12_1_1`: `LUdisp`, the LU factorization of a
  Cauchy-like matrix computed from its generators.
* Algorithm 12.1.2, `GolubVanLoan.Chapter12.algorithm_12_1_2`: `LUdispPiv`, the same factorization
  with partial pivoting.
* §12.1.7, `GolubVanLoan.Chapter12.IsToeplitzLike`, `GolubVanLoan.Chapter12.IsHankelLike` and
  `GolubVanLoan.Chapter12.IsToeplitzPlusHankelLike`: $Z_1 A - A Z_{-1}$, $Z_1^T A - A Z_{-1}$ or
  $Y_{0,0} A - A Y_{1,1}$ has rank at most $r$.
* Equation (12.1.12), `GolubVanLoan.Chapter12.dstMatrix`: the orthogonal DST-I matrix
  $\mathcal{S}_n$.
* Equation (12.1.13), `GolubVanLoan.Chapter12.dctMatrix`: the orthogonal DCT-II matrix
  $\mathcal{C}_n$.

## Main results

* Equation (12.1.3), `GolubVanLoan.Chapter12.equation_12_1_3`: if
  $\operatorname{rank}_{F,G}(A) = r$, then $FA - AG = RS^T$ for some
  $R, S \in \mathbb{R}^{n \times r}$.
* §12.1.2, `GolubVanLoan.Chapter12.cauchy_displacement`: the Cauchy matrix
  $a_{kj} = 1/(\omega_k - \nu_j)$ satisfies $\Omega A - A \Lambda = ee^T$ and is Cauchy-like of
  displacement rank $1$.
* Equation (12.1.4), `GolubVanLoan.Chapter12.equation_12_1_4`: $\Omega A - A \Lambda = RS^T$ if and
  only if $a_{kj} = r_k^T s_j / (\omega_k - \nu_j)$ for all $k, j$.
* Theorem 12.1.1, `GolubVanLoan.Chapter12.theorem_12_1_1`: the Schur complement $A_1$ of
  $\alpha = a_{11} \neq 0$ satisfies $\Omega_1 A_1 - A_1 \Lambda_1 = \tilde R_1 \tilde S_1^T$ with
  explicitly updated generators.
* Theorem 12.1.1, `GolubVanLoan.Chapter12.theorem_12_1_1_b`: the displacement rank of the Schur
  complement is at most that of $A$.
* Algorithm 12.1.1, `GolubVanLoan.Chapter12.algorithm_12_1_1_spec`: in exact arithmetic, `LUdisp`
  returns an LU factorization of $A$ when the leading principal submatrices of orders
  $1, \dots, n - 1$ are nonsingular.
* §12.1.6, `GolubVanLoan.Chapter12.displacement_permute`: row and column permutations of a
  Cauchy-like matrix act on $\Omega$, $\Lambda$, $R$ and $S$.
* Algorithm 12.1.2, `GolubVanLoan.Chapter12.algorithm_12_1_2_spec`: in exact arithmetic, for
  nonsingular $A$, `LUdispPiv` returns $PA = LU$ with $|l_{ij}| \le 1$.
* Equation (12.1.8), `GolubVanLoan.Chapter12.equation_12_1_8`: a Toeplitz matrix is Toeplitz-like of
  displacement rank at most $2$.
* Equation (12.1.9), `GolubVanLoan.Chapter12.equation_12_1_9`: a Toeplitz matrix is
  Toeplitz-plus-Hankel-like of displacement rank at most $4$.
* §12.1.7, `GolubVanLoan.Chapter12.disjoint_spectra_displacement_operators`: the three Sylvester
  operators of §12.1.7 are injective, and the spectra of their two matrices are disjoint.
* Equation (12.1.10), `GolubVanLoan.Chapter12.equation_12_1_10`: a Hankel matrix $H$ is Hankel-like
  of displacement rank at most $2$, and $\mathcal{E}_n H$ is Toeplitz.
* Equation (12.1.11), `GolubVanLoan.Chapter12.equation_12_1_11`: a Hankel matrix and the sum of a
  Toeplitz and a Hankel matrix are Toeplitz-plus-Hankel-like of displacement rank at most $4$.
* §12.1.8, `GolubVanLoan.Chapter12.cauchyLike_of_diagonalizable`: diagonalization of $F$ and $G$
  turns $A$ into a Cauchy-like matrix, and a solution of the transformed system gives a solution of
  $Ax = b$.
* Equation (12.1.12), `GolubVanLoan.Chapter12.equation_12_1_12`: $\mathcal{S}_n$ is symmetric and
  orthogonal and diagonalizes $Y_{0,0}$.
* Equation (12.1.13), `GolubVanLoan.Chapter12.equation_12_1_13`: $\mathcal{C}_n$ is orthogonal and
  diagonalizes $Y_{1,1}$.

## Notation

* `ν`: the vector of the diagonal entries of $\Lambda$, which the source calls $\lambda$. The Lean
  name differs because lambda is a keyword of Lean.

## Conventions

* Indices are 0-based: the source's $\omega_1$ is `ω 0`. The block partitions $A = \begin{bmatrix}
  \alpha & g^T \\ f & B \end{bmatrix}$, $R = \begin{bmatrix} r_1^T \\ R_1 \end{bmatrix}$ and
  $S = \begin{bmatrix} s_1^T \\ S_1 \end{bmatrix}$ are read through `Fin.succ`. The pivot is
  `A 0 0`, $f$ is `fun i => A i.succ 0`, $g$ is `fun j => A 0 j.succ`, $B$ is
  `A.submatrix Fin.succ Fin.succ`, and $r_1$ is `R 0`.
* $\Omega = \operatorname{diag}(\omega)$ is `Matrix.diagonal ω` and
  $\Lambda = \operatorname{diag}(\nu)$ is `Matrix.diagonal ν`. For the vector of ones $e$, the
  matrix $ee^T$ is `Matrix.vecMulVec 1 1`.
* $Z_\varphi$, with ones on the subdiagonal and $\varphi$ in the top right corner, is
  `Matrix.cyclicShift n φ`. $Y_{\gamma,\delta}$, with ones on the two off-diagonals, $\gamma$ in the
  top left corner and $\delta$ in the bottom right corner, is `Matrix.cornerTridiagonal n γ δ`. The
  exchange matrix $\mathcal{E}_n$ is `Matrix.exchange n`.

## Implementation notes

* The displacement $FA - AG$ is `Matrix.sylvesterMap F G A`, and $\operatorname{rank}_{F,G}(A)$ is
  `Matrix.displacementRank F G A`. The source puts the nonsingularity of the Sylvester operator into
  the definition (12.1.2). Here it is a hypothesis only where a result uses it.
* The algorithms are monadic programs with a rounding hook `rnd`, as in the algorithm conventions of
  `NumlibSurface.GolubVanLoan`. They recurse on the size $N + 1$. Their vectors are computed entry
  by entry by `GolubVanLoan.Chapter12.vecLoop`, and their dot products by `FloatingPoint.dotAccum`.
  The source analyses no rounding errors in this section, so there are only exact specifications,
  about `Id.run (algorithm_12_1_1 pure …)` and `Id.run (algorithm_12_1_2 pure …)`.
* A permutation is returned as an `Equiv.Perm`. Its matrix is `Equiv.Perm.permMatrix`.

## Deviations from the source

* **Equation (12.1.3)** (generalization). The source defines the displacement rank only for a
  nonsingular Sylvester operator. The generators exist without this assumption. See
  `GolubVanLoan.Chapter12.equation_12_1_3`.
* **Definition of a Cauchy-like matrix, §12.1.2** (reading). The condition $\omega_k \neq \nu_j$
  from the context is part of the definition, and the informal requirement $r \ll n$ is not. See
  `GolubVanLoan.Chapter12.IsCauchyLike`.
* **Algorithm 12.1.1** (reading). The hypothesis "$A$ has an LU factorization" is read as the
  nonsingularity of the leading principal submatrices of orders $1, \dots, n - 1$. See
  `GolubVanLoan.Chapter12.algorithm_12_1_1_spec`.
* **Definitions of §12.1.7** (reading). The informal requirement $r \ll n$ is not part of the
  definitions. See `GolubVanLoan.Chapter12.IsToeplitzLike`.
* **§12.1.7, after (12.1.9)** (typo). The source prints
  $\lambda(Z_{-1}) \cup \lambda(Z_1) = \emptyset$ for
  $\lambda(Z_{-1}) \cap \lambda(Z_1) = \emptyset$. See
  `GolubVanLoan.Chapter12.disjoint_spectra_displacement_operators`.
* **§12.1.8** (typo). The first display prints $X_G^{-1} G X_F$ for $X_G^{-1} G X_G$. See
  `GolubVanLoan.Chapter12.cauchyLike_of_diagonalizable`.

## Not formalized

* **The non-recursive sketch of Algorithm 12.1.1.**
* **The $n = 4$ example of the Cauchy generator update in §12.1.3.** Numerical examples are out of
  scope for the library.
* **The "Steps 1–4" framework of §12.1.8**, beyond its correctness statement.
* **The flop counts.** Operation counts are out of scope for the library.
* **The Problems of §12.1.** Problems are out of scope for the library. Part (a) of Problem P12.1.1
  is proved as a supporting lemma.
-/

open Matrix

namespace GolubVanLoan.Chapter12

variable {n : ℕ}

/-! ### Displacement rank and Cauchy-like matrices (§12.1.1–12.1.2) -/

/-- **Equation (12.1.3)** of [golub2013matrix]. Let $F, G, A \in \mathbb{R}^{n \times n}$. If the
$\{F, G\}$-displacement rank of $A$ is $r$, then there are generators
$R, S \in \mathbb{R}^{n \times r}$ with $$FA - AG = RS^T.$$

**Generalization.** The source defines the displacement rank (12.1.2) only when the Sylvester
operator $X \mapsto FX - XG$ is nonsingular. The statement holds without this assumption.

The displacement rank is `Matrix.displacementRank F G A`, the rank of
`Matrix.sylvesterMap F G A`. -/
theorem equation_12_1_3 {F G A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (h : displacementRank F G A = r) :
    ∃ R S : Matrix (Fin n) (Fin r) ℝ, F * A - A * G = R * Sᵀ := by
  obtain ⟨R, S, hRS⟩ := displacementRank_le_iff_exists.mp h.le
  exact ⟨R, S, hRS⟩

/-- **§12.1.2** of [golub2013matrix], definition of a Cauchy-like matrix. Let
$\omega, \nu \in \mathbb{R}^n$, $\Omega = \operatorname{diag}(\omega)$ and
$\Lambda = \operatorname{diag}(\nu)$. A matrix $A \in \mathbb{R}^{n \times n}$ is
**Cauchy-like** with respect to $\omega$ and $\nu$ if $\omega_k \neq \nu_j$ for all $k, j$, and
there are $r \in \mathbb{N}$ and $R, S \in \mathbb{R}^{n \times r}$, both of rank $r$, that
satisfy the displacement equation (12.1.4), $$\Omega A - A \Lambda = RS^T.$$

**Reading.** The condition $\omega_k \neq \nu_j$ comes from the context of the definition in the
source, and it is part of the definition here. The source's requirement $r \ll n$ is informal,
and it is not part of the definition. -/
def IsCauchyLike (ω ν : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ k j, ω k ≠ ν j) ∧ ∃ (r : ℕ) (R S : Matrix (Fin n) (Fin r) ℝ), R.rank = r ∧ S.rank = r ∧
    diagonal ω * A - A * diagonal ν = R * Sᵀ

/-- For $n \ge 1$, the all-ones column $e \in \mathbb{R}^{n \times 1}$ has rank $1$. -/
private theorem rank_onesCol (hn : n ≠ 0) :
    (of fun (_ : Fin n) (_ : Fin 1) => (1 : ℝ)).rank = 1 := by
  set e : Matrix (Fin n) (Fin 1) ℝ := of fun _ _ => 1
  have hG : eᵀ * e = (n : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext a b
    rw [Subsingleton.elim a b]
    simp [e, Matrix.mul_apply]
  have hu : IsUnit (eᵀ * e) := by
    rw [hG, isUnit_iff_isUnit_det]
    simp [hn]
  refine le_antisymm ((rank_le_card_width e).trans (by simp)) ?_
  calc 1 = (eᵀ * e).rank := by rw [rank_of_isUnit _ hu, Fintype.card_fin]
    _ ≤ e.rank := rank_mul_le_right _ _

/-- **§12.1.2** of [golub2013matrix], the Cauchy matrix. Let $\omega, \nu \in \mathbb{R}^n$ with
$\omega_k \neq \nu_j$ for all $k, j$, and let $A$ be the Cauchy matrix with entries
$a_{kj} = 1/(\omega_k - \nu_j)$. Then $$\Omega A - A \Lambda = ee^T,$$ where
$\Omega = \operatorname{diag}(\omega)$, $\Lambda = \operatorname{diag}(\nu)$ and
$e \in \mathbb{R}^n$ is the vector of ones. If $n \ge 1$, then $A$ has
$\{\Omega, \Lambda\}$-displacement rank $1$, and $A$ is Cauchy-like with respect to $\omega$ and
$\nu$, with the generators $R = S = e$.

The Cauchy matrix is `Matrix.cauchy ω (-ν)`, and $ee^T$ is `Matrix.vecMulVec 1 1`. -/
theorem cauchy_displacement {ω ν : Fin n → ℝ} (h : ∀ k j, ω k ≠ ν j) :
    diagonal ω * cauchy ω (-ν) - cauchy ω (-ν) * diagonal ν = vecMulVec 1 1 ∧
      (n ≠ 0 → displacementRank (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = 1) ∧
      (n ≠ 0 → IsCauchyLike ω ν (cauchy ω (-ν))) := by
  refine ⟨sylvesterMap_diagonal_cauchy h, displacementRank_diagonal_cauchy h, fun hn =>
    ⟨h, 1, of fun _ _ => 1, of fun _ _ => 1, rank_onesCol hn, rank_onesCol hn, ?_⟩⟩
  have h1 : diagonal ω * cauchy ω (-ν) - cauchy ω (-ν) * diagonal ν = vecMulVec 1 1 :=
    sylvesterMap_diagonal_cauchy h
  rw [h1]
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply]

/-- **Equation (12.1.4)** of [golub2013matrix] and the display after it. Let
$\omega, \nu \in \mathbb{R}^n$ with $\omega_k \neq \nu_j$ for all $k, j$, let
$A \in \mathbb{R}^{n \times n}$, and let $R, S \in \mathbb{R}^{n \times r}$ have the rows
$r_k^T$ and $s_j^T$. Then $\Omega A - A \Lambda = RS^T$ if and only if $$a_{kj} = \frac{r_k^T
s_j}{\omega_k - \nu_j} \quad \text{for all } k, j.$$ So a Cauchy-like matrix is determined by
$\omega$, $\nu$, $R$ and $S$. -/
theorem equation_12_1_4 {ω ν : Fin n → ℝ} (h : ∀ k j, ω k ≠ ν j) {r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {R S : Matrix (Fin n) (Fin r) ℝ} :
    diagonal ω * A - A * diagonal ν = R * Sᵀ ↔ ∀ k j, A k j = (R k ⬝ᵥ S j) / (ω k - ν j) :=
  apply_eq_of_sylvesterMap_diagonal_eq h

/-! ### The generator update (Theorem 12.1.1) -/

section Update

variable {N r : ℕ}

/-- **Theorem 12.1.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ with $n = N + 1$,
let $\omega, \nu \in \mathbb{R}^n$ with $\omega_k \neq \nu_j$ for all $k, j$, and let
$R, S \in \mathbb{R}^{n \times r}$ satisfy (12.1.5), $\Omega A - A \Lambda = RS^T$, where
$\Omega = \operatorname{diag}(\omega)$ and $\Lambda = \operatorname{diag}(\nu)$. Partition $$A =
\begin{bmatrix} \alpha & g^T \\ f & B \end{bmatrix}, \qquad R = \begin{bmatrix} r_1^T \\ R_1
\end{bmatrix}, \qquad S = \begin{bmatrix} s_1^T \\ S_1 \end{bmatrix},$$ and assume
$\alpha \neq 0$. Let $A_1 = B - fg^T/\alpha$, $\tilde R_1 = R_1 - f r_1^T/\alpha$,
$\tilde S_1 = S_1 - g s_1^T/\alpha$, $\Omega_1 = \operatorname{diag}(\omega_2, \dots, \omega_n)$
and $\Lambda_1 = \operatorname{diag}(\nu_2, \dots, \nu_n)$. Then (12.1.6) holds: $$\Omega_1
A_1 - A_1 \Lambda_1 = \tilde R_1 \tilde S_1^T.$$

The hypothesis $\omega_k \neq \nu_j$ is kept as the source prints it; the identity does not use
it. The parts of the partition are read through `Fin.succ`: $f$ is `fun i => A i.succ 0`, $g$ is
`fun j => A 0 j.succ`, $B$ is `A.submatrix Fin.succ Fin.succ`, $r_1$ and $R_1$ are `R 0` and
`R.submatrix Fin.succ id`, and the pivot `A 0 0` is $\alpha$. -/
theorem theorem_12_1_1 {ω ν : Fin (N + 1) → ℝ} (_hων : ∀ k j, ω k ≠ ν j)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ}
    (h : diagonal ω * A - A * diagonal ν = R * Sᵀ) (hα : A 0 0 ≠ 0) :
    diagonal (ω ∘ Fin.succ) * (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) -
      (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) * diagonal (ν ∘ Fin.succ) =
      (R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0)) *
        (S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0))ᵀ :=
  sylvesterMap_diagonal_schurComplement h hα

/-- **Theorem 12.1.1** of [golub2013matrix], the display after the theorem. Let
$A \in \mathbb{R}^{n \times n}$ with $n = N + 1$ and $\omega, \nu \in \mathbb{R}^n$, partition
$A$ as in `GolubVanLoan.Chapter12.theorem_12_1_1`, and assume $\alpha \neq 0$. If
$\operatorname{rank}_{\Omega, \Lambda}(A) \le r$, then the Schur complement
$A_1 = B - fg^T/\alpha$ satisfies $\operatorname{rank}_{\Omega_1, \Lambda_1}(A_1) \le r$.

No hypothesis on the diagonal entries $\omega_k$ and $\nu_j$ is needed. -/
theorem theorem_12_1_1_b {ω ν : Fin (N + 1) → ℝ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (h : displacementRank (diagonal ω) (diagonal ν) A ≤ r) (hα : A 0 0 ≠ 0) :
    displacementRank (diagonal (ω ∘ Fin.succ)) (diagonal (ν ∘ Fin.succ))
      (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) ≤ r :=
  displacementRank_diagonal_schurComplement_le h hα

end Update

/-! ### Fast LU for Cauchy-like matrices (Algorithm 12.1.1) -/

section LUdisp

/-- A vector computed entry by entry in the order of the index list $l$: the loop
`for i in l, y(i) = f(i), end`, written as a `List.foldlM`. An entry whose index is not in $l$
is $0$. -/
def vecLoopOn {M : Type → Type} [Monad M] {β : Type} [Zero β] {k : ℕ} (l : List (Fin k))
    (f : Fin k → M β) : M (Fin k → β) :=
  l.foldlM (fun (y : Fin k → β) i => do
    let b ← f i
    pure (Function.update y i b)) 0

/-- A vector computed entry by entry in increasing index order: the loop
`for i = 1:k, y(i) = f(i), end`, which is `GolubVanLoan.Chapter12.vecLoopOn` over
`List.finRange k`. -/
def vecLoop {M : Type → Type} [Monad M] {β : Type} [Zero β] {k : ℕ} (f : Fin k → M β) :
    M (Fin k → β) :=
  vecLoopOn (List.finRange k) f

/-- In exact arithmetic, a loop over a list $l$ without duplicates that contains every index
computes every entry: the result is the vector $i \mapsto f(i)$. -/
theorem idRun_vecLoopOn {β : Type} [Zero β] {k : ℕ} {l : List (Fin k)} (f : Fin k → Id β)
    (hl : l.Nodup) (hall : ∀ i, i ∈ l) : Id.run (vecLoopOn l f) = fun i => Id.run (f i) := by
  funext i
  have := List.idRun_foldlM_update_apply (fun a (_ : β) => f a) l hl 0 i
  simpa [vecLoopOn, hall i] using this

/-- In exact arithmetic, `GolubVanLoan.Chapter12.vecLoop f` computes the vector $i \mapsto f(i)$. -/
theorem idRun_vecLoop {β : Type} [Zero β] {k : ℕ} (f : Fin k → Id β) :
    Id.run (vecLoop f) = fun i => Id.run (f i) :=
  idRun_vecLoopOn f (List.nodup_finRange k) (List.mem_finRange)

/-- **Algorithm 12.1.1** of [golub2013matrix] (`LUdisp`). Let $n = N + 1$, let
$\omega, \nu \in \mathbb{R}^n$, and let $R, S \in \mathbb{R}^{n \times r}$ be generators of a
Cauchy-like matrix $A$, that is, $\Omega A - A \Lambda = RS^T$. The algorithm computes the
factors $L$ and $U$ of $A = LU$, recursively on $n$. For $n = 1$ it returns $L = 1$ and
$U = r_1^T s_1 / (\omega_1 - \nu_1)$. For $n > 1$ it computes the first column
$a = (R s_1) ./ (\omega - \nu_1)$ of $A$ by entrywise division, and sets $\alpha = a_1$ and
$f = a(2{:}n)$. It computes the rest of the first row,
$g = (S_1 r_1) ./ (\omega_1 - \nu(2{:}n))$, and the updated generators
$\tilde R_1 = R_1 - f r_1^T/\alpha$ and $\tilde S_1 = S_1 - g s_1^T/\alpha$. Then it computes
$[L_1, U_1] = \mathrm{LUdisp}(\omega(2{:}n), \nu(2{:}n), \tilde R_1, \tilde S_1)$ and returns
$$L = \begin{bmatrix} 1 & 0 \\ f/\alpha & L_1 \end{bmatrix}, \qquad U = \begin{bmatrix} \alpha &
g^T \\ 0 & U_1 \end{bmatrix}.$$

Every arithmetic result passes through the rounding hook `rnd`. The dot products are
`FloatingPoint.dotAccum`, and the vectors are computed by `GolubVanLoan.Chapter12.vecLoop`. -/
noncomputable def algorithm_12_1_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {r : ℕ} :
    (N : ℕ) → (ω ν : Fin (N + 1) → ℝ) → (R S : Matrix (Fin (N + 1)) (Fin r) ℝ) →
      M (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ × Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
  | 0, ω, ν, R, S => do
      let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R 0) (S 0) 0
      let u ← rnd (t / (← rnd (ω 0 - ν 0)))
      pure (1, of fun _ _ => u)
  | N + 1, ω, ν, R, S => do
      let a ← vecLoop fun i : Fin (N + 2) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R i) (S 0) 0
        rnd (t / (← rnd (ω i - ν 0)))
      let g ← vecLoop fun j : Fin (N + 1) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (S j.succ) (R 0) 0
        rnd (t / (← rnd (ω 0 - ν j.succ)))
      let R₁ ← vecLoop fun i : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (R i.succ c - (← rnd ((← rnd (a i.succ * R 0 c)) / a 0)))
      let S₁ ← vecLoop fun j : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (S j.succ c - (← rnd ((← rnd (g j * S 0 c)) / a 0)))
      let LU₁ ← algorithm_12_1_1 rnd N (fun i => ω i.succ) (fun j => ν j.succ) (of R₁) (of S₁)
      let l ← vecLoop fun i : Fin (N + 1) => rnd (a i.succ / a 0)
      pure (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (l i') (fun j' => LU₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a 0) g j)
          (fun i' => Fin.cases 0 (fun j' => LU₁.2 i' j') j) i)

variable {r : ℕ}

/-- In exact arithmetic, Algorithm 12.1.1 on a matrix of order $1$ returns $L = 1$ and
$U = r_1^T s_1 / (\omega_1 - \nu_1)$. -/
theorem algorithm_12_1_1_zero (ω ν : Fin 1 → ℝ) (R S : Matrix (Fin 1) (Fin r) ℝ) :
    Id.run (algorithm_12_1_1 pure 0 ω ν R S) = (1, of fun _ _ => (R 0 ⬝ᵥ S 0) / (ω 0 - ν 0)) := by
  simp [algorithm_12_1_1, FloatingPoint.dotAccum_id_finRange]

/-- In exact arithmetic, Algorithm 12.1.1 on a matrix of order $N + 2$ computes $a$, $g$ and the
updated generators $\tilde R_1$, $\tilde S_1$ by their formulas, calls itself on order $N + 1$
for $[L_1, U_1]$, and returns $L = \begin{bmatrix} 1 & 0 \\ f/\alpha & L_1 \end{bmatrix}$ and
$U = \begin{bmatrix} \alpha & g^T \\ 0 & U_1 \end{bmatrix}$. -/
theorem algorithm_12_1_1_succ {N : ℕ} (ω ν : Fin (N + 2) → ℝ)
    (R S : Matrix (Fin (N + 2)) (Fin r) ℝ) :
    Id.run (algorithm_12_1_1 pure (N + 1) ω ν R S) =
      let a : Fin (N + 2) → ℝ := fun i => (R i ⬝ᵥ S 0) / (ω i - ν 0)
      let g : Fin (N + 1) → ℝ := fun j => (S j.succ ⬝ᵥ R 0) / (ω 0 - ν j.succ)
      let LU₁ := Id.run (algorithm_12_1_1 pure N (fun i => ω i.succ) (fun j => ν j.succ)
        (of fun i c => R i.succ c - a i.succ * R 0 c / a 0)
        (of fun j c => S j.succ c - g j * S 0 c / a 0))
      (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (a i'.succ / a 0) (fun j' => LU₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a 0) g j)
          (fun i' => Fin.cases 0 (fun j' => LU₁.2 i' j') j) i) := by
  simp only [algorithm_12_1_1, Id.run_bind, Id.run_pure, idRun_vecLoop,
    FloatingPoint.dotAccum_id_finRange, zero_add]

/-- If $A = LU$ with $L$ unit lower triangular and $U$ upper triangular, then the first row of $A$
is the first row of $U$, $a_{i1} = l_{i1} u_{11}$ for $i \ge 2$, and $a_{ij} = l_{i1} u_{1j} +
\sum_{k \ge 2} l_{ik} u_{kj}$ for $i, j \ge 2$. -/
private theorem isLU_apply_zero_succ {N : ℕ} {A L U : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (h : IsLU A L U) :
    (∀ j, A 0 j = U 0 j) ∧ (∀ i : Fin (N + 1), A i.succ 0 = L i.succ 0 * U 0 0) ∧
      ∀ i j : Fin (N + 1), A i.succ j.succ =
        L i.succ 0 * U 0 j.succ + ∑ k : Fin (N + 1), L i.succ k.succ * U k.succ j.succ := by
  have hL : ∀ k : Fin (N + 1), L 0 k.succ = 0 :=
    fun k => h.isUnitLowerTriangular.isLowerTriangular (Fin.succ_pos k)
  have hU : ∀ k : Fin (N + 1), U k.succ 0 = 0 := fun k => h.isUpperTriangular (Fin.succ_pos k)
  refine ⟨fun j => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [← h.mul_eq, Matrix.mul_apply, Fin.sum_univ_succ, h.isUnitLowerTriangular.diag_eq_one]
    simp [hL]
  · rw [← h.mul_eq, Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hU]
  · rw [← h.mul_eq, Matrix.mul_apply, Fin.sum_univ_succ]

/-- If $L_1$ is unit lower triangular, then so is the bordered matrix
$\begin{bmatrix} 1 & 0 \\ l & L_1 \end{bmatrix}$. -/
private theorem isUnitLowerTriangular_bordered {N : ℕ} (l : Fin (N + 1) → ℝ)
    {L₁ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (h : L₁.IsUnitLowerTriangular) :
    (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases (l i') (fun j' => L₁ i' j') j) i :
        Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ).IsUnitLowerTriangular := by
  refine ⟨fun i j hij' => ?_, fun i => ?_⟩
  · revert hij'
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      intro hij' <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
    · exact absurd hij' (lt_irrefl _)
    · exact absurd hij' (Fin.succ_pos _).not_gt
    · exact h.isLowerTriangular (Fin.succ_lt_succ_iff.1 hij')
  · refine Fin.cases ?_ (fun i => ?_) i <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
    exact h.diag_eq_one i

/-- If $U_1$ is upper triangular, then so is the bordered matrix $\begin{bmatrix} \alpha & g^T \\ 0
& U_1 \end{bmatrix}$. -/
private theorem isUpperTriangular_bordered {N : ℕ} (α : ℝ) (g : Fin (N + 1) → ℝ)
    {U₁ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (h : U₁.IsUpperTriangular) :
    (of fun i j => Fin.cases (Fin.cases α g j)
      (fun i' => Fin.cases 0 (fun j' => U₁ i' j') j) i :
        Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ).IsUpperTriangular := by
  intro i j hij'
  revert hij'
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    intro hij' <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
  · exact absurd hij' (lt_irrefl _)
  · exact absurd hij' (Fin.succ_pos _).not_gt
  · exact h (Fin.succ_lt_succ_iff.1 hij')

/-- If $A = LU$ is an LU factorization with $u_{11} \neq 0$, then the Schur complement of $a_{11}$
in $A$ has the LU factorization $L(2{:}n, 2{:}n)\, U(2{:}n, 2{:}n)$. -/
private theorem isLU_schur {N : ℕ} {A L U : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (h : IsLU A L U) (hα : U 0 0 ≠ 0) :
    IsLU (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ)
      (L.submatrix Fin.succ Fin.succ) (U.submatrix Fin.succ Fin.succ) := by
  obtain ⟨h0j, hi0, hij⟩ := isLU_apply_zero_succ h
  refine ⟨⟨fun i j hij' => h.isUnitLowerTriangular.isLowerTriangular (Fin.succ_lt_succ_iff.2 hij'),
    fun i => h.isUnitLowerTriangular.diag_eq_one _⟩,
    fun i j hij' => h.isUpperTriangular (Fin.succ_lt_succ_iff.2 hij'), ?_⟩
  ext i j
  rw [Matrix.mul_apply, Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, vecMulVec_apply, hij,
    hi0, h0j, h0j]
  simp only [submatrix_apply, smul_eq_mul]
  field_simp
  ring

/-- In exact arithmetic, if $\Omega A - A \Lambda = RS^T$ with $\omega_k \neq \nu_j$ for all $k, j$,
and $A$ has an LU factorization with nonzero pivots $u_{11}, \dots, u_{n-1,n-1}$, then Algorithm
12.1.1 returns an LU factorization of $A$. -/
private theorem algorithm_12_1_1_spec_aux : ∀ (N : ℕ) {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ},
    (∀ k j, ω k ≠ ν j) → diagonal ω * A - A * diagonal ν = R * Sᵀ →
    (∃ L U, IsLU A L U ∧ ∀ i : Fin N, U i.castSucc i.castSucc ≠ 0) →
    IsLU A (Id.run (algorithm_12_1_1 pure N ω ν R S)).1
      (Id.run (algorithm_12_1_1 pure N ω ν R S)).2
  | 0, ω, ν, A, R, S, hων, h, _ => by
      have hA := (equation_12_1_4 hων).1 h 0 0
      rw [algorithm_12_1_1_zero]
      have h0 : ∀ i : Fin (0 + 1), i = 0 := fun i => Fin.ext (Nat.lt_one_iff.1 i.isLt)
      refine ⟨isUnitLowerTriangular_one, fun i j hij => absurd hij (by simp [h0 i, h0 j]),
        ?_⟩
      ext i j
      rw [h0 i, h0 j]
      simp [hA]
  | N + 1, ω, ν, A, R, S, hων, h, ⟨L, U, hLU, hpiv⟩ => by
      obtain ⟨h0j, hi0, hij⟩ := isLU_apply_zero_succ hLU
      have hU0 : U 0 0 ≠ 0 := hpiv 0
      have hα : A 0 0 ≠ 0 := by rw [h0j]; exact hU0
      have ha : ∀ i, (R i ⬝ᵥ S 0) / (ω i - ν 0) = A i 0 := fun i =>
        ((equation_12_1_4 hων).1 h i 0).symm
      have hg : ∀ j : Fin (N + 1), (S j.succ ⬝ᵥ R 0) / (ω 0 - ν j.succ) = A 0 j.succ := fun j => by
        rw [dotProduct_comm]; exact ((equation_12_1_4 hων).1 h 0 j.succ).symm
      set A₁ := A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ with hA₁
      have hS₁ := theorem_12_1_1 hων h hα
      have hR₁ : (of fun i c => R i.succ c - A i.succ 0 * R 0 c / A 0 0 :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0) := by
        ext i c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul]
        ring
      have hS₁' : (of fun j c => S j.succ c - A 0 j.succ * S 0 c / A 0 0 :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0) := by
        ext j c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul]
        ring
      have hrec := algorithm_12_1_1_spec_aux N (ω := fun i => ω i.succ) (ν := fun j => ν j.succ)
        (A := A₁) (R := of fun i c => R i.succ c - A i.succ 0 * R 0 c / A 0 0)
        (S := of fun j c => S j.succ c - A 0 j.succ * S 0 c / A 0 0)
        (fun k j => hων _ _) (by rw [hR₁, hS₁']; exact hS₁)
        ⟨_, _, isLU_schur hLU hU0, fun i => hpiv i.succ⟩
      rw [algorithm_12_1_1_succ]
      simp only [ha, hg]
      set LU₁ := Id.run (algorithm_12_1_1 pure N (fun i => ω i.succ) (fun j => ν j.succ)
        (of fun i c => R i.succ c - A i.succ 0 * R 0 c / A 0 0)
        (of fun j c => S j.succ c - A 0 j.succ * S 0 c / A 0 0))
      refine ⟨isUnitLowerTriangular_bordered _ hrec.isUnitLowerTriangular,
        isUpperTriangular_bordered _ _ hrec.isUpperTriangular, ?_⟩
      · ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [Matrix.mul_apply, Fin.sum_univ_succ, of_apply, Fin.cases_zero, Fin.cases_succ,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero, mul_zero]
        · rw [div_mul_cancel₀ _ hα]
        · have := congrFun (congrFun hrec.mul_eq i) j
          rw [Matrix.mul_apply, Fin.sum_univ_succ] at this
          rw [this, hA₁, Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, vecMulVec_apply,
            smul_eq_mul]
          field_simp
          ring

/-- **Algorithm 12.1.1** of [golub2013matrix], correctness in exact arithmetic. Let $n = N + 1$, let
$\omega, \nu \in \mathbb{R}^n$ with $\omega_k \neq \nu_j$ for all $k, j$, and let
$A \in \mathbb{R}^{n \times n}$ and $R, S \in \mathbb{R}^{n \times r}$ satisfy
$\Omega A - A \Lambda = RS^T$. Assume that the leading principal submatrices $A(1{:}k, 1{:}k)$
are nonsingular for $k = 1, \dots, n - 1$. Then the matrices $L$ and $U$ that the algorithm
computes in exact arithmetic satisfy $A = LU$, with $L$ unit lower triangular and $U$ upper
triangular.

**Reading.** The source assumes that $A$ "has an LU factorization". The statement reads this as
the nonsingularity of the leading principal submatrices of orders $1, \dots, n - 1$. Then the
pivots that the recursion meets are those of Gaussian elimination, and they are nonzero.

The factorization is `Matrix.IsLU`, and the submatrix of order $k$ is
`A.strictLeadingPrincipalSubmatrix k` for the 0-based index `k : Fin n`; the order $0$ is the
empty matrix. The computed factors are `Id.run (algorithm_12_1_1 pure N ω ν R S)`. The existence
of an LU factorization is Theorem 3.2.1, `GolubVanLoan.Chapter03.theorem_3_2_1`. -/
theorem algorithm_12_1_1_spec {N : ℕ} {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ}
    (hων : ∀ k j, ω k ≠ ν j) (h : diagonal ω * A - A * diagonal ν = R * Sᵀ)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLU A (Id.run (algorithm_12_1_1 pure N ω ν R S)).1
      (Id.run (algorithm_12_1_1 pure N ω ν R S)).2 := by
  obtain ⟨L, U, hLU⟩ := Chapter03.theorem_3_2_1 fun k =>
    ((isUnit_iff_isUnit_det _).1 (hA k)).ne_zero
  refine algorithm_12_1_1_spec_aux N hων h ⟨L, U, hLU, fun i => ?_⟩
  have hdet := hLU.det_strictLeadingPrincipalSubmatrix i.succ
  have hu := (isUnit_iff_isUnit_det _).1 (hA i.succ)
  rw [hdet] at hu
  exact (Finset.prod_ne_zero_iff.1 hu.ne_zero) i.castSucc
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.castSucc_lt_succ⟩)

end LUdisp

/-! ### Permutations of Cauchy-like matrices (§12.1.6) -/

/-- Let $P$ be the permutation matrix of a permutation $\sigma$ and let $d \in \mathbb{R}^n$. Then
$P \operatorname{diag}(d) P^T = \operatorname{diag}(d \circ \sigma)$. -/
theorem permMatrix_mul_diagonal_mul_transpose (σ : Equiv.Perm (Fin n)) (d : Fin n → ℝ) :
    σ.permMatrix ℝ * diagonal d * (σ.permMatrix ℝ)ᵀ = diagonal (d ∘ σ) := by
  rw [transpose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [diagonal_apply, Equiv.Perm.inv_def]

/-- The permutation matrix $P$ of a permutation is orthogonal: $P^T P = I$. -/
theorem transpose_permMatrix_mul_self (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℝ)ᵀ * σ.permMatrix ℝ = 1 := by
  rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

/-- **§12.1.6** of [golub2013matrix], permutations of Cauchy-like matrices. Let
$\omega, \nu \in \mathbb{R}^n$, $A \in \mathbb{R}^{n \times n}$ and
$R, S \in \mathbb{R}^{n \times r}$ satisfy $\Omega A - A \Lambda = RS^T$, and let $P$ and $Q$ be
the permutation matrices of permutations $\sigma$ and $\tau$. Then $$(P \Omega P^T)(P A Q^T) -
(P A Q^T)(Q \Lambda Q^T) = (PR)(QS)^T,$$ and the matrices $P \Omega P^T =
\operatorname{diag}(\omega \circ \sigma)$ and $Q \Lambda Q^T = \operatorname{diag}(\nu \circ
\tau)$ are again diagonal. So row and column permutations of a Cauchy-like matrix act on the
data $\{\Omega, \Lambda, R, S\}$.

The permutation matrix $P$ is `σ.permMatrix ℝ`. -/
theorem displacement_permute {ω ν : Fin n → ℝ} {r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {R S : Matrix (Fin n) (Fin r) ℝ} (h : diagonal ω * A - A * diagonal ν = R * Sᵀ)
    (σ τ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℝ * diagonal ω * (σ.permMatrix ℝ)ᵀ) *
          (σ.permMatrix ℝ * A * (τ.permMatrix ℝ)ᵀ) -
        (σ.permMatrix ℝ * A * (τ.permMatrix ℝ)ᵀ) *
          (τ.permMatrix ℝ * diagonal ν * (τ.permMatrix ℝ)ᵀ) =
      (σ.permMatrix ℝ * R) * (τ.permMatrix ℝ * S)ᵀ ∧
      σ.permMatrix ℝ * diagonal ω * (σ.permMatrix ℝ)ᵀ = diagonal (ω ∘ σ) ∧
      τ.permMatrix ℝ * diagonal ν * (τ.permMatrix ℝ)ᵀ = diagonal (ν ∘ τ) := by
  refine ⟨?_, permMatrix_mul_diagonal_mul_transpose σ ω,
    permMatrix_mul_diagonal_mul_transpose τ ν⟩
  have hP := transpose_permMatrix_mul_self σ
  have hQ := transpose_permMatrix_mul_self τ
  calc _ = σ.permMatrix ℝ * (diagonal ω * A - A * diagonal ν) * (τ.permMatrix ℝ)ᵀ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (σ.permMatrix ℝ)ᵀ, hP, Matrix.one_mul,
          ← Matrix.mul_assoc (τ.permMatrix ℝ)ᵀ, hQ, Matrix.one_mul]
    _ = _ := by
        rw [h, transpose_mul]
        simp only [Matrix.mul_assoc]

/-! ### Fast LU with partial pivoting (Algorithm 12.1.2) -/

section LUdispPiv

/-- The pivot of Algorithm 12.1.2 for a vector $a$: the first index $i$ at which $|a_i|$ is largest.
The source chooses a permutation $P$ with $|[Pa]_1|$ maximal; here ties go to the smallest
index. The comparisons act on the computed values and are exact. -/
noncomputable def pivotIndex {k : ℕ} (a : Fin (k + 1) → ℝ) : Fin (k + 1) :=
  (List.finRange (k + 1)).foldl (fun best i => if |a best| < |a i| then i else best) 0

/-- A running-maximum scan of $|a|$ over a list $l$, started at the index $b$, returns an index $p$
with $|a_b| \le |a_p|$ and $|a_i| \le |a_p|$ for every $i \in l$. -/
private theorem abs_le_abs_foldl_max {k : ℕ} (a : Fin k → ℝ) (l : List (Fin k)) (b : Fin k) :
    |a b| ≤ |a (l.foldl (fun best i => if |a best| < |a i| then i else best) b)| ∧
      ∀ i ∈ l, |a i| ≤ |a (l.foldl (fun best i => if |a best| < |a i| then i else best) b)| := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    set b' := if |a b| < |a x| then x else b
    have hb : |a b| ≤ |a b'| ∧ |a x| ≤ |a b'| := by
      simp only [b']
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, not_lt.1 h⟩
    obtain ⟨ih1, ih2⟩ := ih b'
    exact ⟨hb.1.trans ih1, hb.2.trans ih1, ih2⟩

/-- The pivot index $p$ of a vector $a$ has an entry of largest modulus: $|a_i| \le |a_p|$ for all
$i$. -/
theorem abs_le_abs_pivotIndex {k : ℕ} (a : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    |a i| ≤ |a (pivotIndex a)| :=
  (abs_le_abs_foldl_max a _ 0).2 i (List.mem_finRange i)

/-- **Algorithm 12.1.2** of [golub2013matrix] (`LUdispPiv`): Algorithm 12.1.1 with partial pivoting.
Let $n = N + 1$, let $\omega, \nu \in \mathbb{R}^n$, and let $R, S \in \mathbb{R}^{n \times r}$
be generators of a Cauchy-like matrix $A$. For $n = 1$ the algorithm returns $L = 1$,
$U = r_1^T s_1 / (\omega_1 - \nu_1)$ and $P = I$. For $n > 1$ it computes the first column
$a = (R s_1) ./ (\omega - \nu_1)$ of $A$ and chooses an index $i$ of largest $|a_i|$. The
permutation $\Pi$ that swaps $1$ and $i$ is applied to $a$, to the rows of $R$ and to $\omega$.
From the permuted data the algorithm computes $\alpha = a_1$, $f = a(2{:}n)$, $g$, $\tilde R_1$
and $\tilde S_1$ as in Algorithm 12.1.1. Then it computes $[L_1, U_1, P_1] =
\mathrm{LUdispPiv}(\omega(2{:}n), \nu(2{:}n), \tilde R_1, \tilde S_1)$ and returns $$L =
\begin{bmatrix} 1 & 0 \\ P_1 f/\alpha & L_1 \end{bmatrix}, \qquad U = \begin{bmatrix} \alpha &
g^T \\ 0 & U_1 \end{bmatrix}, \qquad P = \begin{bmatrix} 1 & 0 \\ 0 & P_1 \end{bmatrix} \Pi.$$

Every arithmetic result passes through the rounding hook `rnd`. The pivot is
`GolubVanLoan.Chapter12.pivotIndex`. The permutation is returned as an `Equiv.Perm`, built by
`Equiv.Perm.decomposeFin` from the pivot index and the permutation of the recursive call; its
matrix is `Equiv.Perm.permMatrix`. -/
noncomputable def algorithm_12_1_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {r : ℕ} :
    (N : ℕ) → (ω ν : Fin (N + 1) → ℝ) → (R S : Matrix (Fin (N + 1)) (Fin r) ℝ) →
      M (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ × Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ×
        Equiv.Perm (Fin (N + 1)))
  | 0, ω, ν, R, S => do
      let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R 0) (S 0) 0
      let u ← rnd (t / (← rnd (ω 0 - ν 0)))
      pure (1, of fun _ _ => u, 1)
  | N + 1, ω, ν, R, S => do
      let a₀ ← vecLoop fun i : Fin (N + 2) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R i) (S 0) 0
        rnd (t / (← rnd (ω i - ν 0)))
      let σ := Equiv.swap 0 (pivotIndex a₀)
      let g ← vecLoop fun j : Fin (N + 1) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (S j.succ) (R (σ 0)) 0
        rnd (t / (← rnd (ω (σ 0) - ν j.succ)))
      let R₁ ← vecLoop fun i : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (R (σ i.succ) c - (← rnd ((← rnd (a₀ (σ i.succ) * R (σ 0) c)) / a₀ (σ 0))))
      let S₁ ← vecLoop fun j : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (S j.succ c - (← rnd ((← rnd (g j * S 0 c)) / a₀ (σ 0))))
      let LUP₁ ← algorithm_12_1_2 rnd N (fun i => ω (σ i.succ)) (fun j => ν j.succ) (of R₁) (of S₁)
      let l ← vecLoop fun i : Fin (N + 1) => rnd (a₀ (σ i.succ) / a₀ (σ 0))
      pure (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (l (LUP₁.2.2 i')) (fun j' => LUP₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a₀ (σ 0)) g j)
          (fun i' => Fin.cases 0 (fun j' => LUP₁.2.1 i' j') j) i,
        Equiv.Perm.decomposeFin.symm (pivotIndex a₀, LUP₁.2.2))

variable {r : ℕ}

/-- In exact arithmetic, Algorithm 12.1.2 on a matrix of order $1$ returns $L = 1$,
$U = r_1^T s_1 / (\omega_1 - \nu_1)$ and the identity permutation. -/
theorem algorithm_12_1_2_zero (ω ν : Fin 1 → ℝ) (R S : Matrix (Fin 1) (Fin r) ℝ) :
    Id.run (algorithm_12_1_2 pure 0 ω ν R S) =
      (1, of fun _ _ => (R 0 ⬝ᵥ S 0) / (ω 0 - ν 0), 1) := by
  simp [algorithm_12_1_2, FloatingPoint.dotAccum_id_finRange]

/-- In exact arithmetic, Algorithm 12.1.2 on a matrix of order $N + 2$ computes the first column $a$
by its formula, swaps the pivot to the top, computes $g$ and the updated generators from the
permuted data, calls itself on order $N + 1$ for $[L_1, U_1, P_1]$, and returns the bordered
factors $L$, $U$ and the combined permutation. -/
theorem algorithm_12_1_2_succ {N : ℕ} (ω ν : Fin (N + 2) → ℝ)
    (R S : Matrix (Fin (N + 2)) (Fin r) ℝ) :
    Id.run (algorithm_12_1_2 pure (N + 1) ω ν R S) =
      let a₀ : Fin (N + 2) → ℝ := fun i => (R i ⬝ᵥ S 0) / (ω i - ν 0)
      let σ := Equiv.swap 0 (pivotIndex a₀)
      let g : Fin (N + 1) → ℝ := fun j => (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ)
      let LUP₁ := Id.run (algorithm_12_1_2 pure N (fun i => ω (σ i.succ)) (fun j => ν j.succ)
        (of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0))
        (of fun j c => S j.succ c - g j * S 0 c / a₀ (σ 0)))
      (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (a₀ (σ (LUP₁.2.2 i').succ) / a₀ (σ 0))
            (fun j' => LUP₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a₀ (σ 0)) g j)
          (fun i' => Fin.cases 0 (fun j' => LUP₁.2.1 i' j') j) i,
        Equiv.Perm.decomposeFin.symm (pivotIndex a₀, LUP₁.2.2)) := by
  simp only [algorithm_12_1_2, Id.run_bind, Id.run_pure, idRun_vecLoop,
    FloatingPoint.dotAccum_id_finRange, zero_add]

/-- If $A$ is nonsingular and $a_{11} \neq 0$, then the Schur complement of $a_{11}$ in $A$ is
nonsingular. -/
private theorem isUnit_schur {N : ℕ} {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ} (hA : IsUnit A)
    (hα : A 0 0 ≠ 0) :
    IsUnit (A.submatrix Fin.succ Fin.succ -
      (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) := by
  have h := isUnit_schurComplementSingle hA hα
  have he : A.submatrix Fin.succ Fin.succ -
      (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (fun j => A 0 j.succ) =
        (A.schurComplementSingle 0).submatrix (finSuccAboveEquiv 0) (finSuccAboveEquiv 0) := by
    ext i j
    simp only [Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, schurComplementSingle_apply, finSuccAboveEquiv_apply, Fin.succAbove_zero]
    ring
  rw [he, isUnit_iff_isUnit_det, det_submatrix_equiv_self, ← isUnit_iff_isUnit_det]
  exact h

private theorem algorithm_12_1_2_spec_aux : ∀ (N : ℕ) {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ},
    (∀ k j, ω k ≠ ν j) → diagonal ω * A - A * diagonal ν = R * Sᵀ → IsUnit A →
    IsLU ((Id.run (algorithm_12_1_2 pure N ω ν R S)).2.2.permMatrix ℝ * A)
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).1
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).2.1 ∧
      ∀ i j, |(Id.run (algorithm_12_1_2 pure N ω ν R S)).1 i j| ≤ 1
  | 0, ω, ν, A, R, S, hων, h, _ => by
      have hA := (equation_12_1_4 hων).1 h 0 0
      rw [algorithm_12_1_2_zero]
      have h0 : ∀ i : Fin (0 + 1), i = 0 := fun i => Fin.ext (Nat.lt_one_iff.1 i.isLt)
      refine ⟨⟨isUnitLowerTriangular_one, fun i j hij => absurd hij (by simp [h0 i, h0 j]), ?_⟩,
        fun i j => ?_⟩
      · ext i j
        rw [h0 i, h0 j]
        simp [hA]
      · rw [h0 i, h0 j]
        simp
  | N + 1, ω, ν, A, R, S, hων, h, hunit => by
      have hcol : ∀ i, (R i ⬝ᵥ S 0) / (ω i - ν 0) = A i 0 := fun i =>
        ((equation_12_1_4 hων).1 h i 0).symm
      set a₀ : Fin (N + 2) → ℝ := fun i => (R i ⬝ᵥ S 0) / (ω i - ν 0) with ha₀
      set σ := Equiv.swap 0 (pivotIndex a₀) with hσ
      have hσ0 : σ 0 = pivotIndex a₀ := Equiv.swap_apply_left _ _
      have hα : A (σ 0) 0 ≠ 0 := by
        intro h0
        have hall : ∀ i, A i 0 = 0 := fun i => by
          have := abs_le_abs_pivotIndex a₀ i
          rw [← hσ0, show a₀ (σ 0) = A (σ 0) 0 from hcol _, h0, abs_zero] at this
          rw [← hcol i]
          exact abs_nonpos_iff.1 this
        exact ((isUnit_iff_isUnit_det A).1 hunit).ne_zero (det_eq_zero_of_column_eq_zero 0 hall)
      set A' := A.submatrix σ id with hA'
      have hων' : ∀ k j, (ω ∘ σ) k ≠ ν j := fun k j => hων _ _
      have h' : diagonal (ω ∘ σ) * A' - A' * diagonal ν = R.submatrix σ id * Sᵀ :=
        (equation_12_1_4 hων').2 fun k j => (equation_12_1_4 hων).1 h (σ k) j
      have hunit' : IsUnit A' := by
        rw [hA', isUnit_iff_isUnit_det, det_permute]
        refine IsUnit.mul ?_ ((isUnit_iff_isUnit_det A).1 hunit)
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      have hα' : A' 0 0 ≠ 0 := hα
      have hS₁ := theorem_12_1_1 hων' h' hα'
      set A₁ := A'.submatrix Fin.succ Fin.succ -
        (A' 0 0)⁻¹ • vecMulVec (fun i => A' i.succ 0) fun j => A' 0 j.succ with hA₁
      have hg : ∀ j : Fin (N + 1), (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) = A' 0 j.succ :=
        fun j => by rw [dotProduct_comm]; exact ((equation_12_1_4 hων).1 h (σ 0) j.succ).symm
      have hR₁ : (of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0) :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          (R.submatrix σ id).submatrix Fin.succ id -
            (A' 0 0)⁻¹ • vecMulVec (fun i => A' i.succ 0) (R.submatrix σ id 0) := by
        ext i c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul, ha₀, hcol, hA']
        ring
      have hS₁' : (of fun j c => S j.succ c -
            (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) * S 0 c / a₀ (σ 0) :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          S.submatrix Fin.succ id - (A' 0 0)⁻¹ • vecMulVec (fun j => A' 0 j.succ) (S 0) := by
        ext j c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul, hg, ha₀, hcol]
        rw [hA']
        simp only [submatrix_apply, id]
        ring
      obtain ⟨hrec, hbound⟩ := algorithm_12_1_2_spec_aux N (ω := fun i => ω (σ i.succ))
        (ν := fun j => ν j.succ) (A := A₁)
        (R := of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0))
        (S := of fun j c => S j.succ c -
            (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) * S 0 c / a₀ (σ 0))
        (fun k j => hων _ _) (by rw [hR₁, hS₁']; exact hS₁) (isUnit_schur hunit' hα')
      rw [algorithm_12_1_2_succ]
      simp only [← hσ, ← ha₀]
      set LUP₁ := Id.run (algorithm_12_1_2 pure N (fun i => ω (σ i.succ)) (fun j => ν j.succ)
        (of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0))
        (of fun j c => S j.succ c -
            (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) * S 0 c / a₀ (σ 0)))
      have ha : ∀ x, a₀ x = A x 0 := hcol
      have hP : (Equiv.Perm.decomposeFin.symm (pivotIndex a₀, LUP₁.2.2)).permMatrix ℝ * A =
          of fun i j => Fin.cases (A' 0 j) (fun i' => A' (LUP₁.2.2 i').succ j) i := by
        rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [hA', hσ0]
        · simp [hA', hσ]
      refine ⟨⟨isUnitLowerTriangular_bordered _ hrec.isUnitLowerTriangular,
        isUpperTriangular_bordered _ _ hrec.isUpperTriangular, ?_⟩, fun i j => ?_⟩
      · rw [hP]
        have hmul := hrec.mul_eq
        rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul] at hmul
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [Matrix.mul_apply, Fin.sum_univ_succ, of_apply, Fin.cases_zero, Fin.cases_succ,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, hcol]
        · rfl
        · exact hg j
        · rw [div_mul_cancel₀ _ hα]
          rfl
        · have := congrFun (congrFun hmul i) j
          rw [Matrix.mul_apply, Fin.sum_univ_succ] at this
          rw [this, hg, hA₁, submatrix_apply, Matrix.sub_apply, submatrix_apply, Matrix.smul_apply,
            vecMulVec_apply, smul_eq_mul]
          have hα'' : ∀ x, A (σ x) 0 = A' x 0 := fun _ => rfl
          simp only [hα'', id]
          field_simp
          ring
      · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [of_apply, Fin.cases_zero, Fin.cases_succ, hcol]
        · simp
        · simp
        · rw [abs_div, div_le_one (abs_pos.2 hα)]
          have := abs_le_abs_pivotIndex a₀ (σ (LUP₁.2.2 i).succ)
          rw [← hσ0, ha, ha] at this
          exact this
        · exact hbound i j

/-- **Algorithm 12.1.2** of [golub2013matrix], correctness in exact arithmetic. Let $n = N + 1$, let
$\omega, \nu \in \mathbb{R}^n$ with $\omega_k \neq \nu_j$ for all $k, j$, let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, and let $R, S \in \mathbb{R}^{n \times r}$
satisfy $\Omega A - A \Lambda = RS^T$. Then the matrices $L$ and $U$ and the permutation matrix
$P$ that the algorithm computes in exact arithmetic satisfy $$PA = LU,$$ with $L$ unit lower
triangular and $U$ upper triangular, and $|l_{ij}| \le 1$ for all $i, j$.

The factorization is `Matrix.IsLU`, and $P$ is the `Equiv.Perm.permMatrix` of the returned
permutation. The proof tracks the row swap on the generators (§12.1.6) and uses that
nonsingularity passes to the Schur complement. The pivot is nonzero,
$|\alpha| = \max_i |a_i| > 0$, because the first column of a nonsingular $A$ is nonzero. -/
theorem algorithm_12_1_2_spec {N : ℕ} {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ}
    (hων : ∀ k j, ω k ≠ ν j) (h : diagonal ω * A - A * diagonal ν = R * Sᵀ) (hA : IsUnit A) :
    IsLU ((Id.run (algorithm_12_1_2 pure N ω ν R S)).2.2.permMatrix ℝ * A)
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).1
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).2.1 ∧
      ∀ i j, |(Id.run (algorithm_12_1_2 pure N ω ν R S)).1 i j| ≤ 1 :=
  algorithm_12_1_2_spec_aux N hων h hA

end LUdispPiv

/-! ### Toeplitz-like and Hankel-like matrices (§12.1.7) -/

/-- **§12.1.7** of [golub2013matrix], definition of a Toeplitz-like matrix. A matrix
$A \in \mathbb{R}^{n \times n}$ is **Toeplitz-like** of displacement rank at most $r$ if
$Z_1 A - A Z_{-1}$ has rank at most $r$, that is, $Z_1 A - A Z_{-1} = RS^T$ for some
$R, S \in \mathbb{R}^{n \times r}$.

**Reading.** The source's requirement $r \ll n$ is informal, and it is not part of the
definition.

$Z_\varphi$, with ones on the subdiagonal and $\varphi$ in the top right corner, is
`Matrix.cyclicShift n φ`. -/
def IsToeplitzLike (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  displacementRank (cyclicShift n 1) (cyclicShift n (-1)) A ≤ r

/-- **§12.1.7** of [golub2013matrix], definition of a Hankel-like matrix. A matrix
$A \in \mathbb{R}^{n \times n}$ is **Hankel-like** of displacement rank at most $r$ if
$Z_1^T A - A Z_{-1}$ has rank at most $r$, that is, $Z_1^T A - A Z_{-1} = RS^T$ for some
$R, S \in \mathbb{R}^{n \times r}$. -/
def IsHankelLike (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  displacementRank (cyclicShift n 1)ᵀ (cyclicShift n (-1)) A ≤ r

/-- **§12.1.7** of [golub2013matrix], definition of a Toeplitz-plus-Hankel-like matrix. A matrix
$A \in \mathbb{R}^{n \times n}$ is **Toeplitz-plus-Hankel-like** of displacement rank at most
$r$ if $Y_{0,0} A - A Y_{1,1}$ has rank at most $r$, that is, $Y_{0,0} A - A Y_{1,1} = RS^T$ for
some $R, S \in \mathbb{R}^{n \times r}$.

$Y_{\gamma,\delta}$, with ones on the two off-diagonals, $\gamma$ in the top left corner and
$\delta$ in the bottom right corner, is `Matrix.cornerTridiagonal n γ δ`. -/
def IsToeplitzPlusHankelLike (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) A ≤ r

/-- **Equation (12.1.8)** of [golub2013matrix]. Let $T \in \mathbb{R}^{n \times n}$ be a Toeplitz
matrix. Then $Z_1 T - T Z_{-1}$ is zero outside its first row and its last column, and $T$ is
Toeplitz-like of displacement rank at most $2$. -/
theorem equation_12_1_8 {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) :
    (∀ i j : Fin n, 0 < (i : ℕ) → (j : ℕ) + 1 < n →
      (cyclicShift n 1 * T - T * cyclicShift n (-1) : Matrix (Fin n) (Fin n) ℝ) i j = 0) ∧
      IsToeplitzLike 2 T :=
  ⟨fun _ _ hi hj => sylvesterMap_cyclicShift_toeplitz_apply hT hi hj,
    displacementRank_cyclicShift_toeplitz_le hT⟩

/-- **Equation (12.1.9)** of [golub2013matrix]. Let $T \in \mathbb{R}^{n \times n}$ be a Toeplitz
matrix. Then $Y_{0,0} T - T Y_{1,1}$ is zero outside its border, which is its first and last
rows and its first and last columns, and $T$ is Toeplitz-plus-Hankel-like of displacement rank
at most $4$. -/
theorem equation_12_1_9 {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) :
    (∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) + 1 < n → 0 < (j : ℕ) → (j : ℕ) + 1 < n →
      (cornerTridiagonal n 0 0 * T - T * cornerTridiagonal n 1 1 : Matrix (Fin n) (Fin n) ℝ) i j
        = 0) ∧
      IsToeplitzPlusHankelLike 4 T :=
  ⟨fun _ _ hi₀ hi hj₀ hj => sylvesterMap_cornerTridiagonal_toeplitz_apply hT hi₀ hi hj₀ hj,
    displacementRank_cornerTridiagonal_toeplitz_le hT⟩

/-- The transpose of the matrix $Z_\varphi \in \mathbb{R}^{n \times n}$ satisfies
$(Z_\varphi^T)^n = \varphi I$. -/
private theorem transpose_cyclicShift_pow_card (φ : ℝ) :
    (cyclicShift n φ)ᵀ ^ n = φ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← transpose_pow, cyclicShift_pow_card, transpose_smul, transpose_one]

/-- The Sylvester operator $X \mapsto Z_1^T X - X Z_{-1}$ on $\mathbb{R}^{n \times n}$ is injective.
This is part (a) of Problem P12.1.1 of [golub2013matrix]: $Z_1^T X = X Z_{-1}$ gives
$(Z_1^T)^n X = X Z_{-1}^n$, that is, $X = -X$. -/
theorem sylvesterMap_transpose_cyclicShift_injective :
    Function.Injective (sylvesterMap (cyclicShift n (1 : ℝ))ᵀ (cyclicShift n (-1))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero] at hX
  have hsc : SemiconjBy X (cyclicShift n (-1)) (cyclicShift n 1)ᵀ := hX.symm
  have hpow := (hsc.pow_right n).eq
  rw [transpose_cyclicShift_pow_card, cyclicShift_pow_card, one_smul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul ℝ X] at hpow
  exact (smul_eq_zero.mp hpow).resolve_left two_ne_zero

/-- If the Sylvester operator $X \mapsto FX - XG$ of real matrices $F$ and $G$ is injective, then
the spectra of $F$ and $G$ as complex matrices are disjoint. -/
private theorem disjoint_spectrum_of_injective {F G : Matrix (Fin n) (Fin n) ℝ}
    (h : Function.Injective (sylvesterMap F G)) :
    Disjoint (spectrum ℂ F.complexify) (spectrum ℂ G.complexify) := by
  have hinj : Function.Injective (sylvesterMap F.complexify G.complexify) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    rw [sylvesterMap_apply, sub_eq_zero] at hX
    have hre : sylvesterMap F G (X.map Complex.re) = 0 := by
      ext i j
      have := congrArg Complex.re (congrFun (congrFun hX i) j)
      simp only [Matrix.mul_apply, complexify_apply, Complex.re_sum, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at this
      simp only [sylvesterMap_apply, Matrix.sub_apply, Matrix.mul_apply, map_apply,
        Matrix.zero_apply, sub_eq_zero]
      exact this
    have him : sylvesterMap F G (X.map Complex.im) = 0 := by
      ext i j
      have := congrArg Complex.im (congrFun (congrFun hX i) j)
      simp only [Matrix.mul_apply, complexify_apply, Complex.im_sum, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero, zero_add] at this
      simp only [sylvesterMap_apply, Matrix.sub_apply, Matrix.mul_apply, map_apply,
        Matrix.zero_apply, sub_eq_zero]
      exact this
    have h1 := h (hre.trans (map_zero _).symm)
    have h2 := h (him.trans (map_zero _).symm)
    ext i j
    apply Complex.ext
    · simpa using congrFun (congrFun h1 i) j
    · simpa using congrFun (congrFun h2 i) j
  exact Set.disjoint_iff_inter_eq_empty.2 ((Chapter07.lemma_7_1_5 _ _).1
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩)

/-- **§12.1.7** of [golub2013matrix], after (12.1.9). The Sylvester operators
$X \mapsto Z_1 X - X Z_{-1}$, $X \mapsto Z_1^T X - X Z_{-1}$ and
$X \mapsto Y_{0,0} X - X Y_{1,1}$ on $\mathbb{R}^{n \times n}$ are injective, and $$\lambda(Z_1)
\cap \lambda(Z_{-1}) = \emptyset, \qquad \lambda(Z_1^T) \cap \lambda(Z_{-1}) = \emptyset, \qquad
\lambda(Y_{0,0}) \cap \lambda(Y_{1,1}) = \emptyset,$$ where $\lambda(\cdot)$ is the set of
complex eigenvalues. So the precondition of the definition (12.1.2) holds for the displacement
ranks of §12.1.7.

**Typo.** The source prints $\lambda(Z_{-1}) \cup \lambda(Z_1) = \emptyset$. The intended
statement has $\cap$ for $\cup$.

The spectra are those of the complex matrices `Matrix.complexify`. The disjointness of the
spectra follows from the injectivity by Lemma 7.1.5, `GolubVanLoan.Chapter07.lemma_7_1_5`. -/
theorem disjoint_spectra_displacement_operators :
    Function.Injective (sylvesterMap (cyclicShift n (1 : ℝ)) (cyclicShift n (-1))) ∧
      Function.Injective (sylvesterMap (cyclicShift n (1 : ℝ))ᵀ (cyclicShift n (-1))) ∧
      Function.Injective (sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1)) ∧
      Disjoint (spectrum ℂ (cyclicShift n (1 : ℝ)).complexify)
        (spectrum ℂ (cyclicShift n (-1 : ℝ)).complexify) ∧
      Disjoint (spectrum ℂ (cyclicShift n (1 : ℝ))ᵀ.complexify)
        (spectrum ℂ (cyclicShift n (-1 : ℝ)).complexify) ∧
      Disjoint (spectrum ℂ (cornerTridiagonal n 0 0).complexify)
        (spectrum ℂ (cornerTridiagonal n 1 1).complexify) := by
  have h1 := sylvesterMap_cyclicShift_one_neg_one_injective (K := ℝ) (n := n) two_ne_zero
  have h2 := sylvesterMap_transpose_cyclicShift_injective (n := n)
  have h3 := sylvesterMap_cornerTridiagonal_injective (n := n)
  exact ⟨h1, h2, h3, disjoint_spectrum_of_injective h1, disjoint_spectrum_of_injective h2,
    disjoint_spectrum_of_injective h3⟩

/-- **Equation (12.1.10)** of [golub2013matrix]. Let $H \in \mathbb{R}^{n \times n}$ be a Hankel
matrix. Then $Z_1^T H - H Z_{-1}$ is zero outside its last row and its last column, $H$ is
Hankel-like of displacement rank at most $2$, and $\mathcal{E}_n H$ is a Toeplitz matrix, where
$\mathcal{E}_n$ is the exchange matrix. -/
theorem equation_12_1_10 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHankel) :
    (∀ i j : Fin n, (i : ℕ) + 1 < n → (j : ℕ) + 1 < n →
      ((cyclicShift n 1)ᵀ * H - H * cyclicShift n (-1) : Matrix (Fin n) (Fin n) ℝ) i j = 0) ∧
      IsHankelLike 2 H ∧
      (exchange n * H).IsToeplitz :=
  ⟨fun _ _ hi hj => sylvesterMap_cyclicShift_hankel_apply hH hi hj,
    displacementRank_cyclicShift_hankel_le hH, hH.isToeplitz_exchange_mul⟩

/-- **Equation (12.1.11)** of [golub2013matrix] and the sentence after it. Let
$T, H \in \mathbb{R}^{n \times n}$, with $T$ Toeplitz and $H$ Hankel. Then
$Y_{0,0} H - H Y_{1,1}$ is zero outside its border, which is its first and last rows and its
first and last columns, so $\operatorname{rank}_{Y_{0,0}, Y_{1,1}}(H) \le 4$. Moreover
$\operatorname{rank}_{Y_{0,0}, Y_{1,1}}(T + H) \le 4$. -/
theorem equation_12_1_11 {T H : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) (hH : H.IsHankel) :
    (∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) + 1 < n → 0 < (j : ℕ) → (j : ℕ) + 1 < n →
      (cornerTridiagonal n 0 0 * H - H * cornerTridiagonal n 1 1 : Matrix (Fin n) (Fin n) ℝ) i j
        = 0) ∧
      IsToeplitzPlusHankelLike 4 H ∧ IsToeplitzPlusHankelLike 4 (T + H) :=
  ⟨fun _ _ hi₀ hi hj₀ hj => sylvesterMap_cornerTridiagonal_hankel_apply hH hi₀ hi hj₀ hj,
    displacementRank_cornerTridiagonal_hankel_le hH,
    displacementRank_cornerTridiagonal_toeplitz_add_hankel_le hT hH⟩

/-! ### Conversion to Cauchy-like form (§12.1.8) -/

/-- **§12.1.8** of [golub2013matrix], conversion to Cauchy-like form. Let
$F, G, A \in \mathbb{R}^{n \times n}$ and $R, S \in \mathbb{R}^{n \times r}$ satisfy
$FA - AG = RS^T$, and let $X_F, X_G \in \mathbb{R}^{n \times n}$ be nonsingular with $X_F^{-1} F
X_F = \Omega = \operatorname{diag}(\omega)$ and $X_G^{-1} G X_G = \Lambda =
\operatorname{diag}(\nu)$. Then $\tilde A = X_F^{-1} A X_G$ satisfies $$\Omega \tilde A - \tilde
A \Lambda = \tilde R \tilde S^T, \qquad \tilde R = X_F^{-1} R, \quad \tilde S = X_G^T S.$$
Moreover, Steps 1–4 of the source are correct: for $b \in \mathbb{R}^n$, if
$\tilde A \tilde x = X_F^{-1} b$, then $x = X_G \tilde x$ solves $Ax = b$.

**Typo.** The first display of the source prints $X_G^{-1} G X_F$ for $X_G^{-1} G X_G$. -/
theorem cauchyLike_of_diagonalizable {F G A X_F X_G : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    {R S : Matrix (Fin n) (Fin r) ℝ} {ω ν : Fin n → ℝ} (hXF : IsUnit X_F) (hXG : IsUnit X_G)
    (h : F * A - A * G = R * Sᵀ) (hΩ : X_F⁻¹ * F * X_F = diagonal ω)
    (hΛ : X_G⁻¹ * G * X_G = diagonal ν) :
    diagonal ω * (X_F⁻¹ * A * X_G) - (X_F⁻¹ * A * X_G) * diagonal ν = (X_F⁻¹ * R) * (X_Gᵀ * S)ᵀ ∧
      ∀ b x : Fin n → ℝ, (X_F⁻¹ * A * X_G) *ᵥ x = X_F⁻¹ *ᵥ b → A *ᵥ (X_G *ᵥ x) = b := by
  have h1 : X_F * X_F⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hXF)
  have h2 : X_G * X_G⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hXG)
  refine ⟨?_, fun b x hx => ?_⟩
  · rw [← hΩ, ← hΛ]
    calc _ = X_F⁻¹ * (F * A - A * G) * X_G := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc X_F, h1, Matrix.one_mul, ← Matrix.mul_assoc X_G, h2,
            Matrix.one_mul]
      _ = _ := by
          rw [h, transpose_mul, transpose_transpose]
          simp only [Matrix.mul_assoc]
  · have := congrArg (X_F *ᵥ ·) hx
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, h1, Matrix.one_mul, one_mulVec] at this
    rw [mulVec_mulVec]
    exact this

/-! ### Fast eigensystems (12.1.12)–(12.1.13) -/

/-- The DST-I matrix $\mathcal{S}_n$ of equation (12.1.12) of [golub2013matrix], §12.1.8:
$$[\mathcal{S}_n]_{kj} = \sqrt{\frac{2}{n+1}} \sin\left(\frac{kj\pi}{n+1}\right), \qquad k, j =
1, \dots, n.$$ It is the backbone's `Matrix.dst1` scaled to be orthogonal. -/
noncomputable def dstMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  √(2 / ((n : ℝ) + 1)) • dst1 n

/-- **Equation (12.1.12)** of [golub2013matrix]. The DST-I matrix $\mathcal{S}_n$ is symmetric and
orthogonal, and $$\mathcal{S}_n^T Y_{0,0} \mathcal{S}_n = 2
\operatorname{diag}\left(\cos\frac{\pi}{n+1}, \dots, \cos\frac{n\pi}{n+1}\right).$$

$\mathcal{S}_n$ is `GolubVanLoan.Chapter12.dstMatrix n`. Indices are 0-based: the diagonal entry
with index $k$ is $2\cos((k+1)\pi/(n+1))$. -/
theorem equation_12_1_12 :
    (dstMatrix n)ᵀ = dstMatrix n ∧ (dstMatrix n)ᵀ * dstMatrix n = 1 ∧
      (dstMatrix n)ᵀ * cornerTridiagonal n 0 0 * dstMatrix n =
        diagonal fun k : Fin n => 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) := by
  have hc : √(2 / ((n : ℝ) + 1)) * √(2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / 2) = 1 := by
    rw [Real.mul_self_sqrt (by positivity)]
    field_simp
  have hT : (dstMatrix n)ᵀ = dstMatrix n := by
    rw [dstMatrix, transpose_smul, dst1_transpose]
  have hcol : cornerTridiagonal n 0 0 * dst1 n =
      dst1 n * diagonal fun k : Fin n => 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi /
        ((n : ℝ) + 1)) := by
    ext i j
    have h := congrFun (symmTridiagonalToeplitz_mulVec_sineVec (n := n) (a := (1 : ℝ)) (b := 0) j) i
    rw [mul_diagonal, dst1_apply_eq_sineVec, cornerTridiagonal_zero_zero, Matrix.mul_apply]
    simp only [dst1_apply_eq_sineVec]
    rw [show ∑ k, symmTridiagonalToeplitz n (1 : ℝ) 0 i k * sineVec n j k =
      (symmTridiagonalToeplitz n (1 : ℝ) 0 *ᵥ sineVec n j) i from rfl, h, Pi.smul_apply,
      smul_eq_mul]
    ring
  refine ⟨hT, ?_, ?_⟩
  · rw [hT, dstMatrix, Matrix.smul_mul, Matrix.mul_smul, dst1_mul_self, smul_smul, smul_smul, hc,
      one_smul]
  · rw [hT, dstMatrix, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hcol,
      ← Matrix.mul_assoc, dst1_mul_self, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_smul, hc,
      one_smul]

/-- The column scaling $\sqrt{2/n}\, q_j$ of the DCT-II matrix $\mathcal{C}_n$ of (12.1.13) in
[golub2013matrix], with $q_1 = 1/\sqrt{2}$ and $q_j = 1$ for $j \ge 2$: it is $\sqrt{1/n}$ for
the first column and $\sqrt{2/n}$ for the others. -/
noncomputable def dctScale (n : ℕ) (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then √(1 / (n : ℝ)) else √(2 / (n : ℝ))

/-- The DCT-II matrix $\mathcal{C}_n$ of equation (12.1.13) of [golub2013matrix]:
$$[\mathcal{C}_n]_{kj} = \sqrt{\frac{2}{n}}\, q_j \cos\left(\frac{(2k-1)(j-1)\pi}{2n}\right),
\qquad k, j = 1, \dots, n,$$ with $q_1 = 1/\sqrt{2}$ and $q_j = 1$ for $j \ge 2$. It is the
transpose of the backbone's `Matrix.dct2` with its columns scaled by
`GolubVanLoan.Chapter12.dctScale`. -/
noncomputable def dctMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (dct2 n)ᵀ * diagonal (dctScale n)

/-- **Equation (12.1.13)** of [golub2013matrix]. The DCT-II matrix $\mathcal{C}_n$ is orthogonal,
and $$\mathcal{C}_n^T Y_{1,1} \mathcal{C}_n = 2 \operatorname{diag}\left(1, \cos\frac{\pi}{n},
\dots, \cos\frac{(n-1)\pi}{n}\right).$$

$\mathcal{C}_n$ is `GolubVanLoan.Chapter12.dctMatrix n`. Indices are 0-based: the diagonal entry
with index $k$ is $2\cos(k\pi/n)$. The source refers to Problem P12.1.5 for this fact. -/
theorem equation_12_1_13 :
    (dctMatrix n)ᵀ * dctMatrix n = 1 ∧
      (dctMatrix n)ᵀ * cornerTridiagonal n 1 1 * dctMatrix n =
        diagonal fun k : Fin n => 2 * Real.cos ((k : ℕ) * Real.pi / n) := by
  set d : Fin n → ℝ := fun k => if (k : ℕ) = 0 then (n : ℝ) else n / 2 with hd
  have hwd : ∀ k, dctScale n k * d k * dctScale n k = 1 := by
    intro k
    have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
    simp only [dctScale, hd]
    split_ifs
    · rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
      field_simp
    · rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
      field_simp
  have hrow : dct2 n * cornerTridiagonal n 1 1 =
      (diagonal fun k : Fin n => 2 * Real.cos ((k : ℕ) * Real.pi / n)) * dct2 n := by
    rw [← dct2_mul_cornerTridiagonal_one_one_mul_inv, Matrix.mul_assoc _ (dct2 n)⁻¹,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (isUnit_dct2 n)), Matrix.mul_one]
  have hC : (dctMatrix n)ᵀ = diagonal (dctScale n) * dct2 n := by
    rw [dctMatrix, transpose_mul, diagonal_transpose, transpose_transpose]
  have hD : dct2 n * (dct2 n)ᵀ = diagonal d := dct2_mul_transpose n
  constructor
  · rw [hC, dctMatrix, Matrix.mul_assoc, ← Matrix.mul_assoc (dct2 n), hD, diagonal_mul_diagonal,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [← mul_assoc]
    exact hwd k
  · rw [hC, dctMatrix, Matrix.mul_assoc (diagonal _) (dct2 n), hrow]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dct2 n), hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext k
    linear_combination (2 * Real.cos ((k : ℕ) * Real.pi / n)) * hwd k

end GolubVanLoan.Chapter12
