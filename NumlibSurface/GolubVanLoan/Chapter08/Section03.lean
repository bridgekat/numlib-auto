/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighQuotientIteration
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05
import NumlibSurface.GolubVanLoan.Chapter08.Section02

/-!
# Golub and Van Loan, Section 8.3: The symmetric QR algorithm

This module formalizes §8.3 of [golub2013matrix], the symmetric QR algorithm. A symmetric
$A \in \mathbb{R}^{n \times n}$ is first reduced to a symmetric tridiagonal $T = Q^T A Q$ by
Householder reflections (8.3.1), with the symmetric rank-two update $PBP = B - vw^T - wv^T$
(Algorithm 8.3.1). The QR iteration keeps the tridiagonal form, and a zero subdiagonal entry splits
the spectrum of $T$ into the spectra of two smaller blocks. Theorems 8.3.1 and 8.3.2 relate the
tridiagonal decomposition to the Krylov matrix $K(A, Q(:, 1), n)$ and state that $Q$ is essentially
determined by its first column. The module then treats the facts of §8.3.3 about the QR iteration on
tridiagonal matrices (preservation of form, shifts, perfect shifts), the Wilkinson shift (8.3.3),
the explicit single-shift QR iteration (8.3.2), the bulge chase of the implicit shift version
(§8.3.5) with Algorithms 8.3.2 and 8.3.3, the connection with Rayleigh quotient iteration (§8.3.6),
and orthogonal iteration with Ritz acceleration ((8.3.6), §8.3.7).

Algorithm 8.3.1 has a rounding bridge into the backbone relation
`FloatingPoint.RoundsTridiagonalizePert` and the backward error bound
$\hat T = \tilde Q^T (A + E) \tilde Q$ with an explicit constant. The other results specialize the
backbone modules `Numlib.Eigen.QRAlgorithm`, `Numlib.Eigen.RayleighQuotientIteration`,
`Numlib.LinearAlgebra.Matrix.QR` and `Numlib.LinearAlgebra.Matrix.UnreducedHessenberg`, and the
programs call the Householder and Givens programs of §5.1.

## Main definitions

* Algorithm 8.3.1, `GolubVanLoan.Chapter08.algorithm_8_3_1`: Householder tridiagonalization, one
  `GolubVanLoan.Chapter08.tridiagonalizeStep` per column.
* §8.3.1, `GolubVanLoan.Chapter08.IsUnreducedTridiagonal`: a tridiagonal matrix with no zero
  subdiagonal entry.
* (8.3.3), `GolubVanLoan.Chapter08.wilkinsonShift`: the Wilkinson shift $\mu = a_n + d -
  \operatorname{sign}(d)\sqrt{d^2 + b_{n-1}^2}$.
* (8.3.2), `GolubVanLoan.Chapter08.explicitShiftedQR`: the explicit single-shift QR iteration.
* Algorithm 8.3.2, `GolubVanLoan.Chapter08.algorithm_8_3_2`: the implicit symmetric QR step with
  Wilkinson shift.
* Algorithm 8.3.3, `GolubVanLoan.Chapter08.algorithm_8_3_3`: the symmetric QR algorithm.
* (8.3.6), `GolubVanLoan.Chapter08.IsRitzAcceleration`: orthogonal iteration with Ritz acceleration.

## Main results

* (8.3.1), `GolubVanLoan.Chapter08.equation_8_3_1`: a symmetric $A$ has an orthogonal $Q$ with
  $Qe_1 = e_1$ and $Q^T A Q$ symmetric tridiagonal.
* §8.3.1, `GolubVanLoan.Chapter08.householder_conj_eq_sub_rankTwo`: $PBP = B - vw^T - wv^T$ for
  $P = I - \beta vv^T$, $p = \beta Bv$ and $w = p - (\beta p^T v/2) v$.
* Algorithm 8.3.1, `GolubVanLoan.Chapter08.algorithm_8_3_1_rounds`,
  `GolubVanLoan.Chapter08.algorithm_8_3_1_rounding` and
  `GolubVanLoan.Chapter08.algorithm_8_3_1_spec`: every run is a computed tridiagonalization; the
  computed $\hat T$ is $\tilde Q^T (A + E) \tilde Q$ with $\tilde Q$ orthogonal and $\|E\|_F$ of
  order $n^2 u \|A\|_F$; in exact arithmetic the output is $Q^T A Q$ for the product $Q$ of the
  returned reflectors.
* §8.3.1, `GolubVanLoan.Chapter08.tridiagonal_spectrum_split`: a zero subdiagonal entry splits $T$
  into $\operatorname{diag}(T_1, T_2)$ and $\lambda(T) = \lambda(T_1) \cup \lambda(T_2)$.
* Theorem 8.3.1, `GolubVanLoan.Chapter08.theorem_8_3_1`: $Q^T K(A, Q(:, 1), n)$ is upper triangular
  with diagonal $1, t_{21}, t_{21} t_{32}, \dots$.
* Theorem 8.3.2, `GolubVanLoan.Chapter08.theorem_8_3_2`: the implicit Q theorem for tridiagonal
  decompositions.
* §8.3.3, `GolubVanLoan.Chapter08.qr_tridiagonal_preservation`,
  `GolubVanLoan.Chapter08.shifted_qr_tridiagonal` and `GolubVanLoan.Chapter08.perfect_shift`: a QR
  step keeps a symmetric tridiagonal matrix symmetric tridiagonal, with or without shift, and a
  shift by an eigenvalue deflates the last row and column.
* (8.3.3), `GolubVanLoan.Chapter08.equation_8_3_3`: the Wilkinson shift is the eigenvalue of the
  trailing $2 \times 2$ block closer to $t_{nn}$.
* (8.3.2), `GolubVanLoan.Chapter08.equation_8_3_2`: each iterate of the explicit iteration is
  orthogonally similar to $T_0$.
* §8.3.5, `GolubVanLoan.Chapter08.bulgeChase_step`: one rotation moves the bulge one step down the
  band.
* Algorithm 8.3.2, `GolubVanLoan.Chapter08.algorithm_8_3_2_window` and
  `GolubVanLoan.Chapter08.algorithm_8_3_2_spec`: the implicit step is $Z^T T Z$ with
  $Z^T (T - \mu I)$ upper triangular, and it equals the explicit step up to signs.
* Algorithm 8.3.3, `GolubVanLoan.Chapter08.algorithm_8_3_3_spec` and
  `GolubVanLoan.Chapter08.algorithm_8_3_3_eigenvalues`: $D = Q^T (A + E) Q$ with $\|E\|_F \le c \,
  \mathrm{tol} \, \|A\|_F / (1 - c \, \mathrm{tol})$, $c = 2(n - 1)$, and the diagonal of $D$ holds
  the eigenvalues of $A + E$.
* §8.3.6, `GolubVanLoan.Chapter08.rayleigh_qr_connection`: the shifted QR step with
  $\sigma = t_{nn}$ is a step of Rayleigh quotient iteration from $e_n$.
* §8.3.7, `GolubVanLoan.Chapter08.ritzAcceleration_residual`: the Ritz-accelerated basis minimizes
  the residual $\|A \tilde Q_k - \tilde Q_k S\|_F$.

## Conventions

* Tridiagonal matrices are stored as full matrices `Matrix (Fin n) (Fin n) ℝ` with the property
  `Matrix.IsTridiagonal`. "Unreduced" is `GolubVanLoan.Chapter08.IsUnreducedTridiagonal`, which is
  `Matrix.IsUnreducedUpperHessenberg` together with tridiagonality.
* The explicit shifted QR step is the backbone's `Matrix.shiftedQrStep`, with the canonical QR
  factorization `Matrix.qrQ`, `Matrix.qrR`.
* The Wilkinson shift uses $\operatorname{sign}(0) = 1$.

## Implementation notes

* The numbered algorithms call the `house` and `givens` programs of §5.1 on index lists (conventions
  10 and 13 of the library index). Algorithm 8.3.1 returns its reflector data. Algorithm 8.3.2 runs
  on a window of consecutive indices with an accumulator. Algorithm 8.3.3 is a loop of at most
  `fuel` passes with a `done` flag.
* The exact semantics are loop invariants at `Id`. For Algorithm 8.3.1, the cleaned array after step
  $k$ is $(P_0 \cdots P_k)^T A (P_0 \cdots P_k)$ for the returned reflector data; the rounding
  bridge of a step identifies no reflector, so this is not read off the bridge. For Algorithm 8.3.2,
  the invariant is the bulge chase on a window, the state being the block similarity
  `GolubVanLoan.Chapter07.blockConj` of §7.5 (`GolubVanLoan.Chapter08.algorithm_8_3_2_window`), and
  the implicit-shift principle gives the triangularity of $Z^T (T - \mu I)$.
* Theorems 8.3.1 and 8.3.2 restate the Krylov-matrix theorem and the implicit Q theorem of §7.4.
* The program (8.3.2) is `GolubVanLoan.Chapter08.explicitShiftedQR`, with its exact semantics
  `GolubVanLoan.Chapter08.equation_8_3_2`. The display (8.3.6) defines the process
  `GolubVanLoan.Chapter08.IsRitzAcceleration`, and the statement of §8.3.7 about it has the content
  name `GolubVanLoan.Chapter08.ritzAcceleration_residual`.

## Deviations from the source

* **§8.3.1, the rank-two update** (generalization).
  `GolubVanLoan.Chapter08.householder_conj_eq_sub_rankTwo` proves the algebraic formula before
  requiring a Householder coefficient.
* **Algorithm 8.3.2, implicit versus explicit step** (reading).
  `GolubVanLoan.Chapter08.algorithm_8_3_2_spec` proves the explicit-step comparison up to
  diagonal signs under shifted nonsingularity.
* **Equation (8.3.6)** (generalization). `GolubVanLoan.Chapter08.IsRitzAcceleration` accepts any
  real $A$ for which the iterate data include an orthogonal diagonalization of each projected
  matrix.
* **Equation (8.3.1) and Algorithm 8.3.1** (reading). The tridiagonal reduction fixes the first
  coordinate vector. `GolubVanLoan.Chapter08.algorithm_8_3_1` keeps the reflectors separately
  and mirrors the lower-triangular trailing update. Its rounding theorem gives a dimension-
  dependent explicit coefficient under stated rounding-model hypotheses.
* **Theorem 8.3.1 and the spectral split** (generalization).
  `GolubVanLoan.Chapter08.theorem_8_3_1` uses a tridiagonal reduction without requiring
  symmetry. `GolubVanLoan.Chapter08.tridiagonal_spectrum_split` uses vanishing couplings on both
  sides and retains multiplicities.
* **Equation (8.3.2)** (reading). `GolubVanLoan.Chapter08.explicitShiftedQR` uses the canonical
  QR decomposition, a rule depending on the current iterate, and a supplied initial matrix. The
  associated theorem states orthogonal similarity and symmetry for any symmetric start.
* **Algorithms 8.3.2–8.3.3** (reading). The implicit step accepts a working window and
  accumulates rotations. The outer algorithm uses a finite pass budget and always accumulates
  the orthogonal factor. Its error and eigenvalue results are exact-arithmetic estimates for
  threshold deflations, conditional on the stop flag where diagonalization is needed.
* **§8.3.6, the Rayleigh quotient connection** (reading).
  `GolubVanLoan.Chapter08.rayleigh_qr_connection` makes the shifted solve’s nonsingularity
  explicit and gives the next iterate up to the sign of $r_{nn}$.
* **§8.3.7, Ritz acceleration** (reading). `GolubVanLoan.Chapter08.ritzAcceleration_residual`
  formalizes the residual minimum over coefficient matrices in the selected subspace, with
  invariance under its Ritz rotation.
* **§8.3.3, preservation of form** (correction). The source states it for every QR factorization
  $T = QR$. For singular $T$ the orthogonal factor is not unique ($T = 0 = Q \cdot 0$ for every
  orthogonal $Q$), and the claim fails. The statements assume that $T$ (or $T - sI$) is nonsingular
  or that $(Q, R)$ is the Givens QR factorization. See
  `GolubVanLoan.Chapter08.qr_tridiagonal_preservation` and
  `GolubVanLoan.Chapter08.shifted_qr_tridiagonal`.
* **Equation (8.3.3)** (reading). The source does not fix $\operatorname{sign}(0)$. Lean uses
  $\operatorname{sign}(0) = 1$ to select one of the two equally close eigenvalues when $d=0$.
  See `GolubVanLoan.Chapter08.wilkinsonShift`.
* **Theorem 8.3.2** (generalization). The source assumes that $A$ is symmetric and that $T$ and
  $S$ are tridiagonal. The Lean theorem only needs the latter assumption. See
  `GolubVanLoan.Chapter08.theorem_8_3_2`.

## Not formalized

* **Cubic convergence of the shifted QR iteration (§8.3.4).** The source quotes Wilkinson's result
  without proof.
* **The convergence rate of Ritz acceleration (§8.3.7).** The source quotes Stewart's result without
  proof.
* **The backward error of the eigenvalues computed by Algorithm 8.3.3.** The source gives
  $\|E\|_2 \approx u \|A\|_2$ without a derivation; it rests on rounding models of Givens-based
  iterations.
* **Storage and operation counts.**
-/

open Matrix FloatingPoint

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### Reduction to tridiagonal form (§8.3.1) -/

/-- **Equation (8.3.1)** of [golub2013matrix], the tridiagonal decomposition. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then there is an orthogonal
$Q \in \mathbb{R}^{n \times n}$ such that $T = Q^T A Q$ is symmetric and tridiagonal, and
$Q e_1 = e_1$ when $n \ge 1$.

**Reading.** The source introduces the tridiagonal reduction. Lean also records that the
Householder product fixes the first coordinate vector whenever it exists. -/
theorem equation_8_3_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, (Qᵀ * A * Q).IsSymm ∧ (Qᵀ * A * Q).IsTridiagonal ∧
      ∀ h : 0 < n, Q *ᵥ Pi.single ⟨0, h⟩ 1 = Pi.single ⟨0, h⟩ 1 := by
  have hsymm : ∀ Q : Matrix (Fin n) (Fin n) ℝ, (Qᵀ * A * Q).IsSymm := fun Q => by
    exact hA.transpose_mul_mul Q
  rcases n with _ | M
  · exact ⟨1, one_mem _, hsymm 1, fun i j _ => Fin.elim0 i, fun h => absurd h (lt_irrefl 0)⟩
  · refine ⟨hessenbergQ A, hessenbergQ_mem_orthogonalGroup A, hsymm _, ?_, fun h => ?_⟩
    · have h := isTridiagonal_hessenbergReduce_of_isHermitian (A := A) (isHermitian_iff_isSymm.2 hA)
      rwa [hessenbergReduce_eq_conj, conjTranspose_eq_transpose_of_trivial] at h
    · rw [mulVec_single_one]
      ext i
      rw [col_apply, show (⟨0, h⟩ : Fin (M + 1)) = 0 from rfl, hessenbergQ_apply_zero A i]
      by_cases hi : i = 0 <;> simp [hi, Matrix.one_apply]

/-- **Section 8.3.1** of [golub2013matrix], the symmetric Householder update. Let
$B \in \mathbb{R}^{n \times n}$ be symmetric, $v \in \mathbb{R}^n$, $\beta \in \mathbb{R}$ and
$P = I - \beta v v^T$. With $p = \beta B v$ and $w = p - (\beta p^T v / 2) v$,
$$P B P = B - v w^T - w v^T.$$

The identity holds for every $\beta$, not only for $\beta = 2/v^T v$.

**Generalization.** The rank-two formula holds for arbitrary $\beta$ and $v$. The source uses a
nonzero Householder vector with $\beta=2/(v^Tv)$. -/
theorem householder_conj_eq_sub_rankTwo {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (v : Fin n → ℝ) (β : ℝ) :
    let p := β • (B *ᵥ v)
    let w := p - ((β * (v ⬝ᵥ p)) / 2) • v
    (1 - β • vecMulVec v v) * B * (1 - β • vecMulVec v v) =
      B - vecMulVec v w - vecMulVec w v := by
  intro p w
  have hB' : Bᴴ = B := by rw [conjTranspose_eq_transpose_of_trivial]; exact hB
  have h := conj_one_sub_smul_vecMulVec_eq_sub (R := ℝ) two_ne_zero hB' v (β := β)
    (star_trivial β) (p := p) (w := w) rfl (by simp [w])
  simpa using h

/-- For a list $T$ of indices, the list of the pairs $(i, j)$ with $i, j \in T$ and $j \le i$, row
by row in the order of $T$: the lower triangle of the block $T \times T$. -/
def lowerPairs (T : List (Fin n)) : List (Fin n × Fin n) :=
  T.flatMap fun i => (T.filter (· ≤ i)).map fun j => (i, j)

/-- The array that step $k$ of Algorithm 8.3.1 writes, for $k + 1 < n$ (0-based), from the array
$A$, the computed lower triangle $L$ of the trailing block and the computed norm $\nu$. The
entry $(r, s)$ with $r, s \ge k + 1$ is $L(r, s)$ if $s \le r$ and $L(s, r)$ otherwise (a copy
of the mirror image); the entries $(k + 1, k)$ and $(k, k + 1)$ are $\nu$; every other entry is
that of $A$. -/
def tridiagonalizeOut (k : Fin n) (hk : (k : ℕ) + 1 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (L : Fin n × Fin n → ℝ) (ν : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun r s =>
    if (k : ℕ) + 1 ≤ r ∧ (k : ℕ) + 1 ≤ s then (if s ≤ r then L (r, s) else L (s, r))
    else if (r = ⟨k + 1, hk⟩ ∧ s = k) ∨ (r = k ∧ s = ⟨k + 1, hk⟩) then ν else A r s

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- Step $k$ of Algorithm 8.3.1 on the working array $A$, for $k + 1 < n$ (0-based), with the index
list $T_k = [k + 1, \dots, n - 1]$ (convention 10). It computes:
* $(v, \beta) = \mathrm{house}(A(T_k, k))$ by `GolubVanLoan.Chapter05.houseOn`;
* $p_i = \mathrm{fl}(\beta \, \mathrm{fl}(A(i, T_k) v))$ for $i \in T_k$, each inner product by
  Algorithm 1.1.1 from $0$;
* $h = \mathrm{fl}(\mathrm{fl}(\beta \, \mathrm{fl}(p^T v)) / 2)$ and
  $w_i = \mathrm{fl}(p_i - \mathrm{fl}(h v_i))$;
* the new norm $\nu = \mathrm{fl}(\sqrt{\mathrm{fl}(A(T_k, k)^T A(T_k, k))})$, the source's
  $A(k+1, k) = A(k, k+1) = \|A(k{+}1{:}n, k)\|_2$;
* the lower triangle of $A(T_k, T_k) - v w^T - w v^T$, entry by entry as
  $\mathrm{fl}(\mathrm{fl}(a_{ij} - \mathrm{fl}(v_i w_j)) - \mathrm{fl}(w_i v_j))$ for
  $j \le i$, from the entries of $A$ before the update, then mirrored.

It returns the array `GolubVanLoan.Chapter08.tridiagonalizeOut` and $(v, \beta)$.

**Reading.** The source describes computing the upper triangle using symmetry. Lean evaluates
the lower triangle and mirrors the result, computes the subdiagonal length, and returns the
reflector separately. -/
noncomputable def tridiagonalizeStep (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ)) := do
  let T := Chapter05.indexFrom n (k + 1)
  let vβ ← Chapter05.houseOn rnd T (fun i => A i k)
  let p ← T.foldlM (fun (p : Fin n → ℝ) i => do
    let b ← (do rnd (vβ.2 * (← dotAccum rnd T (A i) vβ.1 0)))
    pure (Function.update p i b)) 0
  let h ← rnd ((← rnd (vβ.2 * (← dotAccum rnd T p vβ.1 0))) / 2)
  let w ← T.foldlM (fun (w : Fin n → ℝ) i => do
    let b ← (do rnd (p i - (← rnd (h * vβ.1 i))))
    pure (Function.update w i b)) 0
  let ν ← rnd √(← dotAccum rnd T (fun i => A i k) (fun i => A i k) 0)
  let L ← (lowerPairs T).foldlM (fun (L : Fin n × Fin n → ℝ) ij => do
    let b ← (do rnd ((← rnd (A ij.1 ij.2 - (← rnd (vβ.1 ij.1 * w ij.2)))) -
      (← rnd (w ij.1 * vβ.1 ij.2))))
    pure (Function.update L ij b)) fun ij => A ij.1 ij.2
  pure (tridiagonalizeOut k hk A L ν, vβ)

/-- **Algorithm 8.3.1** of [golub2013matrix] (Householder tridiagonalization). "Given a symmetric
$A \in \mathbb{R}^{n \times n}$, the following algorithm overwrites $A$ with $T = Q^T A Q$,
where $T$ is tridiagonal and $Q = H_1 \cdots H_{n-2}$ is the product of Householder
transformations."
```
for k = 1:n-2
    [v, β] = house(A(k+1:n, k))
    p = β A(k+1:n, k+1:n) v
    w = p - (β pᵀv / 2) v
    A(k+1, k) = ‖A(k+1:n, k)‖₂; A(k, k+1) = A(k+1, k)
    A(k+1:n, k+1:n) = A(k+1:n, k+1:n) - v wᵀ - w vᵀ
end
```
The program runs `GolubVanLoan.Chapter08.tridiagonalizeStep` for the 0-based
$k = 0, \dots, n - 3$, and returns the array together with the reflector data $(v_k, \beta_k)$
in the order of application (convention 13). These data are the "factored form" of $Q$ that
Algorithm 8.3.3 accumulates.

The entries $A(k{+}2{:}n, k)$ are left as they were. The source does not overwrite them either,
and they are never read again. For $n \le 2$ the program does nothing.

**Reading.** The source describes storing reflectors in the subdiagonal portion of the array
and computing the upper triangular part of the trailing update. Lean returns a separate
reflector list, computes the lower triangle and mirrors it, and reads the final tridiagonal
from the band. -/
noncomputable def algorithm_8_3_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) :=
  (List.finRange (n - 2)).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ))
      (k : Fin (n - 2)) => do
    let r ← tridiagonalizeStep rnd (k.castLE (Nat.sub_le n 2))
      (by rw [Fin.val_castLE]; omega) st.1
    pure (r.1, st.2 ++ [r.2])) (A, [])

end Programs

/-- The tridiagonal part of $A$: the entries $a_{ij}$ with $|i - j| \le 1$, and $0$ elsewhere. It is
an exact copy, with no arithmetic. -/
def tridiagonalPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) ≤ j + 1 ∧ (j : ℕ) ≤ i + 1 then A i j else 0

/-! ### Algorithm 8.3.1: the rounding bridge and the rounding bound -/

/-- The array after $k$ steps of Algorithm 8.3.1 with the entries that are never read again set to
$0$: the vectors below the subdiagonal of the first $k$ columns, and their mirror images. This
is the $\hat A_k$ of `FloatingPoint.RoundsTridiagonalizePert`. -/
private def bandClean (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j =>
    if ((j : ℕ) < k ∧ (j : ℕ) + 2 ≤ i) ∨ ((i : ℕ) < k ∧ (i : ℕ) + 2 ≤ j) then 0 else A i j

private theorem bandClean_apply_of_le {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hi : k ≤ (i : ℕ)) (hj : k ≤ (j : ℕ)) : bandClean k A i j = A i j := by
  simp only [bandClean, of_apply]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

private theorem bandClean_apply_eq_zero {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (h : ((j : ℕ) < k ∧ (j : ℕ) + 2 ≤ i) ∨ ((i : ℕ) < k ∧ (i : ℕ) + 2 ≤ j)) :
    bandClean k A i j = 0 := by
  simp only [bandClean, of_apply]
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

private theorem bandClean_apply_of_not {k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (h : ¬ (((j : ℕ) < k ∧ (j : ℕ) + 2 ≤ i) ∨ ((i : ℕ) < k ∧ (i : ℕ) + 2 ≤ j))) :
    bandClean k A i j = A i j := by
  simp only [bandClean, of_apply]
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

private theorem bandClean_zero (A : Matrix (Fin n) (Fin n) ℝ) : bandClean 0 A = A := by
  ext i j
  exact bandClean_apply_of_le A (Nat.zero_le _) (Nat.zero_le _)

private theorem bandClean_eq_tridiagonalPart (A : Matrix (Fin n) (Fin n) ℝ) :
    bandClean (n - 2) A = tridiagonalPart A := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [bandClean, tridiagonalPart, of_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The indices $i \ge k + 1$ as a subtype are equivalent to the members of the list
`GolubVanLoan.Chapter05.indexFrom n (k + 1)`. -/
private def tailEquiv (k : ℕ) :
    {i : Fin n // k + 1 ≤ (i : ℕ)} ≃ {i // i ∈ Chapter05.indexFrom n (k + 1)} :=
  Equiv.subtypeEquivRight fun _ => Chapter05.mem_indexFrom.symm

/-- For an idempotent model, an inner product accumulated from $0$ over the tail list is a
`FloatingPoint.RoundsDot` on the tail subtype. -/
private theorem roundsDot_tail {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (k : ℕ)
    {x y : Fin n → ℝ} {s : ℝ}
    (h : s ∈ (dotAccum fp.round (Chapter05.indexFrom n (k + 1)) x y 0).run) :
    RoundsDot fp (fun i : {i : Fin n // k + 1 ≤ (i : ℕ)} => x i) (fun i => y i) s :=
  (roundsDot_comp_equiv_iff (tailEquiv k)).2
    (Chapter05.roundsDot_subtype_of_mem_run_dotAccum hfp (Chapter05.nodup_indexFrom _ _) h)

/-- A pair $(i, j)$ is in `GolubVanLoan.Chapter08.lowerPairs T` if and only if $i, j \in T$ and
$j \le i$. -/
private theorem mem_lowerPairs {T : List (Fin n)} {ij : Fin n × Fin n} :
    ij ∈ lowerPairs T ↔ ij.1 ∈ T ∧ ij.2 ∈ T ∧ ij.2 ≤ ij.1 := by
  obtain ⟨i, j⟩ := ij
  simp only [lowerPairs, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, ⟨hb, hba⟩, rfl, rfl⟩; exact ⟨ha, hb, hba⟩
  · rintro ⟨hi, hj, hji⟩; exact ⟨i, hi, j, ⟨hj, hji⟩, rfl, rfl⟩

private theorem nodup_lowerPairs {T : List (Fin n)} (hT : T.Nodup) : (lowerPairs T).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun i _ => (hT.filter _).map fun a b h => (Prod.mk.inj h).2, ?_⟩
  refine hT.imp fun {a b} hab => ?_
  rw [Function.onFun, List.disjoint_left]
  simp only [List.mem_map]
  rintro _ ⟨x, -, rfl⟩ ⟨y, -, hy⟩
  exact hab (Prod.mk.inj hy).1.symm

private theorem tridiagonalizeOut_succ_self (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n × Fin n → ℝ) (ν : ℝ) :
    bandClean ((k : ℕ) + 1) (tridiagonalizeOut k hk A L ν) ⟨k + 1, hk⟩ k = ν := by
  rw [bandClean_apply_of_not (k := (k : ℕ) + 1) (i := ⟨k + 1, hk⟩) (j := k) _ (by simp)]
  simp [tridiagonalizeOut]

private theorem tridiagonalizeOut_self_succ (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n × Fin n → ℝ) (ν : ℝ) :
    bandClean ((k : ℕ) + 1) (tridiagonalizeOut k hk A L ν) k ⟨k + 1, hk⟩ = ν := by
  rw [bandClean_apply_of_not (k := (k : ℕ) + 1) (i := k) (j := ⟨k + 1, hk⟩) _ (by simp)]
  simp [tridiagonalizeOut]

/-- The runs of one step of Algorithm 8.3.1 in a rounding model, unpacked into the runs of its
parts. -/
private theorem tridiagonalizeStep_mem {fp : RoundingModel ℝ} (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) {r : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ)}
    (hr : r ∈ (tridiagonalizeStep fp.round k hk A).run) :
    ∃ (vβ : (Fin n → ℝ) × ℝ) (p w : Fin n → ℝ) (s t h σ ν : ℝ) (L : Fin n × Fin n → ℝ),
      vβ ∈ (Chapter05.houseOn fp.round (Chapter05.indexFrom n (k + 1)) (fun i => A i k)).run ∧
      p ∈ ((Chapter05.indexFrom n (k + 1)).foldlM (fun (p : Fin n → ℝ) i => do
        let b ← (do fp.round (vβ.2 * (← dotAccum fp.round (Chapter05.indexFrom n (k + 1)) (A i)
          vβ.1 0)))
        pure (Function.update p i b)) 0).run ∧
      s ∈ (dotAccum fp.round (Chapter05.indexFrom n (k + 1)) p vβ.1 0).run ∧
      fp.Rounds (vβ.2 * s) t ∧ fp.Rounds (t / 2) h ∧
      w ∈ ((Chapter05.indexFrom n (k + 1)).foldlM (fun (w : Fin n → ℝ) i => do
        let b ← (do fp.round (p i - (← fp.round (h * vβ.1 i))))
        pure (Function.update w i b)) 0).run ∧
      σ ∈ (dotAccum fp.round (Chapter05.indexFrom n (k + 1)) (fun i => A i k)
        (fun i => A i k) 0).run ∧
      fp.Rounds √σ ν ∧
      L ∈ ((lowerPairs (Chapter05.indexFrom n (k + 1))).foldlM
        (fun (L : Fin n × Fin n → ℝ) (ij : Fin n × Fin n) => do
          let b ← (do fp.round ((← fp.round (A ij.1 ij.2 - (← fp.round (vβ.1 ij.1 * w ij.2)))) -
            (← fp.round (w ij.1 * vβ.1 ij.2))))
          pure (Function.update L ij b)) fun (ij : Fin n × Fin n) => A ij.1 ij.2).run ∧
      r = (tridiagonalizeOut k hk A L ν, vβ) := by
  unfold tridiagonalizeStep at hr
  simp only [SetM.mem_run_bind, SetM.mem_run_pure, RoundingModel.mem_run_round] at hr
  obtain ⟨vβ, hvβ, p, hp, s, hs, t, ht, h, hh, w, hw, σ, hσ, ν, hν, L, hL, rfl⟩ := hr
  exact ⟨vβ, p, w, s, t, h, σ, ν, L, hvβ, hp, hs, ht, hh, hw, hσ, hν, hL, rfl⟩

/-- Below row $k$, column $k$ of the cleaned array is column $k$ of the array. -/
private theorem bandClean_col_tail (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => bandClean (k : ℕ) A i k) =
      fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => A i k :=
  funext fun i => bandClean_apply_of_le A (by have := i.2; omega) le_rfl

/-- For an idempotent model with $(18n + 31) u < 1$, the reflector data of a step of Algorithm 8.3.1
are `FloatingPoint.IsReflectorPert` data of order $18n + 31$ for the tail $x$ of column $k$,
with the target $\|x\|_2$. -/
private theorem tridiagonalizeStep_reflector {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1) (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) {vβ : (Fin n → ℝ) × ℝ}
    (hvβ : vβ ∈ (Chapter05.houseOn fp.round (Chapter05.indexFrom n (k + 1))
      (fun i => A i k)).run) :
    IsReflectorPert fp.u (18 * n + 31)
      (fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => A i k) ⟨⟨k + 1, hk⟩, le_rfl⟩
      ‖(WithLp.toLp 2 (fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => A i k) :
        EuclideanSpace ℝ {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)})‖ (fun i => vβ.1 i) vβ.2 := by
  set T := Chapter05.indexFrom n (k + 1) with hTdef
  have hT : T.Nodup := Chapter05.nodup_indexFrom n (k + 1)
  have hne : T ≠ [] := List.ne_nil_of_mem (Chapter05.mem_indexFrom.2 (le_refl ((k : ℕ) + 1)) :
    (⟨k + 1, hk⟩ : Fin n) ∈ T)
  have hu0 := fp.u_nonneg
  have hlen : T.length ≤ n := (List.length_filter_le _ _).trans (by simp)
  have hu' : ((18 * T.length + 31 : ℕ) : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hu0) hu
  obtain ⟨-, hrefl⟩ := Chapter05.houseOn_rounding hfp hT hne hu' (fun i => A i k) hvβ
  have h1 := hrefl.mono hu0 (by omega : 18 * T.length + 31 ≤ 18 * n + 31) hu
  have hnorm :
      ‖(WithLp.toLp 2 (fun j : {j // j ∈ T} => A j.1 k) : EuclideanSpace ℝ {j // j ∈ T})‖ =
      ‖(WithLp.toLp 2 (fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => A i k) :
        EuclideanSpace ℝ {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)})‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    exact (Equiv.sum_comp (tailEquiv (k : ℕ)) (fun j : {j // j ∈ T} => ‖A j.1 k‖ ^ 2)).symm
  rw [hnorm] at h1
  refine Chapter05.IsReflectorPert.of_comp_equiv (tailEquiv (k : ℕ)).symm ?_
  have hpiv : (tailEquiv (k : ℕ)).symm.symm ⟨⟨k + 1, hk⟩, le_rfl⟩ =
      ⟨T.head hne, List.head_mem hne⟩ := Subtype.ext (Chapter05.head_indexFrom hk hne).symm
  rw [hpiv]
  exact h1

/-- For an idempotent model, the update of the trailing block in a step of Algorithm 8.3.1 is a
`FloatingPoint.RoundsSymmRankTwoUpdate` between the cleaned arrays. -/
private theorem tridiagonalizeStep_rankTwo {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (k : Fin n) (hk : (k : ℕ) + 1 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    {vβ : (Fin n → ℝ) × ℝ} {p w : Fin n → ℝ} {s t h ν : ℝ} {L : Fin n × Fin n → ℝ}
    (hp : p ∈ ((Chapter05.indexFrom n (k + 1)).foldlM (fun (p : Fin n → ℝ) i => do
        let b ← (do fp.round (vβ.2 * (← dotAccum fp.round (Chapter05.indexFrom n (k + 1)) (A i)
          vβ.1 0)))
        pure (Function.update p i b)) 0).run)
    (hs : s ∈ (dotAccum fp.round (Chapter05.indexFrom n (k + 1)) p vβ.1 0).run)
    (ht : fp.Rounds (vβ.2 * s) t) (hh : fp.Rounds (t / 2) h)
    (hw : w ∈ ((Chapter05.indexFrom n (k + 1)).foldlM (fun (w : Fin n → ℝ) i => do
        let b ← (do fp.round (p i - (← fp.round (h * vβ.1 i))))
        pure (Function.update w i b)) 0).run)
    (hL : L ∈ ((lowerPairs (Chapter05.indexFrom n (k + 1))).foldlM
        (fun (L : Fin n × Fin n → ℝ) (ij : Fin n × Fin n) => do
          let b ← (do fp.round ((← fp.round (A ij.1 ij.2 - (← fp.round (vβ.1 ij.1 * w ij.2)))) -
            (← fp.round (w ij.1 * vβ.1 ij.2))))
          pure (Function.update L ij b)) fun (ij : Fin n × Fin n) => A ij.1 ij.2).run) :
    RoundsSymmRankTwoUpdate fp vβ.2 (fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => vβ.1 i)
      ((bandClean (k : ℕ) A).submatrix
        (Subtype.val : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} → Fin n) Subtype.val)
      ((bandClean ((k : ℕ) + 1) (tridiagonalizeOut k hk A L ν)).submatrix
        (Subtype.val : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} → Fin n) Subtype.val) := by
  set T := Chapter05.indexFrom n (k + 1) with hTdef
  have hT : T.Nodup := Chapter05.nodup_indexFrom n (k + 1)
  have hmemT : ∀ i : Fin n, i ∈ T ↔ (k : ℕ) + 1 ≤ i := fun i => Chapter05.mem_indexFrom
  have hp' := (SetM.mem_run_foldlM_update_of_nodup
    (fun (i : Fin n) _ _ => (dotAccum fp.round T (A i) vβ.1 0 >>= fun s =>
      fp.round (vβ.2 * s))) T hT (fun _ _ _ _ _ _ => rfl) 0 p).1 hp
  have hw' := (SetM.mem_run_foldlM_update_of_nodup
    (fun (i : Fin n) _ _ => (fp.round (h * vβ.1 i) >>= fun a => fp.round (p i - a))) T hT
    (fun _ _ _ _ _ _ => rfl) 0 w).1 hw
  have hL' := (SetM.mem_run_foldlM_update_of_nodup
    (fun (ij : Fin n × Fin n) _ _ => (fp.round (vβ.1 ij.1 * w ij.2) >>= fun a =>
      fp.round (A ij.1 ij.2 - a) >>= fun b => fp.round (w ij.1 * vβ.1 ij.2) >>= fun c =>
        fp.round (b - c)))
    (lowerPairs T) (nodup_lowerPairs hT) (fun _ _ _ _ _ _ => rfl) _ L).1 hL
  have hin : ∀ i j : Fin n, (k : ℕ) + 1 ≤ i → (k : ℕ) + 1 ≤ j →
      bandClean ((k : ℕ) + 1) (tridiagonalizeOut k hk A L ν) i j =
        if j ≤ i then L (i, j) else L (j, i) := by
    intro i j hi hj
    rw [bandClean_apply_of_le _ hi hj, tridiagonalizeOut, of_apply,
      ite_eq_left_of_eq_true _ _ (eq_true (And.intro hi hj))]
  have hAin : ∀ i j : Fin n, (k : ℕ) + 1 ≤ i → (k : ℕ) + 1 ≤ j →
      bandClean (k : ℕ) A i j = A i j :=
    fun i j hi hj => bandClean_apply_of_le A (by omega) (by omega)
  have hLij : ∀ i j : Fin n, (k : ℕ) + 1 ≤ i → (k : ℕ) + 1 ≤ j → j ≤ i →
      ∃ a b c : ℝ, fp.Rounds (vβ.1 i * w j) a ∧ fp.Rounds (A i j - a) b ∧
        fp.Rounds (w i * vβ.1 j) c ∧ fp.Rounds (b - c) (L (i, j)) := by
    intro i j hi hj hji
    have := hL'.2 (i, j) (mem_lowerPairs.2 ⟨(hmemT i).2 hi, (hmemT j).2 hj, hji⟩)
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at this
    obtain ⟨a, ha, b, hb, c, hc, hx⟩ := this
    exact ⟨a, b, c, ha, hb, hc, hx⟩
  refine ⟨fun i => p i, fun i => w i, s, h, fun i => ?_, roundsDot_tail hfp k hs, ⟨t, ht, hh⟩,
    fun i => ?_, fun i j => ?_, fun i j => ?_⟩
  · have := hp'.2 i ((hmemT i).2 i.2)
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at this
    obtain ⟨r, hr, hpr⟩ := this
    refine ⟨r, ?_, hpr⟩
    have hrow : ((bandClean (k : ℕ) A).submatrix
        (Subtype.val : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} → Fin n) Subtype.val) i =
        fun j : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => A i j :=
      funext fun j => hAin i j i.2 j.2
    rw [hrow]
    exact roundsDot_tail hfp k hr
  · have := hw'.2 i ((hmemT i).2 i.2)
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at this
    obtain ⟨a, ha, hwa⟩ := this
    exact ⟨a, ha, hwa⟩
  · simp only [submatrix_apply]
    rw [hin i j i.2 j.2]
    by_cases hji : (j : Fin n) ≤ i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hji)]
      obtain ⟨a, b, c, ha, hb, hc, hx⟩ := hLij i j i.2 j.2 hji
      exact ⟨i, j, Or.inl ⟨rfl, rfl⟩, a, b, c, ha, by rwa [hAin i j i.2 j.2], hc, hx⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hji)]
      obtain ⟨a, b, c, ha, hb, hc, hx⟩ := hLij j i j.2 i.2 (le_of_not_ge hji)
      exact ⟨j, i, Or.inr ⟨rfl, rfl⟩, a, b, c, ha, by rwa [hAin j i j.2 i.2], hc, hx⟩
  · simp only [submatrix_apply]
    rw [hin j i j.2 i.2, hin i j i.2 j.2]
    rcases lt_trichotomy (i : Fin n) j with hij | hij | hij
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.2 hij)),
        ite_eq_left_of_eq_true _ _ (eq_true hij.le)]
    · rw [hij]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hij.le),
        ite_eq_right_of_eq_false _ _ (eq_false (not_le.2 hij))]

/-- A step of Algorithm 8.3.1 does not change the entries of the cleaned array in the rows and
columns before $k$, nor the entry $(k, k)$. -/
private theorem tridiagonalizeStep_copy (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (L : Fin n × Fin n → ℝ) (ν : ℝ) (i j : Fin n)
    (hij : (i : ℕ) < k ∨ (j : ℕ) < k ∨ ((i : ℕ) = k ∧ (j : ℕ) = k)) :
    bandClean ((k : ℕ) + 1) (tridiagonalizeOut k hk A L ν) i j = bandClean (k : ℕ) A i j := by
  have hnT : ¬ ((k : ℕ) + 1 ≤ i ∧ (k : ℕ) + 1 ≤ j) := by omega
  have hnν : ¬ ((i = ⟨k + 1, hk⟩ ∧ j = k) ∨ (i = k ∧ j = ⟨k + 1, hk⟩)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp at hij
  simp only [bandClean, tridiagonalizeOut, of_apply]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnT), ite_eq_right_of_eq_false _ _ (eq_false hnν)]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The rounding bridge of one step of Algorithm 8.3.1: for an idempotent model with
$(18n + 31) u < 1$, every run of step $k$ maps the cleaned array $\hat A_k$ to a cleaned array
$\hat A_{k+1}$ that is a computed tridiagonalization step
`FloatingPoint.RoundsTridiagonalizeStepPert` of order $18n + 31$. -/
private theorem tridiagonalizeStep_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1) (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) {r : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ)}
    (hr : r ∈ (tridiagonalizeStep fp.round k hk A).run) :
    RoundsTridiagonalizeStepPert fp (18 * n + 31) hk (bandClean k A)
      (bandClean (k + 1) r.1) := by
  obtain ⟨vβ, p, w, s, t, h, σ, ν, L, hvβ, hp, hs, ht, hh, hw, hσ, hν, hL, rfl⟩ :=
    tridiagonalizeStep_mem k hk A hr
  have hcol := bandClean_col_tail k A
  refine ⟨fun i => vβ.1 i, vβ.2, σ, ν, ?_, ?_, hν, tridiagonalizeOut_succ_self k hk A L ν,
    tridiagonalizeOut_self_succ k hk A L ν, fun i hi => ⟨?_, ?_⟩,
    tridiagonalizeStep_rankTwo hfp k hk A hp hs ht hh hw hL,
    tridiagonalizeStep_copy k hk A L ν⟩
  · rw [hcol]
    exact tridiagonalizeStep_reflector hfp hu k hk A hvβ
  · rw [hcol]
    exact roundsDot_tail hfp k hσ
  · exact bandClean_apply_eq_zero (k := (k : ℕ) + 1) (i := i) (j := k) _
      (Or.inl ⟨Nat.lt_succ_self _, hi⟩)
  · exact bandClean_apply_eq_zero (k := (k : ℕ) + 1) (i := k) (j := i) _
      (Or.inr ⟨Nat.lt_succ_self _, hi⟩)

/-- **Algorithm 8.3.1** of [golub2013matrix], rounding bridge. Let $A \in \mathbb{R}^{n \times n}$,
and let the rounding model be idempotent with $(18n + 31) u < 1$. For every output
$(A', \mathrm{data})$ of Algorithm 8.3.1 in the model, there is a sequence
$\hat A_0, \hat A_1, \dots$ of matrices with $\hat A_0 = A$ and $\hat A_{n-2}$ the tridiagonal
part of $A'$, in which each $\hat A_{k+1}$ is a computed tridiagonalization step from
$\hat A_k$.

The relation is `FloatingPoint.RoundsTridiagonalizePert fp (18 * n + 31) A Ahat`. The matrix
$\hat A_k$ is the array of the run after $k$ steps, with the entries that are never read again
(the vectors below the subdiagonal of the reduced columns, and their mirror images) set to $0$.
In each step, the reflector data come from `GolubVanLoan.Chapter05.houseOn_rounding` with order
$18|T_k| + 31 \le 18n + 31$ and target $+\|x\|_2$, the accumulations from $0$ are
`FloatingPoint.RoundsDot` relations on the tail, and the lower-triangle update with its mirror
image is a `FloatingPoint.RoundsSymmRankTwoUpdate`. Idempotence is
`FloatingPoint.RoundingModel.IsIdempotent`. -/
theorem algorithm_8_3_1_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1) (A : Matrix (Fin n) (Fin n) ℝ)
    {out : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (h : out ∈ (algorithm_8_3_1 fp.round A).run) :
    ∃ Ahat : ℕ → Matrix (Fin n) (Fin n) ℝ, Ahat (n - 2) = tridiagonalPart out.1 ∧
      RoundsTridiagonalizePert fp (18 * n + 31) A Ahat := by
  have key := SetM.forall_mem_run_foldlM_finRange (n := n - 2)
    (I := fun j (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) =>
      ∃ Ahat : ℕ → Matrix (Fin n) (Fin n) ℝ, Ahat 0 = A ∧
        (∀ i, i < j → ∀ hi : i < n - 2, RoundsTridiagonalizeStepPert fp (18 * n + 31)
          (show i + 1 < n by omega) (Ahat i) (Ahat (i + 1))) ∧ Ahat j = bandClean j st.1)
    ⟨fun _ => A, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), (bandClean_zero A).symm⟩ ?_
    out h
  · obtain ⟨Ahat, h0, hstep, hlast⟩ := key
    exact ⟨Ahat, by rw [hlast, bandClean_eq_tridiagonalPart], h0, fun i hi => hstep i hi hi⟩
  · rintro k st ⟨Ahat, h0, hstep, hk⟩ st' hst'
    simp only [SetM.mem_run_bind, SetM.mem_run_pure] at hst'
    obtain ⟨r, hr, rfl⟩ := hst'
    have hstep' := tridiagonalizeStep_rounds hfp hu _ _ st.1 hr
    refine ⟨fun i => if i ≤ k then Ahat i else bandClean ((k : ℕ) + 1) r.1, by simp [h0],
      fun i hi hin => ?_, by simp⟩
    rcases Nat.lt_or_ge i k with hik | hik
    · simp only [show i ≤ (k : ℕ) by omega, show i + 1 ≤ (k : ℕ) by omega, ite_true]
      exact hstep i hik hin
    · have hik' : i = k := by omega
      subst hik'
      simp only [le_refl, ite_true, show ¬ ((k : ℕ) + 1 ≤ k) by omega, ite_false]
      rw [hk]
      exact hstep'

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Algorithm 8.3.1** of [golub2013matrix], rounding errors. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, and let the rounding model be idempotent. Let $K = 18n + 31$ and $\epsilon = 9
\gamma_{6K + 2n + 8} + 2 \gamma_{n+1}$, and assume $(6K + 2n + 8) u < 1$ and
$(n - 2) \epsilon < 1$. Let $\hat T$ be the tridiagonal part of the array of an output of
Algorithm 8.3.1. Then $\hat T$ is symmetric and tridiagonal, and there are an orthogonal
$\tilde Q$ and a symmetric $E$ with
$$\hat T = \tilde Q^T (A + E) \tilde Q, \qquad \|E\|_F \le \frac{(n - 2) \epsilon}{1 - (n - 2)
  \epsilon} \|A\|_F.$$

The source states, after the algorithm, that "$\hat T = \tilde Q^T (A + E) \tilde Q$ where
$\tilde Q$ is exactly orthogonal and $E$ is a symmetric matrix satisfying
$\|E\|_F \le c u \|A\|_F$", referring to Wilkinson (*The Algebraic Eigenvalue Problem*, p. 297).
The theorem gives a rigorous constant, of order $n^2 u$. The constant is $\gamma_{n-2}$
evaluated at $\epsilon$ instead of $u$, with $\gamma_m(x) = mx/(1 - mx)$ the function
`FloatingPoint.gamma`.

**Reading.** The source leaves the small constant in its $cu\|A\|_F$ estimate unspecified. Lean
gives an explicit dimension-dependent coefficient and assumes idempotent rounding and the
stated smallness bounds. -/
theorem algorithm_8_3_1_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hcard : ((6 * (18 * n + 31) + 2 * n + 8 : ℕ) : ℝ) * fp.u < 1)
    (hr : ((n - 2 : ℕ) : ℝ) * (9 * gamma fp.u (6 * (18 * n + 31) + 2 * n + 8) +
      2 * gamma fp.u (n + 1)) < 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {out : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (h : out ∈ (algorithm_8_3_1 fp.round A).run) :
    (tridiagonalPart out.1)ᵀ = tridiagonalPart out.1 ∧ (tridiagonalPart out.1).IsTridiagonal ∧
      ∃ Q ∈ orthogonalGroup (Fin n) ℝ, ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧
        tridiagonalPart out.1 = Qᵀ * (A + E) * Q ∧
        ‖E‖ ≤ gamma (9 * gamma fp.u (6 * (18 * n + 31) + 2 * n + 8) + 2 * gamma fp.u (n + 1))
          (n - 2) * ‖A‖ := by
  have hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) fp.u_nonneg) hcard
  obtain ⟨Ahat, hlast, hpert⟩ := algorithm_8_3_1_rounds hfp hu A h
  have := exists_roundsTridiagonalizePert_eq hcard hr hA hpert
  rw [hlast] at this
  exact this

end Frobenius

/-! ### Algorithm 8.3.1: exact semantics -/

/-- The tridiagonal part of every matrix is tridiagonal. -/
theorem isTridiagonal_tridiagonalPart (A : Matrix (Fin n) (Fin n) ℝ) :
    (tridiagonalPart A).IsTridiagonal := by
  rintro i j (⟨l, h1, h2⟩ | ⟨l, h1, h2⟩) <;>
  · rw [Fin.lt_def] at h1 h2
    simp only [tridiagonalPart, of_apply]
    exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))

/-- A sum over the members of a list without duplicates is the sum along the list. -/
private theorem sum_subtype_mem {l : List (Fin n)} (hl : l.Nodup) (g : Fin n → ℝ) :
    ∑ j : {j // j ∈ l}, g j = (l.map g).sum := by
  rw [← List.sum_toFinset g hl, Finset.sum_subtype l.toFinset (fun _ => List.mem_toFinset) g]

/-- The exact run of one step of Algorithm 8.3.1, unpacked. -/
private theorem tridiagonalizeStep_pure (k : Fin n) (hk : (k : ℕ) + 1 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    let T := Chapter05.indexFrom n (k + 1)
    let vβ := Id.run (Chapter05.houseOn pure T (fun i => A i k))
    ∃ (p w : Fin n → ℝ) (L : Fin n × Fin n → ℝ),
      (∀ i, p i = if i ∈ T then vβ.2 * (T.map fun j => A i j * vβ.1 j).sum else 0) ∧
      (∀ i, w i = if i ∈ T then p i - vβ.2 * (T.map fun j => p j * vβ.1 j).sum / 2 * vβ.1 i
        else 0) ∧
      (∀ ij, L ij = if ij ∈ lowerPairs T then
        A ij.1 ij.2 - vβ.1 ij.1 * w ij.2 - w ij.1 * vβ.1 ij.2 else A ij.1 ij.2) ∧
      Id.run (tridiagonalizeStep pure k hk A) =
        (tridiagonalizeOut k hk A L √((T.map fun j => A j k * A j k).sum), vβ) := by
  intro T vβ
  refine ⟨_, _, _, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  simp only [tridiagonalizeStep, dotAccum_pure, pure_bind, zero_add, List.foldlM_pure,
    List.foldl_update_eq_ite]
  rfl

/-- One exact step of Algorithm 8.3.1 as a similarity: if the cleaned array $C = \hat A_k$ is
symmetric, $P = I - \beta v v^T$ with $v$ zero off $T = [k + 1, \dots, n - 1]$ and
$P x = c e_{k+1}$ on $T$ for the tail $x$ of column $k$, $w = p - (\beta p^T v / 2) v$ with
$p = \beta C v$ on $T$, $L$ the lower triangle of $C - v w^T - w v^T$ and $\nu = c$, then the
cleaned output of the step is $P C P$. -/
private theorem bandClean_tridiagonalizeOut {k : Fin n} (hk : (k : ℕ) + 1 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hC : (bandClean (k : ℕ) A).IsSymm) {v w : Fin n → ℝ} {β c : ℝ}
    (hv : ∀ i : Fin n, ¬ (k : ℕ) + 1 ≤ i → v i = 0)
    (hPx : ∀ i : Fin n, (k : ℕ) + 1 ≤ i →
      ((1 - β • vecMulVec v v) *ᵥ fun j => A j k) i = if i = ⟨k + 1, hk⟩ then c else 0)
    (hw : ∀ i : Fin n, (k : ℕ) + 1 ≤ i →
      w i = (β • (bandClean (k : ℕ) A *ᵥ v) -
        ((β * (v ⬝ᵥ β • (bandClean (k : ℕ) A *ᵥ v))) / 2) • v) i)
    {L : Fin n × Fin n → ℝ}
    (hL : ∀ i j : Fin n, (k : ℕ) + 1 ≤ i → (k : ℕ) + 1 ≤ j → j ≤ i →
      L (i, j) = A i j - v i * w j - w i * v j) {ν : ℝ} (hν : ν = c) :
    bandClean ((k : ℕ) + 1) (tridiagonalizeOut k hk A L ν) =
      (1 - β • vecMulVec v v) * bandClean (k : ℕ) A * (1 - β • vecMulVec v v) := by
  set C := bandClean (k : ℕ) A with hCdef
  have hPCP := householder_conj_eq_sub_rankTwo hC v β
  dsimp only at hPCP
  rw [hPCP]
  set wf := β • (C *ᵥ v) - ((β * (v ⬝ᵥ β • (C *ᵥ v))) / 2) • v with hwf
  have hCA : ∀ i j : Fin n, (k : ℕ) ≤ i → (k : ℕ) ≤ j → C i j = A i j :=
    fun i j hi hj => bandClean_apply_of_le A hi hj
  have hC0 : ∀ i j : Fin n, (j : ℕ) < k → (j : ℕ) + 2 ≤ i → C i j = 0 ∧ C j i = 0 := by
    intro i j hj hji
    exact ⟨bandClean_apply_eq_zero A (Or.inl ⟨hj, hji⟩),
      bandClean_apply_eq_zero A (Or.inr ⟨hj, hji⟩)⟩
  have hsym : ∀ i j, C i j = C j i := fun i j => hC.apply j i
  -- `C v` at an index `≤ k` only sees column `k`, through the tail
  have hCv : ∀ s : Fin n, (s : ℕ) ≤ k →
      (C *ᵥ v) s = if (s : ℕ) = k then v ⬝ᵥ (fun j => A j k) else 0 := by
    intro s hs
    rw [mulVec, dotProduct]
    split_ifs with hsk
    · rw [dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (k : ℕ) + 1 ≤ j
      · rw [hsym, hCA j s (by omega) (by omega), show s = k from Fin.ext hsk, mul_comm]
      · rw [hv j hj, mul_zero, zero_mul]
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (k : ℕ) + 1 ≤ j
      · rw [(hC0 j s (by omega) (by omega)).2, zero_mul]
      · rw [hv j hj, mul_zero]
  have hwfs : ∀ s : Fin n, (s : ℕ) ≤ k →
      wf s = β * (if (s : ℕ) = k then v ⬝ᵥ (fun j => A j k) else 0) := by
    intro s hs
    simp only [hwf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv s (by omega), mul_zero,
      sub_zero, hCv s hs]
  ext r s
  simp only [Matrix.sub_apply, vecMulVec_apply]
  by_cases hr : (k : ℕ) + 1 ≤ r <;> by_cases hs : (k : ℕ) + 1 ≤ s
  · -- the trailing block
    rw [bandClean_apply_of_le _ hr hs, tridiagonalizeOut, of_apply,
      ite_eq_left_of_eq_true _ _ (eq_true (And.intro hr hs)), ← hw r hr, ← hw s hs,
      hCA r s (by omega) (by omega)]
    split_ifs with hsr
    · rw [hL r s hr hs hsr]
    · rw [hL s r hs hr (le_of_not_ge hsr), ← hCA r s (by omega) (by omega), hsym,
        hCA s r (by omega) (by omega)]
      ring
  · -- the column block: column `k` becomes `c e_{k+1}`, the others stay `0`
    rw [hv s hs, mul_zero, sub_zero, hwfs s (by omega)]
    by_cases hsk : (s : ℕ) = k
    · have hs' : s = k := Fin.ext hsk
      subst hs'
      have h1 := hPx r hr
      rw [one_sub_smul_vecMulVec_mulVec_apply] at h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (s : ℕ) = s)), hCA r s (by omega) le_rfl,
        ← mul_assoc, mul_comm (v r) β, h1]
      by_cases hrk : r = ⟨s + 1, hk⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hrk), hrk, tridiagonalizeOut_succ_self, hν]
      · have hr2 : (s : ℕ) + 2 ≤ r := by
          have : (r : ℕ) ≠ s + 1 := fun h => hrk (Fin.ext h)
          omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hrk)]
        exact bandClean_apply_eq_zero (k := (s : ℕ) + 1) (i := r) (j := s) _
          (Or.inl ⟨Nat.lt_succ_self _, hr2⟩)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hsk), mul_zero, mul_zero, sub_zero,
        (hC0 r s (by omega) (by omega)).1]
      exact bandClean_apply_eq_zero (k := (k : ℕ) + 1) (i := r) (j := s) _
        (Or.inl ⟨by omega, by omega⟩)
  · -- the row block, by symmetry
    rw [hv r hr, zero_mul, sub_zero, hwfs r (by omega)]
    by_cases hrk : (r : ℕ) = k
    · have hr' : r = k := Fin.ext hrk
      subst hr'
      have h1 := hPx s hs
      rw [one_sub_smul_vecMulVec_mulVec_apply] at h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : (r : ℕ) = r)), hsym,
        hCA s r (by omega) le_rfl, mul_comm (β * _) (v s), ← mul_assoc, mul_comm (v s) β, h1]
      by_cases hsk : s = ⟨r + 1, hk⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hsk), hsk, tridiagonalizeOut_self_succ, hν]
      · have hs2 : (r : ℕ) + 2 ≤ s := by
          have : (s : ℕ) ≠ r + 1 := fun h => hsk (Fin.ext h)
          omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hsk)]
        exact bandClean_apply_eq_zero (k := (r : ℕ) + 1) (i := r) (j := s) _
          (Or.inr ⟨Nat.lt_succ_self _, hs2⟩)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hrk), mul_zero, zero_mul, sub_zero,
        (hC0 s r (by omega) (by omega)).2]
      exact bandClean_apply_eq_zero (k := (k : ℕ) + 1) (i := r) (j := s) _
        (Or.inr ⟨by omega, by omega⟩)
  · -- the leading block is untouched
    rw [hv r hr, hv s hs, zero_mul, mul_zero, sub_zero, sub_zero]
    have hnν : ¬ ((r = ⟨k + 1, hk⟩ ∧ s = k) ∨ (r = k ∧ s = ⟨k + 1, hk⟩)) := by
      rintro (⟨rfl, -⟩ | ⟨-, rfl⟩) <;> simp at hr hs
    simp only [hCdef, bandClean, tridiagonalizeOut, of_apply]
    rw [ite_eq_right_of_eq_false _ _
      (eq_false (show ¬ ((k : ℕ) + 1 ≤ r ∧ (k : ℕ) + 1 ≤ s) by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false hnν)]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- For a symmetric cleaned array $\hat A_k$, the exact step $k$ of Algorithm 8.3.1 returns
reflector data $(v, \beta)$ with $v$ zero on the coordinates $\le k$ and $\beta = 0$ or
$\beta v^T v = 2$, and its cleaned output is $P \hat A_k P$ with $P = I - \beta v v^T$. -/
private theorem tridiagonalizeStep_conj (k : Fin n) (hk : (k : ℕ) + 1 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hC : (bandClean (k : ℕ) A).IsSymm) :
    bandClean ((k : ℕ) + 1) (Id.run (tridiagonalizeStep pure k hk A)).1 =
        (1 - (Id.run (tridiagonalizeStep pure k hk A)).2.2 •
          vecMulVec (Id.run (tridiagonalizeStep pure k hk A)).2.1
            (Id.run (tridiagonalizeStep pure k hk A)).2.1) * bandClean (k : ℕ) A *
        (1 - (Id.run (tridiagonalizeStep pure k hk A)).2.2 •
          vecMulVec (Id.run (tridiagonalizeStep pure k hk A)).2.1
            (Id.run (tridiagonalizeStep pure k hk A)).2.1) ∧
      (∀ i : Fin n, ¬ (k : ℕ) + 1 ≤ i → (Id.run (tridiagonalizeStep pure k hk A)).2.1 i = 0) ∧
      ((Id.run (tridiagonalizeStep pure k hk A)).2.2 = 0 ∨
        (Id.run (tridiagonalizeStep pure k hk A)).2.2 *
          ((Id.run (tridiagonalizeStep pure k hk A)).2.1 ⬝ᵥ
            (Id.run (tridiagonalizeStep pure k hk A)).2.1) = 2) := by
  obtain ⟨p, w, L, hp, hw, hL, heq⟩ := tridiagonalizeStep_pure k hk A
  rw [heq]
  dsimp only
  set T := Chapter05.indexFrom n (k + 1) with hTdef
  have hT : T.Nodup := Chapter05.nodup_indexFrom n (k + 1)
  have hmemT : ∀ i : Fin n, i ∈ T ↔ (k : ℕ) + 1 ≤ i := fun i => Chapter05.mem_indexFrom
  have hne : T ≠ [] := List.ne_nil_of_mem ((hmemT ⟨k + 1, hk⟩).2 le_rfl)
  obtain ⟨-, hvT, hβ, -, hPx⟩ := Chapter05.houseOn_spec hT hne (fun i => A i k)
  rw [Chapter05.head_indexFrom hk hne] at hPx
  set vβ := Id.run (Chapter05.houseOn pure T (fun i => A i k)) with hvβ
  set v := vβ.1
  set β := vβ.2
  set C := bandClean (k : ℕ) A with hCdef
  have hv : ∀ i : Fin n, ¬ (k : ℕ) + 1 ≤ i → v i = 0 := fun i hi => hvT i (by rwa [hmemT])
  have hCA : ∀ i j : Fin n, (k : ℕ) + 1 ≤ i → (k : ℕ) + 1 ≤ j → C i j = A i j :=
    fun i j hi hj => bandClean_apply_of_le A (by omega) (by omega)
  -- `p = β C v` on the tail
  have hCv : ∀ i : Fin n, (k : ℕ) + 1 ≤ i → (C *ᵥ v) i = (T.map fun j => A i j * v j).sum := by
    intro i hi
    rw [mulVec, dotProduct, Chapter05.sum_eq_sum_map_of_nodup hT
      (fun j hj => by rw [hv j (by rwa [← hmemT]), mul_zero])]
    exact congrArg List.sum (List.map_congr_left fun j hj => by
      rw [hCA i j hi ((hmemT j).1 hj)])
  have hpC : ∀ i : Fin n, (k : ℕ) + 1 ≤ i → p i = β * (C *ᵥ v) i := fun i hi => by
    rw [hp, ite_eq_left_of_eq_true _ _ (eq_true ((hmemT i).2 hi)), hCv i hi]
  refine ⟨bandClean_tridiagonalizeOut hk hC hv (w := w) (L := L) (c := ‖(WithLp.toLp 2
      (fun j : {j // j ∈ T} => A j k) : EuclideanSpace ℝ {j // j ∈ T})‖) (fun i hi => ?_)
    (fun i hi => ?_) (fun i j hi hj hji => ?_) ?_, hv, hβ⟩
  · rw [hPx]
    simp only [(hmemT i).2 hi, ite_true]
  · have hvp : v ⬝ᵥ β • (C *ᵥ v) = (T.map fun j => p j * v j).sum := by
      rw [dotProduct, Chapter05.sum_eq_sum_map_of_nodup hT
        (fun j hj => by rw [hv j (by rwa [← hmemT]), zero_mul])]
      refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
      rw [hpC j ((hmemT j).1 hj), Pi.smul_apply, smul_eq_mul]
      ring
    rw [hw, ite_eq_left_of_eq_true _ _ (eq_true ((hmemT i).2 hi)), hpC i hi]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hCdef, hvp]
  · rw [hL, ite_eq_left_of_eq_true _ _
      (eq_true (mem_lowerPairs.2 ⟨(hmemT i).2 hi, (hmemT j).2 hj, hji⟩))]
  · rw [EuclideanSpace.norm_eq]
    congr 1
    rw [sum_subtype_mem hT (fun j => ‖A j k‖ ^ 2)]
    exact congrArg List.sum (List.map_congr_left fun j _ => by
      rw [Real.norm_eq_abs, sq_abs, sq])

/-- The loop invariant of Algorithm 8.3.1 after $j$ steps: the cleaned array is $Q^T A Q$ for the
product $Q$ of the reflector data so far, there are $j$ reflectors, the $k$-th vanishes on the
coordinates $\le k$, and each has $\beta = 0$ or $\beta v^T v = 2$, so that its matrix is the
identity or a Householder matrix. -/
private def TridiagonalizeInv (A : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) : Prop :=
  bandClean j st.1 = (Chapter05.householderProduct st.2)ᵀ * A *
      Chapter05.householderProduct st.2 ∧ st.2.length = j ∧
    (∀ (k : ℕ) (hk : k < st.2.length) (i : Fin n), (i : ℕ) ≤ k → st.2[k].1 i = 0) ∧
    ∀ q ∈ st.2, q.2 = 0 ∨ q.2 * (q.1 ⬝ᵥ q.1) = 2

/-- For symmetric $A$, the loop invariant of Algorithm 8.3.1 holds after the $n - 2$ exact steps. -/
private theorem tridiagonalizeInv_run {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    TridiagonalizeInv A (n - 2) (Id.run (algorithm_8_3_1 pure A)) := by
  have hsymm : ∀ Q : Matrix (Fin n) (Fin n) ℝ, (Qᵀ * A * Q).IsSymm := fun Q => by
    exact hA.transpose_mul_mul Q
  refine List.idRun_foldlM_finRange_induction (TridiagonalizeInv A)
    ⟨by simp [bandClean_zero], rfl, fun k hk => absurd hk (Nat.not_lt_zero _),
      fun q hq => absurd hq List.not_mem_nil⟩ ?_
  rintro k st ⟨hband, hlen, hsupp, hβ⟩
  set k' : Fin n := k.castLE (Nat.sub_le n 2)
  have hk' : (k' : ℕ) + 1 < n := by simp only [k', Fin.val_castLE]; omega
  have hband' : bandClean (k' : ℕ) st.1 = (Chapter05.householderProduct st.2)ᵀ * A *
      Chapter05.householderProduct st.2 := hband
  have hC : (bandClean (k' : ℕ) st.1).IsSymm := by
    rw [hband']
    exact hsymm _
  obtain ⟨hconj, hv, hβ'⟩ := tridiagonalizeStep_conj k' hk' hC
  set r := Id.run (tridiagonalizeStep pure k' hk' st.1) with hr
  change TridiagonalizeInv A (k + 1) (r.1, st.2 ++ [r.2])
  refine ⟨hconj.trans ?_, ?_, fun l hl i hi => ?_, fun q hq => ?_⟩
  · rw [hband', Chapter05.householderProduct_concat, transpose_mul,
      transpose_one_sub_smul_vecMulVec]
    simp only [Matrix.mul_assoc]
  · rw [List.length_append, hlen, List.length_singleton]
  · rw [List.length_append, List.length_singleton] at hl
    rcases Nat.lt_or_ge l st.2.length with hl' | hl'
    · rw [List.getElem_append_left hl']
      exact hsupp l hl' i hi
    · rw [List.getElem_append_right hl']
      simp only [List.getElem_singleton]
      exact hv i (by simp only [k', Fin.val_castLE]; omega)
  · rcases List.mem_append.1 hq with hq | hq
    · exact hβ q hq
    · rw [List.mem_singleton.1 hq]
      exact hβ'

/-- **Algorithm 8.3.1** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, let $(A', \mathrm{data})$ be the output of Algorithm 8.3.1 in exact arithmetic,
and let $Q = P_0 \cdots P_{n-3}$ be the product of the matrices $P_k = I - \beta_k v_k v_k^T$ of
the returned data. Then:
* $Q$ is orthogonal, and $Q e_1 = e_1$ when $n \ge 1$;
* $T = Q^T A Q$ is symmetric and tridiagonal, and it is the tridiagonal part of $A'$;
* there are $n - 2$ reflectors, and $v_k$ vanishes on the coordinates $0, \dots, k$ (0-based),
  so that $P_k$ acts on the coordinates $\ge k + 1$.

The product is `GolubVanLoan.Chapter05.householderProduct data`, built from the returned
$\beta_k$. The entries of $A'$ below the subdiagonal hold the untouched vectors
$A_k(k{+}2{:}n, k)$. The proof is a loop invariant: after step $k$ the cleaned array is
$(P_0 \cdots P_k)^T A (P_0 \cdots P_k)$. Each step is $P C P$ by
`GolubVanLoan.Chapter08.householder_conj_eq_sub_rankTwo` with
`GolubVanLoan.Chapter05.houseOn_spec`, whose $P x = \|x\|_2 e_1$ makes the new norm the exact
subdiagonal entry.

**Reading.** The source describes overwriting $A$ with $T$ and using its subdiagonal storage
for reflectors. The Lean factorization reads $T$ from the returned band and builds $Q$ from a
separate list. -/
theorem algorithm_8_3_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    let out := Id.run (algorithm_8_3_1 pure A)
    let Q := Chapter05.householderProduct out.2
    Q ∈ orthogonalGroup (Fin n) ℝ ∧
      (∀ h : 0 < n, Q *ᵥ Pi.single ⟨0, h⟩ 1 = Pi.single ⟨0, h⟩ 1) ∧
      (Qᵀ * A * Q).IsSymm ∧ (Qᵀ * A * Q).IsTridiagonal ∧ tridiagonalPart out.1 = Qᵀ * A * Q ∧
      out.2.length = n - 2 ∧
      ∀ (k : ℕ) (hk : k < out.2.length) (i : Fin n), (i : ℕ) ≤ k → out.2[k].1 i = 0 := by
  intro out Q
  obtain ⟨hband, hlen, hsupp, hβ⟩ := tridiagonalizeInv_run hA
  rw [bandClean_eq_tridiagonalPart] at hband
  refine ⟨Chapter05.householderProduct_mem_orthogonalGroup hβ,
    fun h => Chapter05.householderProduct_mulVec_single fun q hq => ?_, ?_, ?_, hband, hlen, hsupp⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    exact hsupp k hk _ (Nat.zero_le _)
  · exact hA.transpose_mul_mul Q
  · rw [← hband]
    exact isTridiagonal_tridiagonalPart _

/-- **Section 8.3.1** of [golub2013matrix], unreduced tridiagonal matrices. A tridiagonal
$T \in \mathbb{R}^{n \times n}$ is **unreduced** if no subdiagonal entry vanishes:
$t_{i+1,i} \neq 0$ for $i = 1, \dots, n - 1$.

The definition is `Matrix.IsTridiagonal` together with `Matrix.IsUnreducedUpperHessenberg`. -/
def IsUnreducedTridiagonal (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  T.IsTridiagonal ∧ T.IsUnreducedUpperHessenberg

/-- **Section 8.3.1** of [golub2013matrix], splitting. Let $T \in \mathbb{R}^{n \times n}$ be
tridiagonal with $n = (k + 1) + (l + 1)$, and let $t_{k+2,k+1} = t_{k+1,k+2} = 0$. Then
$$T = \begin{bmatrix} T_1 & 0 \\ 0 & T_2 \end{bmatrix}, \qquad T_1 = T(1{:}k{+}1, 1{:}k{+}1),
  \quad T_2 = T(k{+}2{:}n, k{+}2{:}n),$$
and $\det(\lambda I - T) = \det(\lambda I - T_1) \det(\lambda I - T_2)$, so that
$\lambda(T) = \lambda(T_1) \cup \lambda(T_2)$ with multiplicity.

The block form is stated after reindexing $T$ by `finSumFinEquiv` to
`Fin (k + 1) ⊕ Fin (l + 1)`. The two zero entries are at the 0-based positions $(k + 1, k)$ and
$(k, k + 1)$.

**Generalization.** The source splits a symmetric tridiagonal matrix at a zero subdiagonal
entry. Lean permits nonsymmetric tridiagonal matrices when both cross-boundary entries vanish
and uses a characteristic-polynomial product, preserving multiplicities. -/
theorem tridiagonal_spectrum_split {k l : ℕ}
    {T : Matrix (Fin (k + 1 + (l + 1))) (Fin (k + 1 + (l + 1))) ℝ} (hT : T.IsTridiagonal)
    (h₁ : T (Fin.natAdd (k + 1) 0) (Fin.castAdd (l + 1) (Fin.last k)) = 0)
    (h₂ : T (Fin.castAdd (l + 1) (Fin.last k)) (Fin.natAdd (k + 1) 0) = 0) :
    T.submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks (T.submatrix (Fin.castAdd (l + 1)) (Fin.castAdd (l + 1))) 0 0
          (T.submatrix (Fin.natAdd (k + 1)) (Fin.natAdd (k + 1))) ∧
      T.charpoly = (T.submatrix (Fin.castAdd (l + 1)) (Fin.castAdd (l + 1))).charpoly *
        (T.submatrix (Fin.natAdd (k + 1)) (Fin.natAdd (k + 1))).charpoly := by
  have hblock : T.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (T.submatrix (Fin.castAdd (l + 1)) (Fin.castAdd (l + 1))) 0 0
        (T.submatrix (Fin.natAdd (k + 1)) (Fin.natAdd (k + 1))) := by
    ext (i | i) (j | j)
    · rfl
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₁₂, Matrix.zero_apply]
      by_cases hij : (i : ℕ) = k ∧ (j : ℕ) = 0
      · have hi : i = Fin.last k := Fin.ext hij.1
        have hj : j = 0 := Fin.ext hij.2
        rw [hi, hj]; exact h₂
      · refine hT _ _ (Or.inr ⟨⟨i + 1, by omega⟩, ?_, ?_⟩)
        · simp [Fin.lt_def]
        · simp only [Fin.lt_def, Fin.val_natAdd]; omega
    · simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      by_cases hij : (i : ℕ) = 0 ∧ (j : ℕ) = k
      · have hi : i = 0 := Fin.ext hij.1
        have hj : j = Fin.last k := Fin.ext hij.2
        rw [hi, hj]; exact h₁
      · refine hT _ _ (Or.inl ⟨⟨j + 1, by omega⟩, ?_, ?_⟩)
        · simp [Fin.lt_def]
        · simp only [Fin.lt_def, Fin.val_natAdd]; omega
    · rfl
  refine ⟨hblock, ?_⟩
  rw [← charpoly_fromBlocks_zero₁₂, ← hblock]
  exact (charpoly_reindex finSumFinEquiv.symm T).symm

/-! ### Properties of the tridiagonal decomposition (§8.3.2) -/

/-- **Theorem 8.3.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, let
$Q$ be orthogonal with $T = Q^T A Q$ tridiagonal, and let $R = Q^T K(A, Q(:, 1), n)$, where
$K(A, v, n) = [v \,|\, Av \,|\, \cdots \,|\, A^{n-1} v]$ is the Krylov matrix. Then $R$ is upper
triangular, $r_{11} = 1$ and $r_{i+1,i+1} = t_{i+1,i} r_{ii}$ for $i = 1, \dots, n - 1$, so that
$$r_{ii} = t_{21} t_{32} \cdots t_{i,i-1}.$$
If $R$ is nonsingular, then $T$ is unreduced. If $R$ is singular and $k$ is the smallest index
with $r_{kk} = 0$, then $k \ge 2$ and $k$ is the smallest index with $t_{k,k-1} = 0$.

The Krylov matrix is `GolubVanLoan.Chapter07.krylovMatrix`, and $n = N + 1$. In the last
statement, with 0-based indices, $k = i + 1$ for the first $i$ with $t_{i+1,i} = 0$. The matrix
$A$ need not be symmetric. The proof uses $Q^T K(A, Q e_1, n) = K(T, e_1, n)$, whose column
$T^j e_1$ is supported on the first $j + 1$ coordinates with last entry
$t_{21} \cdots t_{j+1,j}$.

**Generalization.** The source assumes symmetric $A$ as well as a tridiagonal reduction. The
Lean theorem needs only the tridiagonal reduction for its Krylov conclusions. -/
theorem theorem_8_3_1 {N : ℕ} {A Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hT : (Qᵀ * A * Q).IsTridiagonal) :
    (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)).IsUpperTriangular ∧
      (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)) 0 0 = 1 ∧
      (∀ i : Fin N, (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)) i.succ i.succ =
        (Qᵀ * A * Q) i.succ i.castSucc *
          (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)) i.castSucc i.castSucc) ∧
      (IsUnit (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)).det →
        IsUnreducedTridiagonal (Qᵀ * A * Q)) ∧
      (∀ k : Fin (N + 1), (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)) k k = 0 →
        (∀ j < k, (Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1)) j j ≠ 0) →
        ∃ i : Fin N, i.succ = k ∧ (Qᵀ * A * Q) i.succ i.castSucc = 0 ∧
          ∀ i' : Fin N, i' < i → (Qᵀ * A * Q) i'.succ i'.castSucc ≠ 0) := by
  have hR : Qᵀ * Chapter07.krylovMatrix A (Q.col 0) (N + 1) =
      krylovMatrix (Qᵀ * A * Q) (Pi.single 0 1) (N + 1) := by
    have h := conjTranspose_mul_krylovMatrix hQ A (Pi.single 0 1) (N + 1)
    rwa [mulVec_single_one, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  have hH := hT.isUpperHessenberg
  rw [hR]
  refine ⟨hH.isUpperTriangular_krylovMatrix, krylovMatrix_single_zero_zero _,
    hH.krylovMatrix_succ_succ, fun hu => ⟨hT, ?_⟩, fun k hk hmin => ?_⟩
  · exact (Chapter07.theorem_7_4_3 hQ A).2
      (by rwa [hR, and_iff_right hH.isUpperTriangular_krylovMatrix])
  · induction k using Fin.cases with
    | zero => rw [krylovMatrix_single_zero_zero] at hk; exact absurd hk one_ne_zero
    | succ i =>
      refine ⟨i, rfl, ?_, fun i' hi' => ?_⟩
      · rw [hH.krylovMatrix_succ_succ] at hk
        exact (mul_eq_zero.1 hk).resolve_right (hmin _ Fin.castSucc_lt_succ)
      · have h1 := hmin i'.succ (Fin.succ_lt_succ_iff.2 hi')
        rw [hH.krylovMatrix_succ_succ] at h1
        exact left_ne_zero_of_mul h1

/-- **Theorem 8.3.2** of [golub2013matrix] (implicit Q theorem, tridiagonal form). Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $Q = [q_1 | \cdots | q_n]$ and
$V = [v_1 | \cdots | v_n]$ be orthogonal with $T = Q^T A Q$ and $S = V^T A V$ tridiagonal and
$q_1 = v_1$. Let $1 \le k \le n$ with $t_{i+1,i} \neq 0$ for $i = 1, \dots, k - 1$; this holds
for the smallest $k$ with $t_{k+1,k} = 0$, and for $k = n$ if $T$ is unreduced. Then
* $v_i = \pm q_i$ for $i = 1, \dots, k$;
* $|s_{i,i-1}| = |t_{i,i-1}|$ for $i = 2, \dots, k$;
* if $k < n$ and $t_{k+1,k} = 0$, then $s_{k+1,k} = 0$.

**Generalization.** The source assumes symmetry of $A$ and tridiagonality of $T$ and $S$.
The Lean theorem only uses tridiagonality of $T$ and $S$.

The Lean index `k` is the $k - 1$ of this statement, and all indices are 0-based. The theorem is
Theorem 7.4.2 (`GolubVanLoan.Chapter07.theorem_7_4_2`) for the tridiagonal, hence upper
Hessenberg, matrices $T$ and $S$. -/
theorem theorem_8_3_2 {N : ℕ} {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hT : (Qᵀ * A * Q).IsTridiagonal) (hS : (Vᵀ * A * V).IsTridiagonal) (h0 : V.col 0 = Q.col 0)
    {k : ℕ} (hk : k ≤ N) (hsub : ∀ i : Fin N, (i : ℕ) < k → (Qᵀ * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → V.col i = Q.col i ∨ V.col i = -Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        |(Vᵀ * A * V) i.succ i.castSucc| = |(Qᵀ * A * Q) i.succ i.castSucc|) ∧
      (∀ i : Fin N, (i : ℕ) = k → (Qᵀ * A * Q) i.succ i.castSucc = 0 →
        (Vᵀ * A * V) i.succ i.castSucc = 0) :=
  Chapter07.theorem_7_4_2 hQ hV hT.isUpperHessenberg hS.isUpperHessenberg h0 hk hsub

/-! ### The QR iteration and tridiagonal matrices (§8.3.3) -/

/-- **Section 8.3.3** of [golub2013matrix], preservation of form. Let
$T \in \mathbb{R}^{n \times n}$ be symmetric and tridiagonal, and let $T = QR$ with $Q$
orthogonal and $R$ upper triangular. Assume that $T$ is nonsingular or that $(Q, R)$ is the
Givens QR factorization `Matrix.hessenbergGivensQR T`. Then $Q$ is upper Hessenberg (lower
bandwidth $1$), $R$ has upper bandwidth $2$, and
$$T_+ = RQ = Q^T T Q$$
is symmetric and tridiagonal.

**Correction.** The source states the claim for every QR factorization. For singular $T$ the
orthogonal factor is not unique, and the claim fails: $T = 0 = Q \cdot 0$ for every orthogonal
$Q$, which need not be upper Hessenberg. The theorem assumes that $T$ is nonsingular or that the
factorization is the Givens one. -/
theorem qr_tridiagonal_preservation {T Q R : Matrix (Fin n) (Fin n) ℝ} (hTs : T.IsSymm)
    (hT : T.IsTridiagonal) (hcase : IsUnit T.det ∨ (Q, R) = hessenbergGivensQR T)
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R.IsUpperTriangular) (hQR : T = Q * R) :
    Q.HasLowerBandwidth 1 ∧ R.HasUpperBandwidth 2 ∧ R * Q = Qᵀ * T * Q ∧
      (R * Q).IsSymm ∧ (R * Q).IsTridiagonal := by
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQH : Q.IsUpperHessenberg := by
    rcases hcase with hdet | hG
    · exact hT.isUpperHessenberg.isUpperHessenberg_of_eq_mul hdet hR hQR
    · rw [show Q = (hessenbergGivensQR T).1 by rw [← hG]]
      exact (hessenbergGivensQR_spec hT.isUpperHessenberg).2.2.2
  have hRQ : R * Q = Qᵀ * T * Q := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hsym : (R * Q).IsSymm := by
    rw [hRQ]
    exact hTs.transpose_mul_mul Q
  have hRQH : (R * Q).IsUpperHessenberg := hR.mul_isUpperHessenberg hQH
  refine ⟨isUpperHessenberg_iff_hasLowerBandwidth_one.1 hQH, ?_, hRQ, hsym,
    hRQH.isTridiagonal_of_isSymm hsym⟩
  -- `R = Qᵀ T`, a product of upper bandwidths `1` and `1`
  have hRe : R = Qᵀ * T := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQt : Qᵀ.HasUpperBandwidth 1 := by
    rw [← hasLowerBandwidth_transpose_iff, transpose_transpose]
    exact isUpperHessenberg_iff_hasLowerBandwidth_one.1 hQH
  have hTu : T.HasUpperBandwidth 1 := by
    rw [← hasLowerBandwidth_transpose_iff, hTs.eq]
    exact isUpperHessenberg_iff_hasLowerBandwidth_one.1 hT.isUpperHessenberg
  rw [hRe]
  exact hQt.mul hTu

/-- **Section 8.3.3** of [golub2013matrix], shifts. Let $T \in \mathbb{R}^{n \times n}$ be symmetric
and tridiagonal, let $s \in \mathbb{R}$, and let $T - sI = QR$ with $Q$ orthogonal and $R$ upper
triangular. Assume that $T - sI$ is nonsingular or that $(Q, R)$ is the Givens QR factorization
of $T - sI$. Then
$$T_+ = RQ + sI = Q^T T Q$$
is symmetric and tridiagonal.

**Correction.** As for `GolubVanLoan.Chapter08.qr_tridiagonal_preservation`, the claim of the
source for every QR factorization fails when $T - sI$ is singular; the theorem assumes
nonsingularity or the Givens factorization. -/
theorem shifted_qr_tridiagonal {T Q R : Matrix (Fin n) (Fin n) ℝ} (hTs : T.IsSymm)
    (hT : T.IsTridiagonal) {s : ℝ}
    (hcase : IsUnit (T - s • 1).det ∨ (Q, R) = hessenbergGivensQR (T - s • 1))
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R.IsUpperTriangular) (hQR : T - s • 1 = Q * R) :
    R * Q + s • 1 = Qᵀ * T * Q ∧ (R * Q + s • 1).IsSymm ∧ (R * Q + s • 1).IsTridiagonal := by
  have hTs' : (T - s • 1).IsSymm := by
    rw [IsSymm, transpose_sub, transpose_smul, transpose_one, hTs.eq]
  have hT' : (T - s • 1).IsTridiagonal := fun i j hij => by
    rw [Matrix.sub_apply, hT i j hij, Matrix.smul_apply, one_apply_ne, smul_zero, sub_zero]
    rintro rfl
    rcases hij with ⟨c, h1, h2⟩ | ⟨c, h1, h2⟩ <;> exact lt_asymm h1 h2
  obtain ⟨-, -, hRQ, hsym, htri⟩ := qr_tridiagonal_preservation hTs' hT' hcase hQ hR hQR
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [hRQ, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
      hQQ, sub_add_cancel]
  · rw [IsSymm, transpose_add, hsym.eq, transpose_smul, transpose_one]
  · intro i j hij
    rw [Matrix.add_apply, htri i j hij, Matrix.smul_apply, one_apply_ne, smul_zero, add_zero]
    rintro rfl
    rcases hij with ⟨c, h1, h2⟩ | ⟨c, h1, h2⟩ <;> exact lt_asymm h1 h2

/-- **Section 8.3.3** of [golub2013matrix], perfect shifts. Let $T \in \mathbb{R}^{n \times n}$ with
$n \ge 1$ be symmetric, tridiagonal and unreduced, and let $s \in \mathbb{R}$. Then the first
$n - 1$ columns of $T - sI$ are linearly independent. If moreover $s$ is an eigenvalue of $T$
and $T - sI = QR$ is any factorization with $Q$ orthogonal and $R$ upper triangular, then
$r_{nn} = 0$ and the last column of $T_+ = RQ + sI$ is $s e_n$. -/
theorem perfect_shift {N : ℕ} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hTs : T.IsSymm)
    (hT : IsUnreducedTridiagonal T) (s : ℝ) :
    LinearIndependent ℝ (fun j : Fin N => (T - s • 1).col j.castSucc) ∧
      (s ∈ spectrum ℝ T → ∀ Q R : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
        Q ∈ orthogonalGroup _ ℝ → R.IsUpperTriangular → T - s • 1 = Q * R →
          R (Fin.last N) (Fin.last N) = 0 ∧
            ∀ i, (R * Q + s • 1) i (Fin.last N) = if i = Fin.last N then s else 0) := by
  have hli := (hT.2.sub_smul_one s).linearIndependent_init_cols
  refine ⟨hli, fun hs Q R hQ hR hQR => ?_⟩
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQdet : Q.det ≠ 0 := by
    intro h
    have := congrArg det hQQ
    rw [det_mul, det_transpose, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hdet0 : (T - s • 1).det = 0 := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, eval_charpoly] at hs
    have e : T - s • 1 = -(scalar (Fin (N + 1)) s - T) := by
      rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
    rw [e, det_neg, hs, mul_zero]
  have hRdet : R.det = 0 := by
    rw [hQR, det_mul] at hdet0
    exact (mul_eq_zero.1 hdet0).resolve_left hQdet
  -- the first `N` columns of `R` are independent, and supported in the first `N` rows
  have hliR : LinearIndependent ℝ (fun j : Fin N => R.col j.castSucc) := by
    refine LinearIndependent.of_comp Q.mulVecLin ?_
    convert hli using 1
    funext j
    simp [hQR, col_mul_eq_mulVec_col]
  set R' := R.submatrix Fin.castSucc Fin.castSucc
  set P : Matrix (Fin (N + 1)) (Fin N) ℝ := (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).submatrix
    id Fin.castSucc
  have hcolR : ∀ j : Fin N, R.col j.castSucc = P *ᵥ R'.col j := fun j => by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · have h0 : R (Fin.last N) j.castSucc = 0 := hR (Fin.castSucc_lt_last j)
      simp [P, R', col_apply, mulVec, dotProduct, h0,
        (Fin.castSucc_ne_last _).symm]
    · simp [P, R', col_apply, mulVec, dotProduct, Matrix.one_apply, Fin.castSucc_inj]
  have hliR' : LinearIndependent ℝ (fun j : Fin N => R'.col j) := by
    refine LinearIndependent.of_comp P.mulVecLin ?_
    convert hliR using 1
    funext j
    simp [hcolR]
  have hR'det : R'.det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).1 (linearIndependent_col_iff_isUnit.1 hliR')).ne_zero
  have hRtri : R'.IsUpperTriangular := fun i j hij => hR (Fin.castSucc_lt_castSucc_iff.2 hij)
  have hlast : R (Fin.last N) (Fin.last N) = 0 := by
    rw [det_of_isUpperTriangular hR, Fin.prod_univ_castSucc] at hRdet
    rw [det_of_isUpperTriangular hRtri] at hR'det
    exact (mul_eq_zero.1 hRdet).resolve_left hR'det
  refine ⟨hlast, fun i => ?_⟩
  have hrow : ∀ j, R (Fin.last N) j = 0 := fun j => by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · exact hR (Fin.castSucc_lt_last j)
    · exact hlast
  have hsym : (R * Q + s • 1).IsSymm := by
    have e : R * Q + s • 1 = Qᵀ * T * Q := by
      have hRe : R = Qᵀ * (T - s • 1) := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      rw [hRe, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
        hQQ, sub_add_cancel]
    rw [e]
    exact hTs.transpose_mul_mul Q
  rw [← hsym.apply]
  by_cases hi : i = Fin.last N
  · subst hi
    simp [Matrix.add_apply, Matrix.mul_apply, hrow]
  · simp [Matrix.add_apply, Matrix.mul_apply, hrow, hi, Ne.symm hi]

/-! ### Explicit single-shift QR iteration (§8.3.4) -/

/-- **Equation (8.3.3)** of [golub2013matrix], the Wilkinson shift. Let
$T \in \mathbb{R}^{n \times n}$ with $n \ge 2$, and let the trailing $2 \times 2$ block of $T$
be $\begin{bmatrix} a_{n-1} & b_{n-1} \\ b_{n-1} & a_n \end{bmatrix}$. The **Wilkinson shift**
is
$$\mu = a_n + d - \operatorname{sign}(d) \sqrt{d^2 + b_{n-1}^2}, \qquad d = (a_{n-1} - a_n)/2,$$
with $\operatorname{sign}(0) = 1$.

**Reading.** The source does not fix $\operatorname{sign}(0)$. The value
$\operatorname{sign}(0) = 1$ makes $\mu$ an eigenvalue of the trailing block also when $d = 0$.

The entry $b_{n-1}$ is read below the diagonal, as $t_{n,n-1}$; $T$ need not be symmetric for
the definition. The order is $n = N + 2$. -/
noncomputable def wilkinsonShift {N : ℕ} (T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : ℝ :=
  let a := T (Fin.last (N + 1)) (Fin.last (N + 1))
  let a' := T (Fin.last N).castSucc (Fin.last N).castSucc
  let b := T (Fin.last (N + 1)) (Fin.last N).castSucc
  let d := (a' - a) / 2
  a + d - (if 0 ≤ d then 1 else -1) * Real.sqrt (d ^ 2 + b ^ 2)

/-- **Equation (8.3.3)** of [golub2013matrix]. Let $T \in \mathbb{R}^{n \times n}$ with $n \ge 2$,
and let $a = t_{nn}$, $a' = t_{n-1,n-1}$, $b = t_{n,n-1}$, $d = (a' - a)/2$ and
$\sigma = \operatorname{sign}(d)$, with $\operatorname{sign}(0) = 1$. Then the Wilkinson shift
$\mu$ satisfies:
* $(\mu - a')(\mu - a) - b^2 = 0$, so $\mu$ is an eigenvalue of
  $\begin{bmatrix} a' & b \\ b & a \end{bmatrix}$;
* $|\mu - a| \le |\mu' - a|$ for the other root $\mu' = a + d + \sigma \sqrt{d^2 + b^2}$, so
  $\mu$ is the eigenvalue closer to $a$;
* $\mu = a - b^2 / (d + \sigma \sqrt{d^2 + b^2})$, the form that Algorithm 8.3.2 computes.

**Reading.** Proves the eigenvalue equation, distance comparison and rationalized form with explicit
tie convention.
-/
theorem equation_8_3_3 {N : ℕ} (T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) :
    let a := T (Fin.last (N + 1)) (Fin.last (N + 1))
    let a' := T (Fin.last N).castSucc (Fin.last N).castSucc
    let b := T (Fin.last (N + 1)) (Fin.last N).castSucc
    let d := (a' - a) / 2
    let σ : ℝ := if 0 ≤ d then 1 else -1
    (wilkinsonShift T - a') * (wilkinsonShift T - a) - b ^ 2 = 0 ∧
      |wilkinsonShift T - a| ≤ |(a + d + σ * Real.sqrt (d ^ 2 + b ^ 2)) - a| ∧
      wilkinsonShift T = a - b ^ 2 / (d + σ * Real.sqrt (d ^ 2 + b ^ 2)) := by
  intro a a' b d σ
  have hμ : wilkinsonShift T = a + d - σ * Real.sqrt (d ^ 2 + b ^ 2) := rfl
  have ha' : a' = a + 2 * d := by simp only [d]; ring
  have hσ : σ ^ 2 = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσa : |σ| = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσd : 0 ≤ σ * d := by
    simp only [σ]; split_ifs with h
    · linarith
    · nlinarith
  rw [hμ]
  clear_value σ d b a' a
  set S := Real.sqrt (d ^ 2 + b ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS : S ^ 2 = d ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [ha']
    linear_combination S ^ 2 * hσ + hSS
  · have e1 : a + d - σ * S - a = σ * (σ * d - S) := by linear_combination (-d) * hσ
    have e2 : a + d + σ * S - a = σ * (σ * d + S) := by linear_combination (-d) * hσ
    rw [e1, e2, abs_mul, abs_mul, hσa, one_mul, one_mul, abs_of_nonneg (add_nonneg hσd hS0)]
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · by_cases hden : d + σ * S = 0
    · have hd0 : σ * d + S = 0 := by linear_combination σ * hden - S * hσ
      have hSz : S = 0 := by linarith
      have hdz : σ * d = 0 := by linarith
      have hdz' : d = 0 := by
        have : σ ^ 2 * d = 0 := by rw [sq, mul_assoc, hdz, mul_zero]
        rwa [hσ, one_mul] at this
      rw [hden, div_zero, hSz, hdz']
      ring
    · have hq : b ^ 2 / (d + σ * S) = σ * S - d := by
        rw [div_eq_iff hden]
        linear_combination (-S ^ 2) * hσ - hSS
      rw [hq]
      ring

/-- **Equation (8.3.2)** of [golub2013matrix], the explicit single-shift QR iteration. For a rule
$\mathrm{shift}$ that chooses a shift for each matrix, and for
$T_0 \in \mathbb{R}^{n \times n}$, the iterates are
$$\mu = \mathrm{shift}(T_k), \qquad T_k - \mu I = UR, \qquad T_{k+1} = RU + \mu I.$$

One step is the backbone's `Matrix.shiftedQrStep`, with the canonical QR factorization. Examples
of shift rules are $T \mapsto t_{nn}$ and the Wilkinson shift
`GolubVanLoan.Chapter08.wilkinsonShift`.

**Reading.** The source permits any real shift chosen at each iteration and starts with a
tridiagonal reduction. Lean uses a rule depending on the current matrix, a supplied initial
matrix, and the canonical QR factorization. -/
noncomputable def explicitShiftedQR (shift : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (T₀ : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => T₀
  | k + 1 => shiftedQrStep (shift (explicitShiftedQR shift T₀ k)) (explicitShiftedQR shift T₀ k)

/-- **Equation (8.3.2)** of [golub2013matrix], exact semantics. For every shift rule, every
symmetric $T_0 \in \mathbb{R}^{n \times n}$ and every $k$, there is an orthogonal $Q$ with
$T_k = Q^T T_0 Q$, and $T_k$ is symmetric.

That one step keeps a symmetric tridiagonal matrix tridiagonal, when the shifted matrix is
nonsingular, is `GolubVanLoan.Chapter08.shifted_qr_tridiagonal`.

**Reading.** This exact-semantics theorem states orthogonal similarity and symmetry from any
symmetric initial matrix. The source’s tridiagonal preservation belongs to the separate shifted
QR result. -/
theorem equation_8_3_2 (shift : Matrix (Fin n) (Fin n) ℝ → ℝ)
    {T₀ : Matrix (Fin n) (Fin n) ℝ} (hT₀ : T₀.IsSymm) (k : ℕ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, explicitShiftedQR shift T₀ k = Qᵀ * T₀ * Q ∧
      (explicitShiftedQR shift T₀ k).IsSymm := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp [explicitShiftedQR], hT₀⟩
  | succ k ih =>
    obtain ⟨Q, hQ, hk, hs⟩ := ih
    set T := explicitShiftedQR shift T₀ k
    set U := qrQ (T - shift T • 1)
    have hU : U ∈ orthogonalGroup (Fin n) ℝ := by
      have := conjTranspose_qrQ_mul_self (T - shift T • 1)
      rw [conjTranspose_eq_transpose_of_trivial] at this
      exact (mem_orthogonalGroup_iff' _ ℝ).2 this
    have hstep : explicitShiftedQR shift T₀ (k + 1) = Uᵀ * T * U := by
      rw [explicitShiftedQR, shiftedQrStep_eq_conj, conjTranspose_eq_transpose_of_trivial]
    refine ⟨Q * U, Submonoid.mul_mem _ hQ hU, ?_, ?_⟩
    · rw [hstep, hk, transpose_mul]
      simp only [Matrix.mul_assoc]
    · rw [hstep]
      exact hs.transpose_mul_mul U

/-! ### Implicit shift version (§8.3.5) -/

/-- **Section 8.3.5** of [golub2013matrix], one step of the bulge chase. In this statement indices
are 0-based. Let $T \in \mathbb{R}^{n \times n}$ be symmetric and $k + 3 < n$, and let $T$ be
tridiagonal except for the bulge $z_k = t_{k+2,k} = t_{k,k+2}$. Let $c, s \in \mathbb{R}$
satisfy $s b_k + c z_k = 0$, where $b_k = t_{k+1,k}$. Let $G = G(k + 1, k + 2, \theta)$ be the
Givens rotation of the source with cosine $c$ and sine $s$. Then $G^T T G$ is tridiagonal except
for the entries $(k + 3, k + 1)$ and $(k + 1, k + 3)$, and
$$(G^T T G)_{k+3,k+1} = z_{k+1} = -s \, b_{k+2}, \qquad b_{k+2} = t_{k+3,k+2}.$$
So the bulge moves one step down the band.

The rotation is `Matrix.planeRotation (k+1) (k+2) c (-s)`. The statement does not need
$c^2 + s^2 = 1$. -/
theorem bulgeChase_step {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsSymm) {k : ℕ}
    (hk : k + 3 < n)
    (hband : ∀ i j : Fin n, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      ¬ ((i : ℕ) = k + 2 ∧ (j : ℕ) = k) → ¬ ((i : ℕ) = k ∧ (j : ℕ) = k + 2) → T i j = 0)
    {c s : ℝ}
    (hzero : s * T ⟨k + 1, by omega⟩ ⟨k, by omega⟩ + c * T ⟨k + 2, by omega⟩ ⟨k, by omega⟩ = 0) :
    let G := planeRotation (⟨k + 1, by omega⟩ : Fin n) ⟨k + 2, by omega⟩ c (-s)
    (∀ i j : Fin n, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      ¬ ((i : ℕ) = k + 3 ∧ (j : ℕ) = k + 1) → ¬ ((i : ℕ) = k + 1 ∧ (j : ℕ) = k + 3) →
        (Gᵀ * T * G) i j = 0) ∧
      (Gᵀ * T * G) ⟨k + 3, hk⟩ ⟨k + 1, by omega⟩ = -s * T ⟨k + 3, hk⟩ ⟨k + 2, by omega⟩ := by
  intro G
  set a : Fin n := ⟨k + 1, by omega⟩ with ha
  set b : Fin n := ⟨k + 2, by omega⟩ with hb
  set z : Fin n := ⟨k, by omega⟩ with hz
  have ha' : (a : ℕ) = k + 1 := rfl
  have hb' : (b : ℕ) = k + 2 := rfl
  have hz' : (z : ℕ) = k := rfl
  have hab : a ≠ b := fun h => by rw [Fin.ext_iff, ha', hb'] at h; omega
  have hsym : ∀ i j, T i j = T j i := fun i j => (hT.apply i j).symm
  have hT0 : ∀ i j : Fin n, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      ¬ ((i : ℕ) = k + 2 ∧ (j : ℕ) = k) → ¬ ((i : ℕ) = k ∧ (j : ℕ) = k + 2) → T i j = 0 := hband
  have hbase : s * T a z + c * T b z = 0 := hzero
  refine ⟨fun i j hij hn1 hn2 => ?_, ?_⟩
  · by_cases hia : i = a
    · subst hia
      have hja : j ≠ a := by rintro rfl; omega
      have hjb : j ≠ b := by rintro rfl; omega
      rw [conj_planeRotation_apply_row_j hab T hja hjb,
        hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
      ring
    by_cases hib : i = b
    · subst hib
      have hja : j ≠ a := by rintro rfl; omega
      have hjb : j ≠ b := by rintro rfl; omega
      rw [conj_planeRotation_apply_row_k hab T hja hjb]
      by_cases hjk : (j : ℕ) = k
      · have hj : j = z := Fin.ext hjk
        rw [hj, neg_neg]
        linear_combination hbase
      · rw [hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
        ring
    by_cases hja : j = a
    · subst hja
      have hia' : (i : ℕ) ≠ k + 1 := fun h => hia (Fin.ext h)
      have hib' : (i : ℕ) ≠ k + 2 := fun h => hib (Fin.ext h)
      rw [conj_planeRotation_apply_col_j hab T hia hib,
        hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
      ring
    by_cases hjb : j = b
    · subst hjb
      have hia' : (i : ℕ) ≠ k + 1 := fun h => hia (Fin.ext h)
      have hib' : (i : ℕ) ≠ k + 2 := fun h => hib (Fin.ext h)
      rw [conj_planeRotation_apply_col_k hab T hia hib]
      by_cases hik : (i : ℕ) = k
      · have hi : i = z := Fin.ext hik
        rw [hi, neg_neg, hsym z a, hsym z b]
        linear_combination hbase
      · rw [hT0 _ _ (by omega) (by omega) (by omega), hT0 _ _ (by omega) (by omega) (by omega)]
        ring
    have hia' : (i : ℕ) ≠ k + 1 := fun h => hia (Fin.ext h)
    have hib' : (i : ℕ) ≠ k + 2 := fun h => hib (Fin.ext h)
    have hja' : (j : ℕ) ≠ k + 1 := fun h => hja (Fin.ext h)
    have hjb' : (j : ℕ) ≠ k + 2 := fun h => hjb (Fin.ext h)
    rw [conj_planeRotation_apply_of_ne hab T hia hib hja hjb]
    exact hT0 i j hij (by omega) (by omega)
  · have h3a : (⟨k + 3, hk⟩ : Fin n) ≠ a := fun h => by rw [Fin.ext_iff, ha'] at h; simp at h
    have h3b : (⟨k + 3, hk⟩ : Fin n) ≠ b := fun h => by rw [Fin.ext_iff, hb'] at h; simp at h
    rw [conj_planeRotation_apply_col_j hab T h3a h3b,
      hT0 ⟨k + 3, hk⟩ a (Or.inr (by rw [ha'])) (by simp [ha']) (by simp [ha'])]
    ring

/-! ### Algorithms 8.3.2 and 8.3.3 (§8.3.5) -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The Wilkinson shift as Algorithm 8.3.2 computes it from $a' = t_{n-1,n-1}$, $a = t_{nn}$ and
$b = t_{n,n-1}$:
$$d = \mathrm{fl}(\mathrm{fl}(a' - a)/2), \qquad \mu = \mathrm{fl}\Bigl(a -
  \mathrm{fl}\bigl(\mathrm{fl}(b^2) / \mathrm{fl}(d + \operatorname{sign}(d) \,
  \mathrm{fl}(\sqrt{\mathrm{fl}(\mathrm{fl}(d^2) + \mathrm{fl}(b^2))}))\bigr)\Bigr),$$
with $\operatorname{sign}(0) = 1$. The product with $\operatorname{sign}(d)$ is a copy or a
negation, and is exact.

**Reading.** Same rationalized shift using rounded operations and a deterministic positive tie
branch.
-/
noncomputable def wilkinsonShiftComputed (a' a b : ℝ) : M ℝ := do
  let d ← rnd ((← rnd (a' - a)) / 2)
  let b2 ← rnd (b * b)
  let r ← rnd √(← rnd ((← rnd (d * d)) + b2))
  let den ← rnd (d + (if 0 ≤ d then r else -r))
  rnd (a - (← rnd (b2 / den)))

/-- One rotation of Algorithm 8.3.2 on the state $(T, Q, \mathrm{prev})$, at the pair $(a, b)$ of
consecutive window indices. The pair $(x, z)$ is $(x_0, z_0)$ for the first rotation
($\mathrm{prev}$ empty) and $(t_{a,\mathrm{prev}}, t_{b,\mathrm{prev}})$ afterwards, the
source's $x = t_{k+1,k}$, $z = t_{k+2,k}$ (copies). The rotation computes
$[c, s] = \mathrm{givens}(x, z)$, then $T \leftarrow G(a, b, \theta)^T T \, G(a, b, \theta)$
over the window $w$ (rows, then columns) and $Q \leftarrow Q \, G(a, b, \theta)$ over all rows,
and records $a$ as the new $\mathrm{prev}$. -/
noncomputable def implicitQRRotate (w : List (Fin n)) (x₀ z₀ : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Option (Fin n))
    (ab : Fin n × Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Option (Fin n)) := do
  let xz : ℝ × ℝ := st.2.2.elim (x₀, z₀) fun pr => (st.1 ab.1 pr, st.1 ab.2 pr)
  let cs ← Chapter05.algorithm_5_1_3 rnd xz.1 xz.2
  let T₁ ← Chapter05.givensApplyLeft rnd ab.1 ab.2 cs.1 cs.2 w st.1
  let T₂ ← Chapter05.givensApplyRight rnd ab.1 ab.2 cs.1 cs.2 w T₁
  let Q₁ ← Chapter05.givensApplyRight rnd ab.1 ab.2 cs.1 cs.2 (List.finRange n) st.2.1
  pure (T₂, Q₁, some ab.1)

/-- **Algorithm 8.3.2** of [golub2013matrix] (implicit symmetric QR step with Wilkinson shift).
"Given an unreduced symmetric tridiagonal matrix $T$, the following algorithm overwrites $T$
with $Z^T T Z$, where $Z = G_1 \cdots G_{n-1}$ is a product of Givens rotations with the
property that $Z^T (T - \mu I)$ is upper triangular and $\mu$ is that eigenvalue of $T$'s
trailing 2-by-2 principal submatrix closer to $t_{nn}$."
```
d = (t_{n-1,n-1} - t_nn)/2
μ = t_nn - t²_{n,n-1} / (d + sign(d) √(d² + t²_{n,n-1}))
x = t₁₁ - μ;  z = t₂₁
for k = 1:n-1
    [c, s] = givens(x, z)
    T = G_kᵀ T G_k,  G_k = G(k, k+1, θ)
    if k < n-1:  x = t_{k+1,k};  z = t_{k+2,k}
end
```
The program runs on a window $w = [w_0, \dots, w_{N-1}]$ of consecutive indices (convention 10).
The step of the source is the window of all indices, and Algorithm 8.3.3 runs the program on its
unreduced block. The program also performs the optional accumulation
$Q \leftarrow Q G_1 \cdots G_{N-1}$ of the source, and returns $(Z^T T Z, QZ)$, where $Z$ acts
on the window. For $N \le 1$ it does nothing. The shift is
`GolubVanLoan.Chapter08.wilkinsonShiftComputed` of the last two window indices, and
$x_0 = \mathrm{fl}(t_{w_0 w_0} - \mu)$.

**Reading.** Lean embeds the source step in a consecutive window and updates an accumulated
factor. The source gives a full-order step and describes accumulation separately. -/
noncomputable def algorithm_8_3_2 (w : List (Fin n)) (T Q : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  match w with
  | f₀ :: f₁ :: rest => do
    let l := (f₁ :: rest).getLast (List.cons_ne_nil _ _)
    let l' := (f₀ :: f₁ :: rest).dropLast.getLast (by simp)
    let μ ← wilkinsonShiftComputed rnd (T l' l') (T l l) (T l l')
    let x₀ ← rnd (T f₀ f₀ - μ)
    let st ← ((f₀ :: f₁ :: rest).zip (f₁ :: rest)).foldlM
      (implicitQRRotate rnd (f₀ :: f₁ :: rest) x₀ (T f₁ f₀)) (T, Q, none)
    pure (st.1, st.2.1)
  | _ => pure (T, Q)

/-- The deflation pass of Algorithm 8.3.3: for $i = 1, \dots, n - 1$ in turn, set
$d_{i+1,i} = d_{i,i+1} = 0$ if
$$|d_{i+1,i}| \le \mathrm{fl}(\mathrm{tol} \cdot \mathrm{fl}(|d_{ii}| + |d_{i+1,i+1}|)).$$
The right side is rounded; the absolute values and the comparison are exact. -/
noncomputable def deflate (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (D : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
    if h : (i : ℕ) + 1 < n then do
      let e ← rnd (tol * (← rnd (|D i i| + |D ⟨i + 1, h⟩ ⟨i + 1, h⟩|)))
      if |D ⟨i + 1, h⟩ i| ≤ e then
        pure (of fun r s => if (r = ⟨i + 1, h⟩ ∧ s = i) ∨ (r = i ∧ s = ⟨i + 1, h⟩) then 0
          else D r s)
      else pure D
    else pure D) D

/-- The last maximal run of consecutive couplings that are nonzero, as a window of indices. Let
$\mathrm{nz}(i)$ mean that the coupling between $i$ and $i + 1$ is nonzero, let $e < n$ be the
largest index with $\mathrm{nz}(e)$, and let $p$ be the smallest index with $\mathrm{nz}$ on all
of $p, \dots, e$. The window is $[p, \dots, e + 1]$, and it is empty if no $\mathrm{nz}(i)$ with
$i < n$ holds. The computation uses only exact comparisons of indices. -/
noncomputable def lastRunWindow (n : ℕ) (nz : ℕ → Prop) [DecidablePred nz] : List (Fin n) :=
  match ((List.range n).filter fun i => nz i).getLast? with
  | none => []
  | some e =>
    let p := (((List.range (e + 1)).filter fun i => ¬ nz i).getLast?).elim 0 (· + 1)
    (List.finRange n).filter fun i => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ e + 1

open Classical in
/-- The unreduced block $D_{22}$ of Algorithm 8.3.3 as a window of consecutive indices. With the
largest $q$ such that the trailing $q \times q$ block $D_{33}$ is diagonal and decoupled, and
the smallest $p$ such that $D_{22} = D(p{:}n{-}q, p{:}n{-}q)$ is unreduced, the window is
$[p, \dots, n - q - 1]$ (0-based). The coupling between $i$ and $i + 1$ is the subdiagonal entry
$d_{i+1,i}$, and the window is empty when all of them vanish ($q = n$). -/
noncomputable def unreducedWindow (D : Matrix (Fin n) (Fin n) ℝ) : List (Fin n) :=
  lastRunWindow n fun i => ∃ h : i + 1 < n, D ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0

/-- One pass of the loop "until $q = n$" of Algorithm 8.3.3 on the state $(D, Q, \mathrm{done})$. If
$\mathrm{done}$ holds, the pass does nothing. Otherwise it deflates $D$ and finds the window of
$D_{22}$; if the window is empty ($q = n$) it sets $\mathrm{done}$, and otherwise it applies
Algorithm 8.3.2 to the window with the accumulator $Q$.

**Reading.** Same deflation and active step with explicit stopping status.
-/
noncomputable def symmetricQRPass (tol : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2 then pure st else do
    let D ← deflate rnd tol st.1
    match unreducedWindow D with
    | [] => pure (D, st.2.1, true)
    | w => do
      let DQ ← algorithm_8_3_2 rnd w D st.2.1
      pure (DQ.1, DQ.2, false)

/-- **Algorithm 8.3.3** of [golub2013matrix] (symmetric QR algorithm). "Given
$A \in \mathbb{R}^{n \times n}$ (symmetric) and a tolerance $\mathrm{tol}$ greater than the unit
roundoff, this algorithm computes an approximate symmetric Schur decomposition $Q^T A Q = D$."
```
Use Algorithm 8.3.1 to compute the tridiagonalization T = (P₁ ⋯ P_{n-2})ᵀ A (P₁ ⋯ P_{n-2})
Set D = T and form Q = P₁ ⋯ P_{n-2}
until q = n
    For i = 1:n-1, set d_{i+1,i} and d_{i,i+1} to zero if |d_{i+1,i}| ≤ tol(|d_ii| + |d_{i+1,i+1}|)
    Find the largest q and the smallest p such that D = diag(D₁₁, D₂₂, D₃₃) with D₃₃
    diagonal (q × q) and D₂₂ unreduced
    if q < n: apply Algorithm 8.3.2 to D₂₂: D = diag(I_p, Z, I_q)ᵀ D diag(I_p, Z, I_q),
              Q = Q diag(I_p, Z, I_q)
end
```
The initial $D$ is the tridiagonal part of the array of Algorithm 8.3.1; the entries of that
array below the subdiagonal hold nothing of $T$. The initial $Q$ is the forward accumulation
(§5.1.6, `GolubVanLoan.Chapter05.forwardAccumulation`) of the returned reflector data, which are
never rebuilt (convention 13). The loop "until $q = n$" runs at most `fuel` passes, with a
`done` flag (convention 3). The result is $(D, Q, \mathrm{done})$.

**Reading.** The source loops until the trailing diagonal block is the whole matrix and treats
accumulating $Q$ as optional. Lean always accumulates $Q$ and returns a stop flag after a
bounded number of passes. -/
noncomputable def algorithm_8_3_3 (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let Adata ← algorithm_8_3_1 rnd A
  let Q ← Chapter05.forwardAccumulation rnd Adata.2
  (List.range fuel).foldlM (fun st _ => symmetricQRPass rnd tol st)
    (tridiagonalPart Adata.1, Q, false)

end Programs

/-! ### Algorithm 8.3.2: exact semantics -/

section ImplicitQR

open Chapter07 (francisWindow blockConj IsBlockSupported)

/-- A Givens rotation in two distinct indices of the window $[p, m)$ acts on the window only. -/
private theorem isBlockSupported_givensRotation {p m : ℕ} {a b : Fin n}
    (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < m) (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < m) (hab : a ≠ b) (c s : ℝ) :
    IsBlockSupported p m (Chapter05.givensRotation a b c s) := fun i j hij => by
  rw [Chapter05.givensRotation, planeRotation_apply hab]
  have hja : ¬ (j = a ∧ p ≤ (i : ℕ) ∧ (i : ℕ) < m) := fun h => hij ⟨h.2, h.1 ▸ ha⟩
  have hjb : ¬ (j = b ∧ p ≤ (i : ℕ) ∧ (i : ℕ) < m) := fun h => hij ⟨h.2, h.1 ▸ hb⟩
  by_cases hj : j = a
  · subst hj
    have hi : ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) := fun h => hja ⟨rfl, h⟩
    have hia : i ≠ j := fun e => hi (e ▸ ha)
    have hib : i ≠ b := fun e => hi (e ▸ hb)
    simp [hia, hib, one_apply_ne hia]
  · by_cases hj' : j = b
    · subst hj'
      have hi : ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) := fun h => hjb ⟨rfl, h⟩
      have hia : i ≠ a := fun e => hi (e ▸ ha)
      have hib : i ≠ j := fun e => hi (e ▸ hb)
      simp [hj, hia, hib, one_apply_ne hib]
    · simp only [hj, hj', ↓reduceIte, Matrix.one_apply]

/-- A block similarity of a symmetric matrix is symmetric. -/
private theorem isSymm_blockConj {p m : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsSymm)
    (Z : Matrix (Fin n) (Fin n) ℝ) : (blockConj p m Z X).IsSymm := by
  have hZ : (Zᵀ * X * Z).IsSymm := by
    exact hX.transpose_mul_mul Z
  ext i j
  simp only [transpose_apply, Chapter07.blockConj, of_apply]
  by_cases h : (p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
    exact hZ.apply i j
  · rw [ite_eq_right h,
      ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]
    exact hX.apply i j

/-- For $P$ acting on the window $[p, m)$, the row update over the columns of the window followed by
the column update over the rows of the window is the block similarity
`GolubVanLoan.Chapter07.blockConj p m P X`. -/
private theorem blockConj_eq_of_isBlockSupported {p m : ℕ} {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsBlockSupported p m P) :
    (of fun (r q : Fin n) => if p ≤ (r : ℕ) ∧ (r : ℕ) < m then
        ((of fun (r q : Fin n) => if p ≤ (q : ℕ) ∧ (q : ℕ) < m then (Pᵀ * X) r q else X r q) *
          P) r q
      else (of fun (r q : Fin n) => if p ≤ (q : ℕ) ∧ (q : ℕ) < m then (Pᵀ * X) r q
        else X r q) r q) =
      blockConj p m P X := by
  -- `P` is the identity off the window
  have hPo : ∀ t q : Fin n, ¬ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) → P t q = if t = q then 1 else 0 :=
    fun t q hq => by rw [hP t q (fun h => hq h.2), Matrix.one_apply]
  have hPo' : ∀ t q : Fin n, ¬ (p ≤ (t : ℕ) ∧ (t : ℕ) < m) → P t q = if t = q then 1 else 0 :=
    fun t q ht => by rw [hP t q (fun h => ht h.1), Matrix.one_apply]
  -- `Pᵀ X` agrees with `X` on the rows off the window
  have hPX : ∀ r q : Fin n, ¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < m) → (Pᵀ * X) r q = X r q := by
    intro r q hr
    rw [Matrix.mul_apply, Finset.sum_eq_single r]
    · rw [transpose_apply, hPo' r r hr, ite_eq_left rfl, one_mul]
    · intro t _ htr
      rw [transpose_apply, hPo t r hr, ite_eq_right htr, zero_mul]
    · simp
  ext r q
  simp only [Chapter07.blockConj, of_apply]
  by_cases hr : p ≤ (r : ℕ) ∧ (r : ℕ) < m
  · rw [ite_eq_left hr]
    by_cases hq : p ≤ (q : ℕ) ∧ (q : ℕ) < m
    · rw [ite_eq_left ⟨hr, hq⟩, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [of_apply]
      by_cases ht : p ≤ (t : ℕ) ∧ (t : ℕ) < m
      · rw [ite_eq_left ht]
      · rw [ite_eq_right ht, hPo' t q ht, ite_eq_right (fun e : t = q => ht (e ▸ hq)), mul_zero,
          mul_zero]
    · rw [ite_eq_right
        (fun h : (p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) => hq h.2),
        Matrix.mul_apply, Finset.sum_eq_single q]
      · rw [of_apply, ite_eq_right hq, hPo q q hq, ite_eq_left rfl, mul_one]
      · intro t _ htq
        rw [hPo t q hq, ite_eq_right htq, mul_zero]
      · simp
  · rw [ite_eq_right hr,
      ite_eq_right (fun h : (p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) => hr h.1)]
    split_ifs
    · exact hPX r q hr
    · rfl

/-- One exact rotation of Algorithm 8.3.2 on a window: with $(c, s) = \mathrm{givens}(x, z)$ for the
first pair $(x_0, z_0)$ or the entries $(t_{a,\mathrm{prev}}, t_{b,\mathrm{prev}})$, the new
state is the block similarity by $G(a, b, \theta)$, and the accumulator is multiplied by
$G(a, b, \theta)$. -/
private theorem implicitQRRotate_pure {p m : ℕ} {a b : Fin n}
    (ha : p ≤ (a : ℕ) ∧ (a : ℕ) < m) (hb : p ≤ (b : ℕ) ∧ (b : ℕ) < m) (hab : a ≠ b)
    (x₀ z₀ : ℝ) (X Q : Matrix (Fin n) (Fin n) ℝ) (prev : Option (Fin n)) :
    let xz : ℝ × ℝ := prev.elim (x₀, z₀) fun pr => (X a pr, X b pr)
    let cs := Id.run (Chapter05.algorithm_5_1_3 pure xz.1 xz.2)
    Id.run (implicitQRRotate pure (francisWindow n p m) x₀ z₀ (X, Q, prev) (a, b)) =
      (blockConj p m (Chapter05.givensRotation a b cs.1 cs.2) X,
        Q * Chapter05.givensRotation a b cs.1 cs.2, some a) := by
  intro xz cs
  have hw := Chapter07.nodup_francisWindow n p m
  change (Id.run (Chapter05.givensApplyRight pure a b cs.1 cs.2 (francisWindow n p m)
      (Id.run (Chapter05.givensApplyLeft pure a b cs.1 cs.2 (francisWindow n p m) X))),
    Id.run (Chapter05.givensApplyRight pure a b cs.1 cs.2 (List.finRange n) Q), some a) = _
  rw [Chapter05.givensApplyLeft_spec hab _ _ hw, Chapter05.givensApplyRight_spec hab _ _ hw,
    Chapter05.givensApplyRight_spec_of_forall_mem hab _ _ (List.nodup_finRange n)
      List.mem_finRange]
  simp only [Chapter07.mem_francisWindow]
  rw [blockConj_eq_of_isBlockSupported (isBlockSupported_givensRotation ha hb hab _ _)]

/-- The zero pattern of the bulge chase on the window $[p, m)$ after $j$ rotations: below the
diagonal, the block is tridiagonal except for the bulge at $(p + j + 1, p + j - 1)$, and there
is no bulge for $j = 0$. -/
private def IsChased (p m j : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i l : Fin n, p ≤ (l : ℕ) → (i : ℕ) < m → (l : ℕ) + 2 ≤ i →
    ¬ (1 ≤ j ∧ (i : ℕ) = p + j + 1 ∧ (l : ℕ) + 1 = p + j) → X i l = 0

/-- One bulge-chasing rotation: if $X$ has the zero pattern after $j$ rotations and the rotation
$G(a, b, \theta)$ with $a = p + j$ and $b = a + 1$ annihilates the bulge
($s x_{a,a-1} + c x_{b,a-1} = 0$, vacuous for $j = 0$), then the block similarity has the zero
pattern after $j + 1$ rotations: the bulge moves one step down. -/
private theorem isChased_blockConj {p m j : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hc : IsChased p m j X) {a b : Fin n} (ha : (a : ℕ) = p + j) (hb : (b : ℕ) = p + j + 1)
    (hbm : (b : ℕ) < m) {c s : ℝ}
    (hzero : ∀ pr : Fin n, 1 ≤ j → (pr : ℕ) + 1 = p + j → s * X a pr + c * X b pr = 0) :
    IsChased p m (j + 1) (blockConj p m (Chapter05.givensRotation a b c s) X) := by
  intro i l hl him hil hnb
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  simp only [Chapter07.blockConj, of_apply]
  rw [ite_eq_left ⟨⟨by omega, him⟩, ⟨hl, by omega⟩⟩]
  change ((planeRotation a b c (-s))ᵀ * X * planeRotation a b c (-s)) i l = 0
  by_cases hia : i = a
  · subst hia
    have hla : l ≠ i := fun e => by rw [e] at hil; omega
    have hlb : l ≠ b := fun e => by rw [e, hb, ha] at hil; omega
    rw [conj_planeRotation_apply_row_j hab X hla hlb, hc i l hl (by omega) hil (by omega),
      hc b l hl hbm (by omega) (by omega)]
    ring
  by_cases hib : i = b
  · subst hib
    have hla : l ≠ a := fun e => by rw [e, ha] at hil; omega
    have hlb : l ≠ i := fun e => by rw [e] at hil; omega
    rw [conj_planeRotation_apply_row_k hab X hla hlb]
    by_cases hl1 : (l : ℕ) + 1 = p + j
    · linear_combination hzero l (by omega) hl1
    · rw [hc a l hl (by omega) (by omega) (by omega), hc i l hl him (by omega) (by omega)]
      ring
  by_cases hla : l = a
  · subst hla
    rw [conj_planeRotation_apply_col_j hab X hia hib, hc i l hl him (by omega) (by omega),
      hc i b (by omega) him (by omega) (by omega)]
    ring
  by_cases hlb : l = b
  · subst hlb
    rw [conj_planeRotation_apply_col_k hab X hia hib, hc i a (by omega) him (by omega) (by omega),
      hc i l hl him (by omega) (by omega)]
    ring
  rw [conj_planeRotation_apply_of_ne hab X hia hib hla hlb]
  exact hc i l hl him hil fun h => hib (Fin.ext (by omega))

/-- A Givens rotation in the indices $a \neq b$ fixes $e_q$ for every $q$ other than $a$ and $b$. -/
theorem givensRotation_mulVec_single_of_ne {a b q : Fin n} (hab : a ≠ b) (hqa : q ≠ a)
    (hqb : q ≠ b) (c s : ℝ) :
    Chapter05.givensRotation a b c s *ᵥ Pi.single q 1 = Pi.single q 1 := by
  funext t
  rw [mulVec_single_one, col_apply, Chapter05.givensRotation, planeRotation_apply hab]
  simp only [hqa, hqb, ↓reduceIte, Pi.single_apply]

/-- The loop invariant of Algorithm 8.3.2 on the window $[p, m)$ after $j$ rotations: the state
$(X, Q', \mathrm{prev})$ is $(\mathrm{blockConj}(p, m, Z, T), QZ, a_{j-1})$ for an orthogonal
$Z$ acting on the window, $X$ is symmetric with the zero pattern of the chase, and for $j \ge 1$
the first column $Z e_p$ is that of the first rotation $G(p, p + 1, \theta_0)$, where
$c_0^2 + s_0^2 = 1$ and $s_0 x_0 + c_0 z_0 = 0$. -/
private def ChaseInv (p m : ℕ) (f₀ f₁ : Fin n) (T Q : Matrix (Fin n) (Fin n) ℝ) (x₀ z₀ : ℝ)
    (j : ℕ) (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Option (Fin n)) : Prop :=
  ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z ∈ orthogonalGroup (Fin n) ℝ ∧ IsBlockSupported p m Z ∧
    st.1 = blockConj p m Z T ∧ st.2.1 = Q * Z ∧ st.1.IsSymm ∧ IsChased p m j st.1 ∧
    st.2.2.elim (j = 0) (fun pr => 1 ≤ j ∧ (pr : ℕ) + 1 = p + j) ∧ (j = 0 → Z = 1) ∧
    (1 ≤ j → ∃ c₀ s₀ : ℝ, c₀ ^ 2 + s₀ ^ 2 = 1 ∧ s₀ * x₀ + c₀ * z₀ = 0 ∧
      Z *ᵥ Pi.single f₀ 1 = Chapter05.givensRotation f₀ f₁ c₀ s₀ *ᵥ Pi.single f₀ 1)

/-- A tridiagonal matrix has the zero pattern of the chase before the first rotation. -/
private theorem isChased_zero_of_isTridiagonal {p m : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsTridiagonal) : IsChased p m 0 T := fun i l _ _ hil _ =>
  hT i l (Or.inl ⟨⟨(l : ℕ) + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simp; omega)⟩)

/-- The bulge chase of Algorithm 8.3.2 on a window: the loop invariant holds after the $m - p - 1$
rotations. -/
private theorem chaseInv_run {p m : ℕ} (hm : m ≤ n) (hpm : p + 2 ≤ m)
    {T : Matrix (Fin n) (Fin n) ℝ} (hTs : T.IsSymm) (hT : T.IsTridiagonal)
    (Q : Matrix (Fin n) (Fin n) ℝ) (x₀ z₀ : ℝ) (f₀ f₁ : Fin n) (hf₀ : (f₀ : ℕ) = p)
    (hf₁ : (f₁ : ℕ) = p + 1) :
    ChaseInv p m f₀ f₁ T Q x₀ z₀ (m - p - 1)
      (Id.run (((francisWindow n p m).zip (francisWindow n p m).tail).foldlM
        (implicitQRRotate pure (francisWindow n p m) x₀ z₀) (T, Q, none))) := by
  set w := francisWindow n p m with hwdef
  have hlen : w.length = m - p := Chapter07.length_francisWindow hm
  have hval : ∀ k (hk : k < w.length), (w[k] : ℕ) = p + k := Chapter07.val_getElem_francisWindow hm
  have hzlen : (w.zip w.tail).length = m - p - 1 := by simp [hlen]
  rw [← hzlen]
  refine List.idRun_foldlM_induction' _ _ (init := (T, Q, none))
    ⟨1, one_mem _, Chapter07.isBlockSupported_one p m, by ext i j; simp [Chapter07.blockConj],
    (Matrix.mul_one Q).symm, hTs, isChased_zero_of_isTridiagonal hT, rfl, fun _ => rfl,
    fun h => absurd h (by omega)⟩ ?_
  intro j hj ⟨X, Qa, prev⟩ ⟨Z, hZo, hZb, hX, hQa, hXs, hXc, hprev, hZ1, hcol⟩
  simp only at hX hQa hXs hXc hprev
  rw [hzlen] at hj
  have hja : j < w.length := by omega
  have hjb : j + 1 < w.length := by omega
  have hpair : (w.zip w.tail)[j]'(by rw [hzlen]; exact hj) = (w[j], w[j + 1]) := by
    simp [List.getElem_zip, List.getElem_tail]
  rw [hpair]
  set a := w[j] with hadef
  set b := w[j + 1] with hbdef
  have ha : (a : ℕ) = p + j := hval j hja
  have hb : (b : ℕ) = p + j + 1 := hval (j + 1) hjb
  have hab : a ≠ b := fun e => by rw [Fin.ext_iff, ha, hb] at e; omega
  rw [implicitQRRotate_pure ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hab]
  set xz : ℝ × ℝ := prev.elim (x₀, z₀) fun pr => (X a pr, X b pr) with hxz
  obtain ⟨hcs, hzcs, -⟩ := Chapter05.algorithm_5_1_3_spec xz.1 xz.2
  set cs := Id.run (Chapter05.algorithm_5_1_3 pure xz.1 xz.2)
  set G := Chapter05.givensRotation a b cs.1 cs.2 with hG
  have hGb : IsBlockSupported p m G :=
    isBlockSupported_givensRotation ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hab _ _
  refine ⟨Z * G, Submonoid.mul_mem _ hZo (Chapter05.givensRotation_mem_orthogonalGroup hab hcs),
    hZb.mul hGb, ?_, ?_, isSymm_blockConj hXs G, ?_, ⟨Nat.succ_pos _, by omega⟩,
    fun h => absurd h (Nat.succ_ne_zero _), fun _ => ?_⟩
  · rw [hX, Chapter07.blockConj_blockConj hGb]
  · rw [hQa, Matrix.mul_assoc]
  · refine isChased_blockConj hXc ha hb (by omega) fun pr hj1 hpr => ?_
    cases prev with
    | none => exact absurd (hprev : j = 0) (Nat.one_le_iff_ne_zero.1 hj1)
    | some pr' =>
      have h2 : (pr' : ℕ) + 1 = p + j := hprev.2
      have hpr' : pr' = pr := Fin.ext (Nat.add_right_cancel (h2.trans hpr.symm))
      subst hpr'
      exact hzcs
  · rcases Nat.eq_zero_or_pos j with rfl | hj1
    · -- the first rotation
      cases prev with
      | some pr => exact absurd hprev.1 (by omega)
      | none =>
        have ha' : a = f₀ := Fin.ext (by rw [ha, hf₀]; rfl)
        have hb' : b = f₁ := Fin.ext (by rw [hb, hf₁])
        refine ⟨cs.1, cs.2, hcs, hzcs, ?_⟩
        rw [hZ1 rfl, Matrix.one_mul, hG, ha', hb']
    · obtain ⟨c₀, s₀, h₀, hz₀, he₀⟩ := hcol hj1
      refine ⟨c₀, s₀, h₀, hz₀, ?_⟩
      rw [← mulVec_mulVec, givensRotation_mulVec_single_of_ne hab
        (fun e => by rw [e, ha] at hf₀; omega) (fun e => by rw [e, hb] at hf₀; omega), he₀]

/-- In exact arithmetic, the shift of Algorithm 8.3.2 is $a - b^2 / (d + \operatorname{sign}(d)
\sqrt{d^2 + b^2})$ with $d = (a' - a)/2$ and $\operatorname{sign}(0) = 1$.

**Reading.** Same rationalized shift with positive sign selected at zero.
-/
theorem wilkinsonShiftComputed_pure (a' a b : ℝ) :
    Id.run (wilkinsonShiftComputed pure a' a b) =
      a - b ^ 2 / ((a' - a) / 2 + (if 0 ≤ (a' - a) / 2 then 1 else -1) *
        √(((a' - a) / 2) ^ 2 + b ^ 2)) := by
  change a - b * b / ((a' - a) / 2 + (if 0 ≤ (a' - a) / 2 then √((a' - a) / 2 * ((a' - a) / 2) +
    b * b) else -√((a' - a) / 2 * ((a' - a) / 2) + b * b))) = _
  split_ifs <;> ring_nf

/-- A symmetric block similarity of a tridiagonal matrix, whose block has the zero pattern of the
chase after the last rotation, is tridiagonal. -/
private theorem isTridiagonal_of_isChased {p m : ℕ} {T Z X : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsTridiagonal) (hX : X = blockConj p m Z T) (hXs : X.IsSymm)
    (hXc : IsChased p m (m - p - 1) X) : X.IsTridiagonal := by
  have hlow : ∀ i j : Fin n, (j : ℕ) + 2 ≤ i → X i j = 0 := by
    intro i j hji
    by_cases hin : (p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)
    · exact hXc i j hin.2.1 hin.1.2 hji (by omega)
    · rw [hX]
      simp only [Chapter07.blockConj, of_apply]
      rw [ite_eq_right hin]
      exact hT i j (Or.inl ⟨⟨(j : ℕ) + 1, by omega⟩, Fin.lt_def.2 (by simp),
        Fin.lt_def.2 (by simp; omega)⟩)
  rintro i j (⟨k, hjk, hki⟩ | ⟨k, hik, hkj⟩)
  · rw [Fin.lt_def] at hjk hki
    exact hlow i j (by omega)
  · rw [Fin.lt_def] at hik hkj
    rw [← hXs.apply i j]
    exact hlow j i (by omega)

/-- **Algorithm 8.3.2** of [golub2013matrix] on a window, exact semantics. This is what Algorithm
8.3.3 runs on its unreduced block $D_{22}$. Let $T \in \mathbb{R}^{n \times n}$ be symmetric and
tridiagonal, let $Q \in \mathbb{R}^{n \times n}$, and let $[p, m)$ be a window of at least two
indices, $p + 2 \le m \le n$ (0-based). Let $\mu$ be the exact Wilkinson shift of the trailing
$2 \times 2$ block of $T(p{:}m, p{:}m)$, computed from $t_{m-2,m-2}$, $t_{m-1,m-1}$ and
$t_{m-1,m-2}$. Then the exact output $(T', Q')$ of Algorithm 8.3.2 on the window satisfies the
following. There is an orthogonal $Z$ that acts on the window only, such that
* $T'$ is $Z^T T Z$ on the block and $T$ elsewhere, and $Q' = QZ$;
* $T'$ is symmetric and tridiagonal;
* $Z e_p = G(p, p + 1, \theta_0) e_p$ for some $c_0, s_0$ with $c_0^2 + s_0^2 = 1$ and
  $s_0 (t_{pp} - \mu) + c_0 t_{p+1,p} = 0$.

The window is `GolubVanLoan.Chapter07.francisWindow n p m`, the first statement is $T' = $
`GolubVanLoan.Chapter07.blockConj p m Z T`, and $Z$ is the product of the $m - p - 1$ rotations.
The proof is the bulge-chasing invariant: after $j$ rotations the block is tridiagonal except
for one bulge at $(p + j + 1, p + j - 1)$ (§8.3.5, `GolubVanLoan.Chapter08.bulgeChase_step`),
and the last rotation pushes the bulge out of the block.

**Generalization.** The source presents a full-order step on an unreduced tridiagonal. This
theorem gives the exact rotation and tridiagonal structure for a window of a symmetric
tridiagonal, with other entries unchanged by the window update. -/
theorem algorithm_8_3_2_window {p m : ℕ} (hm : m ≤ n) (hpm : p + 2 ≤ m)
    {T : Matrix (Fin n) (Fin n) ℝ} (hTs : T.IsSymm) (hT : T.IsTridiagonal)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    let out := Id.run (algorithm_8_3_2 pure (francisWindow n p m) T Q)
    let μ := Id.run (wilkinsonShiftComputed pure (T ⟨m - 2, by omega⟩ ⟨m - 2, by omega⟩)
      (T ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) (T ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩))
    ∃ Z ∈ orthogonalGroup (Fin n) ℝ, IsBlockSupported p m Z ∧
      out.1 = blockConj p m Z T ∧ out.2 = Q * Z ∧ out.1.IsSymm ∧ out.1.IsTridiagonal ∧
      ∃ c₀ s₀ : ℝ, c₀ ^ 2 + s₀ ^ 2 = 1 ∧
        s₀ * (T ⟨p, by omega⟩ ⟨p, by omega⟩ - μ) + c₀ * T ⟨p + 1, by omega⟩ ⟨p, by omega⟩ = 0 ∧
        Z *ᵥ Pi.single ⟨p, by omega⟩ 1 =
          Chapter05.givensRotation ⟨p, by omega⟩ ⟨p + 1, by omega⟩ c₀ s₀ *ᵥ
            Pi.single ⟨p, by omega⟩ 1 := by
  intro out μ
  have hlen : (francisWindow n p m).length = m - p := Chapter07.length_francisWindow hm
  have hval : ∀ k (hk : k < (francisWindow n p m).length),
      ((francisWindow n p m)[k] : ℕ) = p + k := Chapter07.val_getElem_francisWindow hm
  obtain ⟨f₀, f₁, rest, hw⟩ :=
    List.exists_cons_cons_of_two_le_length (l := francisWindow n p m) (by omega)
  have hf₀ : (f₀ : ℕ) = p := by
    have h := hval 0 (by omega)
    rwa [List.getElem_of_eq hw, List.getElem_cons_zero] at h
  have hf₁ : (f₁ : ℕ) = p + 1 := by
    have h := hval 1 (by omega)
    rwa [List.getElem_of_eq hw, List.getElem_cons_succ, List.getElem_cons_zero] at h
  have hlen' : (f₀ :: f₁ :: rest).length = m - p := hw ▸ hlen
  have hval' : ∀ k (hk : k < (f₀ :: f₁ :: rest).length), ((f₀ :: f₁ :: rest)[k] : ℕ) = p + k :=
    fun k hk => by rw [← List.getElem_of_eq hw]; exact hval k (by omega)
  -- the trailing pair of the window
  have hl : (f₁ :: rest).getLast (List.cons_ne_nil _ _) = ⟨m - 1, by omega⟩ := by
    refine Fin.ext ?_
    rw [← List.getLast_cons (List.cons_ne_nil f₁ rest) (a := f₀), List.getLast_eq_getElem,
      hval' _ (by omega), hlen']
    simp only
    omega
  have hl' : (f₀ :: f₁ :: rest).dropLast.getLast (by simp) = ⟨m - 2, by omega⟩ := by
    refine Fin.ext ?_
    rw [List.getLast_eq_getElem, List.getElem_dropLast, hval' _ (by simp)]
    simp only [List.length_dropLast, hlen']
    omega
  have hf₀' : f₀ = ⟨p, by omega⟩ := Fin.ext hf₀
  have hf₁' : f₁ = ⟨p + 1, by omega⟩ := Fin.ext hf₁
  -- the program is the fold of `implicitQRRotate` over the consecutive pairs
  have key := chaseInv_run hm hpm hTs hT Q (T f₀ f₀ - μ) (T f₁ f₀) f₀ f₁ hf₀ hf₁
  set st := Id.run (((francisWindow n p m).zip (francisWindow n p m).tail).foldlM
    (implicitQRRotate pure (francisWindow n p m) (T f₀ f₀ - μ) (T f₁ f₀)) (T, Q, none)) with hst
  have hout : out = (st.1, st.2.1) := by
    change Id.run (algorithm_8_3_2 pure (francisWindow n p m) T Q) = _
    rw [hst, hw, List.tail_cons]
    simp only [algorithm_8_3_2]
    rw [hl, hl']
    rfl
  obtain ⟨Z, hZo, hZb, hX, hQa, hXs, hXc, -, -, hcol⟩ := key
  obtain ⟨c₀, s₀, hcs, hz, he⟩ := hcol (by omega)
  rw [hout]
  refine ⟨Z, hZo, hZb, hX, hQa, hXs, isTridiagonal_of_isChased hT hX hXs hXc, c₀, s₀, hcs, ?_,
    ?_⟩
  · rw [← hf₀', ← hf₁']
    exact hz
  · rw [← hf₀', ← hf₁']
    exact he

/-- The first column of the Givens rotation in the indices $1$ and $2$ is $c e_1 - s e_2$ (0-based
indices $0$ and $1$ in Lean). -/
theorem givensRotation_mulVec_single_zero {N : ℕ} (c s : ℝ) :
    Chapter05.givensRotation (0 : Fin (N + 2)) 1 c s *ᵥ Pi.single 0 1 =
      c • Pi.single 0 1 - s • Pi.single 1 1 := by
  funext t
  rw [mulVec_single_one, col_apply, Chapter05.givensRotation,
    planeRotation_apply (by simp)]
  by_cases h0 : t = 0
  · subst h0; simp
  · by_cases h1 : t = 1
    · subst h1; simp
    · simp [h0, h1]

/-- **Algorithm 8.3.2** of [golub2013matrix], exact semantics. "Given an unreduced symmetric
tridiagonal matrix $T$, the following algorithm overwrites $T$ with $Z^T T Z$, where
$Z = G_1 \cdots G_{n-1}$ is a product of Givens rotations with the property that
$Z^T (T - \mu I)$ is upper triangular and $\mu$ is that eigenvalue of $T$'s trailing 2-by-2
principal submatrix closer to $t_{nn}$." Let $T \in \mathbb{R}^{n \times n}$ with $n \ge 2$ be
unreduced, symmetric and tridiagonal, let $Q \in \mathbb{R}^{n \times n}$, and let $\mu$ be the
Wilkinson shift (8.3.3) of $T$. Then the exact output $(T', Q')$ of Algorithm 8.3.2 on all
indices satisfies the following. There is an orthogonal $Z$ with
* $T' = Z^T T Z$ and $Q' = QZ$;
* $T'$ symmetric and tridiagonal;
* $Z e_1$ a multiple of $(T - \mu I) e_1$, the source's $Z e_1 = U e_1$;
* $Z^T (T - \mu I)$ upper triangular.

Consequently, if $T - \mu I$ is nonsingular, then $T' = D \, T_+ D$ for a diagonal $D$ with
entries $\pm 1$, where $T_+$ is the explicit shifted step `Matrix.shiftedQrStep μ T` of (8.3.2):
the implicit step is the explicit one up to signs.

The order is $n = N + 2$, and $\mu$ is `GolubVanLoan.Chapter08.wilkinsonShift T`. The
triangularity is the implicit-shift principle
`Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`, which is also behind
Theorem 8.3.2. The signs come from `Matrix.IsShiftedQrStep.unique_of_isUnit`.

**Reading.** The source describes the explicit and implicit shifted step as essentially the
same. Lean specifies the first column up to scale and proves diagonal-sign similarity to the
chosen explicit step when $T-\mu I$ is invertible. -/
theorem algorithm_8_3_2_spec {N : ℕ} {T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hTs : T.IsSymm) (hT : IsUnreducedTridiagonal T) (Q : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) :
    let out := Id.run (algorithm_8_3_2 pure (List.finRange (N + 2)) T Q)
    ∃ Z ∈ orthogonalGroup (Fin (N + 2)) ℝ, out.1 = Zᵀ * T * Z ∧ out.2 = Q * Z ∧
      out.1.IsSymm ∧ out.1.IsTridiagonal ∧
      Z.col 0 ∈ Submodule.span ℝ {(T - wilkinsonShift T • 1).col 0} ∧
      (Zᵀ * (T - wilkinsonShift T • 1)).IsUpperTriangular ∧
      (IsUnit (T - wilkinsonShift T • 1).det → ∃ d : Fin (N + 2) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
        out.1 = diagonal d * shiftedQrStep (wilkinsonShift T) T * diagonal d) := by
  intro out
  set μ := wilkinsonShift T with hμ
  have hwin := algorithm_8_3_2_window (p := 0) (m := N + 2) le_rfl (by omega) hTs hT.1 Q
  simp only [Chapter07.francisWindow_zero, Chapter07.blockConj_zero] at hwin
  obtain ⟨Z, hZo, -, h1, h2, hs, htri, c₀, s₀, hcs, hz, he⟩ := hwin
  -- the computed shift is the Wilkinson shift
  have hμ' : Id.run (wilkinsonShiftComputed pure (T ⟨N + 2 - 2, by omega⟩ ⟨N + 2 - 2, by omega⟩)
      (T ⟨N + 2 - 1, by omega⟩ ⟨N + 2 - 1, by omega⟩) (T ⟨N + 2 - 1, by omega⟩
        ⟨N + 2 - 2, by omega⟩)) = μ := by
    have e1 : (⟨N + 2 - 1, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) := Fin.ext (by simp)
    have e2 : (⟨N + 2 - 2, by omega⟩ : Fin (N + 2)) = (Fin.last N).castSucc := Fin.ext (by simp)
    rw [e1, e2, wilkinsonShiftComputed_pure, hμ, (equation_8_3_3 T).2.2]
  rw [hμ'] at hz
  have e0 : (⟨0, by omega⟩ : Fin (N + 2)) = 0 := rfl
  have e1 : (⟨0 + 1, by omega⟩ : Fin (N + 2)) = 1 := rfl
  rw [e0, e1] at hz he
  rw [givensRotation_mulVec_single_zero] at he
  -- the first column of `T - μ I`
  have hsub : T 1 0 ≠ 0 := by
    have := hT.2.apply_succ_castSucc_ne_zero (0 : Fin (N + 1))
    simpa using this
  have hT0 : (T - μ • 1).col 0 = (T 0 0 - μ) • Pi.single 0 1 + T 1 0 • Pi.single 1 1 := by
    funext t
    rw [col_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h0 : t = 0
    · subst h0; simp
    · by_cases h1 : t = 1
      · subst h1; simp
      · have ht : T t 0 = 0 := hT.1 t 0 (Or.inl ⟨1, by simp, by
          rw [Fin.lt_def]; have : (t : ℕ) ≠ 0 := fun e => h0 (Fin.ext e)
          have : (t : ℕ) ≠ 1 := fun e => h1 (Fin.ext e)
          simp; omega⟩)
        simp [h0, h1, ht]
  set r := c₀ * (T 0 0 - μ) - s₀ * T 1 0 with hr
  have hTr : (T - μ • 1).col 0 = r • Z.col 0 := by
    have ex : T 0 0 - μ = r * c₀ := by
      rw [hr]; linear_combination (-(T 0 0 - μ)) * hcs + s₀ * hz
    have ez : T 1 0 = -(r * s₀) := by
      rw [hr]; linear_combination (-(T 1 0)) * hcs + c₀ * hz
    rw [← mulVec_single_one Z 0, he, hT0, ex, ez]
    module
  have hr0 : r ≠ 0 := by
    intro h0
    have := congrFun hTr 1
    rw [h0, zero_smul, Pi.zero_apply, col_apply, Matrix.sub_apply, Matrix.smul_apply,
      one_apply_ne (by simp), smul_zero, sub_zero] at this
    exact hsub this
  have hcol : Z.col 0 ∈ Submodule.span ℝ {(T - μ • 1).col 0} := by
    have : Z.col 0 = r⁻¹ • (T - μ • 1).col 0 := by
      rw [hTr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hstar : star Z = Zᵀ := by rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have haeval : Polynomial.aeval T (Polynomial.X - Polynomial.C μ) = T - μ • 1 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hUT : (Zᵀ * (T - μ • 1)).IsUpperTriangular := by
    have := IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval hT.2
      (Polynomial.X - Polynomial.C μ) hZo (by rw [hstar, ← h1]; exact htri.isUpperHessenberg)
      (by rw [haeval, mulVec_single_one]; exact hcol)
    rwa [haeval, hstar] at this
  refine ⟨Z, hZo, h1, h2, hs, htri, hcol, hUT, fun hdet => ?_⟩
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hZo
  have hZZ' : Zᵀ * Z = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hZo
  have hstep : IsShiftedQrStep μ T out.1 := by
    refine ⟨Z, hZo, Zᵀ * (T - μ • 1), hUT, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, hZZ, Matrix.one_mul]
    · rw [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        hZZ', sub_add_cancel]
  obtain ⟨d, hd, hdd⟩ := (isShiftedQrStep_shiftedQrStep μ T).unique_of_isUnit hstep hdet
  refine ⟨d, fun i => ?_, ?_⟩
  · have := hd i
    rw [Real.norm_eq_abs] at this
    exact (abs_eq zero_le_one).1 this
  · rw [hdd, star_eq_conjTranspose, diagonal_conjTranspose, star_trivial]

end ImplicitQR

/-! ### Algorithm 8.3.3: exact semantics -/

section SymmetricQR

open Chapter07 (francisWindow blockConj IsBlockSupported)

/-- The deflation test of Algorithm 8.3.3 at the coupling $a$ (0-based), in exact arithmetic:
$a + 1 < n$ and
$$|d_{a+1,a}| \le \mathrm{tol} \, (|d_{aa}| + |d_{a+1,a+1}|).$$
-/
def IsSmallCoupling (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (a : ℕ) : Prop :=
  ∃ h : a + 1 < n, |D ⟨a + 1, h⟩ ⟨a, by omega⟩| ≤
    tol * (|D ⟨a, by omega⟩ ⟨a, by omega⟩| + |D ⟨a + 1, h⟩ ⟨a + 1, h⟩|)

/-- The position $(r, s)$ is one of the two entries $(a + 1, a)$ and $(a, a + 1)$ of a small
coupling $a < k$. -/
def IsDeflatedPair (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (r s : Fin n) : Prop :=
  ∃ a : ℕ, a < k ∧ ((r : ℕ) = a + 1 ∧ (s : ℕ) = a ∨ (r : ℕ) = a ∧ (s : ℕ) = a + 1) ∧
    IsSmallCoupling tol D a

open Classical in
/-- The array after the first $k$ tests of the deflation pass of Algorithm 8.3.3, in exact
arithmetic: the entries of the small couplings $a < k$ are set to $0$, and all other entries are
unchanged. -/
noncomputable def deflateStage (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  of fun r s => if IsDeflatedPair tol D k r s then 0 else D r s

/-- The result of the deflation pass of Algorithm 8.3.3 in exact arithmetic: the entries of every
small coupling are set to $0$. -/
noncomputable def deflated (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  deflateStage tol D n

private theorem isDeflatedPair_succ {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    {r s : Fin n} :
    IsDeflatedPair tol D (k + 1) r s ↔ IsDeflatedPair tol D k r s ∨
      (((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) ∧
        IsSmallCoupling tol D k) := by
  constructor
  · rintro ⟨a, ha, hp, hs⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
    · exact Or.inl ⟨a, ha, hp, hs⟩
    · exact Or.inr ⟨hp, hs⟩
  · rintro (⟨a, ha, hp, hs⟩ | ⟨hp, hs⟩)
    · exact ⟨a, by omega, hp, hs⟩
    · exact ⟨k, by omega, hp, hs⟩

open Classical in
private theorem deflateStage_succ_apply {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    (r s : Fin n) :
    deflateStage tol D (k + 1) r s =
      if ((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) ∧
        IsSmallCoupling tol D k then 0 else deflateStage tol D k r s := by
  simp only [deflateStage, of_apply]
  by_cases hB : IsDeflatedPair tol D k r s
  · rw [ite_eq_left (isDeflatedPair_succ.2 (Or.inl hB)), ite_eq_left hB, ite_self]
  · rw [ite_eq_right hB]
    by_cases hC : ((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) ∧
        IsSmallCoupling tol D k
    · rw [ite_eq_left (isDeflatedPair_succ.2 (Or.inr hC)), ite_eq_left hC]
    · rw [ite_eq_right (fun h => (isDeflatedPair_succ.1 h).elim hB hC), ite_eq_right hC]

private theorem not_isDeflatedPair_of {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    {r s : Fin n} (h : ¬ ((r : ℕ) = s + 1 ∨ (s : ℕ) = r + 1)) :
    ¬ IsDeflatedPair tol D k r s := by
  rintro ⟨a, -, hp, -⟩
  omega

/-- In exact arithmetic, the deflation pass of Algorithm 8.3.3 sets to $0$ exactly the small
couplings of its input, because every test reads entries that no earlier test has changed. -/
theorem deflate_pure (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (deflate pure tol D) = deflated tol D := by
  unfold deflate deflated
  refine List.idRun_foldlM_finRange_induction (fun k D' => D' = deflateStage tol D k) ?_ ?_
  · ext r s
    simp only [deflateStage, of_apply]
    rw [ite_eq_right (fun ⟨a, ha, _⟩ => absurd ha (Nat.not_lt_zero a))]
  · intro k D' hD'
    have e1 : ∀ i : Fin n, D' i i = D i i := fun i => by
      rw [hD', deflateStage, of_apply, ite_eq_right (not_isDeflatedPair_of (by omega))]
    by_cases h : (k : ℕ) + 1 < n
    · have e2 : D' ⟨k + 1, h⟩ k = D ⟨k + 1, h⟩ k := by
        rw [hD', deflateStage, of_apply, ite_eq_right]
        rintro ⟨a, ha, hp, -⟩
        simp only at hp
        omega
      simp only [h, ↓reduceDIte, pure_bind, e1, e2]
      have hA : ∀ r s : Fin n, ((r = ⟨k + 1, h⟩ ∧ s = k) ∨ (r = k ∧ s = ⟨k + 1, h⟩)) ↔
          ((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) := fun r s => by
        simp [Fin.ext_iff]
      split_ifs with hsm
      · have hsm' : IsSmallCoupling tol D k := ⟨h, hsm⟩
        rw [Id.run_pure, hD']
        ext r s
        rw [of_apply, deflateStage_succ_apply]
        by_cases hp : (r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1
        · rw [ite_eq_left ((hA r s).2 hp), ite_eq_left (And.intro hp hsm')]
        · have hn : ¬ (((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) ∧
              IsSmallCoupling tol D k) := fun h' => hp h'.1
          rw [ite_eq_right (mt (hA r s).1 hp), ite_eq_right hn]
      · have hsm' : ¬ IsSmallCoupling tol D k := fun ⟨_, h'⟩ => hsm h'
        rw [Id.run_pure, hD']
        ext r s
        have hn : ¬ (((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) ∧
            IsSmallCoupling tol D k) := fun h' => hsm' h'.2
        rw [deflateStage_succ_apply, ite_eq_right hn]
    · simp only [h, ↓reduceDIte, Id.run_pure]
      rw [hD']
      ext r s
      have : ¬ IsSmallCoupling tol D k := fun ⟨h', _⟩ => h h'
      have hn : ¬ (((r : ℕ) = k + 1 ∧ (s : ℕ) = k ∨ (r : ℕ) = k ∧ (s : ℕ) = k + 1) ∧
          IsSmallCoupling tol D k) := fun h' => this h'.2
      rw [deflateStage_succ_apply, ite_eq_right hn]

/-- The deflation does not change the entries off the first subdiagonal and superdiagonal. -/
theorem deflated_apply_of_not {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} {r s : Fin n}
    (h : ¬ ((r : ℕ) = s + 1 ∨ (s : ℕ) = r + 1)) : deflated tol D r s = D r s := by
  rw [deflated, deflateStage, of_apply, ite_eq_right (not_isDeflatedPair_of h)]

open Classical in
/-- The deflation sets the entries $(a + 1, a)$ and $(a, a + 1)$ to $0$ if the coupling $a$ is
small, and keeps them otherwise. -/
theorem deflated_apply_succ {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} (a : ℕ) (h : a + 1 < n) :
    deflated tol D ⟨a + 1, h⟩ ⟨a, by omega⟩ =
        (if IsSmallCoupling tol D a then 0 else D ⟨a + 1, h⟩ ⟨a, by omega⟩) ∧
      deflated tol D ⟨a, by omega⟩ ⟨a + 1, h⟩ =
        (if IsSmallCoupling tol D a then 0 else D ⟨a, by omega⟩ ⟨a + 1, h⟩) := by
  have key : ∀ r s : Fin n, ((r : ℕ) = a + 1 ∧ (s : ℕ) = a ∨ (r : ℕ) = a ∧ (s : ℕ) = a + 1) →
      (IsDeflatedPair tol D n r s ↔ IsSmallCoupling tol D a) := fun r s hrs => by
    constructor
    · rintro ⟨b, -, hp, hs⟩
      have : b = a := by omega
      exact this ▸ hs
    · exact fun hs => ⟨a, by omega, hrs, hs⟩
  simp only [deflated, deflateStage, of_apply]
  have k1 := key ⟨a + 1, h⟩ ⟨a, by omega⟩ (Or.inl ⟨rfl, rfl⟩)
  have k2 := key ⟨a, by omega⟩ ⟨a + 1, h⟩ (Or.inr ⟨rfl, rfl⟩)
  by_cases hs : IsSmallCoupling tol D a
  · rw [ite_eq_left (k1.2 hs), ite_eq_left (k2.2 hs)]
    exact ⟨(ite_eq_left hs).symm, (ite_eq_left hs).symm⟩
  · rw [ite_eq_right (mt k1.1 hs), ite_eq_right (mt k2.1 hs)]
    exact ⟨(ite_eq_right hs).symm, (ite_eq_right hs).symm⟩

/-- The window of the unreduced block. Let $\mathrm{nz}$ be a property of indices with
$\mathrm{nz}(i) \Rightarrow i + 1 < n$. Then either the window
`GolubVanLoan.Chapter08.lastRunWindow n nz` is empty and no $\mathrm{nz}(i)$ holds, or there are
$p \le e$ with $e + 1 < n$ such that the window is $[p, e + 2)$, $\mathrm{nz}$ holds on
$p, \dots, e$, $\mathrm{nz}(p - 1)$ fails if $p > 0$, and $\mathrm{nz}(i)$ fails for every
$i > e$. -/
theorem lastRunWindow_spec {nz : ℕ → Prop} [DecidablePred nz] (hnz : ∀ i, nz i → i + 1 < n) :
    (lastRunWindow n nz = [] ∧ ∀ i, ¬ nz i) ∨
      ∃ p e : ℕ, p ≤ e ∧ e + 1 < n ∧ lastRunWindow n nz = francisWindow n p (e + 2) ∧
        (∀ i, p ≤ i → i ≤ e → nz i) ∧ (0 < p → ¬ nz (p - 1)) ∧ ∀ i, e < i → ¬ nz i := by
  unfold lastRunWindow
  cases hl : ((List.range n).filter fun i => nz i).getLast? with
  | none =>
    refine Or.inl ⟨rfl, fun i hi => ?_⟩
    rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hl
    exact hl i (List.mem_range.2 (by have := hnz i hi; omega)) (by simpa using hi)
  | some e =>
    right
    dsimp only
    have hmem := List.mem_of_getLast? hl
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hl
    have hpw : ((List.range n).filter fun i => nz i).Pairwise (· < ·) :=
      List.pairwise_lt_range.filter _
    have hmax : ∀ i, nz i → i ≤ e := fun i hi => by
      have hi' : i ∈ (List.range n).filter fun i => nz i := by
        rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨by have := hnz i hi; omega, hi⟩
      rw [hys] at hi' hpw
      rcases List.mem_append.1 hi' with h | h
      · exact (List.pairwise_append.1 hpw).2.2 i h e (List.mem_singleton_self _) |>.le
      · rw [List.mem_singleton.1 h]
    have he1 := hnz e hmem.2
    cases hq : ((List.range (e + 1)).filter fun i => ¬ nz i).getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hq
      refine ⟨0, e, Nat.zero_le _, he1, ?_, fun i _ hie => ?_, fun h => absurd h (lt_irrefl 0),
        fun i hi h => absurd (hmax i h) (by omega)⟩
      · unfold Chapter07.francisWindow
        refine List.filter_congr fun i _ => ?_
        show decide _ = decide _
        rw [decide_eq_decide, Option.elim_none]
        omega
      · have := hq i (List.mem_range.2 (by omega))
        simpa using this
    | some q =>
      have hqm := List.mem_of_getLast? hq
      rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hqm
      obtain ⟨zs, hzs⟩ := List.getLast?_eq_some_iff.1 hq
      have hpw' : ((List.range (e + 1)).filter fun i => ¬ nz i).Pairwise (· < ·) :=
        List.pairwise_lt_range.filter _
      have hqmax : ∀ i, i ≤ e → ¬ nz i → i ≤ q := fun i hi h => by
        have hi' : i ∈ (List.range (e + 1)).filter fun i => ¬ nz i := by
          rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
          exact ⟨by omega, h⟩
        rw [hzs] at hi' hpw'
        rcases List.mem_append.1 hi' with h | h
        · exact (List.pairwise_append.1 hpw').2.2 i h q (List.mem_singleton_self _) |>.le
        · rw [List.mem_singleton.1 h]
      have hqe : q < e := by
        rcases Nat.lt_or_ge q e with h | h
        · exact h
        · exact absurd hmem.2 (by rw [show e = q by omega]; exact hqm.2)
      refine ⟨q + 1, e, hqe, he1, ?_, fun i hi hie => ?_, fun _ => ?_,
        fun i hi h => absurd (hmax i h) (by omega)⟩
      · unfold Chapter07.francisWindow
        refine List.filter_congr fun i _ => ?_
        show decide _ = decide _
        rw [decide_eq_decide, Option.elim_some]
        omega
      · by_contra h
        have := hqmax i hie h
        omega
      · simpa using hqm.2

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The part of $D$ on the coupling $a$: the entries $(a + 1, a)$ and $(a, a + 1)$, with all other
entries $0$. -/
private def couplingPart (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  of fun r s => if (r : ℕ) = a + 1 ∧ s = a ∨ r = a ∧ (s : ℕ) = a + 1 then D r s else 0

/-- A matrix supported on two distinct positions has squared Frobenius norm equal to the sum of the
squares of its two entries. -/
private theorem frobenius_norm_sq_of_pair {X : Matrix (Fin n) (Fin n) ℝ} {p₁ p₂ : Fin n × Fin n}
    (hp : p₁ ≠ p₂) (hX : ∀ x : Fin n × Fin n, x ≠ p₁ → x ≠ p₂ → X x.1 x.2 = 0) :
    ‖X‖ ^ 2 = X p₁.1 p₁.2 ^ 2 + X p₂.1 p₂.2 ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq, ← Fintype.sum_prod_type']
  have hsub : ∑ x : Fin n × Fin n, ‖X x.1 x.2‖ ^ 2 =
      ∑ x ∈ ({p₁, p₂} : Finset (Fin n × Fin n)), ‖X x.1 x.2‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [hX x hx.1 hx.2, norm_zero, sq, mul_zero]
  rw [hsub, Finset.sum_pair hp, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

/-- For two distinct positions of a matrix $X$, the sum of the squares of the two entries is at most
$\|X\|_F^2$. -/
private theorem sq_add_sq_le_frobenius_norm_sq (X : Matrix (Fin n) (Fin n) ℝ)
    {p₁ p₂ : Fin n × Fin n} (hp : p₁ ≠ p₂) : X p₁.1 p₁.2 ^ 2 + X p₂.1 p₂.2 ^ 2 ≤ ‖X‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq, ← Fintype.sum_prod_type']
  have := Finset.sum_le_univ_sum_of_nonneg (s := ({p₁, p₂} : Finset (Fin n × Fin n)))
    (f := fun x : Fin n × Fin n => ‖X x.1 x.2‖ ^ 2) fun _ => by positivity
  rw [Finset.sum_pair hp] at this
  simpa only [Real.norm_eq_abs, sq_abs] using this

/-- For symmetric $D$, the coupling part of $D$ at $a$ has Frobenius norm $\sqrt{2} \, |d_{a+1,a}|$.
-/
private theorem norm_couplingPart_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsSymm) (a : Fin n)
    (h : (a : ℕ) + 1 < n) : ‖couplingPart D a‖ = √2 * |D ⟨a + 1, h⟩ a| := by
  set b : Fin n := ⟨a + 1, h⟩ with hb
  have hba : b ≠ a := fun e => by rw [Fin.ext_iff] at e; simp [b] at e
  have hsq := frobenius_norm_sq_of_pair (X := couplingPart D a) (p₁ := (b, a)) (p₂ := (a, b))
    (fun e => hba (Prod.ext_iff.1 e).1) fun x h1 h2 => by
      simp only [couplingPart, of_apply]
      refine ite_eq_right fun hx => ?_
      rcases hx with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact h1 (Prod.ext (Fin.ext h3) h4)
      · exact h2 (Prod.ext h3 (Fin.ext h4))
  have e1 : couplingPart D a b a = D b a := by simp [couplingPart, b]
  have e2 : couplingPart D a a b = D a b := by simp [couplingPart, b]
  simp only at hsq
  rw [e1, e2, hD.apply b a] at hsq
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, show D b a ^ 2 + D b a ^ 2 = 2 * D b a ^ 2 by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]

open Classical in
/-- The couplings that the deflation of Algorithm 8.3.3 newly sets to zero: those that are small and
nonzero. -/
private noncomputable def newZeros (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun a => IsSmallCoupling tol D a ∧ ∃ h : (a : ℕ) + 1 < n, D ⟨a + 1, h⟩ a ≠ 0

open Classical in
/-- The couplings $a$ of $D$ with $d_{a+1,a} = 0$. -/
private noncomputable def zeroCouplings (D : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ h : (a : ℕ) + 1 < n, D ⟨a + 1, h⟩ a = 0

/-- There are at most $n - 1$ zero couplings. -/
private theorem card_zeroCouplings_le (D : Matrix (Fin n) (Fin n) ℝ) :
    (zeroCouplings D).card ≤ n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (Finset.card_le_univ _).trans (by simp)
  have hsub : zeroCouplings D ⊆ Finset.univ.erase ⟨n - 1, by omega⟩ := fun a ha => by
    simp only [zeroCouplings, Finset.mem_filter] at ha
    obtain ⟨-, h, -⟩ := ha
    refine Finset.mem_erase.2 ⟨fun e => ?_, Finset.mem_univ _⟩
    rw [e] at h
    simp at h
    omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- The deflation adds exactly the new zeros to the zero couplings. -/
private theorem zeroCouplings_deflated (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    (zeroCouplings (deflated tol D)).card = (zeroCouplings D).card + (newZeros tol D).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext a
    simp only [zeroCouplings, newZeros, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h, h0⟩
      have hd := (deflated_apply_succ (tol := tol) (D := D) a h).1
      by_cases hs : IsSmallCoupling tol D a
      · by_cases hz : D ⟨a + 1, h⟩ a = 0
        · exact Or.inl ⟨h, hz⟩
        · exact Or.inr ⟨hs, h, hz⟩
      · rw [ite_eq_right hs] at hd
        exact Or.inl ⟨h, by rw [← h0]; exact hd.symm⟩
    · rintro (⟨h, h0⟩ | ⟨hs, h, -⟩)
      · refine ⟨h, ?_⟩
        have hd := (deflated_apply_succ (tol := tol) (D := D) a h).1
        by_cases hs : IsSmallCoupling tol D a
        · rw [ite_eq_left hs] at hd; exact hd
        · rw [ite_eq_right hs] at hd; rw [hd]; exact h0
      · refine ⟨h, ?_⟩
        have hd := (deflated_apply_succ (tol := tol) (D := D) a h).1
        rw [ite_eq_left hs] at hd
        exact hd
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [zeroCouplings, newZeros, Finset.mem_filter] at ha hb
    obtain ⟨-, h, h0⟩ := ha
    obtain ⟨-, -, h', hne⟩ := hb
    exact hne h0

/-- For symmetric $D$, the difference between $D$ and its deflation is the sum of the coupling parts
of the new zeros. -/
private theorem sub_deflated_eq_sum {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsSymm) :
    D - deflated tol D = ∑ a ∈ newZeros tol D, couplingPart D a := by
  classical
  ext r s
  rw [Matrix.sub_apply, Matrix.sum_apply]
  by_cases hrs : (r : ℕ) = s + 1 ∨ (s : ℕ) = r + 1
  swap
  · rw [deflated_apply_of_not hrs, sub_self]
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    rw [couplingPart, of_apply, ite_eq_right]
    rintro (⟨h1, rfl⟩ | ⟨rfl, h2⟩) <;> omega
  -- the coupling `c` of the entry
  obtain ⟨c, hc, hcr, hcs⟩ : ∃ c : Fin n, ∃ hc : (c : ℕ) + 1 < n,
      ((r = ⟨c + 1, hc⟩ ∧ s = c) ∨ (r = c ∧ s = ⟨c + 1, hc⟩)) ∧
        ∀ a : Fin n, ((r : ℕ) = a + 1 ∧ s = a ∨ r = a ∧ (s : ℕ) = a + 1) ↔ a = c := by
    rcases hrs with hrs | hrs
    · refine ⟨s, by omega, Or.inl ⟨Fin.ext hrs, rfl⟩, fun a => ⟨?_, ?_⟩⟩
      · rintro (⟨-, rfl⟩ | ⟨rfl, h2⟩)
        · rfl
        · omega
      · rintro rfl; exact Or.inl ⟨hrs, rfl⟩
    · refine ⟨r, by omega, Or.inr ⟨rfl, Fin.ext hrs⟩, fun a => ⟨?_, ?_⟩⟩
      · rintro (⟨h1, rfl⟩ | ⟨rfl, -⟩)
        · omega
        · rfl
      · rintro rfl; exact Or.inr ⟨rfl, hrs⟩
  have hsum : ∑ a ∈ newZeros tol D, couplingPart D a r s =
      if c ∈ newZeros tol D then D r s else 0 := by
    rw [← Finset.sum_ite_eq' (newZeros tol D) c (fun _ => D r s)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [couplingPart, of_apply]
    by_cases hac : a = c
    · rw [ite_eq_left ((hcs a).2 hac), ite_eq_left hac]
    · rw [ite_eq_right (fun h' => hac ((hcs a).1 h')), ite_eq_right hac]
  -- the entry of `D` at the coupling, and its deflation
  have hval : D r s = D ⟨c + 1, hc⟩ c := by
    rcases hcr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hD.apply _ _
  obtain ⟨hd1, hd2⟩ := deflated_apply_succ (tol := tol) (D := D) c hc
  have hdef : deflated tol D r s = if IsSmallCoupling tol D c then 0 else D r s := by
    rcases hcr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hd1
    · exact hd2
  rw [hsum, hdef]
  have hmem : c ∈ newZeros tol D ↔ IsSmallCoupling tol D c ∧ D r s ≠ 0 := by
    simp only [newZeros, Finset.mem_filter, Finset.mem_univ, true_and, hval]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hc, h2⟩⟩
  by_cases hs : IsSmallCoupling tol D c
  · rw [ite_eq_left hs, sub_zero]
    by_cases hz : D r s = 0
    · rw [ite_eq_right (fun h' => (hmem.1 h').2 hz), hz]
    · rw [ite_eq_left (hmem.2 ⟨hs, hz⟩)]
  · rw [ite_eq_right hs, sub_self, ite_eq_right (fun h' => hs (hmem.1 h').1)]

/-- The perturbation by the deflation: for $\mathrm{tol} \ge 0$ and symmetric $D$, the Frobenius
norm of $D$ minus its deflation is at most $2 \, \mathrm{tol} \, \|D\|_F$ times the number of
new zeros. A coupling $b$ with $|b| \le \mathrm{tol}(|x| + |y|)$ costs $\sqrt{2} |b| \le
\sqrt{2} \, \mathrm{tol} \sqrt{2} \sqrt{x^2 + y^2} \le 2 \, \mathrm{tol} \, \|D\|_F$. -/
private theorem norm_sub_deflated_le {tol : ℝ} (htol : 0 ≤ tol) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.IsSymm) :
    ‖D - deflated tol D‖ ≤ (newZeros tol D).card * (2 * tol * ‖D‖) := by
  rw [sub_deflated_eq_sum hD]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun a ha => ?_
  simp only [newZeros, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨⟨h, hsm⟩, -⟩ := ha
  have hsm' : |D ⟨a + 1, h⟩ a| ≤ tol * (|D a a| + |D ⟨a + 1, h⟩ ⟨a + 1, h⟩|) := hsm
  have hdiag := sq_add_sq_le_frobenius_norm_sq D (p₁ := (a, a))
    (p₂ := (⟨a + 1, h⟩, ⟨a + 1, h⟩)) fun e => by
      have := congrArg (fun x => (x.1 : ℕ)) e
      simp at this
  simp only at hdiag
  have hxy : |D a a| + |D ⟨a + 1, h⟩ ⟨a + 1, h⟩| ≤ √2 * ‖D‖ := by
    have h1 : (|D a a| + |D ⟨a + 1, h⟩ ⟨a + 1, h⟩|) ^ 2 ≤ 2 * ‖D‖ ^ 2 := by
      nlinarith [sq_nonneg (|D a a| - |D ⟨a + 1, h⟩ ⟨a + 1, h⟩|), sq_abs (D a a),
        sq_abs (D ⟨a + 1, h⟩ ⟨a + 1, h⟩)]
    have h2 := Real.abs_le_sqrt h1
    rwa [abs_of_nonneg (by positivity), Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (norm_nonneg _)] at h2
  calc ‖couplingPart D a‖ = √2 * |D ⟨a + 1, h⟩ a| := norm_couplingPart_eq hD a h
    _ ≤ √2 * (tol * (√2 * ‖D‖)) := by
        gcongr
        exact hsm'.trans (mul_le_mul_of_nonneg_left hxy htol)
    _ = 2 * tol * ‖D‖ := by
        rw [show √2 * (tol * (√2 * ‖D‖)) = (√2 * √2) * tol * ‖D‖ by ring,
          Real.mul_self_sqrt (by norm_num)]

end Frobenius

/-- The deflation keeps a matrix symmetric. -/
private theorem isSymm_deflated {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsSymm) :
    (deflated tol D).IsSymm := by
  ext i j
  rw [transpose_apply]
  by_cases hij : (i : ℕ) = j + 1 ∨ (j : ℕ) = i + 1
  · rcases hij with hij | hij
    · have hi : i = ⟨j + 1, by omega⟩ := Fin.ext hij
      obtain ⟨h1, h2⟩ := deflated_apply_succ (tol := tol) (D := D) j (by omega)
      simp only [Fin.eta] at h1 h2
      rw [hi, h1, h2, hD.apply ⟨j + 1, by omega⟩ j]
    · have hj : j = ⟨i + 1, by omega⟩ := Fin.ext hij
      obtain ⟨h1, h2⟩ := deflated_apply_succ (tol := tol) (D := D) i (by omega)
      simp only [Fin.eta] at h1 h2
      rw [hj, h1, h2, hD.apply ⟨i + 1, by omega⟩ i]
  · rw [deflated_apply_of_not hij, deflated_apply_of_not (by omega), hD.apply]

/-- The deflation keeps a matrix tridiagonal. -/
private theorem isTridiagonal_deflated {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.IsTridiagonal) : (deflated tol D).IsTridiagonal := fun i j hij => by
  have h : ¬ ((i : ℕ) = j + 1 ∨ (j : ℕ) = i + 1) := by
    rcases hij with ⟨k, h1, h2⟩ | ⟨k, h1, h2⟩ <;> rw [Fin.lt_def] at h1 h2 <;> omega
  rw [deflated_apply_of_not h]
  exact hD i j hij

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The loop invariant of Algorithm 8.3.3 on the state $(D, Q, \mathrm{done})$: $Q$ is orthogonal,
$D$ is symmetric and tridiagonal, $Q^T (A + F) Q = D$ for a symmetric $F$ (the deflations so
far, carried back to $A$) with $\|F\|_F$ at most $\kappa$ times the number of zero couplings of
$D$ whenever $2 \, \mathrm{tol} (\|A\|_F + \kappa (n - 1)) \le \kappa$, and $D$ is diagonal once
$\mathrm{done}$ holds. -/
private def SymmetricQRInv (A : Matrix (Fin n) (Fin n) ℝ) (tol κ : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ st.1.IsSymm ∧ st.1.IsTridiagonal ∧
    (∃ F : Matrix (Fin n) (Fin n) ℝ, Fᵀ = F ∧ st.2.1ᵀ * (A + F) * st.2.1 = st.1 ∧
      (2 * tol * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F‖ ≤ κ * (zeroCouplings st.1).card)) ∧
    (st.2.2 = true → ∀ i j, i ≠ j → st.1 i j = 0)

/-- One exact pass of Algorithm 8.3.3 keeps the loop invariant. -/
private theorem symmetricQRPass_inv {A : Matrix (Fin n) (Fin n) ℝ} {tol κ : ℝ} (htol : 0 ≤ tol)
    (hκ0 : 0 ≤ κ) {st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool}
    (h : SymmetricQRInv A tol κ st) :
    SymmetricQRInv A tol κ (Id.run (symmetricQRPass pure tol st)) := by
  obtain ⟨D, Q, done⟩ := st
  obtain ⟨hQ, hDs, hDt, ⟨F, hFs, hF, hFn⟩, hdone⟩ := h
  dsimp only at hQ hDs hDt hF hFn hdone
  cases done with
  | true => exact ⟨hQ, hDs, hDt, ⟨F, hFs, hF, hFn⟩, hdone⟩
  | false =>
  unfold symmetricQRPass
  simp only [Bool.false_eq_true, ↓reduceIte, Id.run_bind, deflate_pure]
  set D₁ := deflated tol D with hD₁
  have hD₁s : D₁.IsSymm := isSymm_deflated hDs
  have hD₁t : D₁.IsTridiagonal := isTridiagonal_deflated hDt
  have hQt : Qᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    refine (mem_orthogonalGroup_iff' _ ℝ).2 ?_
    rw [transpose_transpose]
    exact (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  -- the deflation, carried back
  set F₁ := F - Q * (D - D₁) * Qᵀ with hF₁
  have hF₁s : F₁ᵀ = F₁ := by
    rw [hF₁, transpose_sub, hFs, transpose_mul, transpose_mul, transpose_transpose, transpose_sub,
      hDs.eq, hD₁s.eq, Matrix.mul_assoc]
  have hF₁eq : Qᵀ * (A + F₁) * Q = D₁ := by
    have e : A + F₁ = (A + F) - Q * (D - D₁) * Qᵀ := by rw [hF₁]; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, hF]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ ℝ).1 hQ, Matrix.mul_one]
    abel
  have hF₁n : 2 * tol * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F₁‖ ≤ κ * (zeroCouplings D₁).card := by
    intro hκ
    have hFb := hFn hκ
    have hz := card_zeroCouplings_le D
    have hDn : ‖D‖ ≤ ‖A‖ + κ * (n - 1 : ℕ) := by
      rw [← hF, frobenius_norm_unitary_mul_mul_unitary hQt (A + F) hQ]
      have h1 := hFb.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.2 hz : ((zeroCouplings D).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ)) hκ0)
      linarith [norm_add_le A F]
    have hconj : ‖Q * (D - D₁) * Qᵀ‖ = ‖D - D₁‖ :=
      frobenius_norm_unitary_mul_mul_unitary hQ (D - D₁) hQt
    have he := norm_sub_deflated_le htol hDs (tol := tol)
    rw [zeroCouplings_deflated, Nat.cast_add]
    calc ‖F₁‖ ≤ ‖F‖ + ‖Q * (D - D₁) * Qᵀ‖ := norm_sub_le _ _
      _ ≤ κ * (zeroCouplings D).card + (newZeros tol D).card * (2 * tol * ‖D‖) := by
          rw [hconj]; exact add_le_add hFb he
      _ ≤ κ * (zeroCouplings D).card + (newZeros tol D).card * κ := by
          gcongr
          nlinarith
      _ = κ * ((zeroCouplings D).card + (newZeros tol D).card) := by ring
  -- the window of the unreduced block
  have hspec := lastRunWindow_spec (n := n)
    (nz := fun i => ∃ h : i + 1 < n, D₁ ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0) (fun i ⟨h, _⟩ => h)
  have hwin : unreducedWindow D₁ = lastRunWindow n
      (fun i => ∃ h : i + 1 < n, D₁ ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0) := rfl
  split
  · -- `q = n`: `D₁` is diagonal
    rename_i hw
    rw [Id.run_pure]
    refine ⟨hQ, hD₁s, hD₁t, ⟨F₁, hF₁s, hF₁eq, hF₁n⟩, fun _ i j hij => ?_⟩
    change D₁ i j = 0
    have hnz : ∀ i, ¬ ∃ h : i + 1 < n, D₁ ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0 := by
      rcases hspec with ⟨-, hno⟩ | ⟨p, e, hpe, he, hw', -⟩
      · exact hno
      · rw [← hwin, hw] at hw'
        have : (⟨p, by omega⟩ : Fin n) ∈ Chapter07.francisWindow n p (e + 2) :=
          Chapter07.mem_francisWindow.2 ⟨le_rfl, show p < e + 2 by omega⟩
        rw [← hw'] at this
        exact absurd this List.not_mem_nil
    have hsub : ∀ a : Fin n, ∀ h : (a : ℕ) + 1 < n, D₁ ⟨a + 1, h⟩ a = 0 := fun a h => by
      by_contra h0
      exact hnz a ⟨h, h0⟩
    rcases lt_trichotomy (i : ℕ) j with hl | he | hl
    · by_cases hj : (j : ℕ) = i + 1
      · rw [← hD₁s.apply, show j = ⟨i + 1, by omega⟩ from Fin.ext hj]
        exact hsub i (by omega)
      · exact hD₁t i j (Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp),
          Fin.lt_def.2 (by simp; omega)⟩)
    · exact absurd (Fin.ext he) hij
    · by_cases hi : (i : ℕ) = j + 1
      · rw [show i = ⟨j + 1, by omega⟩ from Fin.ext hi]
        exact hsub j (by omega)
      · exact hD₁t i j (Or.inl ⟨⟨j + 1, by omega⟩, Fin.lt_def.2 (by simp),
          Fin.lt_def.2 (by simp; omega)⟩)
  · -- `q < n`: Algorithm 8.3.2 on the window
    rename_i hne
    obtain ⟨p, e, hpe, he, hw', hrun, hbefore, hafter⟩ : ∃ p e : ℕ, p ≤ e ∧ e + 1 < n ∧
        unreducedWindow D₁ = Chapter07.francisWindow n p (e + 2) ∧
        (∀ i, p ≤ i → i ≤ e → ∃ h : i + 1 < n, D₁ ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0) ∧
        (0 < p → ¬ ∃ h : p - 1 + 1 < n, D₁ ⟨p - 1 + 1, h⟩ ⟨p - 1, by omega⟩ ≠ 0) ∧
        ∀ i, e < i → ¬ ∃ h : i + 1 < n, D₁ ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0 := by
      rcases hspec with ⟨hw0, -⟩ | ⟨p, e, hpe, he, hw', h1, h2, h3⟩
      · exact absurd (hwin.trans hw0) hne
      · exact ⟨p, e, hpe, he, hwin.trans hw', h1, h2, h3⟩
    rw [hw', Id.run_bind, Id.run_pure]
    obtain ⟨Z, hZo, hZb, h1, h2, hs, ht, -⟩ :=
      algorithm_8_3_2_window (p := p) (m := e + 2) (by omega) (by omega) hD₁s hD₁t Q
    -- `D₁` is decoupled along the window
    have hzl : ∀ i j : Fin n, (j : ℕ) + 1 = i → (i : ℕ) = p → D₁ i j = 0 := by
      intro i j hji hip
      have hp : 0 < p := by omega
      have hp1 : p - 1 + 1 < n := by omega
      have hp2 : p - 1 < n := by omega
      have := hbefore hp
      push Not at this
      have e1 : i = ⟨p - 1 + 1, hp1⟩ := Fin.ext (by simp only; omega)
      have e2 : j = ⟨p - 1, hp2⟩ := Fin.ext (by simp only; omega)
      subst e1 e2
      exact this hp1
    have hzr : ∀ i j : Fin n, (i : ℕ) + 1 = j → (i : ℕ) = e + 1 → D₁ i j = 0 := by
      intro i j hij hie
      have he2 : e + 1 + 1 < n := by omega
      have := hafter (e + 1) (by omega)
      push Not at this
      have e1 : j = ⟨e + 1 + 1, he2⟩ := Fin.ext (by simp only; omega)
      have e2 : i = ⟨e + 1, he⟩ := Fin.ext (by simp only; omega)
      subst e1 e2
      rw [← hD₁s.apply]
      exact this he2
    have hdec : ∀ i j : Fin n, (p ≤ (i : ℕ) ∧ (i : ℕ) < e + 2) →
        ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < e + 2) → D₁ i j = 0 ∧ D₁ j i = 0 := by
      intro i j hi hj
      suffices H : D₁ i j = 0 from ⟨H, by rw [← hD₁s.apply]; exact H⟩
      by_cases hji : (j : ℕ) + 1 = i
      · exact hzl i j hji (by omega)
      by_cases hij : (i : ℕ) + 1 = j
      · exact hzr i j hij (by omega)
      rcases lt_trichotomy (i : ℕ) j with hl | hl | hl
      · exact hD₁t i j (Or.inr ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp),
          Fin.lt_def.2 (by simp; omega)⟩)
      · exact absurd ⟨hl ▸ hi.1, hl ▸ hi.2⟩ hj
      · exact hD₁t i j (Or.inl ⟨⟨j + 1, by omega⟩, Fin.lt_def.2 (by simp),
          Fin.lt_def.2 (by simp; omega)⟩)
    have hconj := Chapter07.blockConj_eq_of_decoupled hZb hdec
    -- the zero couplings survive
    have hzero : (zeroCouplings D₁).card ≤
        (zeroCouplings (Id.run (algorithm_8_3_2 pure (Chapter07.francisWindow n p (e + 2))
          D₁ Q)).1).card := by
      refine Finset.card_le_card fun a ha => ?_
      simp only [zeroCouplings, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨h, h0⟩ := ha
      refine ⟨h, ?_⟩
      rw [h1]
      simp only [Chapter07.blockConj, of_apply]
      rw [ite_eq_right]
      · exact h0
      · rintro ⟨⟨-, h2⟩, h3, -⟩
        obtain ⟨_, hne0⟩ := hrun a h3 (by have h2' : (a : ℕ) + 1 < e + 2 := h2; omega)
        exact hne0 h0
    simp only [SymmetricQRInv]
    refine ⟨by rw [h2]; exact Submonoid.mul_mem _ hQ hZo, hs, ht, ⟨F₁, hF₁s, ?_, fun hκ => ?_⟩,
      fun h' => absurd h' (by simp)⟩
    · rw [h1, h2, hconj, ← hF₁eq, transpose_mul]
      simp only [Matrix.mul_assoc]
    · exact (hF₁n hκ).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hzero) hκ0)

/-- The deflation bound of Algorithms 8.3.3 and 8.6.2. Let $a, \mathrm{tol}, \nu \ge 0$, let
$N, z \in \mathbb{N}$ with $z \le N$, let $c = a N \mathrm{tol} < 1$, let $F \in \mathbb{R}$,
and let $\kappa = a \, \mathrm{tol} \, \nu / (1 - c)$. If
$a \, \mathrm{tol} (\nu + \kappa N) \le \kappa$ implies $F \le \kappa z$, then
$$F \le \frac{c \, \nu}{1 - c}.$$

In the applications, each pass perturbs by at most $a \, \mathrm{tol}$ times the current norm
per new zero, there are at most $N$ zeros, $\nu$ is $\|A\|_F$ and $F$ is the norm of the total
perturbation. The value $\kappa$ is the fixed point of
$\kappa = a \, \mathrm{tol} (\nu + \kappa N)$. -/
theorem deflation_bound {a tol nA F : ℝ} {N z : ℕ} (ha : 0 ≤ a) (htol : 0 ≤ tol) (hnA : 0 ≤ nA)
    (hc : a * N * tol < 1) (hz : z ≤ N)
    (hF : a * tol * (nA + a * tol * nA / (1 - a * N * tol) * N) ≤
        a * tol * nA / (1 - a * N * tol) → F ≤ a * tol * nA / (1 - a * N * tol) * z) :
    F ≤ a * N * tol * nA / (1 - a * N * tol) := by
  have h1c : 0 < 1 - a * N * tol := by linarith
  have hκ0 : 0 ≤ a * tol * nA / (1 - a * N * tol) := div_nonneg (by positivity) h1c.le
  have hne : 1 - a * N * tol ≠ 0 := h1c.ne'
  have hκeq : a * tol * (nA + a * tol * nA / (1 - a * N * tol) * N) =
      a * tol * nA / (1 - a * N * tol) := by
    rw [eq_div_iff hne, show a * tol * (nA + a * tol * nA / (1 - a * N * tol) * N) *
        (1 - a * N * tol) = a * tol * nA * (1 - a * N * tol) +
          a * tol * (a * tol * nA) * N * ((1 - a * N * tol) / (1 - a * N * tol)) by ring,
      div_self hne]
    ring
  calc F ≤ a * tol * nA / (1 - a * N * tol) * z := hF hκeq.le
    _ ≤ a * tol * nA / (1 - a * N * tol) * N :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hz) hκ0
    _ = _ := by
        rw [div_mul_eq_mul_div]
        congr 1
        ring

/-- **Algorithm 8.3.3** of [golub2013matrix] (symmetric QR algorithm), exact semantics. The source
says that the algorithm computes "an approximate symmetric Schur decomposition $Q^T A Q = D$".
Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $\mathrm{tol} \ge 0$ and
$\mathrm{fuel} \in \mathbb{N}$, and let $(D, Q, \mathrm{done})$ be the output of Algorithm 8.3.3
in exact arithmetic. Let $c = 2(n - 1)$. Then $Q$ is orthogonal, $D$ is symmetric and
tridiagonal, and there is a symmetric $E$ with
$$D = Q^T (A + E) Q, \qquad \|E\|_F \le \frac{c \, \mathrm{tol}}{1 - c \, \mathrm{tol}} \|A\|_F
  \quad \text{if } c \, \mathrm{tol} < 1.$$
If the loop stopped on its test within the fuel ($\mathrm{done}$, that is $q = n$), then $D$ is
diagonal.

The matrix $E$ is the sum of the deflations $d_{i+1,i} := 0$, carried back to $A$. Each
deflation zeroes a coupling with $|d_{i+1,i}| \le \mathrm{tol}(|d_{ii}| + |d_{i+1,i+1}|)$ of the
current $D$, of Frobenius norm $\sqrt{2} |d_{i+1,i}| \le 2 \, \mathrm{tol} \, \|D\|_F \le 2 \,
\mathrm{tol} (\|A\|_F + \|E\|_F)$, and a zeroed coupling stays zero, so there are at most
$n - 1$ deflations. The forward form $Q^T A Q = D + E$ with $E$ supported on the deflated
positions is false: a later rotation on a window $[p, \dots]$ mixes a deflated entry at
$(p, p - 1)$ into $(p + 1, p - 1)$. Convergence, that some finite fuel suffices, is Wilkinson's
theorem and is not claimed.

**Reading.** The exact-arithmetic theorem bounds threshold deflation error in Frobenius norm
for a finite prefix. Diagonalization requires the stop flag. The source describes the spectral-
norm effect of floating-point error for a completed run. -/
theorem algorithm_8_3_3_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {tol : ℝ}
    (htol : 0 ≤ tol) (fuel : ℕ) :
    let out := Id.run (algorithm_8_3_3 pure tol A fuel)
    out.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ out.1.IsSymm ∧ out.1.IsTridiagonal ∧
      (∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ out.2.1ᵀ * (A + E) * out.2.1 = out.1 ∧
        (2 * ((n - 1 : ℕ) : ℝ) * tol < 1 →
          ‖E‖ ≤ 2 * ((n - 1 : ℕ) : ℝ) * tol * ‖A‖ / (1 - 2 * ((n - 1 : ℕ) : ℝ) * tol))) ∧
      (out.2.2 = true → ∀ i j, i ≠ j → out.1 i j = 0) := by
  intro out
  set c : ℝ := 2 * ((n - 1 : ℕ) : ℝ) * tol with hc
  set κ : ℝ := if c < 1 then 2 * tol * ‖A‖ / (1 - c) else 0 with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    split_ifs with h
    · exact div_nonneg (by positivity) (by linarith)
    · exact le_rfl
  -- the initial state
  obtain ⟨hQ₀, -, hsymm₀, htri₀, hband₀, -, -⟩ := algorithm_8_3_1_spec hA
  have h0 : SymmetricQRInv A tol κ
      (tridiagonalPart (Id.run (algorithm_8_3_1 pure A)).1,
        Id.run (Chapter05.forwardAccumulation pure (Id.run (algorithm_8_3_1 pure A)).2),
        false) := by
    rw [Chapter05.forwardAccumulation_spec]
    refine ⟨hQ₀, ?_, ?_, ⟨0, transpose_zero, by rw [add_zero, hband₀], fun _ => ?_⟩,
      fun h => absurd h (by simp)⟩
    · rw [hband₀]; exact hsymm₀
    · rw [hband₀]; exact htri₀
    · rw [norm_zero]
      exact mul_nonneg hκ0 (Nat.cast_nonneg _)
  have key : SymmetricQRInv A tol κ out :=
    List.idRun_foldlM_induction (l := List.range fuel) (fun _ st => SymmetricQRInv A tol κ st) h0
      fun _ _ h => symmetricQRPass_inv htol hκ0 h
  obtain ⟨hQ, hDs, hDt, ⟨F, hFs, hF, hFn⟩, hdone⟩ := key
  refine ⟨hQ, hDs, hDt, ⟨F, hFs, hF, fun hc1 => ?_⟩, hdone⟩
  have hκ : κ = 2 * tol * ‖A‖ / (1 - c) := by rw [hκdef, ite_eq_left hc1]
  rw [hκ, hc] at hFn
  exact deflation_bound (by norm_num) htol (norm_nonneg _) hc1 (card_zeroCouplings_le out.1) hFn

/-- **Algorithm 8.3.3** of [golub2013matrix], the computed eigenvalues, "using Corollary 8.1.6". Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $\mathrm{tol} \ge 0$ and
$\mathrm{fuel} \in \mathbb{N}$, and let $(D, Q, \mathrm{done})$ be the output of Algorithm 8.3.3
in exact arithmetic, with $c = 2(n - 1)$. If $\mathrm{done}$ holds, then there is $E$ with
$A + E$ symmetric, $\|E\|_F \le c \, \mathrm{tol} \, \|A\|_F / (1 - c \, \mathrm{tol})$ if
$c \, \mathrm{tol} < 1$, and for every $k$:
* $\lambda_k(A + E)$ is a diagonal entry of $D$;
* $|\lambda_k(A + E) - \lambda_k(A)| \le \|E\|_2$.

The computed eigenvalues are the $\hat\lambda_i = d_{ii}$. The proof takes $E$ from
`GolubVanLoan.Chapter08.algorithm_8_3_3_spec`, for which $D = Q^T (A + E) Q$, and the bound is
`GolubVanLoan.Chapter08.corollary_8_1_6`.

**Reading.** The bound for the sorted diagonal results follows from exact-arithmetic threshold
deflation in Frobenius norm, conditional on stopping. The source discusses eigenvalue error in
terms of unit roundoff and the spectral norm. -/
theorem algorithm_8_3_3_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {tol : ℝ}
    (htol : 0 ≤ tol) (fuel : ℕ) :
    let out := Id.run (algorithm_8_3_3 pure tol A fuel)
    out.2.2 = true → ∃ (E : Matrix (Fin n) (Fin n) ℝ) (hAE : (A + E).IsSymm),
      (2 * ((n - 1 : ℕ) : ℝ) * tol < 1 →
        ‖E‖ ≤ 2 * ((n - 1 : ℕ) : ℝ) * tol * ‖A‖ / (1 - 2 * ((n - 1 : ℕ) : ℝ) * tol)) ∧
      ∀ k, (∃ i, symmEigenvalue hAE k = out.1 i i) ∧
        |symmEigenvalue hAE k - symmEigenvalue hA k| ≤ lpOpNorm 2 E := by
  intro out hdone
  obtain ⟨hQ, -, -, ⟨E, hEs, hEq, hEn⟩, hdiag⟩ := algorithm_8_3_3_spec hA htol fuel
  have hES : E.IsSymm := hEs
  have hAE : (A + E).IsSymm := hA.add hES
  refine ⟨E, hAE, hEn, fun k => ⟨?_, corollary_8_1_6 hA hES hAE k⟩⟩
  have hmem := symmEigenvalue_mem_spectrum hAE k
  have hD : out.1 = diagonal fun i => out.1 i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij]
      exact hdiag hdone i j hij
  have hsim : spectrum ℝ (A + E) = spectrum ℝ out.1 := by
    rw [← hEq]
    exact (spectrum.units_conjugate (u := ⟨out.2.1ᵀ, out.2.1,
      (mem_orthogonalGroup_iff' _ ℝ).1 hQ, (mem_orthogonalGroup_iff _ ℝ).1 hQ⟩)).symm
  rw [hsim, hD, spectrum_diagonal] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, hi.symm⟩

end Frobenius

end SymmetricQR

/-! ### The Rayleigh quotient connection (§8.3.6) -/

/-- **Section 8.3.6** of [golub2013matrix]. Let $T \in \mathbb{R}^{n \times n}$ with $n \ge 1$ be
symmetric, let $\sigma = t_{nn}$, let $T - \sigma I = QR$ be the QR factorization, and let $q_n$
be the last column of $Q$. Then
$$(T - \sigma I) q_n = r_{nn} e_n, \qquad r(e_n) = t_{nn},$$
and if $T - \sigma I$ is nonsingular, one step of Rayleigh quotient iteration (8.2.6) from
$x_0 = e_n$ gives $x_1 = \pm q_n$.

The factorization is the canonical `Matrix.qrQ`, `Matrix.qrR`, and the iteration is
`GolubVanLoan.Chapter08.rayleighQuotientIteration`.

**Reading.** The source identifies the next iterate with $q_n$. Lean assumes nonsingularity for
the Rayleigh solve and gives equality up to the sign of the diagonal element $r_{nn}$. -/
theorem rayleigh_qr_connection {N : ℕ} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT : T.IsSymm) :
    let σ := T (Fin.last N) (Fin.last N)
    let Q := qrQ (T - σ • 1)
    (T - σ • 1) *ᵥ Q.col (Fin.last N) =
        qrR (T - σ • 1) (Fin.last N) (Fin.last N) • Pi.single (Fin.last N) 1 ∧
      rayleighQuotient T (Pi.single (Fin.last N) 1) = σ ∧
      (IsUnit (T - σ • 1) →
        rayleighQuotientIteration T (Pi.single (Fin.last N) 1) 1 = Q.col (Fin.last N) ∨
          rayleighQuotientIteration T (Pi.single (Fin.last N) 1) 1 = -Q.col (Fin.last N)) := by
  intro σ Q
  have hsym : (T - σ • 1)ᵀ = T - σ • 1 := by
    rw [transpose_sub, transpose_smul, transpose_one, hT.eq]
  have h1 : (T - σ • 1) *ᵥ Q.col (Fin.last N) =
      qrR (T - σ • 1) (Fin.last N) (Fin.last N) • Pi.single (Fin.last N) 1 := by
    have h := toEuclideanLin_transpose_euclideanCol_qrQ_last (T - σ • 1)
    rw [hsym] at h
    exact congrArg WithLp.ofLp h
  have hr : rayleighQuotient T (Pi.single (Fin.last N) 1) = σ := by
    simp [rayleighQuotient, σ, col_apply]
  refine ⟨h1, hr, fun hu => ?_⟩
  set r := qrR (T - σ • 1) (Fin.last N) (Fin.last N)
  have hQQ : Qᴴ * Q = 1 := conjTranspose_qrQ_mul_self _
  have hqn : ‖(WithLp.toLp 2 (Q.col (Fin.last N)) : EuclideanSpace ℝ (Fin (N + 1)))‖ = 1 := by
    rw [← mulVec_single_one, ← toEuclideanLin_toLp,
      norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQQ]
    have := PiLp.norm_single (p := 2) (β := fun _ : Fin (N + 1) => ℝ) (Fin.last N) (1 : ℝ)
    rwa [norm_one] at this
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    have hinj := (Matrix.mulVec_injective_iff_isUnit).2 hu
    have : Q.col (Fin.last N) = 0 := hinj (by rw [h1, mulVec_zero])
    rw [this] at hqn
    simp at hqn
  -- `z = (T - σI)⁻¹ e_n = q_n / r`
  have hz : (T - rayleighQuotient T (Pi.single (Fin.last N) 1) • 1)⁻¹ *ᵥ
      Pi.single (Fin.last N) 1 = r⁻¹ • Q.col (Fin.last N) := by
    rw [hr]
    have hdet := (isUnit_iff_isUnit_det _).1 hu
    have : Pi.single (Fin.last N) (1 : ℝ) = r⁻¹ • ((T - σ • 1) *ᵥ Q.col (Fin.last N)) := by
      rw [h1, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [this, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  simp only [rayleighQuotientIteration]
  rw [hz, WithLp.toLp_smul, norm_smul, hqn, mul_one, smul_smul, Real.norm_eq_abs, abs_inv,
    inv_inv]
  rcases lt_or_gt_of_ne hr0 with h | h
  · right
    rw [abs_of_neg h, neg_mul, mul_inv_cancel₀ hr0, neg_smul, one_smul]
  · left
    rw [abs_of_pos h, mul_inv_cancel₀ hr0, one_smul]

/-! ### Orthogonal iteration with Ritz acceleration (§8.3.7) -/

/-- **Equation (8.3.6)** of [golub2013matrix], orthogonal iteration with Ritz acceleration. Let
$A \in \mathbb{R}^{n \times n}$. Sequences $Q_k, \tilde Q_k \in \mathbb{R}^{n \times r}$ and
$S_k, U_k, D_k \in \mathbb{R}^{r \times r}$ form a **Ritz-accelerated orthogonal iteration** for
$A$ if $Q_0^T Q_0 = I$ and, for every $k \ge 1$:
* $A Q_{k-1} = \tilde Q_k R_k$ is a thin QR factorization;
* $S_k = \tilde Q_k^T A \tilde Q_k$;
* $U_k$ is orthogonal and $U_k^T S_k U_k = D_k$ is diagonal (a Schur decomposition);
* $Q_k = \tilde Q_k U_k$.

The thin QR step is `Matrix.IsOrthogonalIterationStep`, which allows every choice of
factorization.

**Generalization.** The source works in the symmetric eigenproblem setting. The Lean predicate
takes any real $A$ and requires the projected orthogonal diagonalization as part of the iterate
data. -/
def IsRitzAcceleration {r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Q Qt : ℕ → Matrix (Fin n) (Fin r) ℝ) (S U D : ℕ → Matrix (Fin r) (Fin r) ℝ) : Prop :=
  (Q 0)ᵀ * Q 0 = 1 ∧ ∀ k, IsOrthogonalIterationStep A (Q k) (Qt (k + 1)) ∧
    S (k + 1) = (Qt (k + 1))ᵀ * A * Qt (k + 1) ∧ U (k + 1) ∈ orthogonalGroup (Fin r) ℝ ∧
    (U (k + 1))ᵀ * S (k + 1) * U (k + 1) = D (k + 1) ∧ (D (k + 1)).IsDiag ∧
    Q (k + 1) = Qt (k + 1) * U (k + 1)

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Section 8.3.7** of [golub2013matrix]. Let $Q_k, \tilde Q_k, S_k, U_k, D_k$ be a
Ritz-accelerated orthogonal iteration for $A \in \mathbb{R}^{n \times n}$. Then for every
$k \ge 1$
$$\|A Q_k - Q_k D_k\|_F = \|A \tilde Q_k - \tilde Q_k S_k\|_F = \min_{S \in \mathbb{R}^{r \times
  r}} \|A \tilde Q_k - \tilde Q_k S\|_F.$$
So the columns of $Q_k$ are the best basis from the standpoint of minimizing the residual.

The minimum is Theorem 8.1.14 (`GolubVanLoan.Chapter08.theorem_8_1_14`). The matrix $A$ need not
be symmetric.

**Reading.** The Lean equality minimizes over all small coefficient matrices for the current
thin basis and proves invariance under the specified Ritz rotation. It does not compare
different iterate subspaces. Symmetry of $A$ is unnecessary once the stated Ritz factors exist. -/
theorem ritzAcceleration_residual {r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q Qt : ℕ → Matrix (Fin n) (Fin r) ℝ} {S U D : ℕ → Matrix (Fin r) (Fin r) ℝ}
    (h : IsRitzAcceleration A Q Qt S U D) (k : ℕ) :
    ‖A * Q (k + 1) - Q (k + 1) * D (k + 1)‖ = ‖A * Qt (k + 1) - Qt (k + 1) * S (k + 1)‖ ∧
      IsLeast (Set.range fun B : Matrix (Fin r) (Fin r) ℝ => ‖A * Qt (k + 1) - Qt (k + 1) * B‖)
        ‖A * Qt (k + 1) - Qt (k + 1) * S (k + 1)‖ := by
  obtain ⟨-, hk⟩ := h
  obtain ⟨⟨R, hQR⟩, hS, hU, hD, -, hQ⟩ := hk k
  have hUU : U (k + 1) * (U (k + 1))ᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hQQ : (Qt (k + 1))ᵀ * Qt (k + 1) = 1 := by
    have := hQR.conjTranspose_mul_self
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨?_, ?_⟩
  · have e : A * Q (k + 1) - Q (k + 1) * D (k + 1) =
        (A * Qt (k + 1) - Qt (k + 1) * S (k + 1)) * U (k + 1) := by
      rw [hQ, ← hD, Matrix.sub_mul]
      congr 1
      · rw [Matrix.mul_assoc]
      · simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (Qt (k + 1)) (U (k + 1)), hUU, Matrix.mul_one]
    rw [e]
    have := frobenius_norm_unitary_mul_mul_unitary (one_mem (unitaryGroup (Fin n) ℝ))
      (A * Qt (k + 1) - Qt (k + 1) * S (k + 1)) hU
    rwa [Matrix.one_mul] at this
  · have e : A * Qt (k + 1) - Qt (k + 1) * S (k + 1) =
        (1 - Qt (k + 1) * (Qt (k + 1))ᵀ) * A * Qt (k + 1) := by
      rw [hS, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact theorem_8_1_14 A hQQ

end Frobenius

end GolubVanLoan.Chapter08
