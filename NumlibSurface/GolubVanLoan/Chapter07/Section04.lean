/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.Companion
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub and Van Loan, Section 7.4: The Hessenberg and Real Schur Forms

This module formalizes §7.4 of [golub2013matrix] for real matrices $A \in \mathbb{R}^{n \times n}$.
It covers the real Schur decomposition (Theorem 7.4.1), the QR step on an upper Hessenberg matrix by
Givens rotations (Algorithm 7.4.1), the Hessenberg decomposition $U_0^T A U_0 = H$ (7.4.3) and its
computation by Householder reflections (Algorithm 7.4.2) with Wilkinson's backward error bound, the
implicit Q theorem (Theorem 7.4.2), Krylov matrices and unreduced Hessenberg matrices (Theorem
7.4.3), the geometric multiplicity of the eigenvalues of an unreduced Hessenberg matrix (Theorem
7.4.4), and the companion matrix decomposition (7.4.4) with nonderogatory matrices (§7.4.6).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.RealSchur` (quasi-triangular
matrices), `Numlib.LinearAlgebra.Matrix.UnreducedHessenberg` (unreduced Hessenberg and Krylov
matrices), `Numlib.LinearAlgebra.Matrix.Companion` (companion matrices) and
`Numlib.FloatingPoint.Householder` (the rounding analysis of the Householder reduction). The
algorithms reuse the Householder and Givens programs of §5.1 and Algorithm 5.2.5.

## Main definitions

* Algorithm 7.4.1, `GolubVanLoan.Chapter07.algorithm_7_4_1`: one QR step on an upper Hessenberg
  matrix by $n - 1$ Givens rotations.
* §7.4.3, `GolubVanLoan.Chapter07.hessenbergPart`: the upper Hessenberg part of the array that
  Algorithm 7.4.2 returns.
* Algorithm 7.4.2, `GolubVanLoan.Chapter07.algorithm_7_4_2`: the Householder reduction to Hessenberg
  form.
* §7.4.5, `GolubVanLoan.Chapter07.IsUnreduced`: an upper Hessenberg matrix with no zero subdiagonal
  entries.
* §7.4.5, `GolubVanLoan.Chapter07.krylovMatrix`: the Krylov matrix $K(A, v, j) = [v \mid Av \mid
  \cdots \mid A^{j-1} v]$.
* (7.4.4), `GolubVanLoan.Chapter07.companion`: the companion matrix of $c_0, \dots, c_{n-1}$.
* §7.4.6, `GolubVanLoan.Chapter07.IsNonderogatory`: every eigenvalue has geometric multiplicity at
  most one.

## Main results

* Theorem 7.4.1, `GolubVanLoan.Chapter07.theorem_7_4_1`: every real matrix is orthogonally similar
  to an upper quasi-triangular matrix whose $2 \times 2$ diagonal blocks have no real eigenvalue.
* Algorithm 7.4.1, `GolubVanLoan.Chapter07.algorithm_7_4_1_spec`: in exact arithmetic the algorithm
  computes $H_+ = RQ$ for $H = QR$, and $Q$ and $H_+$ are upper Hessenberg.
* (7.4.3), `GolubVanLoan.Chapter07.equation_7_4_3`: every real matrix has a Hessenberg decomposition
  $U_0^T A U_0 = H$ with $U_0 e_1 = e_1$.
* Algorithm 7.4.2, `GolubVanLoan.Chapter07.algorithm_7_4_2_spec`: in exact arithmetic the algorithm
  computes a Hessenberg decomposition.
* §7.4.3, `GolubVanLoan.Chapter07.algorithm_7_4_2_rounds`: every run in the rounding model is a
  sequence of computed Householder steps of the backbone.
* §7.4.3, `GolubVanLoan.Chapter07.algorithm_7_4_2_rounding`: the computed $\hat H$ satisfies
  $\hat H = Q^T (A + E) Q$ with $Q$ orthogonal and $\|E\|_F$ of order $n^2 u \|A\|_F$.
* Theorem 7.4.2, `GolubVanLoan.Chapter07.theorem_7_4_2`: the implicit Q theorem.
* Theorem 7.4.2, `GolubVanLoan.Chapter07.theorem_7_4_2_essential`: if $H$ is unreduced, then
  $Z = QD$ and $G = DHD$ with $D = \operatorname{diag}(\pm 1)$.
* Theorem 7.4.3, `GolubVanLoan.Chapter07.theorem_7_4_3`: $Q^T A Q$ is unreduced upper Hessenberg if
  and only if $Q^T K(A, Q(:,1), n)$ is nonsingular upper triangular.
* Theorem 7.4.4, `GolubVanLoan.Chapter07.theorem_7_4_4`: every eigenvalue of an unreduced upper
  Hessenberg matrix has geometric multiplicity one.
* (7.4.4), `GolubVanLoan.Chapter07.equation_7_4_4`: if $K(A, x, n) c = -A^n x$, then $A K = K C$ for
  the companion matrix $C$.
* §7.4.6, `GolubVanLoan.Chapter07.isNonderogatory_of_isSimilar_unreduced`: a matrix similar to an
  unreduced Hessenberg matrix is nonderogatory.

## Conventions

* The matrices are real, `Matrix (Fin n) (Fin n) ℝ`. An orthogonal matrix is an element of
  `Matrix.orthogonalGroup (Fin n) ℝ`, and the transpose $Q^T$ is `Qᵀ`. The complex eigenvalues of a
  real matrix are those of `Matrix.complexify`.
* Upper quasi-triangular is `Matrix.IsQuasiUpperTriangular`. Unreduced upper Hessenberg is
  `Matrix.IsUnreducedUpperHessenberg`, which is `GolubVanLoan.Chapter07.IsUnreduced` here.
* Indices are 0-based. The source's $h_{k+1,k}$ for $k = 1, \dots, n - 1$ is `H ⟨k+1, _⟩ ⟨k, _⟩` for
  $k < n - 1$.

## Implementation notes

* Algorithm 7.4.1 calls Algorithm 5.2.5 for its first loop, as the source does ("See Algorithm
  5.2.5"). Its second loop applies `GolubVanLoan.Chapter05.givensApplyRight` on the index lists
  `GolubVanLoan.Chapter05.indexTo`. The theorem `GolubVanLoan.Chapter07.algorithm_7_4_1_spec` gives
  its exact semantics; the source gives no rounding analysis.
* Algorithm 7.4.2 is built from the programs `GolubVanLoan.Chapter05.houseOn`,
  `GolubVanLoan.Chapter05.householderApplyLeft` and `GolubVanLoan.Chapter05.householderApplyRight`
  on index lists, with one pass `GolubVanLoan.Chapter07.hessenbergReduceStep` per column. It stores
  the Householder vectors below the subdiagonal, and it also returns the reflector data, the pairs
  $(v, \beta)$ with the $\beta$ that `house` returned.
* The orthogonal factor is `GolubVanLoan.Chapter05.householderProduct` of the returned data. It is
  never rebuilt from a stored vector with $\beta = 2/(v^T v)$: when `house` returns $\beta = 0$, the
  rebuilt matrix $I - 2 e_1 e_1^T$ is not the identity that was applied.
* The exact semantics of Algorithm 7.4.2 is `GolubVanLoan.Chapter07.algorithm_7_4_2_spec`. The
  theorem `GolubVanLoan.Chapter07.algorithm_7_4_2_rounds` relates every run in the relational
  rounding model to `FloatingPoint.RoundsHessenbergReducePert`, and
  `GolubVanLoan.Chapter07.algorithm_7_4_2_rounding` is Wilkinson's backward error bound with an
  explicit constant.

## Deviations from the source

* **Algorithm 7.4.2** (reading). The program returns the compact storage array and a separate
  list of reflector vectors and coefficients. The upper Hessenberg part of the array is $H$. See
  `GolubVanLoan.Chapter07.algorithm_7_4_2`.
* **§7.4.3, rounding analysis** (reading). The source states a bound with an unspecified
  constant times $n^2u$. The theorem gives an explicit nested $\gamma$ bound with idempotent
  rounding and quantitative smallness assumptions. See
  `GolubVanLoan.Chapter07.algorithm_7_4_2_rounding`.
* **Theorem 7.4.2** (generalization). The first part allows any prefix with nonzero subdiagonal
  entries. The essential-uniqueness statement requires only one unreduced output. See
  `GolubVanLoan.Chapter07.theorem_7_4_2` and `GolubVanLoan.Chapter07.theorem_7_4_2_essential`.
* **Theorem 7.4.4** (typo). The proof's rank calculation concerns $H - \lambda I$, printed as $A
  - \lambda I$. See `GolubVanLoan.Chapter07.theorem_7_4_4`.
* **Equation (7.4.4)** (generalization). The identity $AK=KC$ needs only a solution of $Kc=-A^n
  x$. Nonsingularity is required for the similarity conclusion. See
  `GolubVanLoan.Chapter07.equation_7_4_4`.

## Not formalized

* **§7.4.4, the level-3 block Hessenberg reduction and the WY form.** It is a discussion at the
  level of BLAS operations.
* **The flop counts.**
* **The remark that the computation of eigenvalues through the companion matrix "can be highly
  unstable".** The source makes no precise statement.
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.4.1 The real Schur decomposition -/

/-- **Theorem 7.4.1** of [golub2013matrix] (real Schur decomposition). For every
$A \in \mathbb{R}^{n \times n}$ there is an orthogonal $Q \in \mathbb{R}^{n \times n}$ such that
$Q^T A Q$ is upper quasi-triangular, as in (7.4.2): it is block upper triangular with diagonal
blocks $R_{ii}$ of size $1 \times 1$ or $2 \times 2$, and each $2 \times 2$ diagonal block has
no real eigenvalue, so that its eigenvalues are a pair of complex conjugate nonreal numbers.

The block structure is a monotone block index `p : Fin n → ℕ` whose fibres have at most two
elements, with $Q^T A Q$ block triangular for it in the sense of `Matrix.BlockTriangular`. That
a $2 \times 2$ block has no real eigenvalue is stated as: no real $\mu$ is in the real spectrum
of the block. -/
theorem theorem_7_4_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, (Qᵀ * A * Q).IsQuasiUpperTriangular ∧
      ∃ p : Fin n → ℕ, Monotone p ∧ (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
        (Qᵀ * A * Q).BlockTriangular p ∧
        ∀ k, (Finset.univ.filter fun i => p i = k).card = 2 → ∀ μ : ℝ,
          μ ∉ spectrum ℝ ((Qᵀ * A * Q).toBlock (fun i => p i = k) (fun i => p i = k)) := by
  obtain ⟨Q, hQ, p, hp, hcard, htri, hirr⟩ :=
    exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks A
  exact ⟨Q, hQ, ⟨p, hp, hcard, htri⟩, p, hp, hcard, htri, hirr⟩

/-! ### §7.4.2 A Hessenberg QR step: Algorithm 7.4.1 -/

section HessenbergQRStep

open GolubVanLoan.Chapter05

/-- **Algorithm 7.4.1** of [golub2013matrix] (Hessenberg QR step). "If $H$ is an $n$-by-$n$ upper
Hessenberg matrix, then this algorithm overwrites $H$ with $H_+ = RQ$ where $H = QR$ is the QR
factorization of $H$":
```
for k = 1:n-1
    [c_k, s_k] = givens(H(k, k), H(k+1, k))
    H(k:k+1, k:n) = [c_k s_k; -s_k c_k]ᵀ H(k:k+1, k:n)
end
for k = 1:n-1
    H(1:k+1, k:k+1) = H(1:k+1, k:k+1) [c_k s_k; -s_k c_k]
end
```

The matrix has size $n = k + 1$ for the Lean argument $k$. The first loop is Algorithm 5.2.5,
`GolubVanLoan.Chapter05.algorithm_5_2_5`, which also returns the rotations $(c_k, s_k)$. The
second loop applies them with `GolubVanLoan.Chapter05.givensApplyRight`, in step $k$ of the loop
on the rows $1, \dots, k + 1$ of the source. Every arithmetic result passes through the rounding
hook `rnd`; the hook `pure` in the monad `Id` gives exact arithmetic. -/
noncomputable def algorithm_7_4_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {k : ℕ}
    (H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := do
  let st ← algorithm_5_2_5 rnd H
  (List.finRange k).foldlM (fun (H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin k) =>
    givensApplyRight rnd j.castSucc j.succ (st.2 j).1 (st.2 j).2 (indexTo (k + 1) (j + 1)) H)
    st.1

/-- In the second loop of Algorithm 7.4.1 started from an upper triangular $R$, the array after $t$
passes is $R G_1 \cdots G_t$, because the rows that each update leaves out are zero in the
affected columns. -/
private theorem foldl_givensApplyRight_eq {k : ℕ} (cs : Fin k → ℝ × ℝ)
    {R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hR : R.IsUpperTriangular) :
    ∀ t ≤ k, ((List.finRange k).take t).foldl
      (fun (H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin k) =>
        Id.run (givensApplyRight pure j.castSucc j.succ (cs j).1 (cs j).2
          (indexTo (k + 1) (j + 1)) H))
      R = R * hessenbergRotationsProd cs t := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [hessenbergRotationsProd]
  | succ t ih =>
    intro ht
    rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hget : (List.finRange k)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
    rw [hget, ih (by omega), hessenbergRotationsProd_succ _ ht]
    set j : Fin k := ⟨t, ht⟩ with hj
    set a : Fin (k + 1) := j.castSucc with ha
    set b : Fin (k + 1) := j.succ with hb
    have hav : (a : ℕ) = t := rfl
    have hbv : (b : ℕ) = t + 1 := rfl
    have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
    obtain ⟨hH, hI⟩ := hessenbergRotationsProd_shape cs t (by omega)
    rw [givensApplyRight_spec hab _ _ (nodup_indexTo _ _)]
    ext r q
    rw [of_apply, ← Matrix.mul_assoc]
    split_ifs with hr
    · rfl
    · have hr' : t + 1 < (r : ℕ) := by
        simp only [mem_indexTo, not_le] at hr
        simpa [hj] using hr
      have hzero : ∀ c : Fin (k + 1), (c : ℕ) ≤ t + 1 →
          (R * hessenbergRotationsProd cs t) r c = 0 := by
        intro c hc
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hlr : l < r
        · rw [hR hlr, zero_mul]
        · have hl : t + 1 < (l : ℕ) := by
            have := not_lt.1 hlr
            have : (r : ℕ) ≤ l := this
            omega
          rcases Nat.lt_or_ge t (c : ℕ) with hct | hct
          · rw [hI l c hct, ite_eq_right (fun h => by rw [h] at hl; omega), mul_zero]
          · rw [hH l c (by omega), mul_zero]
      rw [givensRotation, mul_planeRotation_apply hab]
      split_ifs with hqa hqb
      · rw [hzero a (by omega), hzero b (by omega), hqa, hzero a (by omega)]; ring
      · rw [hzero a (by omega), hzero b (by omega), hqb, hzero b (by omega)]; ring
      · rfl

/-- **Algorithm 7.4.1** of [golub2013matrix], correctness in exact arithmetic. Let
$H \in \mathbb{R}^{n \times n}$ be upper Hessenberg with $n \ge 1$, and let $H_+$ be the output
of Algorithm 7.4.1 in exact arithmetic. Then there are an orthogonal $Q$ and an upper triangular
$R$ with
$$H = QR, \qquad H_+ = RQ,$$
so that $H_+$ is obtained from $H$ by a QR step. Moreover $Q$ and $H_+$ are upper Hessenberg:
"It is easy to confirm that the matrix $Q = G_1 \cdots G_{n-1}$ is upper Hessenberg. Thus,
$RQ = H_+$ is also upper Hessenberg."

The output in exact arithmetic is `Id.run (algorithm_7_4_1 pure H)`, and the QR step is also
stated as `Matrix.IsShiftedQrStep` with shift $0$. The source gives no rounding analysis of the
algorithm. The proof uses `GolubVanLoan.Chapter05.algorithm_5_2_5_spec` for the factorization. -/
theorem algorithm_7_4_1_spec {k : ℕ} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (hH : H.IsUpperHessenberg) :
    IsShiftedQrStep 0 H (Id.run (algorithm_7_4_1 pure H)) ∧
      ∃ Q ∈ orthogonalGroup (Fin (k + 1)) ℝ, ∃ R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ,
        R.IsUpperTriangular ∧ H = Q * R ∧ Id.run (algorithm_7_4_1 pure H) = R * Q ∧
          Q.IsUpperHessenberg ∧ (Id.run (algorithm_7_4_1 pure H)).IsUpperHessenberg := by
  obtain ⟨hQR, hQH⟩ := algorithm_5_2_5_spec H hH
  set st := Id.run (algorithm_5_2_5 pure H) with hst
  set Q := (List.ofFn fun j : Fin k => givensRotation j.castSucc j.succ (st.2 j).1
    (st.2 j).2).prod with hQ
  have hRt : st.1.IsUpperTriangular := fun i j hij => hQR.apply_eq_zero i j hij
  have hQeq : Q = hessenbergRotationsProd st.2 k := by
    rw [hQ, hessenbergRotationsProd, List.take_of_length_le (by simp), List.ofFn_eq_map]
  have hrun : Id.run (algorithm_7_4_1 pure H) = st.1 * Q := by
    rw [hQeq, ← foldl_givensApplyRight_eq st.2 hRt k le_rfl, List.take_of_length_le (by simp)]
    change Id.run (List.foldlM (fun (H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin k) =>
      givensApplyRight pure j.castSucc j.succ (st.2 j).1 (st.2 j).2 (indexTo (k + 1) (j + 1)) H)
      st.1 (List.finRange k)) = _
    rw [List.idRun_foldlM]
  have hHQR : H = Q * st.1 := hQR.mul_eq.symm
  have hH' : (st.1 * Q).IsUpperHessenberg := hRt.mul_isUpperHessenberg hQH
  refine ⟨⟨Q, hQR.mem_unitaryGroup, st.1, hRt, by rw [zero_smul, sub_zero, hHQR], ?_⟩,
    Q, hQR.mem_unitaryGroup, st.1, hRt, hHQR, hrun, hQH, hrun ▸ hH'⟩
  rw [hrun, zero_smul, add_zero]

end HessenbergQRStep

/-! ### §7.4.3 The Hessenberg decomposition -/

/-- **Equation (7.4.3)** of [golub2013matrix] (Hessenberg decomposition). For every
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$ there is an orthogonal
$U_0 \in \mathbb{R}^{n \times n}$ such that $U_0^T A U_0$ is upper Hessenberg and
$U_0 e_1 = e_1$.

The condition $U_0 e_1 = e_1$ holds because the reflectors of the Householder reduction act only
on the coordinates $2, \dots, n$. -/
theorem equation_7_4_3 {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∃ U₀ ∈ orthogonalGroup (Fin (N + 1)) ℝ, (U₀ᵀ * A * U₀).IsUpperHessenberg ∧
      U₀ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  refine ⟨hessenbergQ A, hessenbergQ_mem_orthogonalGroup A, ?_, ?_⟩
  · have h := isUpperHessenberg_hessenbergReduce (A := A)
    rwa [hessenbergReduce_eq_conj, conjTranspose_eq_transpose_of_trivial] at h
  · ext i
    rw [mulVec_single_one, col_apply, hessenbergQ_apply_zero, Matrix.one_apply, Pi.single_apply]

/-- **Section 7.4.3** of [golub2013matrix], the array of Algorithm 7.4.2. For
$A \in \mathbb{R}^{n \times n}$, the matrix with the entries $a_{ij}$ of $A$ on and above the
subdiagonal ($i \le j + 1$) and $0$ below it. Algorithm 7.4.2 returns an array that holds $H$ in
its upper Hessenberg part and the essential parts of the Householder vectors below the
subdiagonal ("The $k$th Householder matrix can be represented in $A(k+2{:}n, k)$"); this
function reads $H$ from the array. -/
def hessenbergPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) ≤ j + 1 then A i j else 0

/-! ### §7.4.3 The Householder reduction: Algorithm 7.4.2 -/

section HessenbergReduction

open FloatingPoint GolubVanLoan.Chapter05

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of Algorithm 7.4.2 of [golub2013matrix], on a state that consists of the array and the
list of reflector data. For the source's step $k$, with $k = 1, \dots, n - 2$ and Lean argument
$k - 1$, the pass computes
```
[v, β] = house(A(k+1:n, k))
A(k+1:n, k:n) = (I - β v vᵀ) A(k+1:n, k:n)
A(1:n, k+1:n) = A(1:n, k+1:n) (I - β v vᵀ)
```
then stores $v(k+2{:}n)$ in $A(k+2{:}n, k)$ and appends the pair $(v, \beta)$ to the data.

The copy of $v$ into the array is exact. Here `house` is `GolubVanLoan.Chapter05.houseOn` on the
0-based index list $[k, \dots, n-1]$, so $v$ is zero off this list and $1$ at its first index,
and $\beta$ is the value that `house` returned. The two updates are
`GolubVanLoan.Chapter05.householderApplyLeft` and `GolubVanLoan.Chapter05.householderApplyRight`
on index lists. -/
noncomputable def hessenbergReduceStep
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) (k : Fin (n - 2)) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) := do
  let vβ ← houseOn rnd (indexFrom n (k + 1)) fun i => st.1 i (Fin.castLE (Nat.sub_le n 2) k)
  let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom n (k + 1)) (indexFrom n k) st.1
  let A ← householderApplyRight rnd vβ.1 vβ.2 (List.finRange n) (indexFrom n (k + 1)) A
  pure (of fun i j => if j = Fin.castLE (Nat.sub_le n 2) k ∧ (k : ℕ) + 2 ≤ i then vβ.1 i
    else A i j, st.2 ++ [vβ])

/-- **Algorithm 7.4.2** of [golub2013matrix] (Householder reduction to Hessenberg form). "Given
$A \in \mathbb{R}^{n \times n}$, the following algorithm overwrites $A$ with $H = U_0^T A U_0$
where $H$ is upper Hessenberg and $U_0$ is a product of Householder matrices": for
$k = 1, \dots, n - 2$ it runs one pass, `GolubVanLoan.Chapter07.hessenbergReduceStep`. The
program returns the array, which holds $H$ in its upper Hessenberg part and the Householder
vectors below it, together with the reflector data $[(v_1, \beta_1), \dots, (v_{n-2},
\beta_{n-2})]$.

The data give $U_0$ as `GolubVanLoan.Chapter05.householderProduct`, without rebuilding a
reflector from a stored vector. The matrix $H$ is `GolubVanLoan.Chapter07.hessenbergPart` of the
array. Every arithmetic result passes through the rounding hook `rnd`.

**Reading.** The source permits compact storage below the subdiagonal. The program returns that
array together with the reflector vectors and coefficients, so the Hessenberg matrix is its
`hessenbergPart`. -/
noncomputable def algorithm_7_4_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) :=
  (List.finRange (n - 2)).foldlM (hessenbergReduceStep rnd) (A, [])

end Programs

/-- The invariant of Algorithm 7.4.2 after $t$ passes, in exact arithmetic. A state (array, data)
satisfies it for the input $A_0$ when the following hold. The data has $t$ entries $(v, \beta)$,
each with $\beta = 0$ or $\beta v^T v = 2$, and the $l$-th vector (0-based) vanishes at the
indices $\le l$. Let $U_t$ be the product of the reflectors of the data and $W = U_t^T A_0 U_t$;
then $W$ vanishes below the subdiagonal in the columns $j < t$, and the array agrees with $W$ at
all other entries. The invariant puts no condition on the array below the subdiagonal in the
columns $j < t$, where the algorithm stores the Householder vectors. -/
def HessenbergReduceInv (A₀ : Matrix (Fin n) (Fin n) ℝ) (t : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) : Prop :=
  st.2.length = t ∧
  (∀ p ∈ st.2, p.2 = 0 ∨ p.2 * (p.1 ⬝ᵥ p.1) = 2) ∧
  (∀ (l : ℕ) (hl : l < st.2.length) (j : Fin n), (j : ℕ) ≤ l → (st.2[l]).1 j = 0) ∧
  ∀ i j : Fin n, ((j : ℕ) < t ∧ (j : ℕ) + 2 ≤ i →
      ((householderProduct st.2)ᵀ * A₀ * householderProduct st.2) i j = 0) ∧
    (¬((j : ℕ) < t ∧ (j : ℕ) + 2 ≤ i) →
      st.1 i j = ((householderProduct st.2)ᵀ * A₀ * householderProduct st.2) i j)

/-- A reflector $I - \beta v v^T$ with $v$ zero off the list $o$ agrees with the identity in the
rows that are not in $o$. -/
private theorem reflector_apply_of_not_mem {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) {i : Fin n} (hi : i ∉ o) (j : Fin n) :
    (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ) i j =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp [vecMulVec_apply, hv i hi]

/-- If $v$ is zero off the list $o$, the entries of $N (I - \beta v v^T)$ in the columns of $o$
depend only on the entries of $N$ in the columns of $o$. -/
private theorem mul_reflector_apply_congr {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) {N₁ N₂ : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (hN : ∀ l ∈ o, N₁ i l = N₂ i l) {j : Fin n} (hj : j ∈ o) :
    (N₁ * (1 - β • vecMulVec v v)) i j = (N₂ * (1 - β • vecMulVec v v)) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ o
  · rw [hN l hl]
  · rw [reflector_apply_of_not_mem hv β hl, one_apply_ne (fun h => hl (by rw [h]; exact hj)),
      mul_zero, mul_zero]

/-- One exact pass of Algorithm 7.4.2 keeps the invariant: if a state satisfies
`GolubVanLoan.Chapter07.HessenbergReduceInv` for $A_0$ after $k$ passes, then the state after
the next pass satisfies it after $k + 1$ passes. This is the derivation of the algorithm in the
source: with $P_k = \operatorname{diag}(I_k, \tilde P_k)$, the matrix
$(P_1 \cdots P_k)^T A (P_1 \cdots P_k)$ is upper Hessenberg in its first $k$ columns. -/
theorem hessenbergReduceStep_inv {A₀ : Matrix (Fin n) (Fin n) ℝ} (k : Fin (n - 2))
    {st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (h : HessenbergReduceInv A₀ k st) :
    HessenbergReduceInv A₀ (k + 1) (Id.run (hessenbergReduceStep pure st k)) := by
  obtain ⟨hlen, hβ, hsupp, hW⟩ := h
  set k' : Fin n := Fin.castLE (Nat.sub_le n 2) k with hk'
  have hk'v : (k' : ℕ) = k := rfl
  have hkn : (k : ℕ) + 2 < n := by have := k.2; omega
  set o := indexFrom n (k + 1) with ho
  have hmo : ∀ i : Fin n, i ∈ o ↔ (k : ℕ) + 1 ≤ i := fun i => by simp [ho]
  have hone : o ≠ [] := indexFrom_ne_nil (by omega)
  set x : Fin n → ℝ := fun i => st.1 i k' with hx
  obtain ⟨-, hvout, hβv, -, hPx⟩ := houseOn_spec (nodup_indexFrom n (k + 1)) hone x
  set vβ := Id.run (houseOn pure o x) with hvβ
  set P : Matrix (Fin n) (Fin n) ℝ := 1 - vβ.2 • vecMulVec vβ.1 vβ.1 with hP
  set U := householderProduct st.2 with hU
  set W := Uᵀ * A₀ * U with hWdef
  set B := Id.run (householderApplyLeft pure vβ.1 vβ.2 o (indexFrom n k) st.1) with hB
  set C := Id.run (householderApplyRight pure vβ.1 vβ.2 (List.finRange n) o B) with hC
  have hrun : Id.run (hessenbergReduceStep pure st k) =
      (of fun (i j : Fin n) => if j = k' ∧ (k : ℕ) + 2 ≤ i then vβ.1 i else C i j,
        st.2 ++ [vβ]) := rfl
  have hBeq : B = of fun i q => if q ∈ indexFrom n k then (P * st.1) i q else st.1 i q :=
    householderApplyLeft_spec (nodup_indexFrom n (k + 1)) (nodup_indexFrom n k) hvout _ _
  have hCeq : C = B * P :=
    householderApplyRight_spec_of_forall_mem (List.nodup_finRange n) (nodup_indexFrom n (k + 1))
      List.mem_finRange hvout _ _
  have hU' : householderProduct (st.2 ++ [vβ]) = U * P := householderProduct_concat _ _
  have hW' : (householderProduct (st.2 ++ [vβ]))ᵀ * A₀ * householderProduct (st.2 ++ [vβ]) =
      P * W * P := by
    rw [hU', transpose_mul, hP, transpose_one_sub_smul_vecMulVec, hWdef]
    simp only [Matrix.mul_assoc]
  -- the column `k` of `W` is `x`
  have hWx : ∀ l, W l k' = x l := fun l => ((hW l k').2 (by rw [hk'v]; omega)).symm
  -- the columns `< k` of `W` vanish on `o`
  have hWo : ∀ j : Fin n, (j : ℕ) < k → ∀ l ∈ o, W l j = 0 :=
    fun j hj l hl => (hW l j).1 ⟨hj, by have := (hmo l).1 hl; omega⟩
  -- the columns `≥ k` of `A` are those of `W`
  have hAW : ∀ l : Fin n, ∀ j : Fin n, (k : ℕ) ≤ j → st.1 l j = W l j :=
    fun l j hj => (hW l j).2 (by omega)
  rw [hrun]
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hβ p hp
    · rw [List.mem_singleton.1 hp]; exact hβv
  · intro l hl j hj
    dsimp only at hl ⊢
    rcases Nat.lt_or_ge l st.2.length with hl' | hl'
    · rw [List.getElem_append_left hl']
      exact hsupp l hl' j hj
    · have hlk : l = k := by simp at hl; omega
      rw [List.getElem_append_right hl']
      simp only [hlen, hlk, Nat.sub_self, List.getElem_cons_zero]
      exact hvout j (by rw [hmo]; omega)
  · intro i j
    rw [hW']
    dsimp only
    rcases Nat.lt_or_ge (j : ℕ) k with hjk | hjk
    · -- an old column
      have hjo : j ∉ o := by rw [hmo]; omega
      have hPW : (P * W * P) i j = W i j := by
        rw [mul_one_sub_smul_vecMulVec_apply_of_notMem hvout _ _ _ hjo,
          one_sub_smul_vecMulVec_mul_apply_of_forall hvout _ _ (hWo j hjk) _]
      rw [hPW]
      refine ⟨fun h => (hW i j).1 ⟨hjk, h.2⟩, fun h => ?_⟩
      have hjk' : j ≠ k' := fun e => by rw [e] at hjk; omega
      rw [of_apply, ite_eq_right (fun h' => hjk' h'.1), hCeq,
        mul_one_sub_smul_vecMulVec_apply_of_notMem hvout _ _ _ hjo, hBeq, of_apply,
        ite_eq_right (by rw [mem_indexFrom]; omega)]
      exact (hW i j).2 (fun h' => h ⟨by omega, h'.2⟩)
    rcases Nat.lt_or_ge k (j : ℕ) with hjk' | hjk'
    · -- a new column `j > k`, in `o`
      have hjo : j ∈ o := by rw [hmo]; omega
      refine ⟨fun h => absurd h.1 (by omega), fun _ => ?_⟩
      have hjk'' : j ≠ k' := fun e => by rw [e] at hjk'; omega
      rw [of_apply, ite_eq_right (fun h' => hjk'' h'.1), hCeq]
      refine mul_reflector_apply_congr hvout _ (fun l hl => ?_) hjo
      rw [hBeq, of_apply, ite_eq_left (by rw [mem_indexFrom]; have := (hmo l).1 hl; omega)]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hAW r l (by have := (hmo l).1 hl; omega)]
    · -- the column `k`
      have hjeq : j = k' := Fin.ext (by rw [hk'v]; omega)
      subst hjeq
      have hko : k' ∉ o := by rw [hmo]; omega
      have hPWk : (P * W * P) i k' = (P *ᵥ x) i := by
        rw [mul_one_sub_smul_vecMulVec_apply_of_notMem hvout _ _ _ hko]
        change (P *ᵥ fun l => W l k') i = _
        simp_rw [hWx]
      rw [hPWk]
      constructor
      · intro h
        rw [hPx]
        have hih : i ≠ (indexFrom n (k + 1)).head hone := by
          rw [head_indexFrom (by omega) hone]
          intro e
          have := congrArg Fin.val e
          simp only at this
          omega
        simp only [hih, ↓reduceIte, mem_indexFrom, show (k : ℕ) + 1 ≤ i by omega]
      · intro h
        have hik : ¬((k : ℕ) + 2 ≤ i) := fun h' => h ⟨by omega, h'⟩
        rw [of_apply, ite_eq_right (fun h' => hik h'.2), hCeq,
          mul_one_sub_smul_vecMulVec_apply_of_notMem hvout _ _ _ hko, hBeq, of_apply,
          ite_eq_left (by rw [mem_indexFrom]; omega)]
        rfl

/-- In exact arithmetic, the state of Algorithm 7.4.2 after its first $t$ passes, $t \le n - 2$,
satisfies `GolubVanLoan.Chapter07.HessenbergReduceInv` for the input $A$ and $t$ passes. -/
theorem hessenbergReduce_inv (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ t ≤ n - 2, HessenbergReduceInv A t (((List.finRange (n - 2)).take t).foldl
      (fun st k => Id.run (hessenbergReduceStep pure st k)) (A, [])) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [List.take_zero, List.foldl_nil]
    refine ⟨rfl, by simp, by simp, fun i j => ⟨fun h => absurd h.1 (Nat.not_lt_zero _),
      fun _ => by simp⟩⟩
  | succ t ih =>
    intro ht
    rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hget : (List.finRange (n - 2))[t]'(by simpa using ht) = ⟨t, by omega⟩ := by simp
    rw [hget]
    exact hessenbergReduceStep_inv ⟨t, by omega⟩ (ih (by omega))

/-- **Algorithm 7.4.2** of [golub2013matrix], correctness in exact arithmetic. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, let $(A', \mathrm{data})$ be the output of
Algorithm 7.4.2 in exact arithmetic, and let $U_0$ be the product of the reflectors
$I - \beta v v^T$ of the data. Then $U_0$ is orthogonal, the upper Hessenberg part $H$ of $A'$
satisfies
$$H = U_0^T A U_0,$$
$H$ is upper Hessenberg, $U_0 e_1 = e_1$, and the data has $n - 2$ entries, the $l$-th vector
(0-based) vanishing at the indices $\le l$. So the algorithm computes the Hessenberg
decomposition (7.4.3).

The product is `GolubVanLoan.Chapter05.householderProduct` of the returned data. It is built
from the returned pairs $(v, \beta)$ and never from the stored vectors. A reflector rebuilt from
the array with $\beta = 2/(v^T v)$ would be wrong: for $A = \begin{bmatrix} 1 & 2 & 3 \\ 4 & 5 &
6 \\ 0 & 7 & 8 \end{bmatrix}$, `house` returns $\beta = 0$ at the first step, and the rebuilt
reflector $\operatorname{diag}(1, -1, 1)$ does not reproduce $H = A$. The number of entries is
the natural number $n - 2$, which is $0$ for $n \le 2$.

**Correction.** Correctness is formulated for the Hessenberg part of the packed array and its
returned reflector data.
-/
theorem algorithm_7_4_2_spec {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    householderProduct (Id.run (algorithm_7_4_2 pure A)).2 ∈ orthogonalGroup (Fin (N + 1)) ℝ ∧
      hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1 =
        (householderProduct (Id.run (algorithm_7_4_2 pure A)).2)ᵀ * A *
          householderProduct (Id.run (algorithm_7_4_2 pure A)).2 ∧
      (hessenbergPart (Id.run (algorithm_7_4_2 pure A)).1).IsUpperHessenberg ∧
      householderProduct (Id.run (algorithm_7_4_2 pure A)).2 *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      (Id.run (algorithm_7_4_2 pure A)).2.length = N + 1 - 2 ∧
      ∀ (l : ℕ) (hl : l < (Id.run (algorithm_7_4_2 pure A)).2.length) (j : Fin (N + 1)),
        (j : ℕ) ≤ l → ((Id.run (algorithm_7_4_2 pure A)).2[l]).1 j = 0 := by
  have hrun : Id.run (algorithm_7_4_2 pure A) = (List.finRange (N + 1 - 2)).foldl
      (fun st k => Id.run (hessenbergReduceStep pure st k)) (A, []) := by
    unfold algorithm_7_4_2
    rw [List.idRun_foldlM]
  have hinv := hessenbergReduce_inv A (N + 1 - 2) le_rfl
  rw [List.take_of_length_le (by simp), ← hrun] at hinv
  generalize Id.run (algorithm_7_4_2 pure A) = out at hinv ⊢
  obtain ⟨hlen, hβ, hsupp, hW⟩ := hinv
  have hH : hessenbergPart out.1 =
      (householderProduct out.2)ᵀ * A * householderProduct out.2 := by
    ext i j
    rw [hessenbergPart, of_apply]
    split_ifs with hij
    · exact (hW i j).2 (by omega)
    · exact ((hW i j).1 ⟨by have := i.2; omega, by omega⟩).symm
  refine ⟨householderProduct_mem_orthogonalGroup hβ, hH, ?_, ?_, hlen, hsupp⟩
  · rw [isUpperHessenberg_iff_fin]
    intro i j hij
    rw [hessenbergPart, of_apply, ite_eq_right (by omega)]
  · refine householderProduct_mulVec_single fun p hp => ?_
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hp
    exact hsupp l hl 0 (Nat.zero_le _)

/-! ### The rounding bridge of Algorithm 7.4.2 -/

/-- The array of Algorithm 7.4.2 after $t$ passes with the stored Householder vectors replaced by
zeros: the entries $(i, j)$ with $j < t$ and $i \ge j + 2$ (0-based) are set to $0$, and all
other entries are kept. -/
def zeroStored (t : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) < t ∧ (j : ℕ) + 2 ≤ i then 0 else A i j

/-- The positions in the 0-based index list $[k + 1, \dots, n - 1]$ correspond to the indices $i$
with $i \ge k + 1$. -/
private def tailEquiv (k : ℕ) :
    {i : Fin n // i ∈ indexFrom n (k + 1)} ≃ {i : Fin n // k + 1 ≤ (i : ℕ)} :=
  Equiv.subtypeEquivRight fun _ => mem_indexFrom

/-- The 0-based index list $[j, \dots, n - 1]$ has at most $n$ entries. -/
private theorem length_indexFrom_le (j : ℕ) : (indexFrom n j).length ≤ n := by
  rw [indexFrom]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The rounding bridge of one pass of Algorithm 7.4.2. Let the rounding model be idempotent, with
unit roundoff $u$ such that $(18 n + 31) u < 1$. Then every run of pass $k$ in the relational
rounding model takes the array after $k$ passes to the array after $k + 1$ passes, both with the
stored vectors replaced by zeros, by a computed step `FloatingPoint.RoundsHessenbergStepPert` of
order $18 n + 31$. -/
theorem hessenbergReduceStep_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1) (k : Fin (n - 2))
    {st st' : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (h : st' ∈ (hessenbergReduceStep fp.round st k).run) :
    RoundsHessenbergStepPert fp (18 * n + 31) (show (k : ℕ) + 1 < n by have := k.2; omega)
      (zeroStored k st.1) (zeroStored (k + 1) st'.1) := by
  have hkn : (k : ℕ) + 2 < n := by have := k.2; omega
  set k' : Fin n := Fin.castLE (Nat.sub_le n 2) k with hk'
  have hk'v : (k' : ℕ) = k := rfl
  set o := indexFrom n (k + 1) with ho
  have hmo : ∀ i : Fin n, i ∈ o ↔ (k : ℕ) + 1 ≤ i := fun i => by simp [ho]
  have hone : o ≠ [] := indexFrom_ne_nil (by omega)
  have hnod : o.Nodup := nodup_indexFrom n (k + 1)
  have holen : o.length ≤ n := length_indexFrom_le _
  simp only [hessenbergReduceStep, SetM.mem_run_bind, SetM.mem_run_pure] at h
  obtain ⟨vβ, hvβ, B₁, hB₁, B₂, hB₂, rfl⟩ := h
  have hlen : ((18 * o.length + 31 : ℕ) : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) fp.u_nonneg) hu
  obtain ⟨hvout, hrefl⟩ := houseOn_rounding hfp hnod hone hlen _ hvβ
  obtain ⟨hB₁out, hB₁in⟩ := householderApplyLeft_rounds hfp hnod (nodup_indexFrom n k) vβ.1 vβ.2
    st.1 hB₁
  obtain ⟨hB₂out, hB₂in⟩ := householderApplyRight_rounds hfp (List.nodup_finRange n) hnod vβ.1
    vβ.2 B₁ hB₂
  set e := tailEquiv (n := n) k with he
  obtain ⟨c, hrefl⟩ : ∃ c, IsReflectorPert fp.u (18 * o.length + 31)
      (fun i : {i // i ∈ o} => st.1 i k') ⟨o.head hone, List.head_mem hone⟩ c
      (fun i => vβ.1 i) vβ.2 := ⟨_, hrefl⟩
  refine ⟨fun i => vβ.1 i, vβ.2, zeroStored (k + 1) B₁, ⟨c, ?_⟩, fun j hj => ?_,
    fun i j hij => ?_, fun i => ?_, fun i j hj => ?_⟩
  · -- the reflector data, transported to the subtype of the active rows
    have hx : (fun i : {i : Fin n // k + 1 ≤ (i : ℕ)} => zeroStored k st.1 i ⟨k, by omega⟩) =
        fun i : {i : Fin n // k + 1 ≤ (i : ℕ)} => st.1 i k' := by
      funext i
      simp only [zeroStored, of_apply, lt_self_iff_false, false_and, ↓reduceIte]
      rfl
    rw [hx]
    refine IsReflectorPert.of_comp_equiv e ?_
    have hpiv : e.symm ⟨⟨k + 1, by omega⟩, le_rfl⟩ = ⟨o.head hone, List.head_mem hone⟩ :=
      Subtype.ext (head_indexFrom (by omega) hone).symm
    rw [hpiv]
    exact hrefl.mono fp.u_nonneg (by omega) hu
  · -- the column sweep
    refine ⟨fun i => B₁ i j, (roundsHouseholderApplyScaled_comp_equiv_iff e).1 ?_, fun i => ?_⟩
    · have hA : (fun i : {i : Fin n // k + 1 ≤ (i : ℕ)} => zeroStored k st.1 i j) ∘ e =
          fun i : {i : Fin n // i ∈ indexFrom n (k + 1)} => st.1 i j := by
        funext i
        simp only [Function.comp_apply, zeroStored, of_apply]
        rw [ite_eq_right (by omega)]
        rfl
      rw [hA]
      exact hB₁in j (by rw [mem_indexFrom]; exact hj)
    · simp only [zeroStored, of_apply]
      split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  · -- outside the active block
    have hB : B₁ i j = st.1 i j := hB₁out i j (by
      rcases hij with hi | hj
      · exact Or.inl (by rw [hmo]; omega)
      · exact Or.inr (by rw [mem_indexFrom]; omega))
    simp only [zeroStored, of_apply, hB]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  · -- the row sweep
    refine ⟨fun j => B₂ i j, (roundsHouseholderApplyScaled_comp_equiv_iff e).1 ?_, fun j => ?_⟩
    · have hC : (fun j : {i : Fin n // k + 1 ≤ (i : ℕ)} => zeroStored (k + 1) B₁ i j) ∘ e =
          fun j : {j : Fin n // j ∈ indexFrom n (k + 1)} => B₁ i j := by
        funext j
        simp only [Function.comp_apply, zeroStored, of_apply]
        rw [ite_eq_right (by have := (e j).2; omega)]
        rfl
      rw [hC]
      exact hB₂in i (List.mem_finRange i)
    · have hj := j.2
      simp only [zeroStored, of_apply]
      rw [ite_eq_right (by omega), ite_eq_right (fun h' => by
        have := congrArg Fin.val h'.1; rw [hk'v] at this; omega)]
  · -- the columns `≤ k` are finished
    have hjo : j ∉ o := by rw [hmo]; omega
    simp only [zeroStored, of_apply]
    split_ifs with h1 h2
    · rfl
    · exfalso
      exact h1 ⟨by omega, by have := h2.2; have := congrArg Fin.val h2.1; omega⟩
    · exact hB₂out i j (Or.inr hjo)

/-- **Section 7.4.3** of [golub2013matrix], the rounding bridge of Algorithm 7.4.2. Let the rounding
model be idempotent, with unit roundoff $u$ such that $(18 n + 31) u < 1$, and let
$A \in \mathbb{R}^{n \times n}$. For every run $(A', \mathrm{data})$ of Algorithm 7.4.2 in the
relational rounding model there is a sequence of arrays $\hat A_0, \hat A_1, \dots$ such that
$\hat A_{n-2}$ is the upper Hessenberg part of $A'$, $\hat A_0 = A$, and each $\hat A_{k+1}$
with $k < n - 2$ is a computed Householder step of order $18 n + 31$ from $\hat A_k$.

The relation is `FloatingPoint.RoundsHessenbergReducePert`, and a step is
`FloatingPoint.RoundsHessenbergStepPert`. The array $\hat A_k$ is the array of the run after $k$
passes with the stored vectors replaced by zeros; the algorithm never reads them again. A
rounding model is idempotent (`FloatingPoint.RoundingModel.IsIdempotent`) when a rounded value
rounds only to itself. The bridge of one pass is
`GolubVanLoan.Chapter07.hessenbergReduceStep_rounds`. -/
theorem algorithm_7_4_2_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1) (A : Matrix (Fin n) (Fin n) ℝ)
    {out : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (h : out ∈ (algorithm_7_4_2 fp.round A).run) :
    ∃ Ahat : ℕ → Matrix (Fin n) (Fin n) ℝ, Ahat (n - 2) = hessenbergPart out.1 ∧
      RoundsHessenbergReducePert fp (18 * n + 31) A Ahat := by
  have H := SetM.forall_mem_run_foldlM_finRange (f := hessenbergReduceStep fp.round)
    (a := (A, [])) (fun t b => t ≤ n - 2 → ∃ Ahat : ℕ → Matrix (Fin n) (Fin n) ℝ,
      Ahat 0 = A ∧ (∀ k (hk : k < n - 2), k < t →
        RoundsHessenbergStepPert fp (18 * n + 31) (show k + 1 < n by omega) (Ahat k)
          (Ahat (k + 1))) ∧ Ahat t = zeroStored t b.1)
    (fun _ => ⟨fun _ => A, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), by
      ext i j; simp [zeroStored]⟩)
    (fun k b hb b' hb' _ => by
      obtain ⟨Ahat, h0, hstep, hlast⟩ := hb (by omega)
      refine ⟨fun m => if m ≤ k then Ahat m else zeroStored (k + 1) b'.1, by simpa using h0,
        fun j hj hjk => ?_, by dsimp only; rw [ite_eq_right (by omega)]⟩
      rcases Nat.lt_or_ge j k with hjk' | hjk'
      · simp only [ite_eq_left (show j ≤ (k : ℕ) by omega),
          ite_eq_left (show j + 1 ≤ (k : ℕ) by omega)]
        exact hstep j hj hjk'
      · have hj' : j = k := by omega
        subst hj'
        simp only [le_refl, ↓reduceIte, ite_eq_right (show ¬((k : ℕ) + 1 ≤ k) by omega)]
        rw [hlast]
        exact hessenbergReduceStep_rounds hfp hu k hb')
  obtain ⟨Ahat, h0, hstep, hlast⟩ := H out h le_rfl
  refine ⟨Ahat, ?_, h0, fun k hk => hstep k hk hk⟩
  rw [hlast]
  ext i j
  simp only [zeroStored, hessenbergPart, of_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; have := i.2; omega)

open scoped Matrix.Norms.Frobenius in
/-- **Section 7.4.3** of [golub2013matrix], Wilkinson's backward error bound for the Hessenberg
reduction. The source states that "the computed Hessenberg matrix $\hat H$ satisfies
$\hat H = Q^T (A + E) Q$ where $Q$ is orthogonal and $\|E\|_F \le c n^2 u \|A\|_F$". Let the
rounding model be idempotent with unit roundoff $u$, let $K = 18 n + 31$, and let
$\gamma_m = m u / (1 - m u)$. Assume $(3K + n + 3) u < 1$ and $2 (n - 2) \varepsilon < 1$ for
$\varepsilon = 3 \gamma_{3K+n+3}$. Then for every run $(A', \mathrm{data})$ of Algorithm 7.4.2
in the relational rounding model, the upper Hessenberg part $\hat H$ of $A'$ is upper
Hessenberg, and there are an orthogonal $Q$ and a matrix $E$ with
$$\hat H = Q^T (A + E) Q, \qquad \|E\|_F \le \frac{2 (n - 2) \varepsilon}{1 - 2 (n - 2)
  \varepsilon} \|A\|_F.$$

The constant is explicit: to first order in $u$ it is $6 (55 n + 96)(n - 2) u$, which has the
form $c n^2 u$ of the source. It comes from the relational calculus of the backbone, not from
Wilkinson's analysis. The matrix $\hat H$ is `GolubVanLoan.Chapter07.hessenbergPart` of the
returned array, and the factor in the bound is `FloatingPoint.gamma ε (2 * (n - 2))`. The proof
combines `GolubVanLoan.Chapter07.algorithm_7_4_2_rounds` with
`FloatingPoint.exists_roundsHessenbergReducePert_eq`.

**Reading.** The source gives an order-$n^2u$ bound with an unspecified small constant. The
theorem gives an explicit nested $\gamma$ bound under idempotent rounding and the two smallness
conditions displayed above. -/
theorem algorithm_7_4_2_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hcard : ((3 * (18 * n + 31) + n + 3 : ℕ) : ℝ) * fp.u < 1)
    (hr : ((2 * (n - 2) : ℕ) : ℝ) * (3 * gamma fp.u (3 * (18 * n + 31) + n + 3)) < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) {out : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (h : out ∈ (algorithm_7_4_2 fp.round A).run) :
    (hessenbergPart out.1).IsUpperHessenberg ∧ ∃ Q ∈ orthogonalGroup (Fin n) ℝ,
      ∃ E : Matrix (Fin n) (Fin n) ℝ, hessenbergPart out.1 = Qᵀ * (A + E) * Q ∧
        ‖E‖ ≤ gamma (3 * gamma fp.u (3 * (18 * n + 31) + n + 3)) (2 * (n - 2)) * ‖A‖ := by
  have hu : ((18 * n + 31 : ℕ) : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) fp.u_nonneg) hcard
  obtain ⟨Ahat, hlast, hpert⟩ := algorithm_7_4_2_rounds hfp hu A h
  rw [← hlast]
  exact exists_roundsHessenbergReducePert_eq hcard hr hpert

end HessenbergReduction

/-! ### §7.4.5 The implicit Q theorem -/

/-- **Section 7.4.5** of [golub2013matrix], definition of unreduced. An upper Hessenberg matrix
$H \in \mathbb{R}^{n \times n}$ is **unreduced** if it has no zero subdiagonal entries:
$h_{k+1,k} \neq 0$ for $k = 1, \dots, n - 1$.

The definition is the backbone's `Matrix.IsUnreducedUpperHessenberg`. The theorem
`GolubVanLoan.Chapter07.isUnreduced_iff` spells it out along the subdiagonal. -/
def IsUnreduced (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.IsUnreducedUpperHessenberg

/-- A matrix $H \in \mathbb{R}^{n \times n}$ is unreduced upper Hessenberg if and only if it is
upper Hessenberg and $h_{k+1,k} \neq 0$ for every $k < n - 1$, with 0-based indices. -/
theorem isUnreduced_iff {H : Matrix (Fin n) (Fin n) ℝ} :
    IsUnreduced H ↔
      H.IsUpperHessenberg ∧ ∀ (k : ℕ) (hk : k + 1 < n), H ⟨k + 1, hk⟩ ⟨k, by omega⟩ ≠ 0 :=
  isUnreducedUpperHessenberg_iff_fin

/-- **Theorem 7.4.2** of [golub2013matrix] (implicit Q theorem). Let
$A \in \mathbb{R}^{n \times n}$, and let $Q = [q_1 \mid \cdots \mid q_n]$ and
$V = [v_1 \mid \cdots \mid v_n]$ be orthogonal, with $Q^T A Q = H$ and $V^T A V = G$ upper
Hessenberg and $v_1 = q_1$. Let $0 \le k \le n - 1$, and assume $h_{i+1,i} \neq 0$ for
$i = 1, \dots, k$. Then $v_i = \pm q_i$ for $i = 1, \dots, k + 1$, and
$|g_{i+1,i}| = |h_{i+1,i}|$ for $i = 1, \dots, k$. Moreover, if $k < n - 1$ and
$h_{k+2,k+1} = 0$, then $g_{k+2,k+1} = 0$.

The source takes for $k$ the position of the first zero subdiagonal entry of $H$, with the
convention for an unreduced $H$ that all subdiagonal entries are nonzero. Here $k$ is any number
such that the first $k$ subdiagonal entries are nonzero. In Lean the matrices have size `N + 1`
and the indices are 0-based: the hypothesis is on the entries `(Qᵀ * A * Q) i.succ i.castSucc`
for $i < k$, and the columns are `Q.col i` and `V.col i`.

**Reading.** Any nonzero prefix suffices for the restricted sign and subdiagonal magnitude
identities.
-/
theorem theorem_7_4_2 {N : ℕ} {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hH : (Qᵀ * A * Q).IsUpperHessenberg) (hG : (Vᵀ * A * V).IsUpperHessenberg)
    (h0 : V.col 0 = Q.col 0) {k : ℕ} (hk : k ≤ N)
    (hsub : ∀ i : Fin N, (i : ℕ) < k → (Qᵀ * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → V.col i = Q.col i ∨ V.col i = -Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        |(Vᵀ * A * V) i.succ i.castSucc| = |(Qᵀ * A * Q) i.succ i.castSucc|) ∧
      (∀ i : Fin N, (i : ℕ) = k → (Qᵀ * A * Q) i.succ i.castSucc = 0 →
        (Vᵀ * A * V) i.succ i.castSucc = 0) :=
  implicitQ_of_apply_eq_zero_real hQ hV hH hG h0 hk hsub

/-- **Theorem 7.4.2** of [golub2013matrix], essential uniqueness. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $Q$ and $Z$ be orthogonal with the same
first column, $Q^T A Q = H$ unreduced upper Hessenberg, and $Z^T A Z = G$ upper Hessenberg. Then
there is $D = \operatorname{diag}(d_1, \dots, d_n)$ with $d_i = \pm 1$ and $d_1 = 1$ such that
$$Z = Q D, \qquad G = D H D.$$
Since $D^{-1} = D$, this says that "$G$ and $H$ are essentially equal".

**Generalization.** It suffices for $H$ to be unreduced. The source's essential-uniqueness
paragraph asks that both $H$ and $G$ be unreduced. -/
theorem theorem_7_4_2_essential {N : ℕ} {A Q Z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hZ : Z ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hH : IsUnreduced (Qᵀ * A * Q)) (hG : (Zᵀ * A * Z).IsUpperHessenberg)
    (h0 : Z.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧ Z = Q * diagonal d ∧
      Zᵀ * A * Z = diagonal d * (Qᵀ * A * Q) * diagonal d :=
  implicitQ_real hQ hZ hH hG h0

/-- **Section 7.4.5** of [golub2013matrix], definition of the Krylov matrix. For
$A \in \mathbb{R}^{n \times n}$, $v \in \mathbb{R}^n$ and $j \ge 0$, the **Krylov matrix** is
$$K(A, v, j) = [v \mid Av \mid A^2 v \mid \cdots \mid A^{j-1} v] \in \mathbb{R}^{n \times j}.$$

This is the backbone's `Matrix.krylovMatrix` for real matrices. -/
def krylovMatrix (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin j) ℝ :=
  Matrix.krylovMatrix A v j

/-- **Theorem 7.4.3** of [golub2013matrix]. Let $A, Q \in \mathbb{R}^{n \times n}$ with $n \ge 1$
and $Q$ orthogonal. Then $Q^T A Q = H$ is an unreduced upper Hessenberg matrix if and only if
$R = Q^T K(A, Q(:,1), n)$ is nonsingular and upper triangular.

Nonsingularity of $R$ is stated as `IsUnit R.det`, and the first column $Q(:,1)$ is `Q.col 0`. -/
theorem theorem_7_4_3 {N : ℕ} {Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    IsUnreduced (Qᵀ * A * Q) ↔
      (Qᵀ * krylovMatrix A (Q.col 0) (N + 1)).IsUpperTriangular ∧
        IsUnit (Qᵀ * krylovMatrix A (Q.col 0) (N + 1)).det := by
  have h := isUnreducedUpperHessenberg_conj_iff_krylovMatrix hQ A
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- Every eigenvalue of a complex matrix has geometric multiplicity at least one. -/
private theorem one_le_finrank_eigenspace {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : 1 ≤ Module.finrank ℂ (Module.End.eigenspace (toLin' M) μ) := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul M μ).1 hμ
  refine Submodule.one_le_finrank_iff.2 fun h => hv0 ?_
  have hmem : v ∈ Module.End.eigenspace (toLin' M) μ := by
    rw [Module.End.mem_eigenspace_iff, toLin'_apply]; exact hv
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

/-- Every eigenvalue of the complexification of an unreduced upper Hessenberg matrix has geometric
multiplicity at most one. -/
private theorem finrank_eigenspace_le_one_of_isUnreduced {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUnreduced H) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (toLin' H.complexify) μ) ≤ 1 := by
  cases n with
  | zero =>
    have : Module.finrank ℂ (Fin 0 → ℂ) = 0 := by simp
    exact (Submodule.finrank_le _).trans (by omega)
  | succ N =>
    exact IsUnreducedUpperHessenberg.finrank_eigenspace_le_one
      (hH.map (f := Complex.ofRealHom) Complex.ofReal_injective) μ

/-- **Theorem 7.4.4** of [golub2013matrix]. If $\lambda \in \mathbb{C}$ is an eigenvalue of an
unreduced upper Hessenberg matrix $H \in \mathbb{R}^{n \times n}$, then its geometric
multiplicity is $1$:
$$\dim \operatorname{null}(H - \lambda I) = 1.$$

The proof uses that the first $n - 1$ columns of $H - \lambda I$ are linearly independent, so
that $\operatorname{rank}(H - \lambda I) \ge n - 1$. The source writes $A - \lambda I$ for
$H - \lambda I$ in this proof. The eigenvalue and the null space are those of
`Matrix.complexify H`.

**Typo.** The proof in the source writes $\operatorname{rank}(A - \lambda I)$, although the
matrix under discussion is $H$. -/
theorem theorem_7_4_4 {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUnreduced H) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ H.complexify) :
    Module.finrank ℂ (Module.End.eigenspace (toLin' H.complexify) μ) = 1 :=
  le_antisymm (finrank_eigenspace_le_one_of_isUnreduced hH μ) (one_le_finrank_eigenspace hμ)

/-! ### §7.4.6 The companion matrix decomposition -/

/-- **Equation (7.4.4)** of [golub2013matrix], the companion matrix. For
$c = (c_0, \dots, c_{n-1}) \in \mathbb{R}^n$, the companion matrix $C$ has ones on the
subdiagonal, last column $-c$, and zeros elsewhere:
$$C = \begin{bmatrix} 0 & 0 & \cdots & 0 & -c_0 \\ 1 & 0 & \cdots & 0 & -c_1 \\ 0 & 1 & \cdots &
  0 & -c_2 \\ \vdots & & \ddots & & \vdots \\ 0 & 0 & \cdots & 1 & -c_{n-1} \end{bmatrix}.$$

The backbone's `Matrix.companion` puts the coefficients in the first row;
`GolubVanLoan.Chapter07.companion_eq` relates the two layouts. -/
def companion (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (j : ℕ) + 1 = n then -c i else if (i : ℕ) = j + 1 then 1 else 0

/-- The coefficient of $z^i$ in $z^n + c_{n-1} z^{n-1} + \cdots + c_0$ is $c_i$ for $i < n$. -/
private theorem coeff_X_pow_add_sum (c : Fin n → ℝ) (i : Fin n) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff i = c i := by
  have hi : (i : ℕ) ≠ n := i.isLt.ne
  simp only [coeff_add, coeff_X_pow, hi, ↓reduceIte, zero_add, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · simp
  · rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h).symm hji

/-- The companion matrix (7.4.4) of $c$ is the transpose of the backbone's `Matrix.companion p n`
for $p(z) = z^n + \sum_{i<n} c_i z^i$, with its rows and columns in reverse order. -/
theorem companion_eq (c : Fin n → ℝ) :
    companion c = ((Matrix.companion (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) n)ᵀ).submatrix
      Fin.rev Fin.rev := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [companion, of_apply, submatrix_apply, transpose_apply, companion_apply, Fin.val_rev]
  by_cases hjn : (j : ℕ) + 1 = n
  · have h2 : n - 1 - (n - ((i : ℕ) + 1)) = i := by omega
    simp only [hjn, Nat.sub_self, h2, ↓reduceIte, coeff_X_pow_add_sum]
  · have h1 : n - ((j : ℕ) + 1) ≠ 0 := by omega
    have h3 : ((i : ℕ) = j + 1) ↔ (n - ((j : ℕ) + 1) = n - ((i : ℕ) + 1) + 1) := by omega
    simp only [hjn, h1, ↓reduceIte, h3]

/-- The characteristic polynomial of the companion matrix $C$ of (7.4.4) is $\det(zI - C) = c_0 +
c_1 z + \cdots + c_{n-1} z^{n-1} + z^n$, as stated in §7.4.6. -/
theorem charpoly_companion' (c : Fin n → ℝ) :
    (companion c).charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ) := by
  have hdeg := degree_sum_fin_lt c
  have hmonic : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).Monic := monic_X_pow_add hdeg
  have hnat : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  rw [companion_eq, show ∀ M : Matrix (Fin n) (Fin n) ℝ, M.submatrix Fin.rev Fin.rev =
      reindex Fin.revPerm Fin.revPerm M from fun M => rfl, charpoly_reindex, charpoly_transpose,
    charpoly_companion hmonic hnat]

/-- **Equation (7.4.4)** of [golub2013matrix], the companion matrix decomposition. Let
$A \in \mathbb{R}^{n \times n}$ and $x, c \in \mathbb{R}^n$, and let $K = K(A, x, n)$ be the
Krylov matrix. If $K c = -A^n x$, then
$$A K = K C,$$
where $C$ is the companion matrix of $c$, and $\det(zI - C) = c_0 + c_1 z + \cdots + c_{n-1}
z^{n-1} + z^n$. If moreover $K$ is nonsingular, then $K^{-1} A K = C$, and the characteristic
polynomial of $A$ is $c_0 + c_1 z + \cdots + c_{n-1} z^{n-1} + z^n$.

**Generalization.** The identities $AK=KC$ and the characteristic polynomial of $C$ hold for
any supplied solution of $Kc=-A^n x$. Invertibility of $K$ is required for the similarity and
for identifying the characteristic polynomial of $A$. -/
theorem equation_7_4_4 {A : Matrix (Fin n) (Fin n) ℝ} {x c : Fin n → ℝ}
    (hc : krylovMatrix A x n *ᵥ c = -(A ^ n *ᵥ x)) :
    A * krylovMatrix A x n = krylovMatrix A x n * companion c ∧
      (companion c).charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ) ∧
      (IsUnit (krylovMatrix A x n) →
        (krylovMatrix A x n)⁻¹ * A * krylovMatrix A x n = companion c ∧
          A.charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)) := by
  set K := krylovMatrix A x n
  have hAK : A * K = K * companion c := by
    ext r j
    have hj := j.isLt
    have lhs : (A * K) r j = (A ^ ((j : ℕ) + 1) *ᵥ x) r := by
      rw [pow_succ', ← mulVec_mulVec]
      rfl
    rw [lhs, Matrix.mul_apply]
    by_cases hjn : (j : ℕ) + 1 = n
    · have hsum : ∑ i, K r i * companion c i j = -(K *ᵥ c) r := by
        simp only [companion, of_apply, hjn, ↓reduceIte, mulVec, dotProduct,
          ← Finset.sum_neg_distrib, mul_neg]
      rw [hsum, hc, Pi.neg_apply, neg_neg, hjn]
    · have hj1 : (j : ℕ) + 1 < n := by omega
      rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj1⟩]
      · simp only [companion, of_apply, hjn, ↓reduceIte, mul_one]
        rfl
      · intro i _ hi
        have hi' : ¬ ((i : ℕ) = j + 1) := fun h => hi (Fin.ext h)
        simp only [companion, of_apply, hjn, hi', ↓reduceIte, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hchar := charpoly_companion' c
  refine ⟨hAK, hchar, fun hK => ⟨?_, ?_⟩⟩
  · rw [Matrix.mul_assoc, hAK, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det K).1 hK), Matrix.one_mul]
  · have hsim : IsSimilar A (K⁻¹ * A * K) := ⟨K, hK, rfl⟩
    rw [hsim.charpoly_eq, Matrix.mul_assoc, hAK, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det K).1 hK), Matrix.one_mul, hchar]

/-- **Section 7.4.6** of [golub2013matrix], definition of nonderogatory. A matrix
$A \in \mathbb{R}^{n \times n}$ is **nonderogatory** if each of its complex eigenvalues has
geometric multiplicity one: $\dim \operatorname{null}(A - \lambda I) \le 1$ for every
$\lambda \in \mathbb{C}$.

The condition is stated for every $\lambda \in \mathbb{C}$; it holds trivially when $\lambda$ is
not an eigenvalue. The null space is that of `Matrix.complexify A`. -/
def IsNonderogatory (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ : ℂ, Module.finrank ℂ (Module.End.eigenspace (toLin' A.complexify) μ) ≤ 1

/-- **Section 7.4.6** of [golub2013matrix]. Let $A, H \in \mathbb{R}^{n \times n}$, with $A$ similar
to $H$ and $H$ unreduced upper Hessenberg. Then $A$ is nonderogatory. This is the remark that
"$A$ is similar to an unreduced Hessenberg matrix only if each eigenvalue has unit geometric
multiplicity".

Similarity is `Matrix.IsSimilar`: $H = C^{-1} A C$ for a nonsingular real $C$. The proof
transports Theorem 7.4.4 along the complexified similarity. -/
theorem isNonderogatory_of_isSimilar_unreduced {A H : Matrix (Fin n) (Fin n) ℝ}
    (hs : IsSimilar A H) (hH : IsUnreduced H) : IsNonderogatory A := by
  obtain ⟨X, hX, rfl⟩ := hs
  have hsim : IsSimilar A.complexify (X⁻¹ * A * X).complexify :=
    ⟨X.complexify, (isUnit_complexify_iff X).2 hX, by
      rw [complexify_mul, complexify_mul, complexify_inv]⟩
  intro μ
  have h := finrank_eigenspace_le_one_of_isUnreduced hH μ
  have e1 := eigenspace_mulVecLin_eq_ker A.complexify μ
  have e2 := eigenspace_mulVecLin_eq_ker (X⁻¹ * A * X).complexify μ
  change Module.finrank ℂ (Module.End.eigenspace (A.complexify).mulVecLin μ) ≤ 1
  change Module.finrank ℂ (Module.End.eigenspace ((X⁻¹ * A * X).complexify).mulVecLin μ) ≤ 1 at h
  rw [e1, (hsim.sub_smul_one μ).finrank_ker_mulVecLin_eq, ← e2]
  exact h

end GolubVanLoan.Chapter07
