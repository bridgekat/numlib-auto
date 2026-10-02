import Numlib.LinearAlgebra.Matrix.Companion
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub–Van Loan §7.4: the Hessenberg and real Schur forms

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.4: the real Schur decomposition (Theorem 7.4.1), the Hessenberg
decomposition (7.4.3) and the array reading of Algorithm 7.4.2 (`hessenbergPart`), the implicit Q
theorem (Theorem 7.4.2), Krylov matrices and unreduced Hessenberg matrices (Theorem 7.4.3),
geometric multiplicity one (Theorem 7.4.4), and the companion matrix decomposition (7.4.4) with
nonderogatory matrices (§7.4.6).

## Conventions

Real: `Matrix (Fin n) (Fin n) ℝ`, orthogonal `Q ∈ Matrix.orthogonalGroup (Fin n) ℝ`, `Qᵀ`. Upper
quasi-triangular is the backbone's `Matrix.IsQuasiUpperTriangular`; unreduced is
`Matrix.IsUnreducedUpperHessenberg` (the surface's `IsUnreduced`). Indices are 0-based: the book's
`H(k+1, k)`, `k = 1:n-1`, is `H ⟨k+1, _⟩ ⟨k, _⟩`, `k < n - 1`. Complex eigenvalues of a real matrix
are those of `Matrix.complexify`.

## Algorithms

Algorithm 7.4.1 (the Hessenberg QR step) calls chapter 5's Algorithm 5.2.5 for its first loop (the
book: "See Algorithm 5.2.5") and `givensApplyRight` on the index lists `indexTo (k + 1) (j + 1)` for
its second; `algorithm_7_4_1_spec` is its exact semantics (a QR step with an upper Hessenberg `Q`;
the book gives no rounding analysis). Algorithm 7.4.2 (Householder reduction to Hessenberg form) is
`houseOn`, `householderApplyLeft` and `householderApplyRight` on index lists, one pass
`hessenbergReduceStep` per column; it stores the Householder vectors below the subdiagonal and
returns the reflector data `(v, β)` (convention 13). `algorithm_7_4_2_spec` is the exact Hessenberg
decomposition with `U₀ = householderProduct data`, `algorithm_7_4_2_rounds` the bridge to the
backbone's `FloatingPoint.RoundsHessenbergReducePert`, and `algorithm_7_4_2_rounding` Wilkinson's
backward error `‖E‖_F ≤ c n² u ‖A‖_F` with an explicit constant.

## Not formalized

§7.4.4 (level-3 block Hessenberg reduction and the WY form: BLAS-level discussion); flop counts;
"this calculation can be highly unstable" for companion-matrix methods (no statement).
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-- Over `ℝ` the star of a matrix is its transpose. -/
private theorem star_eq_transpose_real {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : star M = Mᵀ := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-! ### §7.4.1 The real Schur decomposition -/

/-- **Theorem 7.4.1 (real Schur decomposition)** (7.4.2). For `A ∈ ℝ^{n×n}` there is an orthogonal
`Q` with `Qᵀ A Q` upper quasi-triangular: block upper triangular for a monotone block index `p` with
blocks `R_ii` of size `1` or `2`, each `2 × 2` block having a pair of complex conjugate (nonreal)
eigenvalues — it has no real eigenvalue. -/
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

/-- **Algorithm 7.4.1** (the Hessenberg QR step): "If `H` is an `n`-by-`n` upper Hessenberg
matrix, then this algorithm overwrites `H` with `H₊ = RQ` where `H = QR` is the QR factorization
of `H`":
```
for k = 1:n-1
    [c_k, s_k] = givens(H(k, k), H(k+1, k))
    H(k:k+1, k:n) = [c_k s_k; -s_k c_k]ᵀ H(k:k+1, k:n)
end
for k = 1:n-1
    H(1:k+1, k:k+1) = H(1:k+1, k:k+1) [c_k s_k; -s_k c_k]
end
```
With `n = k + 1`. The first loop is chapter 5's Algorithm 5.2.5 ("See Algorithm 5.2.5"), which
returns the rotations `(c_k, s_k)`; the second applies them on the rows `0, …, k + 1`
(`givensApplyRight` on `indexTo`). -/
noncomputable def algorithm_7_4_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {k : ℕ}
    (H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := do
  let st ← algorithm_5_2_5 rnd H
  (List.finRange k).foldlM (fun (H : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (j : Fin k) =>
    givensApplyRight rnd j.castSucc j.succ (st.2 j).1 (st.2 j).2 (indexTo (k + 1) (j + 1)) H)
    st.1

/-- The second loop of Algorithm 7.4.1 multiplies `R` by the rotations: after `t` passes the
array is `R G₁ ⋯ G_t`. The rows `> t + 1` of the columns `t, t + 1` of `R G₁ ⋯ G_{t-1}` vanish
(`R` is upper triangular, the partial product Hessenberg and the identity beyond column `t`), so
restricting the update to the rows `≤ t + 1` changes nothing. -/
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
        rw [mul_apply]
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

/-- **Algorithm 7.4.1 computes a QR step**, exactly (no rounding analysis in the book): for
upper Hessenberg `H`, `H₊ = Id.run (algorithm_7_4_1 pure H)` is a QR step
(`Matrix.IsShiftedQrStep 0 H H₊`) for `H = Q R` with `Q = G₁ ⋯ G_{n-1}` orthogonal and `R` upper
triangular, `H₊ = R Q`; "It is easy to confirm that the matrix `Q = G₁ ⋯ G_{n-1}` is upper
Hessenberg. Thus, `RQ = H₊` is also upper Hessenberg." Chapter 5's `algorithm_5_2_5_spec` gives
the factorization, `foldl_givensApplyRight_eq` the product `R Q`. -/
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

/-- **(7.4.3), the Hessenberg decomposition**: for `A ∈ ℝ^{n×n}` there is an orthogonal `U₀` with
`U₀ᵀ A U₀` upper Hessenberg and `U₀ e₁ = e₁` (the Householder reduction's reflectors act on the
coordinates `≥ 2` only). -/
theorem equation_7_4_3 {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∃ U₀ ∈ orthogonalGroup (Fin (N + 1)) ℝ, (U₀ᵀ * A * U₀).IsUpperHessenberg ∧
      U₀ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  refine ⟨hessenbergQ A, hessenbergQ_mem_orthogonalGroup A, ?_, ?_⟩
  · have h := isUpperHessenberg_hessenbergReduce (A := A)
    rwa [hessenbergReduce_eq_conj, conjTranspose_eq_transpose_of_trivial] at h
  · ext i
    rw [mulVec_single_one, col_apply, hessenbergQ_apply_zero, one_apply, Pi.single_apply]

/-- **§7.4.3, the array of Algorithm 7.4.2**: the book's reading of an array that holds `H` in its
upper Hessenberg part and the essential parts of the Householder vectors below the subdiagonal
("The `k`th Householder matrix can be represented in `A(k+2:n, k)`"): the entries on or above the
subdiagonal, `hessenbergPart A i j = A i j` for `i ≤ j + 1`, and `0` below. -/
def hessenbergPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) ≤ j + 1 then A i j else 0

/-! ### §7.4.3 The Householder reduction: Algorithm 7.4.2 -/

section HessenbergReduction

open FloatingPoint GolubVanLoan.Chapter05

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **One pass of Algorithm 7.4.2** (0-based `k < n - 2`, the book's `k + 1`), on the state
(array, reflector data):
```
[v, β] = house(A(k+1:n, k))
A(k+1:n, k:n) = (I - β v vᵀ) A(k+1:n, k:n)
A(1:n, k+1:n) = A(1:n, k+1:n) (I - β v vᵀ)
```
then `v(k+2:n)` is stored in `A(k+2:n, k)` ("The `k`th Householder matrix can be represented in
`A(k+2:n, k)`"; copies, not rounded) and `(v, β)` — with the `β` that `house` returned
(convention 13) — is appended to the data. `house` is chapter 5's `houseOn` on the index list
`[k+1, …, n-1]` (`v` is zero off it and `1` at `k + 1`), the updates are `householderApplyLeft`
and `householderApplyRight` on index lists (convention 10). -/
noncomputable def hessenbergReduceStep
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) (k : Fin (n - 2)) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) := do
  let vβ ← houseOn rnd (indexFrom n (k + 1)) fun i => st.1 i (Fin.castLE (Nat.sub_le n 2) k)
  let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom n (k + 1)) (indexFrom n k) st.1
  let A ← householderApplyRight rnd vβ.1 vβ.2 (List.finRange n) (indexFrom n (k + 1)) A
  pure (of fun i j => if j = Fin.castLE (Nat.sub_le n 2) k ∧ (k : ℕ) + 2 ≤ i then vβ.1 i
    else A i j, st.2 ++ [vβ])

/-- **Algorithm 7.4.2 (Householder Reduction to Hessenberg Form)**: "Given `A ∈ ℝ^{n×n}`, the
following algorithm overwrites `A` with `H = U₀ᵀ A U₀` where `H` is upper Hessenberg and `U₀` is a
product of Householder matrices": `for k = 1:n-2` the pass `hessenbergReduceStep`. Returns the
array (`H` in its upper Hessenberg part, `hessenbergPart`, the Householder vectors below it) and
the reflector data `[(v₁, β₁), …, (v_{n-2}, β_{n-2})]`, so that `U₀ = householderProduct data`
without rebuilding a reflector from a stored vector. -/
noncomputable def algorithm_7_4_2 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) :=
  (List.finRange (n - 2)).foldlM (hessenbergReduceStep rnd) (A, [])

end Programs

/-- **The invariant of Algorithm 7.4.2 after `t` passes**, exact arithmetic: `t` reflectors,
each with `β = 0` or `β vᵀv = 2` and the `l`-th vanishing on the indices `≤ l`; with
`W = U_tᵀ A₀ U_t` (`U_t` the product of the data), `W` vanishes below the subdiagonal in the columns
`< t`, and the array agrees with `W` everywhere else (below the subdiagonal of those columns it
holds the stored vectors). -/
def HessenbergReduceInv (A₀ : Matrix (Fin n) (Fin n) ℝ) (t : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) : Prop :=
  st.2.length = t ∧
  (∀ p ∈ st.2, p.2 = 0 ∨ p.2 * (p.1 ⬝ᵥ p.1) = 2) ∧
  (∀ (l : ℕ) (hl : l < st.2.length) (j : Fin n), (j : ℕ) ≤ l → (st.2[l]).1 j = 0) ∧
  ∀ i j : Fin n, ((j : ℕ) < t ∧ (j : ℕ) + 2 ≤ i →
      ((householderProduct st.2)ᵀ * A₀ * householderProduct st.2) i j = 0) ∧
    (¬((j : ℕ) < t ∧ (j : ℕ) + 2 ≤ i) →
      st.1 i j = ((householderProduct st.2)ᵀ * A₀ * householderProduct st.2) i j)

/-- A reflector `1 - β v vᵀ` with `v` zero off `o` is the identity in the rows off `o`. -/
private theorem reflector_apply_of_not_mem {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) {i : Fin n} (hi : i ∉ o) (j : Fin n) :
    (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ) i j =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp [vecMulVec_apply, hv i hi]

/-- A reflector `1 - β v vᵀ` with `v` zero off `o` is the identity in the columns off `o`. -/
private theorem reflector_apply_of_not_mem' {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) (i : Fin n) {j : Fin n} (hj : j ∉ o) :
    (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ) i j =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp [vecMulVec_apply, hv j hj]

/-- A reflector acting on `o` leaves the rows off `o` of a product unchanged. -/
private theorem reflector_mul_apply_of_not_mem {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) (N : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (hi : i ∉ o)
    (q : Fin n) : ((1 - β • vecMulVec v v) * N) i q = N i q := by
  rw [mul_apply]
  simp_rw [reflector_apply_of_not_mem hv β hi]
  rw [← mul_apply, Matrix.one_mul]

/-- A reflector acting on `o` leaves the columns off `o` of a product unchanged. -/
private theorem mul_reflector_apply_of_not_mem {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) (N : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) {j : Fin n}
    (hj : j ∉ o) : (N * (1 - β • vecMulVec v v)) i j = N i j := by
  rw [mul_apply]
  simp_rw [reflector_apply_of_not_mem' hv β _ hj]
  rw [← mul_apply, Matrix.mul_one]

/-- A reflector acting on `o` leaves a column vanishing on `o` unchanged. -/
private theorem reflector_mul_apply_of_col {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) (N : Matrix (Fin n) (Fin n) ℝ) (i q : Fin n)
    (hN : ∀ l ∈ o, N l q = 0) : ((1 - β • vecMulVec v v) * N) i q = N i q := by
  have hdot : v ⬝ᵥ (fun l => N l q) = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l ∈ o
    · simp [hN l hl]
    · simp [hv l hl]
  change ((1 - β • vecMulVec v v) *ᵥ fun l => N l q) i = N i q
  rw [one_sub_smul_vecMulVec_mulVec_apply, hdot, mul_zero, sub_zero]

/-- Right multiplication by a reflector acting on `o` sees only the columns in `o`. -/
private theorem mul_reflector_apply_congr {o : List (Fin n)} {v : Fin n → ℝ}
    (hv : ∀ i, i ∉ o → v i = 0) (β : ℝ) {N₁ N₂ : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (hN : ∀ l ∈ o, N₁ i l = N₂ i l) {j : Fin n} (hj : j ∈ o) :
    (N₁ * (1 - β • vecMulVec v v)) i j = (N₂ * (1 - β • vecMulVec v v)) i j := by
  rw [mul_apply, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l ∈ o
  · rw [hN l hl]
  · rw [reflector_apply_of_not_mem hv β hl, one_apply_ne (fun h => hl (by rw [h]; exact hj)),
      mul_zero, mul_zero]

/-- **One exact pass keeps the invariant** (the book's derivation of Algorithm 7.4.2: with
`P_k = diag(I_k, P̃_k)`, `(P₁ ⋯ P_k)ᵀ A (P₁ ⋯ P_k)` is upper Hessenberg through its first `k`
columns). `houseOn_spec` maps the tail of column `k` to a multiple of `e_{k+1}`;
`householderApplyLeft_spec` and `householderApplyRight_spec` give `P W P` on the active columns,
the columns `< k` being untouched because `W` vanishes there on the active rows. -/
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
        rw [mul_reflector_apply_of_not_mem hvout _ _ _ hjo,
          reflector_mul_apply_of_col hvout _ _ _ _ (hWo j hjk)]
      rw [hPW]
      refine ⟨fun h => (hW i j).1 ⟨hjk, h.2⟩, fun h => ?_⟩
      have hjk' : j ≠ k' := fun e => by rw [e] at hjk; omega
      rw [of_apply, ite_eq_right (fun h' => hjk' h'.1), hCeq,
        mul_reflector_apply_of_not_mem hvout _ _ _ hjo, hBeq, of_apply,
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
      rw [mul_apply, mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hAW r l (by have := (hmo l).1 hl; omega)]
    · -- the column `k`
      have hjeq : j = k' := Fin.ext (by rw [hk'v]; omega)
      subst hjeq
      have hko : k' ∉ o := by rw [hmo]; omega
      have hPWk : (P * W * P) i k' = (P *ᵥ x) i := by
        rw [mul_reflector_apply_of_not_mem hvout _ _ _ hko]
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
          mul_reflector_apply_of_not_mem hvout _ _ _ hko, hBeq, of_apply,
          ite_eq_left (by rw [mem_indexFrom]; omega)]
        rfl

/-- The invariant holds after the first `t` passes of Algorithm 7.4.2 (exact arithmetic). -/
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

/-- **Algorithm 7.4.2 computes a Hessenberg decomposition** (7.4.3), exactly: with
`(A', data) = Id.run (algorithm_7_4_2 pure A)` and `U₀ = householderProduct data` (the reflectors
built from the returned `(v, β)`, never from the stored vectors): `U₀` is orthogonal,
`hessenbergPart A' = U₀ᵀ A U₀` is upper Hessenberg, `U₀ e₁ = e₁`, and `data` has `n - 2` entries,
the `k`-th vanishing on the indices `≤ k`. The statement is not made with `β = 2/(vᵀv)` rebuilt
from the array: for `A = [[1,2,3],[4,5,6],[0,7,8]]`, `house` returns `β = 0` at `k = 0`, and the
rebuilt `diag(1, -1, 1)` does not reproduce `H = A`. -/
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

/-! ### The bridge -/

/-- The array of Algorithm 7.4.2 after `t` steps with the stored Householder vectors (columns
`< t`, rows below the subdiagonal) replaced by zeros. -/
def zeroStored (t : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (j : ℕ) < t ∧ (j : ℕ) + 2 ≤ i then 0 else A i j

/-- The active rows `k + 1, …` as a list and as a subtype. -/
private def tailEquiv (k : ℕ) :
    {i : Fin n // i ∈ indexFrom n (k + 1)} ≃ {i : Fin n // k + 1 ≤ (i : ℕ)} :=
  Equiv.subtypeEquivRight fun _ => mem_indexFrom

/-- `indexFrom n j` has at most `n` entries. -/
private theorem length_indexFrom_le (j : ℕ) : (indexFrom n j).length ≤ n := by
  rw [indexFrom]
  exact (List.length_filter_le _ _).trans (by simp)

/-- **The bridge of one step of Algorithm 7.4.2**: every run of the step maps the zeroed array
after `k` steps to the zeroed array after `k + 1` steps by a computed step
`FloatingPoint.RoundsHessenbergStepPert` of order `18 n + 31`. -/
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

/-- **The bridge of Algorithm 7.4.2** (convention 12): over an idempotent model with
`(18 n + 31) u < 1`, every run `(A', data)` has a sequence `Â` of arrays — the run's array after `k`
passes with the stored vectors replaced by zeros (they are never read again) — with
`Â (n - 2) = hessenbergPart A'` and `FloatingPoint.RoundsHessenbergReducePert` of order
`18 n + 31`: each pass is a computed step `FloatingPoint.RoundsHessenbergStepPert`
(`hessenbergReduceStep_rounds`). -/
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
/-- **§7.4.3, Wilkinson's backward error of the Hessenberg reduction**, rigorous: "the computed
Hessenberg matrix `Ĥ` satisfies `Ĥ = Qᵀ (A + E) Q` where `Q` is orthogonal and
`‖E‖_F ≤ c n² u ‖A‖_F`". Over an idempotent model with `K = 18 n + 31`, `(3K + n + 3) u < 1` and
`2 (n - 2) ε < 1` for `ε = 3 γ_{3K+n+3}`, every run `(A', data)` of Algorithm 7.4.2 has
`hessenbergPart A'` upper Hessenberg and `= Qᵀ (A + E) Q` with `Q` orthogonal and
`‖E‖_F ≤ γ_{2(n-2)}(ε) ‖A‖_F` (`≈ 6 (55 n + 96)(n - 2) u`): `algorithm_7_4_2_rounds` and the
backbone's `FloatingPoint.exists_roundsHessenbergReducePert_eq`. The constants are the relational
calculus's, not Wilkinson's. -/
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

/-- **§7.4.5, Definition**: an upper Hessenberg matrix is *unreduced* if it has no zero subdiagonal
entries — the backbone's `Matrix.IsUnreducedUpperHessenberg`; `isUnreduced_iff` spells it out
along the subdiagonal. -/
def IsUnreduced (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.IsUnreducedUpperHessenberg

/-- An unreduced upper Hessenberg matrix: upper Hessenberg with `h_{k+1,k} ≠ 0` for every
`k < n - 1` (0-based). -/
theorem isUnreduced_iff {H : Matrix (Fin n) (Fin n) ℝ} :
    IsUnreduced H ↔
      H.IsUpperHessenberg ∧ ∀ (k : ℕ) (hk : k + 1 < n), H ⟨k + 1, hk⟩ ⟨k, by omega⟩ ≠ 0 :=
  isUnreducedUpperHessenberg_iff_fin

/-- **Theorem 7.4.2 (implicit Q theorem).** Let `Q`, `V` be orthogonal with `Qᵀ A Q = H` and
`Vᵀ A V = G` upper Hessenberg and the same first column, `q₁ = v₁`. If the first `k` subdiagonal
entries `h_{i+1,i}`, `i < k` (0-based), are nonzero — the book's "`k + 1` is the smallest index with
`h_{k+1,k} = 0`", or `k = n - 1` when `H` is unreduced — then `v_i = ± q_i` for `i ≤ k`,
`|g_{i+1,i}| = |h_{i+1,i}|` for `i < k`, and `g_{k+1,k} = 0` when `h_{k+1,k} = 0`. -/
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

/-- **The gist of Theorem 7.4.2**: if `Qᵀ A Q = H` is unreduced upper Hessenberg, `Zᵀ A Z = G` is
upper Hessenberg, and `Q`, `Z` have the same first column, then `Z = Q D` and `G = D H D` for a
diagonal `D = diag(±1, …, ±1)` (`D⁻¹ = D`) — "`G` and `H` are essentially equal". -/
theorem theorem_7_4_2_essential {N : ℕ} {A Q Z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hZ : Z ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hH : IsUnreduced (Qᵀ * A * Q)) (hG : (Zᵀ * A * Z).IsUpperHessenberg)
    (h0 : Z.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧ Z = Q * diagonal d ∧
      Zᵀ * A * Z = diagonal d * (Qᵀ * A * Q) * diagonal d :=
  implicitQ_real hQ hZ hH hG h0

/-- **§7.4.5, Definition: the Krylov matrix** `K(A, v, j) = [v | Av | ⋯ | A^{j-1} v] ∈ ℝ^{n×j}`,
the backbone's `Matrix.krylovMatrix`. -/
def krylovMatrix (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin j) ℝ :=
  Matrix.krylovMatrix A v j

/-- **Theorem 7.4.3.** For orthogonal `Q`, `Qᵀ A Q = H` is unreduced upper Hessenberg if and only if
`Qᵀ K(A, Q(:, 1), n) = R` is nonsingular and upper triangular. -/
theorem theorem_7_4_3 {N : ℕ} {Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    IsUnreduced (Qᵀ * A * Q) ↔
      (Qᵀ * krylovMatrix A (Q.col 0) (N + 1)).IsUpperTriangular ∧
        IsUnit (Qᵀ * krylovMatrix A (Q.col 0) (N + 1)).det := by
  have h := isUnreducedUpperHessenberg_conj_iff_krylovMatrix hQ A
  rwa [star_eq_transpose_real] at h

/-- The geometric multiplicity of an eigenvalue is at least one. -/
private theorem one_le_finrank_eigenspace {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ M) : 1 ≤ Module.finrank ℂ (Module.End.eigenspace (toLin' M) μ) := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul M μ).1 hμ
  refine Submodule.one_le_finrank_iff.2 fun h => hv0 ?_
  have hmem : v ∈ Module.End.eigenspace (toLin' M) μ := by
    rw [Module.End.mem_eigenspace_iff, toLin'_apply]; exact hv
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

/-- The geometric multiplicity of every eigenvalue of an unreduced upper Hessenberg matrix is at
most one (the backbone's rank argument, after complexification). -/
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

/-- **Theorem 7.4.4.** If `λ` is an eigenvalue of an unreduced upper Hessenberg `H ∈ ℝ^{n×n}`, its
geometric multiplicity is `1`: `rank(H - λI) ≥ n - 1` because the first `n - 1` columns of
`H - λI` are independent. (The book writes `A - λI` for `H - λI` in the proof.) -/
theorem theorem_7_4_4 {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUnreduced H) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ H.complexify) :
    Module.finrank ℂ (Module.End.eigenspace (toLin' H.complexify) μ) = 1 :=
  le_antisymm (finrank_eigenspace_le_one_of_isUnreduced hH μ) (one_le_finrank_eigenspace hμ)

/-! ### §7.4.6 The companion matrix decomposition -/

/-- **(7.4.4), the companion matrix** in the book's layout: ones on the subdiagonal, last column
`-c`, zeros elsewhere. Its relation to the backbone's `Matrix.companion` (first-row layout) is
`companion_eq`. -/
def companion (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (j : ℕ) + 1 = n then -c i else if (i : ℕ) = j + 1 then 1 else 0

/-- The monic polynomial `z^n + c_{n-1} z^{n-1} + ⋯ + c₀` with coefficients `c`. -/
private theorem coeff_X_pow_add_sum (c : Fin n → ℝ) (i : Fin n) :
    (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff i = c i := by
  have hi : (i : ℕ) ≠ n := i.isLt.ne
  simp only [coeff_add, coeff_X_pow, hi, ↓reduceIte, zero_add, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · simp
  · rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h).symm hji

/-- The companion matrix (7.4.4) is the transpose of the backbone's `Matrix.companion p n` of
`p = z^n + ∑ c_i z^i`, read in reverse order. -/
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

/-- **§7.4.6**: `det(zI - C) = c₀ + c₁ z + ⋯ + c_{n-1} z^{n-1} + z^n` for the companion matrix
(7.4.4). -/
theorem charpoly_companion' (c : Fin n → ℝ) :
    (companion c).charpoly = X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ) := by
  have hdeg := degree_sum_fin_lt c
  have hmonic : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).Monic := monic_X_pow_add hdeg
  have hnat : (X ^ n + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).natDegree = n := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  rw [companion_eq, show ∀ M : Matrix (Fin n) (Fin n) ℝ, M.submatrix Fin.rev Fin.rev =
      reindex Fin.revPerm Fin.revPerm M from fun M => rfl, charpoly_reindex, charpoly_transpose,
    charpoly_companion hmonic hnat]

/-- **§7.4.6 with (7.4.4).** If the Krylov matrix `K = K(A, x, n)` satisfies `K c = -A^n x`, then
`A K = K C` for the companion matrix `C` of `c`, whose characteristic polynomial is
`c₀ + c₁ z + ⋯ + c_{n-1} z^{n-1} + z^n`; so if `K` is nonsingular, `K⁻¹ A K = C` displays `A`'s
characteristic polynomial. -/
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
    rw [lhs, mul_apply]
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

/-- **§7.4.6, Definition**: `A` is *nonderogatory* if each (complex) eigenvalue has unit geometric
multiplicity, `dim null(A - λI) ≤ 1` for every `λ`. -/
def IsNonderogatory (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ : ℂ, Module.finrank ℂ (Module.End.eigenspace (toLin' A.complexify) μ) ≤ 1

/-- **§7.4.6: "`A` is similar to an unreduced Hessenberg matrix only if each eigenvalue has unit
geometric multiplicity"** — Theorem 7.4.4 transported along the (complexified) similarity. -/
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
