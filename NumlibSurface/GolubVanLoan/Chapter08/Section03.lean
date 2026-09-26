import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighQuotientIteration
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter08.Section02

/-!
# Golub–Van Loan §8.3: the symmetric QR algorithm

Surface file for [golub2013matrix] §8.3: the tridiagonal decomposition (8.3.1) and the symmetric
Householder update, unreduced tridiagonal matrices and the splitting of the spectrum, the facts of
§8.3.3 about the QR iteration on tridiagonal matrices (preservation of form, shifts, perfect
shifts), the Wilkinson shift (8.3.3), the explicit shifted iteration (8.3.2), the Rayleigh-quotient
connection (§8.3.6) and orthogonal iteration with Ritz acceleration ((8.3.6), §8.3.7).

## Conventions

Tridiagonal matrices are stored as full `Matrix (Fin n) (Fin n) ℝ` (`Matrix.IsTridiagonal`);
"unreduced" is `IsUnreducedTridiagonal`, chapter 7's `Matrix.IsUnreducedUpperHessenberg` together
with tridiagonality. The explicit shifted step is the backbone's `Matrix.shiftedQrStep` (canonical
`Matrix.qrQ`/`Matrix.qrR`).

The numbered algorithms (8.3.1–8.3.3) call chapter 5's `house`/`givens` helpers on index lists
(conventions 10, 13): Algorithm 8.3.1 returns its reflector data, Algorithm 8.3.2 runs on a
window of consecutive indices with an accumulator, Algorithm 8.3.3 is a `fuel`-bounded loop with a
`done` flag. Algorithm 8.3.1 has the rounding bridge to the backbone's
`FloatingPoint.RoundsTridiagonalizePert` and the book's backward-error bound. Theorems 8.3.1–8.3.2
restate chapter 7's Krylov-matrix and implicit-Q theorems.

## Readings

The Wilkinson shift (8.3.3) needs `sign(0) = 1`. The "preservation of form" fact of §8.3.3 holds
for every QR factorization only when `T` is nonsingular (for singular `T` the orthogonal factor is
not unique: `T = 0 = Q · 0`); the node assumes it.

## Not formalized

Wilkinson's cubic convergence of the shifted QR iteration (quoted), Stewart's rate for Ritz
acceleration (quoted), storage and flop counts.
-/

open Matrix FloatingPoint

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.3.1 Reduction to tridiagonal form -/

/-- **(8.3.1), the tridiagonal decomposition.** For symmetric `A` there is an orthogonal `Q` with
`Qᵀ A Q` symmetric tridiagonal, and `Q` may be taken with first column `e₁`. -/
theorem equation_8_3_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, (Qᵀ * A * Q).IsSymm ∧ (Qᵀ * A * Q).IsTridiagonal ∧
      ∀ h : 0 < n, Q *ᵥ Pi.single ⟨0, h⟩ 1 = Pi.single ⟨0, h⟩ 1 := by
  have hsymm : ∀ Q : Matrix (Fin n) (Fin n) ℝ, (Qᵀ * A * Q).IsSymm := fun Q => by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hA))
  rcases n with _ | M
  · exact ⟨1, one_mem _, hsymm 1, fun i j _ => Fin.elim0 i, fun h => absurd h (lt_irrefl 0)⟩
  · refine ⟨hessenbergQ A, hessenbergQ_mem_orthogonalGroup A, hsymm _, ?_, fun h => ?_⟩
    · have h := isTridiagonal_hessenbergReduce_of_isHermitian (A := A) (isHermitian_iff_isSymm.2 hA)
      rwa [hessenbergReduce_eq_conj, conjTranspose_eq_transpose_of_trivial] at h
    · rw [mulVec_single_one]
      ext i
      rw [col_apply, show (⟨0, h⟩ : Fin (M + 1)) = 0 from rfl, hessenbergQ_apply_zero A i]
      by_cases hi : i = 0 <;> simp [hi, one_apply]

/-- **§8.3.1, the symmetric Householder update.** For symmetric `B`, `P = I - β v vᵀ`,
`p = β B v` and `w = p - (β pᵀv / 2) v`: `P B P = B - v wᵀ - w vᵀ`. -/
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

/-- The lower-triangle index pairs `(i, j)`, `j ≤ i`, of an index list, row by row. -/
def lowerPairs (T : List (Fin n)) : List (Fin n × Fin n) :=
  T.flatMap fun i => (T.filter (· ≤ i)).map fun j => (i, j)

/-- The array written by step `k` of Algorithm 8.3.1 (`k + 1 < n`) from the computed lower triangle
`L` of the trailing block and the fresh norm `ν`: the block `A(T_k, T_k)` from `L`, mirrored
(copies), `ν` at `(k + 1, k)` and `(k, k + 1)`, and `A` elsewhere. -/
def tridiagonalizeOut (k : Fin n) (hk : (k : ℕ) + 1 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (L : Fin n × Fin n → ℝ) (ν : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun r s =>
    if (k : ℕ) + 1 ≤ r ∧ (k : ℕ) + 1 ≤ s then (if s ≤ r then L (r, s) else L (s, r))
    else if (r = ⟨k + 1, hk⟩ ∧ s = k) ∨ (r = k ∧ s = ⟨k + 1, hk⟩) then ν else A r s

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Step `k` of Algorithm 8.3.1** on the working array `A` (`k + 1 < n`), on the tail
`T_k = [k+1, …, n-1]` (convention 10): `(v, β) = house(A(k+1:n, k))` (chapter 5's `houseOn`);
`p = β A(T_k, T_k) v` (each `p_i = fl(β · fl(A(i, T_k) ⬝ v))`, Algorithm 1.1.1 from `0`);
`w = p - (β pᵀv / 2) v` (`h = fl(fl(β fl(pᵀv)) / 2)`, `w_i = fl(p_i - fl(h v_i))`);
`A(k+1, k) = A(k, k+1) = ‖A(k+1:n, k)‖₂` (the fresh norm `fl(√(fl(A(T_k, k)ᵀ A(T_k, k))))`);
`A(T_k, T_k) = A(T_k, T_k) - v wᵀ - w vᵀ`, the lower triangle computed
(`fl(fl(a_ij - fl(v_i w_j)) - fl(w_i v_j))`, `j ≤ i`, from the entries of `A`, which the loop
reads before overwriting them) and mirrored (a copy). Returns the array and `(v, β)`. -/
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

/-- **Algorithm 8.3.1 (Householder tridiagonalization).** "Given a symmetric `A ∈ ℝ^{n×n}`, the
following algorithm overwrites `A` with `T = QᵀAQ`, where `T` is tridiagonal and
`Q = H₁ ⋯ H_{n-2}` is the product of Householder transformations."
```
for k = 1:n-2
    [v, β] = house(A(k+1:n, k))
    p = β A(k+1:n, k+1:n) v
    w = p - (β pᵀv / 2) v
    A(k+1, k) = ‖A(k+1:n, k)‖₂; A(k, k+1) = A(k+1, k)
    A(k+1:n, k+1:n) = A(k+1:n, k+1:n) - v wᵀ - w vᵀ
end
```
0-based `k = 0, …, n-3`, one `tridiagonalizeStep` each; the program returns the array and the
reflector data `(v_k, β_k)` in order of application (convention 13; the book's "factored form"
that Algorithm 8.3.3 accumulates). The entries `A(k+2:n, k)` are left as they were (the book
does not overwrite them either; they are never read again). -/
noncomputable def algorithm_8_3_1 (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) :=
  (List.finRange (n - 2)).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ))
      (k : Fin (n - 2)) => do
    let r ← tridiagonalizeStep rnd (k.castLE (Nat.sub_le n 2))
      (by rw [Fin.val_castLE]; omega) st.1
    pure (r.1, st.2 ++ [r.2])) (A, [])

end Programs

/-- The band of an array (tridiagonal part), the other entries set to `0`: an exact copy. -/
def tridiagonalPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) ≤ j + 1 ∧ (j : ℕ) ≤ i + 1 then A i j else 0

/-! ### Algorithm 8.3.1: the bridge and the rounding bound -/

/-- The array after `k` steps of Algorithm 8.3.1 with the entries it never reads again — the
vectors below the subdiagonal of the reduced columns, and their mirror images — set to `0`: the
`Â_k` of `FloatingPoint.RoundsTridiagonalizePert`. -/
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

/-- The indices `≥ k + 1` as a subtype, and the list `indexFrom n (k + 1)` of them. -/
private def tailEquiv (k : ℕ) :
    {i : Fin n // k + 1 ≤ (i : ℕ)} ≃ {i // i ∈ Chapter05.indexFrom n (k + 1)} :=
  Equiv.subtypeEquivRight fun _ => Chapter05.mem_indexFrom.symm

private theorem head_le_of_pairwise {l : List (Fin n)} (hl : l.Pairwise (· < ·)) (h : l ≠ [])
    {x : Fin n} (hx : x ∈ l) : l.head h ≤ x := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hl hx).le

private theorem head_indexFrom {k : ℕ} (hk : k + 1 < n)
    (hne : Chapter05.indexFrom n (k + 1) ≠ []) :
    (Chapter05.indexFrom n (k + 1)).head hne = ⟨k + 1, hk⟩ := by
  have hpw : (Chapter05.indexFrom n (k + 1)).Pairwise (· < ·) :=
    (List.sortedLT_finRange n).pairwise.filter _
  refine le_antisymm (head_le_of_pairwise hpw hne (Chapter05.mem_indexFrom.2 le_rfl)) ?_
  exact Fin.le_def.2 (Chapter05.mem_indexFrom.1 (List.head_mem hne))

/-- An accumulation from `0` over the tail list is a `RoundsDot` on the tail subtype. -/
private theorem roundsDot_tail {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (k : ℕ)
    {x y : Fin n → ℝ} {s : ℝ}
    (h : s ∈ (dotAccum fp.round (Chapter05.indexFrom n (k + 1)) x y 0).run) :
    RoundsDot fp (fun i : {i : Fin n // k + 1 ≤ (i : ℕ)} => x i) (fun i => y i) s :=
  (roundsDot_comp_equiv_iff (tailEquiv k)).2
    (Chapter05.roundsDot_subtype_of_mem_run_dotAccum hfp (Chapter05.nodup_indexFrom _ _) h)

/-- Reflector data of order `K` are data of every larger order `K'` with `K' u < 1`. -/
private theorem isReflectorPert_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {u : ℝ}
    (hu : 0 ≤ u) {K K' : ℕ} (hK : K ≤ K') (hK' : (K' : ℝ) * u < 1) {x : ι → ℝ} {i : ι} {c : ℝ}
    {vhat : ι → ℝ} {βhat : ℝ} (h : IsReflectorPert u K x i c vhat βhat) :
    IsReflectorPert u K' x i c vhat βhat := by
  obtain ⟨v, β, hO, hmul, hβv, hβ, hv⟩ := h
  exact ⟨v, β, hO, hmul, hβv, hβ.mono hu hK hK', fun j => (hv j).mono hu hK hK'⟩

/-- The lower-triangle pairs of a list are its pairs `(i, j)` with `j ≤ i`. -/
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

/-- The runs of one step of Algorithm 8.3.1, unpacked. -/
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

/-- The tail of column `k` of the cleaned array is that of the array. -/
private theorem bandClean_col_tail (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => bandClean (k : ℕ) A i k) =
      fun i : {i : Fin n // (k : ℕ) + 1 ≤ (i : ℕ)} => A i k :=
  funext fun i => bandClean_apply_of_le A (by have := i.2; omega) le_rfl

/-- The reflector of a step of Algorithm 8.3.1, on the tail subtype, at the common order
`18 n + 31`. -/
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
  have h1 := isReflectorPert_mono hu0 (by omega : 18 * T.length + 31 ≤ 18 * n + 31) hu hrefl
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
      ⟨T.head hne, List.head_mem hne⟩ := Subtype.ext (head_indexFrom hk hne).symm
  rw [hpiv]
  exact h1

/-- The rank-two update of a step of Algorithm 8.3.1 on the tail block. -/
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

/-- The entries of the cleaned array that a step of Algorithm 8.3.1 copies. -/
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

/-- **The bridge of one step of Algorithm 8.3.1**: every run of `tridiagonalizeStep` at step `k`
is a computed tridiagonalization step (`FloatingPoint.RoundsTridiagonalizeStepPert`, order
`18 n + 31`) between the cleaned arrays. -/
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

/-- **The bridge of Algorithm 8.3.1** (convention 12): for an idempotent model with
`(18 n + 31) u < 1`, every run `(A', data)` of Algorithm 8.3.1 has a sequence `Â` with `Â_0 = A`,
`Â_{n-2}` the tridiagonal part of `A'`, and consecutive arrays computed tridiagonalization steps:
`FloatingPoint.RoundsTridiagonalizePert fp (18 n + 31) A Â`. `Â_k` is the run's array after `k`
steps with the never-read vector entries below the subdiagonal of the reduced columns (and their
mirror images) set to `0`. Per step: chapter 5's `houseOn_rounding` (reflector data of order
`18 |T_k| + 31 ≤ 18 n + 31`, target `+‖x‖₂`), the accumulations from `0` as `RoundsDot`s on the
tail, and the lower-triangle update with its mirror a `RoundsSymmRankTwoUpdate`. -/
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

/-- **Rounding errors of Algorithm 8.3.1** (§8.3.1, after the algorithm: "`T̂ = Q̃ᵀ(A + E)Q̃`
where `Q̃` is exactly orthogonal and `E` is a symmetric matrix satisfying `‖E‖_F ≤ c u ‖A‖_F`";
Wilkinson AEP p. 297), rigorous: for an idempotent model with `(6K + 2n + 8) u < 1` and
`(n - 2) ε < 1`, `K = 18 n + 31`, `ε = 9 γ_{6K+2n+8} + 2 γ_{n+1}`, and symmetric `A`, the band
`T̂` of every run of Algorithm 8.3.1 is symmetric tridiagonal and `T̂ = Q̃ᵀ (A + E) Q̃` with `Q̃`
orthogonal, `E` symmetric and `‖E‖_F ≤ γ_{n-2}(ε) ‖A‖_F` (`≈ c n² u`). -/
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
/-- **§8.3.1, "unreduced"**: a tridiagonal `T` is unreduced when no subdiagonal entry vanishes. -/
def IsUnreducedTridiagonal (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  T.IsTridiagonal ∧ T.IsUnreducedUpperHessenberg

/-- **§8.3.1, splitting.** If `T` is tridiagonal of order `(k + 1) + (l + 1)` and
`t_{k+1,k} = t_{k,k+1} = 0` (0-based at `k`, `k + 1`), then `T = diag(T₁, T₂)` with
`T₁ = T(1:k+1, 1:k+1)`, `T₂ = T(k+2:n, k+2:n)`, and `λ(T) = λ(T₁) ∪ λ(T₂)` with multiplicity. -/
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

/-! ### §8.3.2 Properties of the tridiagonal decomposition -/

/-- **Theorem 8.3.1.** If `Qᵀ A Q = T` is a tridiagonal decomposition (`Q` orthogonal, `T`
tridiagonal) and `R = Qᵀ K(A, Q(:, 1), n)` (chapter 7's Krylov matrix), then `R` is upper
triangular with `r₁₁ = 1` and `r_{i+1,i+1} = t_{i+1,i} r_ii`, i.e. `r_ii = t₂₁ t₃₂ ⋯ t_{i,i-1}`;
if `R` is nonsingular, `T` is unreduced; if `R` is singular and `k` is the least index with
`r_kk = 0`, then `k ≥ 2` and `k` is the least index with `t_{k,k-1} = 0` (0-based: `k = i + 1`
with `t_{i+1,i} = 0` and no earlier zero). `Qᵀ K(A, Q e₁, n) = K(T, e₁, n)`, whose columns
`T^j e₁` are supported on the first `j + 1` coordinates with last entry `∏ t_{i+1,i}`. -/
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

/-- **Theorem 8.3.2 (implicit Q theorem, tridiagonal form).** Let `Q`, `V` be orthogonal with
`Qᵀ A Q = T` and `Vᵀ A V = S` tridiagonal and `Q(:, 1) = V(:, 1)`, and let the first `k`
subdiagonal entries `t_{i+1,i}`, `i < k` (0-based), be nonzero — the book's "`k` the smallest
positive integer with `t_{k+1,k} = 0`" (`k = n` if `T` is unreduced). Then `V(:, i) = ± Q(:, i)`
and `|t_{i+1,i}| = |s_{i+1,i}|` up to `k`, and `s_{k+1,k} = 0` when `t_{k+1,k} = 0`. Chapter 7's
Theorem 7.4.2 for the tridiagonal (hence upper Hessenberg) `T`, `S`. (The book takes `A`
symmetric, which makes `T` and `S` tridiagonal; the proof uses only that they are.) -/
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

/-! ### §8.3.3 The QR iteration and tridiagonal matrices -/

/-- **§8.3.3, preservation of form.** If `T` is symmetric tridiagonal and `T = Q R` with `Q`
orthogonal and `R` upper triangular — `T` nonsingular, or `(Q, R)` the Givens QR
`Matrix.hessenbergGivensQR T` (for singular `T` and an arbitrary QR the claim is false,
`T = 0 = Q · 0`) — then `Q` is upper Hessenberg (lower bandwidth `1`), `R` has upper bandwidth `2`,
and `T₊ = R Q = Qᵀ T Q` is symmetric tridiagonal. -/
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
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hTs))
  have hRQH : (R * Q).IsUpperHessenberg := hR.mul_isUpperHessenberg hQH
  refine ⟨isUpperHessenberg_iff_hasLowerBandwidth_one.1 hQH, ?_, hRQ, hsym,
    hRQH.isTridiagonal_of_isSymm hsym⟩
  -- `R = Qᵀ T`, a product of upper bandwidths `1` and `1`
  have hRe : R = Qᵀ * T := by rw [hQR, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hQt : Qᵀ.HasUpperBandwidth 1 := by
    rw [hasUpperBandwidth_iff_transpose, transpose_transpose]
    exact isUpperHessenberg_iff_hasLowerBandwidth_one.1 hQH
  have hTu : T.HasUpperBandwidth 1 := by
    rw [hasUpperBandwidth_iff_transpose, hTs.eq]
    exact isUpperHessenberg_iff_hasLowerBandwidth_one.1 hT.isUpperHessenberg
  rw [hRe]
  exact hQt.mul hTu

/-- **§8.3.3, shifts.** For symmetric tridiagonal `T`, `s ∈ ℝ` and a QR factorization
`T - sI = Q R` (with `T - sI` nonsingular or `(Q, R)` the Givens QR), the shifted step
`T₊ = R Q + s I = Qᵀ T Q` is symmetric tridiagonal. -/
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

/-- **§8.3.3, perfect shifts.** If `T` is symmetric tridiagonal and unreduced, then for every `s`
the first `n - 1` columns of `T - sI` are linearly independent; if moreover `s` is an eigenvalue
and `QR = T - sI` is any QR factorization, then `r_nn = 0` and the last column of
`T₊ = RQ + sI` is `s e_n`. -/
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
      simp [P, R', col_apply, mulVec, dotProduct, one_apply, h0,
        (Fin.castSucc_ne_last _).symm]
    · simp [P, R', col_apply, mulVec, dotProduct, one_apply, Fin.castSucc_inj]
  have hliR' : LinearIndependent ℝ (fun j : Fin N => R'.col j) := by
    refine LinearIndependent.of_comp P.mulVecLin ?_
    convert hliR using 1
    funext j
    simp [hcolR]
  have hR'det : R'.det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).1 (linearIndependent_cols_iff_isUnit.1 hliR')).ne_zero
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
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hTs))
  rw [← hsym.apply]
  by_cases hi : i = Fin.last N
  · subst hi
    simp [Matrix.add_apply, mul_apply, hrow]
  · simp [Matrix.add_apply, mul_apply, hrow, one_apply, hi, Ne.symm hi]

/-! ### §8.3.4 Explicit single-shift QR iteration -/

/-- **The Wilkinson shift (8.3.3)**: for `T` of order `n ≥ 2` with trailing `2 × 2` block
`[a_{n-1} b_{n-1}; b_{n-1} a_n]`, `μ = a_n + d - sign(d) √(d² + b_{n-1}²)`, `d = (a_{n-1} - a_n)/2`,
with `sign(0) = 1`. -/
noncomputable def wilkinsonShift {N : ℕ} (T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : ℝ :=
  let a := T (Fin.last (N + 1)) (Fin.last (N + 1))
  let a' := T (Fin.last N).castSucc (Fin.last N).castSucc
  let b := T (Fin.last (N + 1)) (Fin.last N).castSucc
  let d := (a' - a) / 2
  a + d - (if 0 ≤ d then 1 else -1) * Real.sqrt (d ^ 2 + b ^ 2)

/-- **(8.3.3).** The Wilkinson shift `μ` is an eigenvalue of the trailing `2 × 2` block,
`(μ - a_{n-1})(μ - a_n) - b² = 0`, the one closer to `a_n` (`|μ - a_n| ≤ |μ' - a_n|` for the other
root `μ' = a_n + d + sign(d)√(d² + b²)`), and it equals Algorithm 8.3.2's form
`a_n - b² / (d + sign(d) √(d² + b²))`. -/
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

/-- **(8.3.2), the explicit single-shift QR iteration**: `T_{k+1} = R U + μ I` for the QR
factorization `U R = T_k - μ I` (the backbone's canonical `Matrix.shiftedQrStep`), with the shift
chosen by a rule `shift` (`T ↦ t_nn` or the Wilkinson shift). -/
noncomputable def explicitShiftedQR (shift : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (T₀ : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => T₀
  | k + 1 => shiftedQrStep (shift (explicitShiftedQR shift T₀ k)) (explicitShiftedQR shift T₀ k)

/-- Each iterate of (8.3.2) is orthogonally similar to `T₀`; for symmetric `T₀` it is symmetric,
and for symmetric tridiagonal `T₀` with every shifted matrix nonsingular it stays tridiagonal. -/
theorem explicitShiftedQR_spec (shift : Matrix (Fin n) (Fin n) ℝ → ℝ)
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
      simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
        (isHermitian_conjTranspose_mul_mul U (isHermitian_iff_isSymm.2 hs))

/-! ### §8.3.5 Implicit shift version -/

/-- **§8.3.5, one bulge-chasing step.** Let `T` be symmetric and tridiagonal except for a bulge at
`(k + 2, k)` and `(k, k + 2)` (0-based; the book's `z_k`), and let `(c, s)` satisfy
`s b_k + c z_k = 0` with `b_k = t_{k+1,k}`, `z_k = t_{k+2,k}`. Then after the rotation
`G(k + 1, k + 2, θ)` of the book (`Matrix.planeRotation (k+1) (k+2) c (-s)`), `Gᵀ T G` is
tridiagonal except for a bulge at `(k + 3, k + 1)` and `(k + 1, k + 3)`, of value
`z_{k+1} = -s b_{k+2}` (`b_{k+2} = t_{k+3,k+2}`): the bulge moves one step down the band. -/
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

/-! ### §8.3.5 Algorithms 8.3.2 and 8.3.3 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The Wilkinson shift as Algorithm 8.3.2 computes it from `a' = t_{n-1,n-1}`, `a = t_nn` and
`b = t_{n,n-1}`: `d = fl(fl(a' - a)/2)`,
`μ = fl(a - fl(fl(b²) / fl(d + sign(d) fl(√(fl(fl(d²) + fl(b²)))))))` (`sign(0) = 1`; the sign
is a copy or a negation, exact). -/
noncomputable def wilkinsonShiftComputed (a' a b : ℝ) : M ℝ := do
  let d ← rnd ((← rnd (a' - a)) / 2)
  let b2 ← rnd (b * b)
  let r ← rnd √(← rnd ((← rnd (d * d)) + b2))
  let den ← rnd (d + (if 0 ≤ d then r else -r))
  rnd (a - (← rnd (b2 / den)))

/-- One bulge-chasing rotation of Algorithm 8.3.2 on the state `(T, Q, prev)`, at the pair
`(a, b)` of consecutive window indices: `x, z` are `t_{11} - μ`, `t_{21}` for the first pair
(`prev = none`) and `t_{a,prev}`, `t_{b,prev}` afterwards (the book's `x = t_{k+1,k}`,
`z = t_{k+2,k}`, copies); `[c, s] = givens(x, z)`, `T = G(a,b,θ)ᵀ T G(a,b,θ)` over the window `w`
(rows, then columns) and `Q = Q G(a,b,θ)` (all rows). -/
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

/-- **Algorithm 8.3.2 (implicit symmetric QR step with Wilkinson shift).** "Given an unreduced
symmetric tridiagonal matrix `T`, the following algorithm overwrites `T` with `ZᵀTZ`, where
`Z = G₁ ⋯ G_{n-1}` is a product of Givens rotations with the property that `Zᵀ(T - μI)` is upper
triangular and `μ` is that eigenvalue of `T`'s trailing 2-by-2 principal submatrix closer to
`t_nn`."
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
On a window `w = [w₀, …, w_{N-1}]` of consecutive indices (convention 10: the book's step is
`w = List.finRange n`, and Algorithm 8.3.3 runs it on its unreduced block), with the book's
optional accumulation `Q = Q G₁ ⋯ G_{N-1}`; the result is `(Zᵀ T Z, Q Z)`. For `N ≤ 1` nothing
is done. -/
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

/-- The deflation pass of Algorithm 8.3.3: for `i = 1:n-1`, set `d_{i+1,i} = d_{i,i+1} = 0` if
`|d_{i+1,i}| ≤ fl(tol · fl(|d_ii| + |d_{i+1,i+1}|))` (the right side rounded; `|·|` and the
comparison exact). -/
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

/-- The last maximal run of consecutive indices with a nonzero coupling: for `nz i` meaning "the
entry coupling `i` and `i + 1` is nonzero", with `e` the largest such `i` and `p` the smallest
index with `nz` on all of `p, …, e`, the window `[p, …, e + 1]`; empty if no `nz i` holds. Pure
index computation on exact comparisons. -/
noncomputable def lastRunWindow (n : ℕ) (nz : ℕ → Prop) [DecidablePred nz] : List (Fin n) :=
  match ((List.range n).filter fun i => nz i).getLast? with
  | none => []
  | some e =>
    let p := (((List.range (e + 1)).filter fun i => ¬ nz i).getLast?).elim 0 (· + 1)
    (List.finRange n).filter fun i => p ≤ (i : ℕ) ∧ (i : ℕ) ≤ e + 1

open Classical in
/-- The unreduced block `D₂₂` of Algorithm 8.3.3 as a window of consecutive indices: with the
largest `q` such that the trailing `q × q` block `D₃₃` is diagonal and decoupled, and the smallest
`p` such that `D₂₂ = D(p:n-q, p:n-q)` is unreduced, the window `[p, …, n-q-1]` (0-based); empty
when `q = n` (`D` diagonal). -/
noncomputable def unreducedWindow (D : Matrix (Fin n) (Fin n) ℝ) : List (Fin n) :=
  lastRunWindow n fun i => ∃ h : i + 1 < n, D ⟨i + 1, h⟩ ⟨i, by omega⟩ ≠ 0

/-- One pass of the `until q = n` loop of Algorithm 8.3.3 on `(D, Q, done)`: deflate, find the
window of `D₂₂`, stop if it is empty (`q = n`), else apply Algorithm 8.3.2 to it with the
accumulator `Q`. -/
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

/-- **Algorithm 8.3.3 (symmetric QR algorithm).** "Given `A ∈ ℝ^{n×n}` (symmetric) and a
tolerance `tol` greater than the unit roundoff, this algorithm computes an approximate symmetric
Schur decomposition `QᵀAQ = D`."
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
`D` is the band of Algorithm 8.3.1's array (the entries below the subdiagonal hold nothing of
`T`), `Q` the forward accumulation (§5.1.6) of its returned reflector data (never rebuilt,
convention 13); the `until` loop is at most `fuel` passes with a `done` flag (convention 3). The
result is `(D, Q, done)`. -/
noncomputable def algorithm_8_3_3 (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let Adata ← algorithm_8_3_1 rnd A
  let Q ← Chapter05.forwardAccumulation rnd Adata.2
  (List.range fuel).foldlM (fun st _ => symmetricQRPass rnd tol st)
    (tridiagonalPart Adata.1, Q, false)

end Programs

/-! ### §8.3.6 The Rayleigh quotient connection -/

/-- **§8.3.6.** For symmetric `T` of order `N + 1`, the shift `σ = t_nn` and the QR factorization
`T - σI = QR` (`Matrix.qrQ`, `Matrix.qrR`): `(T - σI) q_n = r_nn e_n` for the last column `q_n` of
`Q`, `r(e_n) = t_nn`, and if `T - σI` is nonsingular, one step of Rayleigh quotient iteration
(8.2.6) from `x_0 = e_n` gives `x_1 = ± q_n`. -/
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

/-! ### §8.3.7 Orthogonal iteration with Ritz acceleration -/

/-- **(8.3.6), orthogonal iteration with Ritz acceleration**: `Q_0` with orthonormal columns; for
`k ≥ 1`, `A Q_{k-1} = Q̃_k R_k` (a thin QR, `Matrix.IsOrthogonalIterationStep`),
`S_k = Q̃_kᵀ A Q̃_k`, `U_kᵀ S_k U_k = D_k` diagonal with `U_k` orthogonal (Schur),
`Q_k = Q̃_k U_k`. -/
def IsRitzAcceleration {r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Q Qt : ℕ → Matrix (Fin n) (Fin r) ℝ) (S U D : ℕ → Matrix (Fin r) (Fin r) ℝ) : Prop :=
  (Q 0)ᵀ * Q 0 = 1 ∧ ∀ k, IsOrthogonalIterationStep A (Q k) (Qt (k + 1)) ∧
    S (k + 1) = (Qt (k + 1))ᵀ * A * Qt (k + 1) ∧ U (k + 1) ∈ orthogonalGroup (Fin r) ℝ ∧
    (U (k + 1))ᵀ * S (k + 1) * U (k + 1) = D (k + 1) ∧ (D (k + 1)).IsDiag ∧
    Q (k + 1) = Qt (k + 1) * U (k + 1)

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§8.3.7.** For a Ritz-accelerated iteration, `‖A Q_k - Q_k D_k‖_F = ‖A Q̃_k - Q̃_k S_k‖_F`,
and this is `min_S ‖A Q̃_k - Q̃_k S‖_F` (Theorem 8.1.14): the columns of `Q_k` are the best basis
from the standpoint of minimizing the residual. -/
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
