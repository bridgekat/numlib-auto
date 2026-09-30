import Numlib.Eigen.QRAlgorithm
import Numlib.Eigen.RayleighQuotientIteration
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section05
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
`FloatingPoint.RoundsTridiagonalizePert` and the book's backward-error bound. The exact semantics
are loop invariants at `Id`: for Algorithm 8.3.1, the cleaned array after step `k` is
`(P₀ ⋯ P_k)ᵀ A (P₀ ⋯ P_k)` for the returned reflector data (the step bridge identifies no
reflector, so this is not read off it); for Algorithm 8.3.2, the bulge chase on a window, the
state being chapter 7's block similarity `blockConj` (`algorithm_8_3_2_window`), and the
implicit-shift principle for the triangularity of `Zᵀ(T - μI)`. Theorems 8.3.1–8.3.2 restate
chapter 7's Krylov-matrix and implicit-Q theorems.

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


/-- An accumulation from `0` over the tail list is a `RoundsDot` on the tail subtype. -/
private theorem roundsDot_tail {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (k : ℕ)
    {x y : Fin n → ℝ} {s : ℝ}
    (h : s ∈ (dotAccum fp.round (Chapter05.indexFrom n (k + 1)) x y 0).run) :
    RoundsDot fp (fun i : {i : Fin n // k + 1 ≤ (i : ℕ)} => x i) (fun i => y i) s :=
  (roundsDot_comp_equiv_iff (tailEquiv k)).2
    (Chapter05.roundsDot_subtype_of_mem_run_dotAccum hfp (Chapter05.nodup_indexFrom _ _) h)


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

/-! ### Algorithm 8.3.1: exact semantics -/

/-- The band of an array is tridiagonal. -/
theorem isTridiagonal_tridiagonalPart (A : Matrix (Fin n) (Fin n) ℝ) :
    (tridiagonalPart A).IsTridiagonal := by
  rintro i j (⟨l, h1, h2⟩ | ⟨l, h1, h2⟩) <;>
  · rw [Fin.lt_def] at h1 h2
    simp only [tridiagonalPart, of_apply]
    exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))

/-- A sum over the members of a duplicate-free list is the sum along the list. -/
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

/-- **The exact step of Algorithm 8.3.1, as a similarity.** With `C = Â_k` symmetric (the cleaned
array), `P = I - β v vᵀ` the reflector of `house` on the tail of column `k` (`v` zero off
`T = [k+1, …, n-1]`, `P x = c e_{k+1}` on `T`), `w = p - (β pᵀv/2) v` with `p = β C v` on `T`,
the trailing block `L = C - v wᵀ - w vᵀ` (lower triangle) and `ν = c`: the cleaned output of the
step is `P C P`. -/
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

/-- **One exact step of Algorithm 8.3.1**: for a symmetric cleaned array `Â_k`, the step returns
reflector data `(v, β)` with `v` zero off `[k+1, …, n-1]` and `β = 0 ∨ β vᵀv = 2`, and the cleaned
output array is `P Â_k P`, `P = I - β v vᵀ`. -/
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



/-- The loop invariant of Algorithm 8.3.1 after `j` steps: the cleaned array is `Qᵀ A Q` for the
product `Q` of the reflector data so far, there are `j` reflectors, the `k`-th vanishing on the
coordinates `≤ k`, and each is the identity or a Householder matrix. -/
private def TridiagonalizeInv (A : Matrix (Fin n) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) : Prop :=
  bandClean j st.1 = (Chapter05.householderProduct st.2)ᵀ * A *
      Chapter05.householderProduct st.2 ∧ st.2.length = j ∧
    (∀ (k : ℕ) (hk : k < st.2.length) (i : Fin n), (i : ℕ) ≤ k → st.2[k].1 i = 0) ∧
    ∀ q ∈ st.2, q.2 = 0 ∨ q.2 * (q.1 ⬝ᵥ q.1) = 2

/-- The loop invariant of Algorithm 8.3.1 holds after every step. -/
private theorem tridiagonalizeInv_run {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    TridiagonalizeInv A (n - 2) (Id.run (algorithm_8_3_1 pure A)) := by
  have hsymm : ∀ Q : Matrix (Fin n) (Fin n) ℝ, (Qᵀ * A * Q).IsSymm := fun Q => by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hA))
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

/-- **Exact semantics of Algorithm 8.3.1.** For symmetric `A` and
`(A', data) := Id.run (algorithm_8_3_1 pure A)`, with
`Q = GolubVanLoan.Chapter05.householderProduct data = P₀ ⋯ P_{n-3}` (`P_k = I - β_k v_k v_kᵀ` from
the **returned** `β_k`): `Q` is orthogonal with `Q e₁ = e₁`, `T := Qᵀ A Q` is symmetric
tridiagonal, and `A'` agrees with `T` on the band (`tridiagonalPart A' = T`; the entries below
the subdiagonal are the untouched `A_k(k+2:n, k)`). There are `n - 2` reflectors and `v_k`
vanishes on the coordinates `≤ k`: `P_k` acts on the coordinates `≥ k + 1`. Loop invariant: after
step `k` the cleaned array is `(P₀ ⋯ P_k)ᵀ A (P₀ ⋯ P_k)`, each step being `P C P` by
`householder_conj_eq_sub_rankTwo` with chapter 5's `houseOn_spec` (`P x = ‖x‖₂ e₁`, which makes
the fresh norm the exact subdiagonal entry). -/
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
  · simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hA))
  · rw [← hband]
    exact isTridiagonal_tridiagonalPart _

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

/-! ### Algorithm 8.3.2: exact semantics -/

section ImplicitQR

open Chapter07 (francisWindow blockConj IsBlockSupported)

/-- **The Hoare rule of a list loop in `Id`**, with the invariant indexed by the step count:
`List.idRun_foldlM_induction` with the step quantified over natural indices. -/
theorem idRun_foldlM_induction {α β : Type} {f : β → α → Id β} (l : List α) (I : ℕ → β → Prop)
    (a : β) (h0 : I 0 a)
    (hs : ∀ (k : ℕ) (hk : k < l.length) (c : β), I k c → I (k + 1) (Id.run (f c l[k]))) :
    I l.length (Id.run (l.foldlM f a)) :=
  List.idRun_foldlM_induction I h0 fun i c hc => hs i i.2 c hc

/-- A Givens rotation in two window indices acts on the window. -/
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
    · simp only [hj, hj', ↓reduceIte, one_apply]

/-- A block similarity of a symmetric matrix is symmetric. -/
private theorem isSymm_blockConj {p m : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsSymm)
    (Z : Matrix (Fin n) (Fin n) ℝ) : (blockConj p m Z X).IsSymm := by
  have hZ : (Zᵀ * X * Z).IsSymm := by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Z (isHermitian_iff_isSymm.2 hX))
  ext i j
  simp only [transpose_apply, Chapter07.blockConj, of_apply]
  by_cases h : (p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
    exact hZ.apply i j
  · rw [ite_eq_right h,
      ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]
    exact hX.apply i j

/-- **The two sweeps of a rotation on a window are a block similarity**: the row update over the
window's columns followed by the column update over the window's rows is `blockConj p m P X` for
any `P` acting on the window (the rotation). -/
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
    fun t q hq => by rw [hP t q (fun h => hq h.2), one_apply]
  have hPo' : ∀ t q : Fin n, ¬ (p ≤ (t : ℕ) ∧ (t : ℕ) < m) → P t q = if t = q then 1 else 0 :=
    fun t q ht => by rw [hP t q (fun h => ht h.1), one_apply]
  -- `Pᵀ X` agrees with `X` on the rows off the window
  have hPX : ∀ r q : Fin n, ¬ (p ≤ (r : ℕ) ∧ (r : ℕ) < m) → (Pᵀ * X) r q = X r q := by
    intro r q hr
    rw [mul_apply, Finset.sum_eq_single r]
    · rw [transpose_apply, hPo' r r hr, ite_eq_left rfl, one_mul]
    · intro t _ htr
      rw [transpose_apply, hPo t r hr, ite_eq_right htr, zero_mul]
    · simp
  ext r q
  simp only [Chapter07.blockConj, of_apply]
  by_cases hr : p ≤ (r : ℕ) ∧ (r : ℕ) < m
  · rw [ite_eq_left hr]
    by_cases hq : p ≤ (q : ℕ) ∧ (q : ℕ) < m
    · rw [ite_eq_left ⟨hr, hq⟩, mul_apply, mul_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [of_apply]
      by_cases ht : p ≤ (t : ℕ) ∧ (t : ℕ) < m
      · rw [ite_eq_left ht]
      · rw [ite_eq_right ht, hPo' t q ht, ite_eq_right (fun e : t = q => ht (e ▸ hq)), mul_zero,
          mul_zero]
    · rw [ite_eq_right
        (fun h : (p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) => hq h.2),
        mul_apply, Finset.sum_eq_single q]
      · rw [of_apply, ite_eq_right hq, hPo q q hq, ite_eq_left rfl, mul_one]
      · intro t _ htq
        rw [hPo t q hq, ite_eq_right htq, mul_zero]
      · simp
  · rw [ite_eq_right hr,
      ite_eq_right (fun h : (p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) => hr h.1)]
    split_ifs
    · exact hPX r q hr
    · rfl

/-- **One rotation of Algorithm 8.3.2 on a window, exactly**: with `(c, s) = givens(x, z)` for
`(x, z)` the first pair `(x₀, z₀)` or the entries `(t_{a,prev}, t_{b,prev})`, the new state is the
block similarity by `G(a, b, θ)` and the accumulator times `G(a, b, θ)`. -/
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

/-- **The zero pattern of the bulge chase** on the window `[p, m)` after `j` rotations: the block
is symmetric-tridiagonal below the diagonal except for the bulge at `(p + j + 1, p + j - 1)`
(none for `j = 0`). -/
private def IsChased (p m j : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i l : Fin n, p ≤ (l : ℕ) → (i : ℕ) < m → (l : ℕ) + 2 ≤ i →
    ¬ (1 ≤ j ∧ (i : ℕ) = p + j + 1 ∧ (l : ℕ) + 1 = p + j) → X i l = 0

/-- **One bulge-chasing rotation** (§8.3.5): if the block of a symmetric `X` has the zero pattern
after `j` rotations and the rotation `G(a, b, θ)`, `a = p + j`, `b = a + 1`, annihilates the
bulge (`s x_{a,a-1} + c x_{b,a-1} = 0`, vacuous for `j = 0`), the block similarity has the zero
pattern after `j + 1` rotations: the bulge moves one step down. -/
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

/-- A rotation in two indices other than `q` fixes `e_q`. -/
theorem givensRotation_mulVec_single_of_ne {a b q : Fin n} (hab : a ≠ b) (hqa : q ≠ a)
    (hqb : q ≠ b) (c s : ℝ) :
    Chapter05.givensRotation a b c s *ᵥ Pi.single q 1 = Pi.single q 1 := by
  funext t
  rw [mulVec_single_one, col_apply, Chapter05.givensRotation, planeRotation_apply hab]
  simp only [hqa, hqb, ↓reduceIte, Pi.single_apply]

/-- The loop invariant of Algorithm 8.3.2 on the window `[p, m)` after `j` rotations: the state
`(X, Q', prev)` is `(blockConj p m Z T, Q Z, a_{j-1})` for an orthogonal `Z` acting on the
window, `X` is symmetric with the zero pattern of the chase, and for `j ≥ 1` the first column
`Z e_p` is that of the first rotation `G(p, p+1, θ₀)`, `(c₀, s₀) = givens(x₀, z₀)`. -/
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

/-- **The bulge chase of Algorithm 8.3.2 on a window**, the loop: the invariant `ChaseInv` holds
after the `m - p - 1` rotations. -/
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
  refine idRun_foldlM_induction _ _ _ ⟨1, one_mem _, Chapter07.isBlockSupported_one p m, ?_,
    (Matrix.mul_one Q).symm, hTs, isChased_zero_of_isTridiagonal hT, rfl, fun _ => rfl,
    fun h => absurd h (by omega)⟩ ?_
  · ext i j
    simp [Chapter07.blockConj]
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


/-- The exact Wilkinson shift of Algorithm 8.3.2 is the book's closed form
`a - b² / (d + sign(d) √(d² + b²))`. -/
theorem wilkinsonShiftComputed_pure (a' a b : ℝ) :
    Id.run (wilkinsonShiftComputed pure a' a b) =
      a - b ^ 2 / ((a' - a) / 2 + (if 0 ≤ (a' - a) / 2 then 1 else -1) *
        √(((a' - a) / 2) ^ 2 + b ^ 2)) := by
  change a - b * b / ((a' - a) / 2 + (if 0 ≤ (a' - a) / 2 then √((a' - a) / 2 * ((a' - a) / 2) +
    b * b) else -√((a' - a) / 2 * ((a' - a) / 2) + b * b))) = _
  split_ifs <;> ring_nf

/-- A block similarity of a tridiagonal matrix whose block is tridiagonal below the diagonal and
which is symmetric is tridiagonal. -/
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

/-- **Algorithm 8.3.2 on a window** (what Algorithm 8.3.3 runs on its unreduced block `D₂₂`): for a
symmetric tridiagonal `T` and a window `[p, m)` of at least two indices, the exact run
`(T', Q')` has an orthogonal `Z` acting on the window only (the product of the `m - p - 1`
rotations) with `T' = blockConj p m Z T` (`Zᵀ T Z` on the block, `T` elsewhere), `Q' = Q Z`, `T'`
symmetric tridiagonal, and `Z e_p = G(p, p+1, θ₀) e_p` for the first rotation, `(c₀, s₀)` the
Givens pair of `(t_pp - μ, t_{p+1,p})` (`s₀ (t_pp - μ) + c₀ t_{p+1,p} = 0`), `μ` the exact Wilkinson
shift of the block's trailing `2 × 2` block. The proof is the bulge-chasing invariant: after `j`
rotations the block is tridiagonal but for one bulge at `(p + j + 1, p + j - 1)` (§8.3.5,
`bulgeChase_step`), which the last rotation pushes out of the block. -/
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

/-- The first column of a Givens rotation `G(0, 1, θ)`: `c e₀ - s e₁`. -/
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

/-- **Exact semantics of Algorithm 8.3.2** ("Given an unreduced symmetric tridiagonal matrix `T`,
the following algorithm overwrites `T` with `ZᵀTZ`, where `Z = G₁ ⋯ G_{n-1}` is a product of
Givens rotations with the property that `Zᵀ(T - μI)` is upper triangular and `μ` is that
eigenvalue of `T`'s trailing 2-by-2 principal submatrix closer to `t_nn`"): for an unreduced
symmetric tridiagonal `T` of order `n = N + 2`, any `Q`, and
`(T', Q') := Id.run (algorithm_8_3_2 pure (List.finRange n) T Q)`, with `μ = wilkinsonShift T`
(8.3.3): there is an orthogonal `Z` (the product of the `n - 1` rotations) with `T' = Zᵀ T Z`,
`Q' = Q Z`, `T'` symmetric tridiagonal, `Z e₁` parallel to `(T - μ I) e₁` (the book's
`Z e₁ = U e₁`) and `Zᵀ (T - μ I)` upper triangular. Consequently, when `T - μ I` is nonsingular,
`T' = D (Matrix.shiftedQrStep μ T) D` for a diagonal `D` with entries `±1`: the implicit step is
the explicit one (8.3.2) up to signs. The triangularity is the implicit-shift principle
`Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval` (behind Theorem 8.3.2), the
signs `Matrix.IsShiftedQrStep.unique_of_isUnit`. -/
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
    rw [col_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply]
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

/-- The test of the deflation of Algorithm 8.3.3 at the coupling `a`, exactly:
`|d_{a+1,a}| ≤ tol (|d_aa| + |d_{a+1,a+1}|)`. -/
def IsSmallCoupling (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (a : ℕ) : Prop :=
  ∃ h : a + 1 < n, |D ⟨a + 1, h⟩ ⟨a, by omega⟩| ≤
    tol * (|D ⟨a, by omega⟩ ⟨a, by omega⟩| + |D ⟨a + 1, h⟩ ⟨a + 1, h⟩|)

/-- `(r, s)` is one of the two entries of a small coupling `a < k`. -/
def IsDeflatedPair (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (r s : Fin n) : Prop :=
  ∃ a : ℕ, a < k ∧ ((r : ℕ) = a + 1 ∧ (s : ℕ) = a ∨ (r : ℕ) = a ∧ (s : ℕ) = a + 1) ∧
    IsSmallCoupling tol D a

open Classical in
/-- The array after the first `k` tests of the deflation pass of Algorithm 8.3.3, exactly: the
small couplings among the first `k` set to `0`. -/
noncomputable def deflateStage (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  of fun r s => if IsDeflatedPair tol D k r s then 0 else D r s

/-- The exact result of the deflation pass of Algorithm 8.3.3: every small coupling set to `0`. -/
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

/-- **The deflation pass of Algorithm 8.3.3, exactly**: every test reads entries no earlier step
has changed, so the pass zeroes exactly the small couplings of its input. -/
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

/-- The deflation keeps the entries off the first sub- and superdiagonals. -/
theorem deflated_apply_of_not {tol : ℝ} {D : Matrix (Fin n) (Fin n) ℝ} {r s : Fin n}
    (h : ¬ ((r : ℕ) = s + 1 ∨ (s : ℕ) = r + 1)) : deflated tol D r s = D r s := by
  rw [deflated, deflateStage, of_apply, ite_eq_right (not_isDeflatedPair_of h)]

open Classical in
/-- The deflation sets the small couplings, and only those, to `0`. -/
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

/-- **The window of the unreduced block** (`lastRunWindow`): empty when no coupling is nonzero,
and otherwise the window `[p, e + 2)` of a maximal run `p, …, e` of nonzero couplings, preceded by
a zero coupling (or `p = 0`) and followed only by zero couplings. -/
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

/-- The part of `D` on the coupling `a`: the entries `(a + 1, a)` and `(a, a + 1)`. -/
private def couplingPart (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  of fun r s => if (r : ℕ) = a + 1 ∧ s = a ∨ r = a ∧ (s : ℕ) = a + 1 then D r s else 0

private theorem norm_toLp_single_one' (c : Fin n) :
    ‖(WithLp.toLp 2 (Pi.single c (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have h : ‖(WithLp.toLp 2 (Pi.single c (1 : ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 ^ 2 := by
    rw [← dotProduct_self_eq_norm_sq]
    simp
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h

/-- The coupling part of a symmetric matrix has norm at most `2 |d_{a+1,a}|`. -/
private theorem norm_couplingPart_le {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsSymm) (a : Fin n)
    (h : (a : ℕ) + 1 < n) : ‖couplingPart D a‖ ≤ 2 * |D ⟨a + 1, h⟩ a| := by
  set b : Fin n := ⟨a + 1, h⟩ with hb
  have hba : b ≠ a := fun e => by rw [Fin.ext_iff] at e; simp [b] at e
  have e : couplingPart D a = D b a • (vecMulVec (Pi.single b 1) (Pi.single a 1) +
      vecMulVec (Pi.single a 1) (Pi.single b 1)) := by
    ext r s
    have hr : (r : ℕ) = a + 1 ↔ r = b := by simp [b, Fin.ext_iff]
    have hs : (s : ℕ) = a + 1 ↔ s = b := by simp [b, Fin.ext_iff]
    simp only [couplingPart, of_apply, hr, hs, Matrix.smul_apply, Matrix.add_apply,
      vecMulVec_apply, Pi.single_apply, smul_eq_mul]
    by_cases h1 : r = b ∧ s = a
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hba]
    · by_cases h2 : r = a ∧ s = b
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hba, Ne.symm hba, hD.apply]
      · rw [ite_eq_right (not_or.2 ⟨h1, h2⟩)]
        have p1 : (if r = b then (1 : ℝ) else 0) * (if s = a then 1 else 0) = 0 := by
          by_cases hrb : r = b
          · rw [ite_eq_right (fun h' => h1 ⟨hrb, h'⟩), mul_zero]
          · rw [ite_eq_right hrb, zero_mul]
        have p2 : (if r = a then (1 : ℝ) else 0) * (if s = b then 1 else 0) = 0 := by
          by_cases hra : r = a
          · rw [ite_eq_right (fun h' => h2 ⟨hra, h'⟩), mul_zero]
          · rw [ite_eq_right hra, zero_mul]
        rw [p1, p2, add_zero, mul_zero]
  rw [e, norm_smul, Real.norm_eq_abs]
  have e1 := frobenius_norm_vecMulVec_le (Pi.single b (1 : ℝ)) (Pi.single a 1)
  have e2 := frobenius_norm_vecMulVec_le (Pi.single a (1 : ℝ)) (Pi.single b 1)
  rw [norm_toLp_single_one', norm_toLp_single_one', mul_one] at e1 e2
  have := norm_add_le (vecMulVec (Pi.single b (1 : ℝ)) (Pi.single a 1))
    (vecMulVec (Pi.single a (1 : ℝ)) (Pi.single b 1))
  have := abs_nonneg (D b a)
  nlinarith

open Classical in
/-- The couplings the deflation of Algorithm 8.3.3 newly sets to zero. -/
private noncomputable def newZeros (tol : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun a => IsSmallCoupling tol D a ∧ ∃ h : (a : ℕ) + 1 < n, D ⟨a + 1, h⟩ a ≠ 0

open Classical in
/-- The zero couplings `d_{a+1,a} = 0` of `D`. -/
private noncomputable def zeroCouplings (D : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ h : (a : ℕ) + 1 < n, D ⟨a + 1, h⟩ a = 0

/-- There are at most `n - 1` couplings. -/
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

/-- The deflation removes the coupling parts of the new zeros. -/
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

/-- **The deflation perturbation**: `‖D - deflated D‖_F ≤ 4 tol ‖D‖_F` per new zero. -/
private theorem norm_sub_deflated_le {tol : ℝ} (htol : 0 ≤ tol) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D.IsSymm) :
    ‖D - deflated tol D‖ ≤ (newZeros tol D).card * (4 * tol * ‖D‖) := by
  rw [sub_deflated_eq_sum hD]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun a ha => ?_
  simp only [newZeros, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨⟨h, hsm⟩, -⟩ := ha
  refine (norm_couplingPart_le hD a h).trans ?_
  have h1 := abs_apply_le_frobenius_norm D a a
  have h2 := abs_apply_le_frobenius_norm D ⟨a + 1, h⟩ ⟨a + 1, h⟩
  have hsm' : |D ⟨a + 1, h⟩ a| ≤ tol * (|D a a| + |D ⟨a + 1, h⟩ ⟨a + 1, h⟩|) := hsm
  nlinarith

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

/-- The loop invariant of Algorithm 8.3.3 on the state `(D, Q, done)`: `Q` is orthogonal, `D` is
symmetric tridiagonal, `Qᵀ (A + F) Q = D` for a symmetric `F` (the deflations so far, carried
back), of norm at most `κ` per zero coupling of `D` (when `κ` is large enough), and `D` is
diagonal once `done`. -/
private def SymmetricQRInv (A : Matrix (Fin n) (Fin n) ℝ) (tol κ : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) : Prop :=
  st.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ st.1.IsSymm ∧ st.1.IsTridiagonal ∧
    (∃ F : Matrix (Fin n) (Fin n) ℝ, Fᵀ = F ∧ st.2.1ᵀ * (A + F) * st.2.1 = st.1 ∧
      (4 * tol * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F‖ ≤ κ * (zeroCouplings st.1).card)) ∧
    (st.2.2 = true → ∀ i j, i ≠ j → st.1 i j = 0)

/-- **One pass of Algorithm 8.3.3 keeps the invariant.** -/
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
  have hF₁n : 4 * tol * (‖A‖ + κ * (n - 1 : ℕ)) ≤ κ → ‖F₁‖ ≤ κ * (zeroCouplings D₁).card := by
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
      _ ≤ κ * (zeroCouplings D).card + (newZeros tol D).card * (4 * tol * ‖D‖) := by
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

/-- **Exact semantics of Algorithm 8.3.3** (the symmetric QR algorithm, "an approximate symmetric
Schur decomposition `QᵀAQ = D`"): for symmetric `A`, `0 ≤ tol` and any `fuel`, the exact run
`(D, Q, done)` has `Q` orthogonal, `D` symmetric tridiagonal, and `D = Qᵀ (A + E) Q` for a
symmetric `E` (the deflations `d_{i+1,i} := 0`, carried back to `A`), with
`‖E‖_F ≤ c tol ‖A‖_F / (1 - c tol)` for `c = 4 (n - 1)` whenever `c tol < 1`; and if the loop
stopped on its test (`done`, `q = n`) within the fuel, `D` is diagonal. Each deflation zeroes a
coupling `|d_{i+1,i}| ≤ tol (|d_ii| + |d_{i+1,i+1}|)` of the current `D`, of Frobenius norm
`≤ 4 tol ‖D‖_F ≤ 4 tol (‖A‖_F + ‖E‖_F)`, and a zeroed coupling stays zero, so there are at most
`n - 1` of them. The forward form `QᵀAQ = D + E` with `E` supported on the deflated positions is
false: a later rotation on a window `[p, …]` mixes a deflated entry at `(p, p - 1)` into
`(p + 1, p - 1)`. Convergence (that some finite fuel suffices) is Wilkinson's theorem and is not
claimed. -/
theorem algorithm_8_3_3_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {tol : ℝ}
    (htol : 0 ≤ tol) (fuel : ℕ) :
    let out := Id.run (algorithm_8_3_3 pure tol A fuel)
    out.2.1 ∈ orthogonalGroup (Fin n) ℝ ∧ out.1.IsSymm ∧ out.1.IsTridiagonal ∧
      (∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ out.2.1ᵀ * (A + E) * out.2.1 = out.1 ∧
        (4 * ((n - 1 : ℕ) : ℝ) * tol < 1 →
          ‖E‖ ≤ 4 * ((n - 1 : ℕ) : ℝ) * tol * ‖A‖ / (1 - 4 * ((n - 1 : ℕ) : ℝ) * tol))) ∧
      (out.2.2 = true → ∀ i j, i ≠ j → out.1 i j = 0) := by
  intro out
  set c : ℝ := 4 * ((n - 1 : ℕ) : ℝ) * tol with hc
  set κ : ℝ := if c < 1 then 4 * tol * ‖A‖ / (1 - c) else 0 with hκdef
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
  have hκ : κ = 4 * tol * ‖A‖ / (1 - c) := by rw [hκdef, ite_eq_left hc1]
  have h1c : 0 < 1 - c := by linarith
  have hκeq : 4 * tol * (‖A‖ + κ * (n - 1 : ℕ)) = κ := by
    rw [hκ]
    field_simp
    rw [hc]
    ring
  have hF' := hFn hκeq.le
  have hz := card_zeroCouplings_le out.1
  calc ‖F‖ ≤ κ * (zeroCouplings out.1).card := hF'
    _ ≤ κ * (n - 1 : ℕ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hz) hκ0
    _ = c * ‖A‖ / (1 - c) := by rw [hκ, hc]; field_simp
    _ = _ := by rw [hc]

end Frobenius

end SymmetricQR

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
