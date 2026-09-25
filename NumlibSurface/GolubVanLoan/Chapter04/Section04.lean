import Mathlib.Algebra.Order.Star.Real
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Matrix.SymmetricIndefinite
import NumlibSurface.GolubVanLoan.Chapter04.Section02

/-!
# Golub–Van Loan §4.4: symmetric indefinite systems

Surface file for [golub2013matrix] §4.4: the Aasen factorization `P A Pᵀ = L T Lᵀ` (4.4.1) and the
block `L D Lᵀ` factorization of the diagonal pivoting methods (4.4.2), with their solve chains; the
Parlett–Reid update at the heart of (4.4.3); the Hessenberg relation (4.4.5) behind Aasen's
method, and Aasen's method without pivoting (4.4.14) as a program (`aasenNoPivot`) with its exact
specification; the pivot step (4.4.15) of Bunch and Parlett and the true multiplier bound of
their pivot strategy; the equilibrium systems of §4.4.5 ((4.4.18), the Cholesky-based
factorization, (4.4.20)). The section has no numbered theorem and no numbered algorithm.

## Conventions

Real symmetric `A : Matrix (Fin n) (Fin n) ℝ`, 0-based. A permutation `P` is a
`σ : Equiv.Perm (Fin n)` acting as `A.submatrix σ σ = P A Pᵀ`. The factorizations are the backbone
specifications `Matrix.IsAasen A L T` (`A = L T Lᵀ`, `L` unit lower triangular with first column
`e₁`, `T` symmetric tridiagonal) and `Matrix.IsBlockLDL A L D` (`A = L D Lᵀ`, `D` a direct sum of
`1 × 1` and `2 × 2` pivot blocks). The equilibrium matrix `[C B; Bᵀ 0]` is the backbone's
`Matrix.saddleMatrix C B 0 = fromBlocks C B Bᴴ 0`, which over `ℝ` is `fromBlocks C B Bᵀ 0`.

Aasen's method (4.4.14) is the book's only form of the method, a display rather than a numbered
algorithm, so it is a content-named program whose exact specification carries the display's
number (`equation_4_4_14`). It follows the algorithm conventions of `NumlibSurface/GolubVanLoan`:
every product, sum, difference and quotient passes through the rounding hook, the inner products
`L(j, 1:j−1) · h(1:j−1)` are running differences from the entry of `A`, and the state holds the
arrays `α`, `β`, `L` of the book, `ℕ`-indexed. The exact specification is read off the run in
the exact model through a loop invariant: after step `j`, the columns `≤ j` satisfy the
recurrences (4.4.10)–(4.4.13), which is what `A = L H`, `H = T Lᵀ`, asks of them.

## Sources

Backbone `Numlib/LinearAlgebra/Matrix/SymmetricIndefinite` (the specifications, their existence
theorems, the Bunch–Parlett multiplier bound, the solve chains) and
`Numlib/LinearAlgebra/Matrix/SchurComplement` (the block factorization and the saddle-point
matrix), chapter 4's §4.2 surface for the Cholesky factor. The derivation steps (4.4.3)–(4.4.4),
(4.4.6)–(4.4.13) (the content of `equation_4_4_14`), the Bunch–Kaufman strategy and
the stability claims of §4.4.4 are not formalized; the growth bounds (4.4.16)–(4.4.17), the
parameter `α = (1 + √17)/8` and (4.4.21) wait on the backbone module
`Numlib/Direct/SymmetricIndefinite`.

## Readings and errata

(4.4.2) states that `P` "is chosen so that the entries in the unit lower triangular `L` satisfy
`|ℓ_ij| ≤ 1`"; this is false for the Bunch–Parlett strategy the section describes (at
`α = (1 + √17)/8`, `A = [1 3/2; 3/2 0]` takes a `1 × 1` pivot with multiplier `3/2`). The true
bound is `max(1/α, 1/(1 − α))` (`equation_4_4_2_multipliers`). (4.4.20) is stated for a diagonal
`C`; the diagonality is not needed. In (4.4.9) the vector `[0; ℓ₅₂; ℓ₅₃; ℓ₅₃; ℓ₅₄]` should read
`[0; ℓ₅₂; ℓ₅₃; ℓ₅₄; 1]`, and (4.4.10) loops from `k = 1`, which needs an undefined `β₀`; the program
follows (4.4.14), whose loop starts at `k = 2`. The symmetric pivot block `E` of (4.4.15) need
not be symmetric for the displayed factorization.
-/

open FloatingPoint Finset Matrix

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### (4.4.1)–(4.4.2) and their solve chains -/

/-- **(4.4.1).** Aasen's factorization "`P A Pᵀ = L T Lᵀ` where `L = (ℓ_ij)` is unit lower
triangular and `T` is tridiagonal. `P` is a permutation chosen such that `|ℓ_ij| ≤ 1`": every
symmetric `A` has such a factorization, with `L(:, 1) = e₁` and `T` symmetric. -/
theorem equation_4_4_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L T : Matrix (Fin n) (Fin n) ℝ),
      IsAasen (A.submatrix σ σ) L T ∧ ∀ i j, |L i j| ≤ 1 :=
  exists_perm_isAasen hA

/-- **(4.4.2).** The diagonal pivoting method "computes a permutation `P` such that
`P A Pᵀ = L D Lᵀ` where `D` is a direct sum of 1-by-1 and 2-by-2 pivot blocks": every symmetric
`A` has such a factorization with `L` unit lower triangular. (The book's claim that `P` can be
chosen with `|ℓ_ij| ≤ 1` is false for its pivot strategy; see `equation_4_4_2_multipliers`.) -/
theorem equation_4_4_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) ℝ),
      IsBlockLDL (A.submatrix σ σ) L D :=
  exists_perm_isBlockLDL hA

/-- **(4.4.2), the multiplier clause in its true form.** With the Bunch–Parlett pivot strategy of
§4.4.3 at a parameter `α ∈ (0, 1)`, the factorization (4.4.2) can be chosen with
`|ℓ_ij| ≤ max(1/α, 1/(1 − α))`: a `1 × 1` pivot has `|e| ≥ α μ₀`, so its multipliers are at most
`1/α`, and a `2 × 2` pivot has `|det E| ≥ (1 − α²) μ₀²`, so its multipliers are at most
`1/(1 − α)`. (At the book's `α = (1 + √17)/8` the bound is about `2.78`, not the printed `1`.) -/
theorem equation_4_4_2_multipliers {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (σ : Equiv.Perm (Fin n)) (L D : Matrix (Fin n) (Fin n) ℝ),
      IsBlockLDL (A.submatrix σ σ) L D ∧ ∀ i j, |L i j| ≤ max α⁻¹ (1 - α)⁻¹ :=
  exists_perm_isBlockLDL_abs_le hA hα0 hα1

/-- **§4.4, the solve chain of (4.4.1).** "`P A Pᵀ = L T Lᵀ`, `L z = P b`, `T w = z`, `Lᵀ y = w`,
`x = Pᵀ y` ⇒ `A x = b`" (`P b = b ∘ σ`, `Pᵀ y = y ∘ σ⁻¹`). -/
theorem aasen_solve {A L T : Matrix (Fin n) (Fin n) ℝ} {σ : Equiv.Perm (Fin n)}
    (h : IsAasen (A.submatrix σ σ) L T) {b z w y : Fin n → ℝ} (hz : L *ᵥ z = b ∘ σ)
    (hw : T *ᵥ w = z) (hy : Lᵀ *ᵥ y = w) : A *ᵥ (y ∘ σ.symm) = b :=
  h.solve hz hw hy

/-- **§4.4, the solve chain of (4.4.2).** "`P A Pᵀ = L D Lᵀ`, `L z = P b`, `D w = z`, `Lᵀ y = w`,
`x = Pᵀ y` ⇒ `A x = b`". -/
theorem blockLDL_solve {A L D : Matrix (Fin n) (Fin n) ℝ} {σ : Equiv.Perm (Fin n)}
    (h : IsBlockLDL (A.submatrix σ σ) L D) {b z w y : Fin n → ℝ} (hz : L *ᵥ z = b ∘ σ)
    (hw : D *ᵥ w = z) (hy : Lᵀ *ᵥ y = w) : A *ᵥ (y ∘ σ.symm) = b :=
  h.solve hz hw hy

/-! ### §4.4.1 The Parlett–Reid algorithm -/

/-- **§4.4.1, the update at the heart of (4.4.3).** "Suppose `B = Bᵀ` and that we wish to form
`B₊ = (I − w e₁ᵀ) B (I − w e₁ᵀ)ᵀ` … If we set `u = B e₁ − (b₁₁/2) w` then
`B₊ = B − w uᵀ − u wᵀ`." Here `e₁` is `Pi.single 0 1` on `Fin (m + 1)`. -/
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

/-- **(4.4.5).** If `A = L T Lᵀ` is an Aasen factorization (no pivoting), then `H = T Lᵀ` is upper
Hessenberg and `A = L H`, so that `A(:, j) = L H(:, j) = ∑_{k ≤ j+1} L(:, k) h_k` — the relation
from which Aasen's method computes `L` column by column. -/
theorem equation_4_4_5 {A L T : Matrix (Fin n) (Fin n) ℝ} (h : IsAasen A L T) :
    (T * Lᵀ).IsUpperHessenberg ∧ A = L * (T * Lᵀ) :=
  h.isUpperHessenberg_mul_transpose

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The column `h(1:j)` of `H = T Lᵀ` in step `j` of Aasen's method (4.4.14), 0-based: from the
state `(α, β, L)`, `h₀ = β₀ ℓ_{j1}`, `h_k = β_{k−1} ℓ_{j,k−1} + α_k ℓ_{jk} + β_k ℓ_{j,k+1}` for
`0 < k < j` ((4.4.10)), and `h_j = a_jj − L(j, 0:j−1) · h(0:j−1)` ((4.4.11)) as a running
difference. -/
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

/-- Step `j` of Aasen's method (4.4.14) up to the new column of `L`: the diagonal entry `α_j` and
the vector `v(j+1:n)` ((4.4.7), a running difference from `A(i, j)`); at `j = 0` the book's
`α₁ = a₁₁`, `v(2:n) = A(2:n, 1)`. -/
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

/-- **(4.4.14), Aasen's method without pivoting**, in the book's operation order (0-based):
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
The state `(α, β, L)` holds the diagonal and subdiagonal of `T` and the unit lower triangular
`L` as `ℕ`-indexed arrays (entries outside `0 ≤ i, k < n` are never read); `h(1:j)` is
`aasenH`, `α_j` and `v` are `aasenColumn`. Every product, sum, difference and quotient is
rounded; the copies `α₁ = a₁₁`, `v = A(:, 1)`, `β_j = v(j+1)` are exact. -/
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

/-! #### Exact semantics of (4.4.14) -/

/-- A loop of updates in which every step reads only entries that earlier steps do not write. -/
private theorem foldl_update_eq {ι κ β : Type*} [DecidableEq κ] (w : ι → κ)
    (h : ι → (κ → β) → β) (l : List ι)
    (hl : l.Pairwise fun a b => w a ≠ w b ∧
      ∀ g g' : κ → β, (∀ t, t ≠ w a → g t = g' t) → h b g = h b g') (f : κ → β) :
    (∀ i ∈ l, l.foldl (fun g i => Function.update g (w i) (h i g)) f (w i) = h i f) ∧
      ∀ t, (∀ i ∈ l, w i ≠ t) →
        l.foldl (fun g i => Function.update g (w i) (h i g)) f t = f t := by
  induction l generalizing f with
  | nil => exact ⟨fun _ hi => absurd hi List.not_mem_nil, fun _ _ => rfl⟩
  | cons a l ih =>
    obtain ⟨hal, hl'⟩ := List.pairwise_cons.1 hl
    obtain ⟨ih1, ih2⟩ := ih hl' (Function.update f (w a) (h a f))
    have hagree : ∀ t, t ≠ w a → Function.update f (w a) (h a f) t = f t :=
      fun t ht => Function.update_of_ne ht _ _
    refine ⟨fun i hi => ?_, fun t ht => ?_⟩
    · rw [List.foldl_cons]
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [ih2 (w i) fun j hj => (hal j hj).1.symm, Function.update_self]
      · rw [ih1 i hi]
        exact (hal i hi).2 _ _ hagree
    · rw [List.foldl_cons, ih2 t fun j hj => ht j (List.mem_cons_of_mem _ hj)]
      exact hagree t (ht a List.mem_cons_self).symm

/-- A running difference in exact arithmetic. -/
private theorem foldl_sub_eq {ι : Type*} (g : ι → ℝ) (l : List ι) (c : ℝ) :
    l.foldl (fun t k => t - g k) c = c - (l.map g).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

/-- The Aasen state: diagonal, subdiagonal and the lower factor, `ℕ`-indexed. -/
private abbrev St := (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℕ → ℝ)

/-- The entries `h_k = H(k, j)`, `k < j`, from the state (the book's (4.4.10), exact). -/
private def hval (s : St) (j k : ℕ) : ℝ :=
  if k = 0 then s.2.1 0 * s.2.2 j 1 else
    s.2.1 (k - 1) * s.2.2 j (k - 1) + s.1 k * s.2.2 j k + s.2.1 k * s.2.2 j (k + 1)

/-- The diagonal entry `h_j` of (4.4.11), exact. -/
private def hdiag (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : ℝ :=
  A j j - ∑ k ∈ Finset.range j, s.2.2 j k * hval s j k

/-- The column `h(0:j)` of `H = T Lᵀ`. -/
private def hfull (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : ℕ → ℝ :=
  Function.update (hval s j) j (hdiag A s j)

/-- The vector `v` of (4.4.7), exact. -/
private def vval (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j i : Fin n) : ℝ :=
  if (j : ℕ) = 0 then A i j else
    A i j - ∑ k ∈ Finset.range (j + 1), s.2.2 i k * hfull A s j k

/-- The diagonal entry `α_j` of (4.4.12), exact. -/
private def αval (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then A j j else hdiag A s j - s.2.1 (j - 1) * s.2.2 j (j - 1)

/-- Column `j` of the state is a finished column of Aasen's method. -/
private def ColDone (A : Matrix (Fin n) (Fin n) ℝ) (s : St) (j : Fin n) : Prop :=
  s.1 j = αval A s j ∧
    (∀ h : (j : ℕ) + 1 < n, s.2.1 j = vval A s j ⟨j + 1, h⟩) ∧
    ∀ (h : (j : ℕ) + 1 < n) (i : Fin n), (j : ℕ) + 2 ≤ i →
      s.2.2 i (j + 1) = vval A s j i / vval A s j ⟨j + 1, h⟩

/-- Two states agree on everything a column `≤ m` formula reads. -/
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

/-- A finished column stays finished under agreement on it. -/
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

/-- The loop invariant after `c` columns. -/
private def Inv (A : Matrix (Fin n) (Fin n) ℝ) (c : ℕ) (s : St) : Prop :=
  (∀ r k, r ≤ k → s.2.2 r k = if r = k then 1 else 0) ∧
    (∀ r k, (k = 0 ∨ c < k) → s.2.2 r k = if r = k then 1 else 0) ∧
    ∀ j : Fin n, (j : ℕ) < c → ColDone A s j


/-- A list sum over `List.range` is the `Finset` sum. -/
private theorem list_sum_range (g : ℕ → ℝ) (j : ℕ) :
    ((List.range j).map g).sum = ∑ k ∈ Finset.range j, g k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A loop writing entry `k` from a value that does not depend on the state. -/
private theorem foldl_update_const (F : ℕ → ℝ) (l : List ℕ) (hl : l.Nodup) (g : ℕ → ℝ) {k : ℕ}
    (hk : k ∈ l) : l.foldl (fun h k => Function.update h k (F k)) g k = F k :=
  (foldl_update_eq (fun k : ℕ => k) (fun k _ => F k) l
    (hl.imp fun hab => ⟨hab, fun _ _ _ => rfl⟩) g).1 k hk

/-- The exact column `h(0:j)`. -/
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
  · rw [Function.update_self, hfull, Function.update_self, foldl_sub_eq, list_sum_range, hdiag]
    congr 1
    exact Finset.sum_congr rfl fun k' hk' => by rw [hF k' (Finset.mem_range.1 hk')]
  · rw [Function.update_of_ne (ne_of_lt hk), hfull, Function.update_of_ne (ne_of_lt hk), hF k hk]

/-- The exact column step: `α_j` and `v`. -/
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
    · have := (foldl_update_eq (fun i : Fin n => (i : ℕ)) (fun i _ =>
          List.foldl (fun t k => t - s.2.2 i k * h k) (A i j) (List.range (j + 1)))
          ((List.finRange n).filter (j < ·))
          (((List.nodup_finRange n).filter _).imp fun hab =>
            ⟨fun e => hab (Fin.ext e), fun _ _ _ => rfl⟩) 0).1 i (by simpa using hi)
      dsimp only
      rw [this, vval, ite_eq_right hj0, foldl_sub_eq, list_sum_range]
      congr 1
      exact Finset.sum_congr rfl fun k hk => by
        rw [hH k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]


/-- The exact run of Aasen's method is one of its runs in the exact model. -/
private theorem aasenNoPivot_mem_exact (A : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (aasenNoPivot pure A) ∈ (aasenNoPivot (RoundingModel.exact ℝ).round A).run := by
  rw [RoundingModel.round_exact]
  simp only [aasenNoPivot, aasenColumn, aasenH, pure_bind, ite_pure, List.foldlM_pure,
    SetM.mem_run_pure]
  rfl

/-- The exact run of Aasen's method keeps the invariant. -/
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
  have hL := foldl_update_eq (fun i : Fin n => (i : ℕ))
    (fun i (L : ℕ → ℕ → ℝ) => Function.update (L i) (j + 1) (r.2 i / r.2 (j + 1)))
    ((List.finRange n).filter (fun i : Fin n => (j : ℕ) + 2 ≤ i))
    (((List.nodup_finRange n).filter _).imp fun hab =>
      ⟨fun e => hab (Fin.ext e), fun g g' hg => by rw [hg _ (Ne.symm fun e => hab (Fin.ext e))]⟩)
    s.2.2
  set L' := List.foldl (fun (L : ℕ → ℕ → ℝ) (i : Fin n) =>
    Function.update L i (Function.update (L i) (j + 1) (r.2 i / r.2 (j + 1)))) s.2.2
    ((List.finRange n).filter (fun i : Fin n => (j : ℕ) + 2 ≤ i)) with hL'
  have hLnew : ∀ (i : Fin n), (j : ℕ) + 2 ≤ i → L' i (j + 1) = r.2 i / r.2 (j + 1) := by
    intro i hi
    rw [hL.1 i (by simpa using hi), Function.update_self]
  have hLold : ∀ (a c : ℕ), (c ≠ (j : ℕ) + 1 ∨ a < (j : ℕ) + 2) → L' a c = s.2.2 a c := by
    intro a c hc
    by_cases ha : ∃ i ∈ (List.finRange n).filter (fun i : Fin n => (j : ℕ) + 2 ≤ i),
        (i : ℕ) = a
    · obtain ⟨i, hi, rfl⟩ := ha
      have hi' : (j : ℕ) + 2 ≤ i := by simpa using hi
      rw [hL.1 i hi, Function.update_of_ne (by omega)]
    · push Not at ha
      rw [hL.2 a ha]
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

/-- **(4.4.14) computes Aasen's factorization.** "Combining these equations … we obtain the Aasen
method without pivoting": for symmetric `A` (of order `N + 1`), if every `v(j+1)` used as a divisor
is nonzero — these are the returned `β_j`, `j + 2 ≤ N` — then the exact run of `aasenNoPivot`
returns `L` and `T = tridiag(β, α, β)` with `A = L T Lᵀ`, `L` unit lower triangular and
`L(:, 1) = e₁`. The invariant of the loop is the book's derivation (4.4.5)–(4.4.13): the columns
`≤ j` of `A = L H`, `H = T Lᵀ` upper Hessenberg, hold with `h(1:j)` the column `j` of `H`. -/
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
    rw [Matrix.mul_assoc, mul_apply]
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

/-- **(4.4.15) with the displayed factorization.** "Suppose `P₁ A P₁ᵀ = [E Cᵀ; C B]` where `P₁` is a
permutation matrix and `s = 1` or `2`. If `A` is nonzero, then it is always possible to choose
these quantities so that `E` is nonsingular, thereby enabling us to write
`P₁ A P₁ᵀ = [I_s 0; C E⁻¹ I_{n−s}] [E 0; 0 B − C E⁻¹ Cᵀ] [I_s E⁻¹ Cᵀ; 0 I_{n−s}]`."
The factorization holds for any nonsingular pivot block `E` (symmetry is not needed), with the
reduced matrix `Ã = B − C E⁻¹ Cᵀ` of (4.4.15); and a nonzero symmetric `A` has a nonsingular
principal pivot of order one (a nonzero diagonal entry) or two (a pair `i ≠ j` with nonzero
principal minor), the book's P4.4.1. -/
theorem equation_4_4_15 {s m : ℕ} {E : Matrix (Fin s) (Fin s) ℝ} (hE : IsUnit E)
    (C : Matrix (Fin m) (Fin s) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    (fromBlocks E Cᵀ C B =
      fromBlocks 1 0 (C * E⁻¹) 1 * fromBlocks E 0 0 (B - C * E⁻¹ * Cᵀ) *
        fromBlocks 1 (E⁻¹ * Cᵀ) 0 1) ∧
    ∀ {A : Matrix (Fin n) (Fin n) ℝ}, A.IsSymm → A ≠ 0 →
      (∃ i, A i i ≠ 0) ∨ ∃ i j, i ≠ j ∧ A i i * A j j - A i j * A j i ≠ 0 := by
  refine ⟨?_, fun hA hA0 => exists_isUnit_principal_pivot hA hA0⟩
  have hinv : E * E⁻¹ = 1 := mul_nonsing_inv E ((isUnit_iff_isUnit_det E).1 hE)
  have hinv' : E⁻¹ * E = 1 := nonsing_inv_mul E ((isUnit_iff_isUnit_det E).1 hE)
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, ← Matrix.mul_assoc, hinv]
  rw [Matrix.mul_assoc C E⁻¹ E, hinv', Matrix.mul_one, add_sub_cancel]

/-! ### §4.4.5 Equilibrium systems -/

/-- The equilibrium matrix `[C B; Bᵀ 0]` is the backbone's saddle-point matrix over `ℝ`. -/
theorem fromBlocks_transpose_zero_eq_saddleMatrix {p : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : fromBlocks C B Bᵀ 0 = C.saddleMatrix B 0 := by
  rw [saddleMatrix, conjTranspose_eq_transpose_of_trivial]

/-- **§4.4.5, the tempting factorization.** "Step 1. Compute the Cholesky factorization
`C = G Gᵀ`. Step 2. Solve `G K = B` for `K`. Step 3. Compute the Cholesky factorization
`H Hᵀ = Kᵀ K = Bᵀ C⁻¹ B`. From this it follows that `A = [G 0; Kᵀ H] [Gᵀ K; 0 −Hᵀ]`": for `C`
symmetric positive definite with Cholesky factor `G = cholesky C` (Theorem 4.2.7), `B` of full
column rank and `G K = B`, the matrix `Kᵀ K = Bᵀ C⁻¹ B` is positive definite and, with
`H = cholesky (Kᵀ K)`, the equilibrium matrix factors as displayed. -/
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

/-- **(4.4.18).** "A very important class of symmetric indefinite matrices have the form
`A = [C B; Bᵀ 0]` where `C` is symmetric positive definite and `B` has full column rank. These
conditions ensure that `A` is nonsingular." -/
theorem equation_4_4_18 {p : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ}
    (hC : C.PosDef) (hB : Function.Injective B.mulVec) : IsUnit (fromBlocks C B Bᵀ 0) := by
  rw [fromBlocks_transpose_zero_eq_saddleMatrix]
  exact isUnit_saddleMatrix_zero hC hB

/-- **(4.4.20).** "In several important applications, `g = 0`, `C` is diagonal, and the solution
subvector `y` is of primary importance. A manipulation shows that this vector is specified by
`y = (Bᵀ C⁻¹ B)⁻¹ Bᵀ C⁻¹ f`": for the equilibrium system (4.4.19) with `g = 0`, `C` symmetric
positive definite (diagonality is not needed) and `B` of full column rank. -/
theorem equation_4_4_20 {p : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ}
    (hC : C.PosDef) (hB : Function.Injective B.mulVec) {x f : Fin n → ℝ} {y : Fin p → ℝ}
    (h : fromBlocks C B Bᵀ 0 *ᵥ Sum.elim x y = Sum.elim f 0) :
    y = (Bᵀ * C⁻¹ * B)⁻¹ *ᵥ ((Bᵀ * C⁻¹) *ᵥ f) := by
  rw [fromBlocks_transpose_zero_eq_saddleMatrix] at h
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    saddleMatrix_zero_mulVec_snd_eq hC hB h

end GolubVanLoan.Chapter04
