/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`, beside `Mathlib.Data.Matrix.Composition`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Composition
import Mathlib.RingTheory.Nilpotent.Basic
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.LU

/-!
# Block tridiagonal matrices and their block LU factorization

A block tridiagonal matrix with `q × q` blocks ([golub2013matrix] §4.5.1–4.5.2; [higham2002accuracy]
§13.2) is the scalar tridiagonal matrix `Matrix.tridiagonalOf E D F` of
`Numlib.LinearAlgebra.Matrix.Hessenberg` *over the block ring* `Matrix (Fin q) (Fin q) K`, and the
matrix the book writes is its flattening by Mathlib's `Matrix.comp`
(`Matrix.blockTridiagonal`; `Matrix.compRingEquiv` is a ring isomorphism, so products and inverses
transport).

## The block LU recurrence

The block LU factorization ([golub2013matrix] (4.5.3)–(4.5.4)) is a recurrence in a
*noncommutative ring*: the pivots `U₀ = D₀`, `U_{i+1} = D_{i+1} − E_i U_i⁻¹ F_i`
(`Matrix.tridiagonalLUPivot`, with `Ring.inverse`) and the multipliers `L_i = E_i U_i⁻¹`
(`Matrix.tridiagonalLUMultiplier`), and when the pivots `U_0, …, U_{N−1}` are units,
`tridiag(E, D, F) = tridiag(L, 1, 0) · tridiag(0, U, F)`, a unit lower bidiagonal times an upper
bidiagonal matrix (`Matrix.tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot`), over any ring. The
sequences are `ℕ`-indexed, the convention of the scalar Thomas recurrence `Matrix.thomasAlpha` of
`Numlib.LinearAlgebra.Matrix.LU`, which is the case of a field
(`Matrix.tridiagonalLUPivot_eq_thomasAlpha`).

## Block diagonal dominance

Block column diagonal dominance in the induced `1`-norm ([golub2013matrix] (4.5.6), Feingold–Varga
1962) is `Matrix.IsStrictBlockColDiagDominant`, for any square block matrix; on a block tridiagonal
matrix it reads `‖D_i⁻¹‖₁ (‖F_{i−1}‖₁ + ‖E_i‖₁) < 1`
(`Matrix.isStrictBlockColDiagDominant_tridiagonalOf_iff`). It makes every pivot nonsingular with
`‖U_i⁻¹‖₁ ≤ ‖D_i⁻¹‖₁ / (1 − ‖D_i⁻¹‖₁ ‖F_{i−1}‖₁)`, the multipliers contractive, `‖L_i‖₁ < 1`
((4.5.7)), the pivots bounded by the matrix, `‖U_i‖₁ ≤ ‖A‖₁` ((4.5.8)), and the matrix
nonsingular. The Neumann bound behind all of them is `Matrix.inducedNorm_inv_one_sub_le` of
`Numlib.Analysis.Matrix.OperatorNorm`.

`Matrix.IsBlockLU.blockBidiagonal_of_blockTridiagonal` (`LU`) is the *labelling* form of the same
shape statement; this module is the constructive form with the recurrence.
-/

open Finset

namespace Matrix

/-! ### The block tridiagonal matrix -/

section Block

variable {R : Type*} {N q : ℕ}

/-- The block tridiagonal matrix ([golub2013matrix] (4.5.2)) with subdiagonal blocks `E i`,
diagonal blocks `D i` and superdiagonal blocks `F i`, flattened: the tridiagonal matrix
`tridiagonalOf E D F` over the block ring, read through `Matrix.comp`. -/
def blockTridiagonal [Zero R] (E F : Fin N → Matrix (Fin q) (Fin q) R)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) R) :
    Matrix (Fin (N + 1) × Fin q) (Fin (N + 1) × Fin q) R :=
  comp _ _ _ _ R (tridiagonalOf E D F)

/-- The entries of a block tridiagonal matrix: the `(k, l)` entry of its `(i, j)` block. -/
theorem blockTridiagonal_apply [Zero R] (E F : Fin N → Matrix (Fin q) (Fin q) R)
    (D : Fin (N + 1) → Matrix (Fin q) (Fin q) R) (i j : Fin (N + 1)) (k l : Fin q) :
    blockTridiagonal E F D (i, k) (j, l) = tridiagonalOf E D F i j k l := rfl

end Block

/-! ### The block LU recurrence -/

section Recurrence

variable {R : Type*} [Ring R]

/-- The pivots of the block LU recurrence ([golub2013matrix] (4.5.4)) over any ring:
`U₀ = D₀` and `U_{i+1} = D_{i+1} − E_i U_i⁻¹ F_i` (`Ring.inverse`). -/
noncomputable def tridiagonalLUPivot (E D F : ℕ → R) : ℕ → R
  | 0 => D 0
  | i + 1 => D (i + 1) - E i * Ring.inverse (tridiagonalLUPivot E D F i) * F i

/-- The multipliers of the block LU recurrence ([golub2013matrix] (4.5.4)):
`L_i = E_i U_i⁻¹`, the solution of `L_i U_i = E_i`. -/
noncomputable def tridiagonalLUMultiplier (E D F : ℕ → R) (i : ℕ) : R :=
  E i * Ring.inverse (tridiagonalLUPivot E D F i)

variable (E D F : ℕ → R)

/-- The first pivot is the first diagonal block. -/
@[simp]
theorem tridiagonalLUPivot_zero : tridiagonalLUPivot E D F 0 = D 0 := rfl

/-- The pivot recurrence through the multipliers: `U_{i+1} = D_{i+1} − L_i F_i`. -/
theorem tridiagonalLUPivot_succ (i : ℕ) :
    tridiagonalLUPivot E D F (i + 1) = D (i + 1) - tridiagonalLUMultiplier E D F i * F i := rfl

/-- The multiplier solves `L_i U_i = E_i` when the pivot is a unit. -/
theorem tridiagonalLUMultiplier_mul_tridiagonalLUPivot {i : ℕ}
    (h : IsUnit (tridiagonalLUPivot E D F i)) :
    tridiagonalLUMultiplier E D F i * tridiagonalLUPivot E D F i = E i :=
  Ring.inverse_mul_cancel_right _ _ h

/-- **The block LU factorization** ([golub2013matrix] (4.5.3)) over any ring: if the pivots
`U_0, …, U_{N−1}` are units, then `tridiag(E, D, F) = tridiag(L, 1, 0) · tridiag(0, U, F)` — a unit
lower bidiagonal times an upper bidiagonal matrix. No hypothesis on the last pivot `U_N` (it may be
singular, as for the scalar LU factorization). -/
theorem tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot {N : ℕ}
    (hU : ∀ i, i < N → IsUnit (tridiagonalLUPivot E D F i)) :
    tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => F i)
      = tridiagonalOf (fun i => tridiagonalLUMultiplier E D F i) 1 0
        * tridiagonalOf 0 (fun i => tridiagonalLUPivot E D F i) (fun i => F i) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  change _ = (tridiagonalOf (fun i : Fin N => tridiagonalLUMultiplier E D F i) 1 0 *ᵥ
    fun r => tridiagonalOf 0 (fun i : Fin (N + 1) => tridiagonalLUPivot E D F i)
      (fun i : Fin N => F i) r j) i
  rw [tridiagonalOf_mulVec]
  simp only [tridiagonalOf, of_apply, Pi.one_apply, Pi.zero_apply, one_mul, zero_mul]
  split_ifs <;> first
    | (exfalso; omega)
    | (simp only [add_zero, zero_add, mul_zero]; done)
    | (have h1 : (i : ℕ) - 1 = j := by omega
       simp only [h1, tridiagonalLUMultiplier_mul_tridiagonalLUPivot E D F (hU j (by omega)),
         add_zero, zero_add]
       done)
    | (have h0 : (i : ℕ) = 0 := by omega
       simp only [h0, tridiagonalLUPivot_zero, add_zero, zero_add])
    | (obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
       simp only [hi', Nat.add_sub_cancel, tridiagonalLUPivot_succ]
       abel1)

/-- **Over a field the block recurrence is the Thomas recurrence** ([quarteroni2000numerical]
(3.53)): `U_i = α_i` for `Matrix.thomasAlpha` with the subdiagonal read one row lower
(`b j = E (j − 1)`), and the multipliers are the shifted `Matrix.thomasBeta`,
`L_i = β_{i+1}`. -/
theorem tridiagonalLUPivot_eq_thomasAlpha {K : Type*} [Field K] (E D F : ℕ → K) (i : ℕ) :
    tridiagonalLUPivot E D F i = thomasAlpha D (fun j => E (j - 1)) F i
      ∧ tridiagonalLUMultiplier E D F i = thomasBeta D (fun j => E (j - 1)) F (i + 1) := by
  induction i with
  | zero =>
    refine ⟨rfl, ?_⟩
    rw [tridiagonalLUMultiplier, thomasBeta_succ, Ring.inverse_eq_inv', div_eq_mul_inv]
    rfl
  | succ i ih =>
    have hU : tridiagonalLUPivot E D F (i + 1)
        = thomasAlpha D (fun j => E (j - 1)) F (i + 1) := by
      rw [tridiagonalLUPivot_succ, thomasAlpha_succ, ih.2]
    refine ⟨hU, ?_⟩
    rw [tridiagonalLUMultiplier, thomasBeta_succ, Ring.inverse_eq_inv', hU, div_eq_mul_inv]
    rfl

end Recurrence

/-! ### Unit triangular block matrices -/

section Triangular

variable {S : Type*} [Ring S] {n : ℕ}

/-- A matrix over a ring whose nonzero entries strictly increase a potential `f` is nilpotent:
`(M ^ k) i j = 0` as soon as `f j < f i + k`. -/
private theorem pow_apply_eq_zero_of_potential (M : Matrix (Fin n) (Fin n) S) (f : Fin n → ℕ)
    (hM : ∀ i j, f j ≤ f i → M i j = 0) (k : ℕ) :
    ∀ i j, f j < f i + k → (M ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero, one_apply_ne]
    rintro rfl
    omega
  | succ k ih =>
    intro i j h
    rw [pow_succ, mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : f j ≤ f r
    · rw [hM r j hr, mul_zero]
    · rw [ih i r (by omega), zero_mul]

/-- `1 + M` is a unit when the nonzero entries of `M` strictly increase a potential. -/
private theorem isUnit_one_add_of_potential (M : Matrix (Fin n) (Fin n) S) (f : Fin n → ℕ)
    (hf : ∀ i, f i < n) (hM : ∀ i j, f j ≤ f i → M i j = 0) : IsUnit (1 + M) := by
  refine IsNilpotent.isUnit_one_add ⟨n, ?_⟩
  ext i j
  exact pow_apply_eq_zero_of_potential M f hM n i j (by have := hf j; omega)

/-- A unit lower bidiagonal matrix over any ring is a unit. -/
private theorem isUnit_tridiagonalOf_one_zero {N : ℕ} (L : Fin N → S) :
    IsUnit (tridiagonalOf L 1 0) := by
  have h : tridiagonalOf L 1 0 = 1 + tridiagonalOf L 0 0 := by
    ext i j
    simp only [tridiagonalOf, of_apply, add_apply, one_apply, Pi.one_apply, Pi.zero_apply,
      Fin.ext_iff]
    split_ifs <;> simp
  rw [h]
  refine isUnit_one_add_of_potential _ (fun i => N - i)
    (fun i => Nat.lt_succ_of_le (Nat.sub_le _ _)) fun i j hij => ?_
  simp only [tridiagonalOf, of_apply, Pi.zero_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- An upper bidiagonal matrix over any ring with unit diagonal entries is a unit. -/
private theorem isUnit_tridiagonalOf_zero {N : ℕ} (U : Fin (N + 1) → S) (F : Fin N → S)
    (hU : ∀ i, IsUnit (U i)) : IsUnit (tridiagonalOf 0 U F) := by
  have hdiag : IsUnit (diagonal U) := by
    refine ⟨⟨diagonal U, diagonal fun i => Ring.inverse (U i), ?_, ?_⟩, rfl⟩ <;>
      rw [diagonal_mul_diagonal, ← diagonal_one] <;> congr 1 <;> funext i
    · exact Ring.mul_inverse_cancel _ (hU i)
    · exact Ring.inverse_mul_cancel _ (hU i)
  have h : tridiagonalOf 0 U F
      = diagonal U * (1 + diagonal (fun i => Ring.inverse (U i)) * tridiagonalOf 0 0 F) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have hone : (diagonal fun i => U i * Ring.inverse (U i)) = 1 := by
      rw [← diagonal_one]
      congr 1
      funext i
      exact Ring.mul_inverse_cancel _ (hU i)
    rw [hone, Matrix.one_mul]
    ext i j
    simp only [tridiagonalOf, of_apply, add_apply, diagonal_apply, Pi.zero_apply, Fin.ext_iff]
    split_ifs <;> simp
  rw [h]
  refine hdiag.mul
    (isUnit_one_add_of_potential _ (fun i => i) (fun i => i.isLt) fun i j hij => ?_)
  rw [diagonal_mul]
  simp only [tridiagonalOf, of_apply, Pi.zero_apply]
  split_ifs <;> first | simp | (exfalso; omega)

end Triangular

/-! ### Block diagonal dominance -/

section Dominance

variable {𝕜 : Type*} [RCLike 𝕜] {q N : ℕ}

/-- **Strict block column diagonal dominance** in the induced `1`-norm ([golub2013matrix] (4.5.6)
for block tridiagonal matrices; the block analogue of column diagonal dominance, Feingold–Varga
1962): for a square matrix `A` of `q × q` blocks, every diagonal block `A j j` is nonsingular and
`‖(A j j)⁻¹‖₁ ∑_{i ≠ j} ‖A i j‖₁ < 1`. (The book writes the condition without the nonsingularity of
the diagonal blocks, which `‖D_i⁻¹‖₁` presupposes.) -/
def IsStrictBlockColDiagDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Matrix (Fin q) (Fin q) 𝕜)) : Prop :=
  ∀ j, IsUnit (A j j) ∧ lpOpNorm 1 (A j j)⁻¹ * ∑ i ∈ univ.erase j, lpOpNorm 1 (A i j) < 1

/-- **Block dominance of a block tridiagonal matrix** ([golub2013matrix] (4.5.6), `0`-based, with
`E_N ≡ F_{−1} ≡ 0`): column `i` has the off-diagonal blocks `F_{i−1}` and `E_i` only, so the
condition reads `‖D_i⁻¹‖₁ (‖F_{i−1}‖₁ + ‖E_i‖₁) < 1` for `i ≤ N`. -/
theorem isStrictBlockColDiagDominant_tridiagonalOf_iff (E D F : ℕ → Matrix (Fin q) (Fin q) 𝕜) :
    (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
        (fun i => F i)).IsStrictBlockColDiagDominant ↔
      ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
        ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))
          + (if i < N then lpOpNorm 1 (E i) else 0)) < 1 := by
  set T := tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => F i) with hT
  have hcol : ∀ j : Fin (N + 1), ∑ r ∈ univ.erase j, lpOpNorm 1 (T r j)
      = (if (j : ℕ) = 0 then 0 else lpOpNorm 1 (F ((j : ℕ) - 1)))
        + (if (j : ℕ) < N then lpOpNorm 1 (E j) else 0) := by
    intro j
    have hg : ∑ r ∈ univ.erase j, lpOpNorm 1 (T r j)
        = ∑ r, (if r = j then 0 else lpOpNorm 1 (T r j)) := by
      rw [← Finset.sum_erase univ (f := fun r => if r = j then 0 else lpOpNorm 1 (T r j))
        (a := j) (by simp)]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [ite_eq_right (Finset.ne_of_mem_erase hr)]
    have hterm : ∀ r : Fin (N + 1), (if r = j then 0 else lpOpNorm 1 (T r j))
        = (if h : (r : ℕ) = j + 1 then lpOpNorm 1 (E j) else 0)
          + (if h : (r : ℕ) + 1 = j then lpOpNorm 1 (F r) else 0) := by
      intro r
      simp only [hT, tridiagonalOf, of_apply, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | simp
    rw [hg, Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_add_distrib,
      sum_dite_val_eq_add_one, sum_dite_val_add_one_eq, add_comm]
    congr 1
    · by_cases h : (j : ℕ) = 0
      · rw [dite_eq_right (by omega), ite_eq_left h]
      · rw [dite_eq_left (by omega), ite_eq_right h]
    · by_cases h : (j : ℕ) < N
      · rw [dite_eq_left (by omega), ite_eq_left h]
      · rw [dite_eq_right (by omega), ite_eq_right h]
  constructor
  · intro h i hi
    have hj := h ⟨i, by omega⟩
    rw [hcol, hT, tridiagonalOf_apply_self] at hj
    exact hj
  · intro h j
    rw [hcol, hT, tridiagonalOf_apply_self]
    exact h j (by omega)

/-- On `0 × 0` blocks every norm vanishes. -/
private theorem lpOpNorm_eq_zero_of_fin_zero (A : Matrix (Fin 0) (Fin 0) 𝕜) :
    lpOpNorm 1 A = 0 := by
  rw [Subsingleton.elim A 0, lpOpNorm_zero]

/-- A `1`-norm bound from a bound on every column sum. -/
private theorem lpOpNorm_one_le_of_forall_sum_le {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m 𝕜} {C : ℝ} (hC : 0 ≤ C) (h : ∀ c, ∑ k, ‖M k c‖ ≤ C) : lpOpNorm 1 M ≤ C := by
  rw [lpOpNorm_one_eq_sup_sum_norm]
  have hle : (univ.sup fun j => ∑ i, ‖M i j‖₊) ≤ ⟨C, hC⟩ := Finset.sup_le fun c _ =>
    NNReal.coe_le_coe.mp (show ((∑ i, ‖M i c‖₊ : NNReal) : ℝ) ≤ C by push_cast; exact h c)
  exact NNReal.coe_le_coe.mpr hle

/-- The column sums of a product: `∑_k ‖(L M) k c‖ ≤ ‖L‖₁ ∑_k ‖M k c‖`. -/
private theorem sum_norm_mul_apply_le {m : Type*} [Fintype m] [DecidableEq m]
    (L M : Matrix m m 𝕜) (c : m) : ∑ k, ‖(L * M) k c‖ ≤ lpOpNorm 1 L * ∑ k, ‖M k c‖ := by
  have h := lpSeminorm_mulVec_le 1 L fun k => M k c
  simp only [lpSeminorm_apply, PiLp.norm_eq_of_L1] at h
  exact h

variable {E D F : ℕ → Matrix (Fin q) (Fin q) 𝕜}

/-- The multiplier bound `‖L_i‖₁ < 1` from the pivot bound at `i` and dominance at `i < N`. -/
private theorem lpOpNorm_multiplier_lt_one {i : ℕ} (hN : i < N)
    (hd : IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ * ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))
        + (if i < N then lpOpNorm 1 (E i) else 0)) < 1)
    (hU : lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹
      ≤ lpOpNorm 1 (D i)⁻¹ /
        (1 - lpOpNorm 1 (D i)⁻¹ * (if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))))
    : lpOpNorm 1 (tridiagonalLUMultiplier E D F i) < 1 := by
  set a := lpOpNorm 1 (D i)⁻¹
  set f := if i = 0 then 0 else lpOpNorm 1 (F (i - 1))
  have ha : 0 ≤ a := lpOpNorm_nonneg _ _
  have hf : 0 ≤ f := by simp only [f]; split_ifs <;> first | rfl | exact lpOpNorm_nonneg _ _
  have he : 0 ≤ lpOpNorm 1 (E i) := lpOpNorm_nonneg _ _
  rw [ite_eq_left hN] at hd
  have hden : 0 < 1 - a * f := by nlinarith [hd.2]
  calc lpOpNorm 1 (tridiagonalLUMultiplier E D F i)
      ≤ lpOpNorm 1 (E i) * lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹ := by
        rw [tridiagonalLUMultiplier, ← nonsing_inv_eq_ringInverse]
        exact lpOpNorm_mul_le _ _ _
    _ ≤ lpOpNorm 1 (E i) * (a / (1 - a * f)) := mul_le_mul_of_nonneg_left hU he
    _ < 1 := by
        rw [← mul_div_assoc, div_lt_one hden]
        nlinarith [hd.2]

/-- The pivots under dominance, with their inverse bound (the induction behind
`IsStrictBlockColDiagDominant.isUnit_tridiagonalLUPivot`). -/
private theorem pivot_of_dominant (hq : 0 < q)
    (hd : ∀ i ≤ N, IsUnit (D i) ∧ lpOpNorm 1 (D i)⁻¹ *
        ((if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))
          + (if i < N then lpOpNorm 1 (E i) else 0)) < 1) :
    ∀ i ≤ N, IsUnit (tridiagonalLUPivot E D F i) ∧ lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹
      ≤ lpOpNorm 1 (D i)⁻¹ / (1 - lpOpNorm 1 (D i)⁻¹ *
        (if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))) := by
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨(hd 0 (Nat.zero_le _)).1, ?_⟩
    simp
  | succ i ih =>
    intro hi
    obtain ⟨hUi, hUi'⟩ := ih (by omega)
    have hL := lpOpNorm_multiplier_lt_one (by omega) (hd i (by omega)) hUi'
    obtain ⟨hD, hdom⟩ := hd (i + 1) hi
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at hdom ⊢
    set a := lpOpNorm 1 (D (i + 1))⁻¹
    have ha : 0 ≤ a := lpOpNorm_nonneg _ _
    have hF : 0 ≤ lpOpNorm 1 (F i) := lpOpNorm_nonneg _ _
    have he : 0 ≤ (if i + 1 < N then lpOpNorm 1 (E (i + 1)) else 0) := by
      split_ifs <;> first | rfl | exact lpOpNorm_nonneg _ _
    set X := (D (i + 1))⁻¹ * (tridiagonalLUMultiplier E D F i * F i)
    have hX : lpOpNorm 1 X ≤ a * lpOpNorm 1 (F i) := by
      calc lpOpNorm 1 X
          ≤ a * lpOpNorm 1 (tridiagonalLUMultiplier E D F i * F i) := lpOpNorm_mul_le _ _ _
        _ ≤ a * (lpOpNorm 1 (tridiagonalLUMultiplier E D F i) * lpOpNorm 1 (F i)) :=
            mul_le_mul_of_nonneg_left (lpOpNorm_mul_le _ _ _) ha
        _ ≤ a * lpOpNorm 1 (F i) := by
            refine mul_le_mul_of_nonneg_left ?_ ha
            nlinarith [lpOpNorm_nonneg 1 (tridiagonalLUMultiplier E D F i)]
    have hX1 : lpOpNorm 1 X < 1 := by nlinarith
    have hdet : IsUnit (D (i + 1)).det := (isUnit_iff_isUnit_det _).mp hD
    have hUeq : tridiagonalLUPivot E D F (i + 1) = D (i + 1) * (1 - X) := by
      rw [tridiagonalLUPivot_succ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
        mul_nonsing_inv _ hdet, Matrix.one_mul]
    have hXi : inducedNorm (lpSeminorm 1) (lpSeminorm 1) X < 1 := by
      rwa [← lpOpNorm_eq_inducedNorm]
    have h1X : IsUnit (1 - X) := isUnit_one_sub_of_inducedNorm_lt_one (lpSeminorm_definite 1) hXi
    have hinv : lpOpNorm 1 (1 - X)⁻¹ ≤ 1 / (1 - lpOpNorm 1 X) := by
      have := inducedNorm_inv_one_sub_le (lpSeminorm_definite 1) hXi
      rwa [← lpOpNorm_eq_inducedNorm, ← lpOpNorm_eq_inducedNorm] at this
    refine ⟨hUeq ▸ hD.mul h1X, ?_⟩
    rw [hUeq, Matrix.mul_inv_rev]
    have hden : 0 < 1 - a * lpOpNorm 1 (F i) := by nlinarith
    calc lpOpNorm 1 ((1 - X)⁻¹ * (D (i + 1))⁻¹)
        ≤ lpOpNorm 1 (1 - X)⁻¹ * a := lpOpNorm_mul_le _ _ _
      _ ≤ 1 / (1 - lpOpNorm 1 X) * a := mul_le_mul_of_nonneg_right hinv ha
      _ ≤ 1 / (1 - a * lpOpNorm 1 (F i)) * a := by
          refine mul_le_mul_of_nonneg_right ?_ ha
          exact one_div_le_one_div_of_le hden (by linarith)
      _ = a / (1 - a * lpOpNorm 1 (F i)) := by ring

/-- **Block dominance makes the pivots nonsingular** ([golub2013matrix] §4.5.2): under strict block
column dominance of `tridiag(E, D, F)`, every pivot `U_i`, `i ≤ N`, is a unit and
`‖U_i⁻¹‖₁ ≤ ‖D_i⁻¹‖₁ / (1 − ‖D_i⁻¹‖₁ ‖F_{i−1}‖₁)`, so the factorization (4.5.3) exists. The
induction carries `‖L_{i−1}‖₁ < 1`: `U_i = D_i (1 − D_i⁻¹ L_{i−1} F_{i−1})` with
`‖D_i⁻¹ L_{i−1} F_{i−1}‖₁ ≤ ‖D_i⁻¹‖₁ ‖F_{i−1}‖₁ < 1`, and the Neumann bound. -/
theorem IsStrictBlockColDiagDominant.isUnit_tridiagonalLUPivot
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i ≤ N) :
    IsUnit (tridiagonalLUPivot E D F i) ∧ lpOpNorm 1 (tridiagonalLUPivot E D F i)⁻¹
      ≤ lpOpNorm 1 (D i)⁻¹ / (1 - lpOpNorm 1 (D i)⁻¹ *
        (if i = 0 then 0 else lpOpNorm 1 (F (i - 1)))) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨isUnit_of_subsingleton _, by simp [lpOpNorm_eq_zero_of_fin_zero]⟩
  exact pivot_of_dominant hq ((isStrictBlockColDiagDominant_tridiagonalOf_iff E D F).mp h) i hi

/-- [golub2013matrix] (4.5.7): under strict block column dominance the multipliers satisfy
`‖L_i‖₁ ≤ 1` (indeed `< 1`) for `i < N`: `‖E_i U_i⁻¹‖₁ ≤ ‖E_i‖₁ ‖D_i⁻¹‖₁ / (1 − ‖D_i⁻¹‖₁ ‖F_{i−1}‖₁)
< 1`. -/
theorem IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUMultiplier_le
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i < N) :
    lpOpNorm 1 (tridiagonalLUMultiplier E D F i) ≤ 1 :=
  (lpOpNorm_multiplier_lt_one hi ((isStrictBlockColDiagDominant_tridiagonalOf_iff E D F).mp h i
    hi.le) (h.isUnit_tridiagonalLUPivot hi.le).2).le

/-- [golub2013matrix] (4.5.8), read as `‖U_i‖₁ ≤ ‖A‖₁` (the printed `‖A_n‖₁` has no referent):
under strict block column dominance the pivots are bounded by the flattened block tridiagonal
matrix. Column by column, `U_i e_c = D_i e_c − L_{i−1} (F_{i−1} e_c)` with `‖L_{i−1}‖₁ ≤ 1`, which
is at most the `1`-norm of the column `(i, c)` of `A`. -/
theorem IsStrictBlockColDiagDominant.lpOpNorm_tridiagonalLUPivot_le
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) {i : ℕ} (hi : i ≤ N) :
    lpOpNorm 1 (tridiagonalLUPivot E D F i)
      ≤ lpOpNorm 1 (blockTridiagonal (fun i : Fin N => E i) (fun i : Fin N => F i)
        fun i : Fin (N + 1) => D i) := by
  set A := blockTridiagonal (fun i : Fin N => E i) (fun i : Fin N => F i)
    fun i : Fin (N + 1) => D i with hA
  -- the column sums of `A` below its norm, restricted to one or two block rows
  have hcolA : ∀ c : Fin q, ∑ p : Fin (N + 1) × Fin q, ‖A p (⟨i, by omega⟩, c)‖ ≤ lpOpNorm 1 A :=
    fun c => sum_norm_le_lpOpNorm_one A _
  have hdiag : ∀ k c, A (⟨i, by omega⟩, k) (⟨i, by omega⟩, c) = D i k c := by
    intro k c
    simp [hA, blockTridiagonal_apply]
  refine lpOpNorm_one_le_of_forall_sum_le (lpOpNorm_nonneg _ _) fun c => ?_
  refine le_trans ?_ (hcolA c)
  rw [Fintype.sum_prod_type]
  set g : Fin (N + 1) → ℝ := fun r => ∑ k, ‖A (r, k) (⟨i, by omega⟩, c)‖ with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => Finset.sum_nonneg fun k _ => norm_nonneg _
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · calc ∑ k, ‖tridiagonalLUPivot E D F 0 k c‖ = g ⟨0, by omega⟩ := by
          simp only [hg, hdiag, tridiagonalLUPivot_zero]
      _ ≤ ∑ r, g r := Finset.single_le_sum (fun r _ => hg0 r) (mem_univ _)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hL := h.lpOpNorm_tridiagonalLUMultiplier_le (i := i') (by omega)
    have hoff : ∀ k, A (⟨i', by omega⟩, k) (⟨i' + 1, by omega⟩, c) = F i' k c := by
      intro k
      simp only [hA, blockTridiagonal_apply, tridiagonalOf, of_apply]
      split_ifs <;> first | (exfalso; omega) | rfl
    have hne : (⟨i' + 1, by omega⟩ : Fin (N + 1)) ≠ ⟨i', by omega⟩ := by simp
    calc ∑ k, ‖tridiagonalLUPivot E D F (i' + 1) k c‖
        ≤ ∑ k, (‖D (i' + 1) k c‖ + ‖(tridiagonalLUMultiplier E D F i' * F i') k c‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [tridiagonalLUPivot_succ, sub_apply]
          exact norm_sub_le _ _
      _ ≤ ∑ k, ‖D (i' + 1) k c‖ + ∑ k, ‖F i' k c‖ := by
          rw [Finset.sum_add_distrib]
          have := sum_norm_mul_apply_le (tridiagonalLUMultiplier E D F i') (F i') c
          have hs : 0 ≤ ∑ k, ‖F i' k c‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
          nlinarith
      _ = g ⟨i' + 1, by omega⟩ + g ⟨i', by omega⟩ := by
          simp only [hg, hdiag, hoff]
      _ = ∑ r ∈ {⟨i' + 1, by omega⟩, ⟨i', by omega⟩}, g r := (Finset.sum_pair hne).symm
      _ ≤ ∑ r, g r :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hg0 r

/-- **A block column diagonally dominant block tridiagonal matrix is nonsingular**
([golub2013matrix] P4.5.1(a), the fact §4.5.2 presupposes): all pivots `U_0, …, U_N` are units, so
the factorization
(4.5.3) is a product of a unit lower bidiagonal and an upper bidiagonal matrix with unit diagonal,
both units of the block matrix ring, and the flattening `Matrix.compRingEquiv` preserves units. -/
theorem IsStrictBlockColDiagDominant.isUnit_blockTridiagonal
    (h : (tridiagonalOf (N := N) (fun i => E i) (fun i => D i)
      (fun i => F i)).IsStrictBlockColDiagDominant) :
    IsUnit (blockTridiagonal (fun i : Fin N => E i) (fun i : Fin N => F i)
      fun i : Fin (N + 1) => D i) := by
  have hU : ∀ i, i ≤ N → IsUnit (tridiagonalLUPivot E D F i) :=
    fun i hi => (h.isUnit_tridiagonalLUPivot hi).1
  have hfac := tridiagonalOf_eq_mul_of_isUnit_tridiagonalLUPivot E D F fun i hi => hU i hi.le
  have hT : IsUnit (tridiagonalOf (N := N) (fun i => E i) (fun i => D i) (fun i => F i)) := by
    rw [hfac]
    exact (isUnit_tridiagonalOf_one_zero _).mul
      (isUnit_tridiagonalOf_zero _ _ fun i => hU i (by omega))
  exact hT.map (compRingEquiv (Fin (N + 1)) (Fin q) 𝕜)

end Dominance
end Matrix
