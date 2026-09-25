/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a file beside `Mathlib.LinearAlgebra.Matrix.Kronecker`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.Cauchy
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.Sylvester
import Numlib.LinearAlgebra.Matrix.Toeplitz

/-!
# Displacement structure

A square matrix `A` has *displacement structure* with respect to two displacement operators `F`,
`G` when its displacement `F A − A G` has low rank; a factorization `F A − A G = R Sᵀ` with
`R S : Matrix n (Fin r) K` is a set of *generators* ([golub2013matrix] §12.1; Kailath, Kung and
Morf 1979; Gohberg, Kailath and Olshevsky 1995).

* The displacement is the Sylvester operator `Matrix.sylvesterMap F G A` of
  `Numlib.LinearAlgebra.Matrix.Sylvester`; this file adds only its rank,
  `Matrix.displacementRank F G A`. When the Sylvester operator is injective, generators determine
  the matrix (`Matrix.eq_of_sylvesterMap_eq`).
* The Cauchy matrix has displacement `e eᵀ` for diagonal operators
  (`Matrix.sylvesterMap_diagonal_cauchy`).
* **The generator update under one step of Gaussian elimination**
  (`Matrix.sylvesterMap_schurComplement`, [golub2013matrix] Theorem 12.1.1, generalized): if the
  first row of `F` and the first column of `G` vanish off the corner, the Schur complement
  `A₁ = B − f gᵀ / α` has displacement `R₁ S₁ᵀ` with explicitly updated generators. The book's
  diagonal case is `Matrix.sylvesterMap_diagonal_schurComplement`.
* The displacement operators of §12.1.7: the cyclic shifts `Z_{±1}` (`Matrix.cyclicShift` of
  `Numlib.LinearAlgebra.Matrix.Permutation`) and the corner-modified tridiagonal matrices
  `Y_{0,0}`, `Y_{1,1}` (`Matrix.cornerTridiagonal` of
  `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`). Their Sylvester operators are injective
  (`Matrix.sylvesterMap_cyclicShift_one_neg_one_injective`,
  `Matrix.sylvesterMap_cornerTridiagonal_injective`), and the displacements of Toeplitz and Hankel
  matrices vanish off the first row and last column, respectively off the border
  (`Matrix.sylvesterMap_cyclicShift_toeplitz_apply`, `Matrix.sylvesterMap_cyclicShift_hankel_apply`,
  `Matrix.sylvesterMap_cornerTridiagonal_toeplitz_apply`,
  `Matrix.sylvesterMap_cornerTridiagonal_hankel_apply`).

## Design

The book puts the nonsingularity of the Sylvester operator into the definition of the displacement
rank ((12.1.2)); here it is a hypothesis exactly where it is used. The support lemmas are stated
entrywise; the rank bounds (12.1.8)–(12.1.11) follow from them by the support bound of
`Numlib.LinearAlgebra.Matrix.Rank`.

## References

* [golub2013matrix] §12.1.
-/

open Finset

namespace Matrix

variable {K : Type*} [Field K]

/-! ### The displacement rank -/

section Rank

variable {n : Type*} [Fintype n]

/-- The `{F, G}`-displacement rank ([golub2013matrix] (12.1.2)): the rank of the displacement
`F A − A G = sylvesterMap F G A`. No nonsingularity of the Sylvester operator is built in. -/
noncomputable def displacementRank (F G A : Matrix n n K) : ℕ :=
  (sylvesterMap F G A).rank

/-- **Generators determine the matrix** when the Sylvester operator is injective
([golub2013matrix] §12.1.1, "if `λ(F) ∩ λ(G) = ∅`"). -/
theorem eq_of_sylvesterMap_eq {F G : Matrix n n K} (hFG : Function.Injective (sylvesterMap F G))
    {A B : Matrix n n K} {r : Type*} [Fintype r] {R S : Matrix n r K}
    (hA : sylvesterMap F G A = R * Sᵀ) (hB : sylvesterMap F G B = R * Sᵀ) : A = B :=
  hFG (hA.trans hB.symm)

end Rank

/-! ### Cauchy matrices -/

/-- **The Cauchy matrix has displacement `e eᵀ`** ([golub2013matrix] §12.1.2): if `ω k ≠ ν j`
for all `k`, `j`, then `diag(ω) C − C diag(ν) = e eᵀ` for the Cauchy matrix
`C = (1 / (ω k − ν j))`, and its displacement rank is `1` when `n ≠ 0`. -/
theorem sylvesterMap_diagonal_cauchy {n : ℕ} {ω ν : Fin n → K} (h : ∀ k j, ω k ≠ ν j) :
    sylvesterMap (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = vecMulVec 1 1 ∧
      (n ≠ 0 → displacementRank (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = 1) := by
  have heq : sylvesterMap (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = vecMulVec 1 1 := by
    ext k j
    rw [sylvesterMap_diagonal_apply, cauchy_apply, vecMulVec_apply, Pi.neg_apply, ← sub_eq_add_neg,
      Pi.one_apply, Pi.one_apply, mul_one]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (h k j))
  refine ⟨heq, fun hn => ?_⟩
  rw [displacementRank, heq]
  refine le_antisymm (rank_vecMulVec_le _ _) ?_
  have : NeZero n := ⟨hn⟩
  by_contra h0
  rw [not_le, Nat.lt_one_iff, rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := congrFun (LinearMap.congr_fun h0 (Pi.single 0 1)) 0
  simp [mulVec, dotProduct] at this

/-! ### The generator update under one elimination step -/

section Schur

variable {N r : ℕ}

/-- **The generator update under one step of Gaussian elimination** ([golub2013matrix]
Theorem 12.1.1, generalized). Let `F G A : Matrix (Fin (N + 1)) (Fin (N + 1)) K` with
`F A − A G = R Sᵀ`, where the first row of `F` and the first column of `G` vanish off the corner,
and `α = A 0 0 ≠ 0`. Write `A = [α gᵀ; f B]`. Then the Schur complement `A₁ = B − f gᵀ / α`
satisfies `F₁ A₁ − A₁ G₁ = R₁ S₁ᵀ` with `F₁`, `G₁` the trailing blocks of `F`, `G` and
`R₁ = R(2:, :) − f r₁ᵀ / α`, `S₁ = S(2:, :) − g s₁ᵀ / α` (`r₁`, `s₁` the first rows of `R`, `S`).
The book's case is `F`, `G` diagonal; the corner hypotheses also cover the lower shift and every
lower/upper triangular pair. -/
theorem sylvesterMap_schurComplement {F G A : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
    {R S : Matrix (Fin (N + 1)) (Fin r) K} (hF : ∀ j : Fin N, F 0 j.succ = 0)
    (hG : ∀ i : Fin N, G i.succ 0 = 0) (h : sylvesterMap F G A = R * Sᵀ) (hα : A 0 0 ≠ 0) :
    sylvesterMap (F.submatrix Fin.succ Fin.succ) (G.submatrix Fin.succ Fin.succ)
        (A.submatrix Fin.succ Fin.succ -
          (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) =
      (R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0)) *
        (S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0))ᵀ := by
  set α := A 0 0 with hαdef
  set a := α⁻¹
  have ha : a * α = 1 := inv_mul_cancel₀ hα
  have E : ∀ p q, (F * A - A * G) p q = ∑ l, R p l * S q l := fun p q => by
    have := congrFun (congrFun h p) q
    simpa only [sylvesterMap_apply, mul_apply, transpose_apply] using this
  ext i j
  have e00 : F 0 0 * α - α * G 0 0 = ∑ l, R 0 l * S 0 l := by
    have := E 0 0
    simp only [sub_apply, mul_apply, Fin.sum_univ_succ, hF, hG, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero] at this
    linear_combination this
  have e0j : F 0 0 * A 0 j.succ - (α * G 0 j.succ + ∑ t : Fin N, A 0 t.succ * G t.succ j.succ) =
      ∑ l, R 0 l * S j.succ l := by
    have := E 0 j.succ
    simp only [sub_apply, mul_apply, Fin.sum_univ_succ, hF, zero_mul, Finset.sum_const_zero,
      add_zero] at this
    linear_combination this
  have ei0 : (F i.succ 0 * α + ∑ t : Fin N, F i.succ t.succ * A t.succ 0) - A i.succ 0 * G 0 0 =
      ∑ l, R i.succ l * S 0 l := by
    have := E i.succ 0
    simp only [sub_apply, mul_apply, Fin.sum_univ_succ, hG, mul_zero, Finset.sum_const_zero,
      add_zero] at this
    linear_combination this
  have eij : (F i.succ 0 * A 0 j.succ + ∑ t : Fin N, F i.succ t.succ * A t.succ j.succ) -
      (A i.succ 0 * G 0 j.succ + ∑ t : Fin N, A i.succ t.succ * G t.succ j.succ) =
      ∑ l, R i.succ l * S j.succ l := by
    have := E i.succ j.succ
    simp only [sub_apply, mul_apply, Fin.sum_univ_succ] at this
    linear_combination this
  have hl : sylvesterMap (F.submatrix Fin.succ Fin.succ) (G.submatrix Fin.succ Fin.succ)
      (A.submatrix Fin.succ Fin.succ -
        a • vecMulVec (fun i' : Fin N => A i'.succ 0) fun j' : Fin N => A 0 j'.succ) i j =
      (∑ t : Fin N, F i.succ t.succ * A t.succ j.succ -
          a * A 0 j.succ * ∑ t : Fin N, F i.succ t.succ * A t.succ 0) -
        (∑ t : Fin N, A i.succ t.succ * G t.succ j.succ -
          a * A i.succ 0 * ∑ t : Fin N, A 0 t.succ * G t.succ j.succ) := by
    simp only [sylvesterMap_apply, sub_apply, mul_apply, submatrix_apply, smul_apply,
      vecMulVec_apply, smul_eq_mul]
    congr 1
    · rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by ring
    · rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by ring
  have hr : ((R.submatrix Fin.succ id - a • vecMulVec (fun i' : Fin N => A i'.succ 0) (R 0)) *
      (S.submatrix Fin.succ id - a • vecMulVec (fun j' : Fin N => A 0 j'.succ) (S 0))ᵀ) i j =
      ∑ l, R i.succ l * S j.succ l - a * A 0 j.succ * ∑ l, R i.succ l * S 0 l -
        a * A i.succ 0 * ∑ l, R 0 l * S j.succ l +
        a * a * A i.succ 0 * A 0 j.succ * ∑ l, R 0 l * S 0 l := by
    simp only [mul_apply, transpose_apply, sub_apply, submatrix_apply, smul_apply,
      vecMulVec_apply, smul_eq_mul, id]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [hl, hr]
  linear_combination eij - a * A 0 j.succ * ei0 - a * A i.succ 0 * e0j +
    a ^ 2 * A i.succ 0 * A 0 j.succ * e00 +
    (F i.succ 0 * A 0 j.succ - A i.succ 0 * G 0 j.succ -
      a * A i.succ 0 * A 0 j.succ * (F 0 0 - G 0 0)) * ha

/-- **Theorem 12.1.1** in the book's form ([golub2013matrix]): for diagonal displacement operators
`Ω = diag(ω)`, `Λ = diag(ν)`, the Schur complement after one elimination step has the updated
generators with respect to `diag(ω₂, …)`, `diag(ν₂, …)`. -/
theorem sylvesterMap_diagonal_schurComplement {ω ν : Fin (N + 1) → K}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) K} {R S : Matrix (Fin (N + 1)) (Fin r) K}
    (h : sylvesterMap (diagonal ω) (diagonal ν) A = R * Sᵀ) (hα : A 0 0 ≠ 0) :
    sylvesterMap (diagonal (ω ∘ Fin.succ)) (diagonal (ν ∘ Fin.succ))
        (A.submatrix Fin.succ Fin.succ -
          (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) =
      (R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0)) *
        (S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0))ᵀ := by
  have hsub : ∀ d : Fin (N + 1) → K,
      (diagonal d).submatrix Fin.succ Fin.succ = diagonal (d ∘ Fin.succ) :=
    fun d => submatrix_diagonal _ _ (Fin.succ_injective _)
  rw [← hsub, ← hsub]
  exact sylvesterMap_schurComplement (fun j => diagonal_apply_ne _ (Fin.succ_ne_zero j).symm)
    (fun i => diagonal_apply_ne _ (Fin.succ_ne_zero i)) h hα

end Schur

/-! ### The cyclic shifts `Z_{±1}` -/

section CyclicShift

variable {n : ℕ}

/-- `(Z_φ A)_ij = A_{i−1, j}` below the first row. -/
theorem cyclicShift_mul_apply_of_pos (φ : K) (A : Matrix (Fin n) (Fin n) K) {i : Fin n}
    (hi : 0 < (i : ℕ)) (j : Fin n) :
    (cyclicShift n φ * A) i j = A ⟨i - 1, by omega⟩ j := by
  have := cyclicShift_mulVec_apply φ (fun l => A l j) i
  rw [dite_eq_right (by omega)] at this
  exact this

/-- `(A Z_φ)_ij = A_{i, j+1}` left of the last column. -/
theorem mul_cyclicShift_apply_of_lt (φ : K) (A : Matrix (Fin n) (Fin n) K) (i : Fin n)
    {j : Fin n} (hj : (j : ℕ) + 1 < n) :
    (A * cyclicShift n φ) i j = A i ⟨j + 1, hj⟩ := by
  rw [mul_apply, sum_eq_single ⟨j + 1, hj⟩]
  · rw [cyclicShift_apply, ite_eq_left rfl, mul_one]
  · intro l _ hl
    have hl' : (l : ℕ) ≠ j + 1 := fun h' => hl (Fin.ext h')
    rw [cyclicShift_apply, ite_eq_right hl', ite_eq_right (by omega), mul_zero]
  · simp

/-- `(Z_φᵀ A)_ij = A_{i+1, j}` above the last row. -/
theorem transpose_cyclicShift_mul_apply_of_lt (φ : K) (A : Matrix (Fin n) (Fin n) K) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) (j : Fin n) :
    ((cyclicShift n φ)ᵀ * A) i j = A ⟨i + 1, hi⟩ j := by
  rw [mul_apply, sum_eq_single ⟨i + 1, hi⟩]
  · rw [transpose_apply, cyclicShift_apply, ite_eq_left rfl, one_mul]
  · intro l _ hl
    have hl' : (l : ℕ) ≠ i + 1 := fun h' => hl (Fin.ext h')
    rw [transpose_apply, cyclicShift_apply, ite_eq_right hl', ite_eq_right (by omega), zero_mul]
  · simp

/-- **The `{Z₁, Z₋₁}` Sylvester operator is injective** ([golub2013matrix] P12.1.1(a), the
nonsingularity (12.1.2) presupposes for (12.1.8)): `Z₁ X = X Z₋₁` gives `Z₁ⁿ X = X Z₋₁ⁿ`, that is
`X = −X`. -/
theorem sylvesterMap_cyclicShift_one_neg_one_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (sylvesterMap (cyclicShift n (1 : K)) (cyclicShift n (-1))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero] at hX
  have hsc : SemiconjBy X (cyclicShift n (-1)) (cyclicShift n 1) := hX.symm
  have hpow := (hsc.pow_right n).eq
  rw [cyclicShift_pow_card, cyclicShift_pow_card, one_smul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul K X] at hpow
  exact (smul_eq_zero.mp hpow).resolve_left h2

/-- **The Toeplitz displacement is supported on the first row and the last column**
([golub2013matrix] (12.1.8)): for a Toeplitz `T`, `(Z₁ T − T Z₋₁)_ij = 0` for `0 < i` and
`j < n − 1`. -/
theorem sylvesterMap_cyclicShift_toeplitz_apply {T : Matrix (Fin n) (Fin n) K} (hT : T.IsToeplitz)
    {i j : Fin n} (hi : 0 < (i : ℕ)) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cyclicShift n 1) (cyclicShift n (-1)) T i j = 0 := by
  rw [sylvesterMap_apply, sub_apply, cyclicShift_mul_apply_of_pos _ _ hi,
    mul_cyclicShift_apply_of_lt _ _ _ hj, sub_eq_zero]
  exact isToeplitz_iff.mp hT _ _ _ _ (by simp only; omega)

/-- **The Hankel displacement is supported on the last row and the last column**
([golub2013matrix] (12.1.10)): for a Hankel `H`, `(Z₁ᵀ H − H Z₋₁)_ij = 0` for `i < n − 1` and
`j < n − 1`. -/
theorem sylvesterMap_cyclicShift_hankel_apply {H : Matrix (Fin n) (Fin n) K} (hH : H.IsHankel)
    {i j : Fin n} (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cyclicShift n 1)ᵀ (cyclicShift n (-1)) H i j = 0 := by
  obtain ⟨h, rfl⟩ := hH
  rw [sylvesterMap_apply, sub_apply, transpose_cyclicShift_mul_apply_of_lt _ _ hi,
    mul_cyclicShift_apply_of_lt _ _ _ hj, hankel_apply, hankel_apply, sub_eq_zero]
  congr 1
  simp only
  omega

end CyclicShift

/-! ### The corner-modified tridiagonal operators `Y_{0,0}`, `Y_{1,1}` -/

section CornerTridiagonal

variable {n : ℕ}

/-- Off the diagonal, `Y_{γ,δ}` is `tridiag(1, 0, 1)`. -/
theorem cornerTridiagonal_apply_of_ne (γ δ : ℝ) {i l : Fin n} (h : i ≠ l) :
    cornerTridiagonal n γ δ i l = if (i : ℕ) + 1 = l ∨ (l : ℕ) + 1 = i then 1 else 0 := by
  rw [cornerTridiagonal, add_apply, diagonal_apply_ne _ h, add_zero,
    symmTridiagonalToeplitz_apply', ite_eq_right (fun h' => h (Fin.ext h'))]

/-- Away from the two corners, the diagonal of `Y_{γ,δ}` vanishes. -/
theorem cornerTridiagonal_apply_self (γ δ : ℝ) {i : Fin n} (hi₀ : 0 < (i : ℕ))
    (hi : (i : ℕ) + 1 < n) : cornerTridiagonal n γ δ i i = 0 := by
  rw [cornerTridiagonal, add_apply, diagonal_apply_eq, symmTridiagonalToeplitz_apply',
    ite_eq_left rfl, ite_eq_right hi₀.ne', ite_eq_right hi.ne]
  ring

/-- A row `i` of `Y_{γ,δ}` away from the corners picks the two neighbours of `i`. -/
private theorem cornerTridiagonal_mul_apply_aux (γ δ : ℝ) {i : Fin n} (hi₀ : 0 < (i : ℕ))
    (hi : (i : ℕ) + 1 < n) (f : Fin n → ℝ) :
    ∑ l, cornerTridiagonal n γ δ i l * f l = f ⟨i - 1, by omega⟩ + f ⟨i + 1, hi⟩ := by
  have hterm : ∀ l, cornerTridiagonal n γ δ i l * f l =
      (if (l : ℕ) + 1 = i then f l else 0) + (if (l : ℕ) = i + 1 then f l else 0) := by
    intro l
    by_cases hil : i = l
    · subst hil
      rw [cornerTridiagonal_apply_self γ δ hi₀ hi, ite_eq_right (by omega),
        ite_eq_right (by omega)]
      ring
    · rw [cornerTridiagonal_apply_of_ne γ δ hil]
      split_ifs <;> first | omega | simp
  have h1 := sum_dite_val_add_one_eq i (fun l (_ : (l : ℕ) + 1 = i) => f l)
  have h2 := sum_dite_val_eq_add_one i (fun l (_ : (l : ℕ) = i + 1) => f l)
  simp only [dite_eq_ite] at h1 h2
  rw [sum_congr rfl fun l _ => hterm l, sum_add_distrib, h1, h2, dite_eq_left hi₀,
    dite_eq_left hi]

/-- `Y_{γ,δ}` is symmetric. -/
theorem cornerTridiagonal_transpose (γ δ : ℝ) :
    (cornerTridiagonal n γ δ)ᵀ = cornerTridiagonal n γ δ := by
  ext i l
  rw [transpose_apply]
  by_cases h : i = l
  · rw [h]
  · rw [cornerTridiagonal_apply_of_ne γ δ h, cornerTridiagonal_apply_of_ne γ δ (Ne.symm h)]
    exact if_congr or_comm rfl rfl

/-- Away from the first and last row, `(Y_{γ,δ} A)_ij = A_{i−1, j} + A_{i+1, j}`. -/
theorem cornerTridiagonal_mul_apply (γ δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) {i : Fin n}
    (hi₀ : 0 < (i : ℕ)) (hi : (i : ℕ) + 1 < n) (j : Fin n) :
    (cornerTridiagonal n γ δ * A) i j = A ⟨i - 1, by omega⟩ j + A ⟨i + 1, hi⟩ j := by
  rw [mul_apply]
  exact cornerTridiagonal_mul_apply_aux γ δ hi₀ hi fun l => A l j

/-- Away from the first and last column, `(A Y_{γ,δ})_ij = A_{i, j−1} + A_{i, j+1}`. -/
theorem mul_cornerTridiagonal_apply (γ δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    {j : Fin n} (hj₀ : 0 < (j : ℕ)) (hj : (j : ℕ) + 1 < n) :
    (A * cornerTridiagonal n γ δ) i j = A i ⟨j - 1, by omega⟩ + A i ⟨j + 1, hj⟩ := by
  rw [mul_apply, ← cornerTridiagonal_mul_apply_aux γ δ hj₀ hj fun l => A i l]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_comm, ← transpose_apply (cornerTridiagonal n γ δ), cornerTridiagonal_transpose]

/-- **The `{Y₀₀, Y₁₁}` displacement of a Toeplitz matrix is supported on the border**
([golub2013matrix] (12.1.9)): `(Y₀₀ T − T Y₁₁)_ij = 0` for `0 < i < n − 1` and `0 < j < n − 1`,
since `T_{i−1,j} + T_{i+1,j} = T_{i,j−1} + T_{i,j+1}`. -/
theorem sylvesterMap_cornerTridiagonal_toeplitz_apply {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsToeplitz) {i j : Fin n} (hi₀ : 0 < (i : ℕ)) (hi : (i : ℕ) + 1 < n)
    (hj₀ : 0 < (j : ℕ)) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) T i j = 0 := by
  rw [sylvesterMap_apply, sub_apply, cornerTridiagonal_mul_apply _ _ _ hi₀ hi,
    mul_cornerTridiagonal_apply _ _ _ _ hj₀ hj,
    isToeplitz_iff.mp hT ⟨i - 1, by omega⟩ j i ⟨j + 1, hj⟩ (by simp only; omega),
    isToeplitz_iff.mp hT ⟨i + 1, hi⟩ j i ⟨j - 1, by omega⟩ (by simp only; omega)]
  ring

/-- **The `{Y₀₀, Y₁₁}` displacement of a Hankel matrix is supported on the border**
([golub2013matrix] (12.1.11)): `(Y₀₀ H − H Y₁₁)_ij = 0` for `0 < i < n − 1` and `0 < j < n − 1`,
since `H_{i−1,j} + H_{i+1,j} = H_{i,j−1} + H_{i,j+1}`. -/
theorem sylvesterMap_cornerTridiagonal_hankel_apply {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHankel) {i j : Fin n} (hi₀ : 0 < (i : ℕ)) (hi : (i : ℕ) + 1 < n)
    (hj₀ : 0 < (j : ℕ)) (hj : (j : ℕ) + 1 < n) :
    sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) H i j = 0 := by
  obtain ⟨h, rfl⟩ := hH
  rw [sylvesterMap_apply, sub_apply, cornerTridiagonal_mul_apply _ _ _ hi₀ hi,
    mul_cornerTridiagonal_apply _ _ _ _ hj₀ hj]
  simp only [hankel_apply]
  rw [show (i : ℕ) - 1 + j = i + (j - 1) by omega, show (i : ℕ) + 1 + j = i + (j + 1) by omega]
  ring

/-- A vector orthogonal to an orthogonal family of `n` nonzero vectors in `ℝⁿ` is zero. -/
private theorem eq_zero_of_forall_dotProduct_eq_zero {v : Fin n → Fin n → ℝ}
    (horth : ∀ k l, k ≠ l → v k ⬝ᵥ v l = 0) (hpos : ∀ k, v k ⬝ᵥ v k ≠ 0) {w : Fin n → ℝ}
    (hw : ∀ k, v k ⬝ᵥ w = 0) : w = 0 := by
  set V : Matrix (Fin n) (Fin n) ℝ := of v
  have hVV : V * Vᵀ = diagonal fun k => v k ⬝ᵥ v k := by
    ext k l
    rw [mul_apply, diagonal_apply]
    change v k ⬝ᵥ v l = _
    split_ifs with h
    · rw [h]
    · exact horth k l h
  have hD : (diagonal fun k => v k ⬝ᵥ v k) * diagonal (fun k => (v k ⬝ᵥ v k)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hpos k)
  have hinv : (Vᵀ * diagonal fun k => (v k ⬝ᵥ v k)⁻¹) * V = 1 := by
    rw [mul_eq_one_comm, ← Matrix.mul_assoc, hVV, hD]
  have hVw : V *ᵥ w = 0 := funext hw
  rw [← one_mulVec w, ← hinv, ← mulVec_mulVec, hVw, mulVec_zero]

/-- The eigenvalues `2 cos((k+1)π/(n+1))` of `Y₀₀` and `2 cos(lπ/n)` of `Y₁₁` are distinct. -/
private theorem cos_ne_cos {k l : Fin n} :
    2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) ≠
      2 * Real.cos ((l : ℕ) * Real.pi / n) := by
  intro h
  have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
  have hk := k.isLt
  have hl := l.isLt
  have h1 : (((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) = (l : ℕ) * Real.pi / n := by
    refine Real.injOn_cos ⟨by positivity, ?_⟩ ⟨by positivity, ?_⟩ (by linarith)
    · rw [div_le_iff₀ (by positivity)]
      have : ((k : ℕ) : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : (k : ℕ) + 1 ≤ n + 1)
      have := mul_le_mul_of_nonneg_right this Real.pi_pos.le
      linarith
    · rw [div_le_iff₀ hn]
      have : ((l : ℕ) : ℝ) ≤ n := by exact_mod_cast hl.le
      have := mul_le_mul_of_nonneg_right this Real.pi_pos.le
      linarith
  have h2 : (((k : ℕ) + 1) * n : ℕ) = ((l : ℕ) * (n + 1) : ℕ) := by
    rw [div_eq_div_iff (by positivity) hn.ne'] at h1
    have h1' : (((k : ℕ) : ℝ) + 1) * n * Real.pi = (l : ℕ) * ((n : ℝ) + 1) * Real.pi := by
      linear_combination h1
    exact_mod_cast mul_right_cancel₀ Real.pi_pos.ne' h1'
  have hdvd : n + 1 ∣ (k + 1) * n := ⟨l, by rw [h2]; ring⟩
  have hcop : Nat.Coprime (n + 1) n := by
    rw [Nat.coprime_self_add_left]
    exact Nat.coprime_one_left n
  have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvd)
  omega

/-- **The `{Y₀₀, Y₁₁}` Sylvester operator is injective** ([golub2013matrix] P12.1.1(b), the book's
"`λ(Y₀₀) ∩ λ(Y₁₁) = ∅`"): the spectra `{2 cos((k+1)π/(n+1))}` and `{2 cos(lπ/n)}` are disjoint,
and both matrices have orthogonal eigenbases (the DST-I and DCT-II vectors), so
`s_kᵀ (Y₀₀ X − X Y₁₁) c_l = (λ_k − μ_l) s_kᵀ X c_l` forces `X = 0`. -/
theorem sylvesterMap_cornerTridiagonal_injective :
    Function.Injective (sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero, cornerTridiagonal_zero_zero] at hX
  have hsymm : (symmTridiagonalToeplitz n 1 0)ᵀ = symmTridiagonalToeplitz n 1 0 := by
    rw [← cornerTridiagonal_zero_zero]
    exact cornerTridiagonal_transpose 0 0
  -- `X c_l = 0` for every DCT-II vector `c_l`
  have hcol : ∀ l : Fin n, X *ᵥ cosineIIVec n l = 0 := by
    intro l
    refine eq_zero_of_forall_dotProduct_eq_zero (v := sineVec n)
      (fun k k' h => by rw [dotProduct_sineVec, ite_eq_right h])
      (fun k => by rw [dotProduct_sineVec, ite_eq_left rfl]; positivity) fun k => ?_
    have e1 : sineVec n k ⬝ᵥ (symmTridiagonalToeplitz n 1 0 *ᵥ (X *ᵥ cosineIIVec n l)) =
        (2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) *
          (sineVec n k ⬝ᵥ (X *ᵥ cosineIIVec n l)) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, symmTridiagonalToeplitz_mulVec_sineVec,
        smul_dotProduct, smul_eq_mul]
      ring
    have e2 : sineVec n k ⬝ᵥ (X *ᵥ (cornerTridiagonal n 1 1 *ᵥ cosineIIVec n l)) =
        (2 * Real.cos ((l : ℕ) * Real.pi / n)) * (sineVec n k ⬝ᵥ (X *ᵥ cosineIIVec n l)) := by
      rw [cornerTridiagonal_one_one_mulVec_cosineIIVec, mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [mulVec_mulVec, hX, ← mulVec_mulVec, e2] at e1
    have := sub_eq_zero.mpr e1
    rw [← sub_mul, mul_eq_zero] at this
    exact this.resolve_left (sub_ne_zero.mpr (cos_ne_cos (k := k) (l := l)).symm)
  -- then every row of `X` is orthogonal to the DCT-II basis
  ext i j
  have hrow : X i = 0 := by
    refine eq_zero_of_forall_dotProduct_eq_zero (v := cosineIIVec n)
      (fun k k' h => by rw [dotProduct_cosineIIVec, ite_eq_right h])
      (fun k => by
        have : (0 : ℝ) < n := by exact_mod_cast k.pos
        rw [dotProduct_cosineIIVec, ite_eq_left rfl]
        split_ifs <;> positivity) fun l => ?_
    rw [dotProduct_comm]
    exact congrFun (hcol l) i
  simpa using congrFun hrow j

end CornerTridiagonal

/-! ### Displacement rank bounds -/

section Bounds

/-- **Generators exist exactly up to the displacement rank** ([golub2013matrix] (12.1.3)):
`displacementRank F G A ≤ r` iff `F A − A G = R Sᵀ` for some `R S : Matrix n (Fin r) K`. -/
theorem displacementRank_le_iff_exists {n : Type*} [Fintype n] {F G A : Matrix n n K} {r : ℕ} :
    displacementRank F G A ≤ r ↔
      ∃ R S : Matrix n (Fin r) K, sylvesterMap F G A = R * Sᵀ :=
  rank_le_iff_exists_mul_transpose _ r

/-- The consequence of Theorem 12.1.1 displayed after its proof ([golub2013matrix] §12.1.3): one
step of Gaussian elimination does not increase the `{diag(ω), diag(ν)}`-displacement rank. -/
theorem displacementRank_diagonal_schurComplement_le {N r : ℕ} {ω ν : Fin (N + 1) → K}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) K}
    (h : displacementRank (diagonal ω) (diagonal ν) A ≤ r) (hα : A 0 0 ≠ 0) :
    displacementRank (diagonal (ω ∘ Fin.succ)) (diagonal (ν ∘ Fin.succ))
      (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) ≤ r := by
  obtain ⟨R, S, hRS⟩ := displacementRank_le_iff_exists.mp h
  exact displacementRank_le_iff_exists.mpr ⟨_, _, sylvesterMap_diagonal_schurComplement hRS hα⟩

variable {n : ℕ}

/-- A square matrix vanishing outside row `a` and column `b` has rank at most `2`. -/
private theorem rank_le_two_of_forall {A : Matrix (Fin n) (Fin n) K} (a b : Fin n)
    (h : ∀ i j, i ≠ a → j ≠ b → A i j = 0) : A.rank ≤ 2 :=
  (rank_le_card_add_card_of_forall_ne_zero A {a} {b} fun i j hij => by
    by_contra hc
    simp only [Finset.mem_singleton, not_or] at hc
    exact hij (h i j hc.1 hc.2)).trans (by simp)

/-- A square matrix vanishing outside rows `a`, `b` and columns `a`, `b` has rank at most `4`. -/
private theorem rank_le_four_of_forall {A : Matrix (Fin n) (Fin n) K} (a b : Fin n)
    (h : ∀ i j, i ≠ a → i ≠ b → j ≠ a → j ≠ b → A i j = 0) : A.rank ≤ 4 := by
  have hc : ({a, b} : Finset (Fin n)).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  refine (rank_le_card_add_card_of_forall_ne_zero A {a, b} {a, b} fun i j hij => ?_).trans
    (by omega)
  by_contra hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  exact hij (h i j hne.1.1 hne.1.2 hne.2.1 hne.2.2)

/-- The empty matrix has rank `0`. -/
private theorem rank_fin_zero (A : Matrix (Fin 0) (Fin 0) K) : A.rank = 0 :=
  Nat.le_zero.mp ((rank_le_card_width A).trans (by simp))

/-- **Toeplitz matrices have `{Z₁, Z₋₁}`-displacement rank at most `2`** ([golub2013matrix]
(12.1.8)): the displacement is supported on the first row and the last column. -/
theorem displacementRank_cyclicShift_toeplitz_le {T : Matrix (Fin n) (Fin n) K}
    (hT : T.IsToeplitz) : displacementRank (cyclicShift n 1) (cyclicShift n (-1)) T ≤ 2 := by
  rcases n with _ | N
  · rw [displacementRank, rank_fin_zero]; omega
  refine rank_le_two_of_forall 0 (Fin.last N) fun i j hi hj => ?_
  have hi' : (i : ℕ) ≠ 0 := fun h' => hi (Fin.ext h')
  have hj' : (j : ℕ) ≠ N := fun h' => hj (Fin.ext h')
  exact sylvesterMap_cyclicShift_toeplitz_apply hT (by omega) (by omega)

/-- **Hankel matrices have `{Z₁ᵀ, Z₋₁}`-displacement rank at most `2`** ([golub2013matrix]
(12.1.10)): the displacement is supported on the last row and the last column. -/
theorem displacementRank_cyclicShift_hankel_le {H : Matrix (Fin n) (Fin n) K}
    (hH : H.IsHankel) : displacementRank (cyclicShift n 1)ᵀ (cyclicShift n (-1)) H ≤ 2 := by
  rcases n with _ | N
  · rw [displacementRank, rank_fin_zero]; omega
  refine rank_le_two_of_forall (Fin.last N) (Fin.last N) fun i j hi hj => ?_
  have hi' : (i : ℕ) ≠ N := fun h' => hi (Fin.ext h')
  have hj' : (j : ℕ) ≠ N := fun h' => hj (Fin.ext h')
  exact sylvesterMap_cyclicShift_hankel_apply hH (by omega) (by omega)

/-- A real matrix whose `{Y₀₀, Y₁₁}`-displacement vanishes off the border has displacement rank
at most `4`. -/
private theorem displacementRank_cornerTridiagonal_le_of_border {A : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) + 1 < n → 0 < (j : ℕ) → (j : ℕ) + 1 < n →
      sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) A i j = 0) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) A ≤ 4 := by
  rcases n with _ | N
  · rw [displacementRank, rank_fin_zero]; omega
  refine rank_le_four_of_forall 0 (Fin.last N) fun i j hi0 hiN hj0 hjN => ?_
  have hi0' : (i : ℕ) ≠ 0 := fun h' => hi0 (Fin.ext h')
  have hiN' : (i : ℕ) ≠ N := fun h' => hiN (Fin.ext h')
  have hj0' : (j : ℕ) ≠ 0 := fun h' => hj0 (Fin.ext h')
  have hjN' : (j : ℕ) ≠ N := fun h' => hjN (Fin.ext h')
  exact h i j (by omega) (by omega) (by omega) (by omega)

/-- **Toeplitz matrices have `{Y₀₀, Y₁₁}`-displacement rank at most `4`** ([golub2013matrix]
(12.1.9)): the displacement is supported on the border. -/
theorem displacementRank_cornerTridiagonal_toeplitz_le {T : Matrix (Fin n) (Fin n) ℝ}
    (hT : T.IsToeplitz) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) T ≤ 4 :=
  displacementRank_cornerTridiagonal_le_of_border fun _ _ hi₀ hi hj₀ hj =>
    sylvesterMap_cornerTridiagonal_toeplitz_apply hT hi₀ hi hj₀ hj

/-- **Hankel matrices have `{Y₀₀, Y₁₁}`-displacement rank at most `4`** ([golub2013matrix]
(12.1.11)). -/
theorem displacementRank_cornerTridiagonal_hankel_le {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHankel) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) H ≤ 4 :=
  displacementRank_cornerTridiagonal_le_of_border fun _ _ hi₀ hi hj₀ hj =>
    sylvesterMap_cornerTridiagonal_hankel_apply hH hi₀ hi hj₀ hj

/-- **Toeplitz-plus-Hankel matrices have `{Y₀₀, Y₁₁}`-displacement rank at most `4`**
([golub2013matrix], the display after (12.1.11)): the displacement is linear, and both
displacements vanish off the border. -/
theorem displacementRank_cornerTridiagonal_toeplitz_add_hankel_le
    {T H : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) (hH : H.IsHankel) :
    displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) (T + H) ≤ 4 :=
  displacementRank_cornerTridiagonal_le_of_border fun _ _ hi₀ hi hj₀ hj => by
    rw [map_add, add_apply, sylvesterMap_cornerTridiagonal_toeplitz_apply hT hi₀ hi hj₀ hj,
      sylvesterMap_cornerTridiagonal_hankel_apply hH hi₀ hi hj₀ hj, add_zero]

end Bounds

end Matrix
