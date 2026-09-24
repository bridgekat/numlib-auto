/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Orthogonal bidiagonalization

Every rectangular matrix is carried by a unitary matrix on each side to an upper bidiagonal one,
`Uᴴ A V = B`: the **Golub–Kahan bidiagonalization** ([golub2013matrix] §5.4.8, (5.4.13);
[quarteroni2000numerical] (5.57); Golub–Kahan 1965), the first stage of every algorithm for the
singular value decomposition and the matrix form of the Golub–Kahan–Lanczos process of
`Numlib/Krylov/Bidiagonalization`.

## Main results

* `Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero`: entrywise, for any `M × N` matrix, the
  entries of `Uᴴ A V` off the diagonal and the first superdiagonal vanish. Tail reflectors
  (`Matrix.householderTail` of `Numlib/LinearAlgebra/Matrix/QR`) alternate on the left (column
  `k`, pivot `k`) and on the right (row `k`, pivot `k + 1`); the right reflector's axis vanishes on
  the columns `≤ k`, so the zeros already created survive.
* `Matrix.exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal`: for `N ≤ M`, `Uᴴ A V` is zero
  below row `N` and upper bidiagonal (`Matrix.IsUpperBidiagonal` of
  `Numlib/LinearAlgebra/Matrix/Hessenberg`) on top.

## Implementation notes

The square bidiagonal shapes `Matrix.IsUpperBidiagonal`, `Matrix.IsLowerBidiagonal` are phrased with
the order on the index and live in `Numlib/LinearAlgebra/Matrix/Hessenberg`; the statements here
are on `Fin M × Fin N`, with the index difference taken in `ℕ` as in the rectangular band
vocabulary of `Numlib/LinearAlgebra/Matrix/Band`.

## References

* [golub2013matrix] §5.4.8.
* [quarteroni2000numerical] §5.8.3.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Golub–Kahan bidiagonalization -/

section Bidiagonal

variable {M N : ℕ}

/-- The left half-step of the bidiagonalization: the tail reflector of column `k` with pivot `k`
clears that column below the diagonal, keeps the rows before `k` and the columns already cleared. -/
private theorem bidiag_left_step (B : Matrix (Fin M) (Fin N) 𝕜) {k : ℕ} (hk : k < N)
    (hB : ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k) → (i : ℕ) ≠ j →
      (i : ℕ) + 1 ≠ j → B i j = 0) :
    ∃ P : Matrix (Fin M) (Fin M) 𝕜, P.IsHermitian ∧ P ∈ Matrix.unitaryGroup (Fin M) 𝕜 ∧
      ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k + 1) → (i : ℕ) ≠ j →
        (i : ℕ) + 1 ≠ j → (P * B) i j = 0 := by
  refine ⟨householder (householderTail (fun i => B i ⟨k, hk⟩) k), isHermitian_householder _,
    householder_householderTail_mem_unitaryGroup _ _, fun i j hij hne1 hne2 => ?_⟩
  rcases hij with hi | hj
  · rw [householder_mul_apply_of_apply_eq_zero (householderTail_apply_of_lt _ hi)]
    exact hB i j (Or.inl hi) hne1 hne2
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · rw [householder_mul_apply, householder_mulVec_eq_self_of_apply_eq_zero fun r hr => ?_]
    · exact hB i j (Or.inr hjk) hne1 hne2
    · have hkr : k ≤ (r : ℕ) := not_lt.1 fun hrk => hr (householderTail_apply_of_lt _ hrk)
      exact hB r j (Or.inr hjk) (by omega) (by omega)
  · have hjκ : j = ⟨k, hk⟩ := Fin.ext hjk
    subst hjκ
    rw [householder_mul_apply]
    rcases lt_or_gt_of_ne hne1 with hik | hik
    · rw [householder_householderTail_mulVec_apply_of_lt _ hik]
      exact hB i _ (Or.inl hik) hne1 hne2
    · exact householder_householderTail_mulVec_apply_of_gt _ hik

/-- The right half-step of the bidiagonalization: the reflector of the conjugate tail axis of row
`k` with pivot `k + 1` clears that row beyond the superdiagonal, keeps the columns `≤ k` and the
rows already cleared. -/
private theorem bidiag_right_step (B : Matrix (Fin M) (Fin N) 𝕜) {k : ℕ} (hk : k < M)
    (hB : ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k + 1) → (i : ℕ) ≠ j →
      (i : ℕ) + 1 ≠ j → B i j = 0) :
    ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k + 1 ∨ (j : ℕ) < k + 1) → (i : ℕ) ≠ j →
        (i : ℕ) + 1 ≠ j → (B * V) i j = 0 := by
  refine ⟨householder (star (householderTail (fun j => B ⟨k, hk⟩ j) (k + 1))),
    householder_star_householderTail_mem_unitaryGroup _ _, fun i j hij hne1 hne2 => ?_⟩
  rcases hij with hi | hj
  swap
  · rw [mul_householder_apply_of_apply_eq_zero
      (by rw [Pi.star_apply, householderTail_apply_of_lt _ hj, star_zero])]
    exact hB i j (Or.inr hj) hne1 hne2
  rw [mul_householder_star_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | hik
  · rw [householder_mulVec_eq_self_of_apply_eq_zero fun r hr => ?_]
    · exact hB i j (Or.inl hik) hne1 hne2
    · have hkr : k + 1 ≤ (r : ℕ) := not_lt.1 fun hrk => hr (householderTail_apply_of_lt _ hrk)
      exact hB i r (Or.inl hik) (by omega) (by omega)
  · have hiκ : i = ⟨k, hk⟩ := Fin.ext hik
    subst hiκ
    rcases lt_or_gt_of_ne hne2 with hjk | hjk
    · exact householder_householderTail_mulVec_apply_of_gt _ hjk
    · rw [householder_householderTail_mulVec_apply_of_lt _ hjk]
      exact hB _ j (Or.inr hjk) hne1 hne2

/-- **The Golub–Kahan bidiagonalization**, entrywise ([quarteroni2000numerical] (5.57);
[golub1989matrix] §5.4.3): any rectangular matrix is carried by a unitary matrix on each side to
one whose only nonzero entries lie on the diagonal and the first superdiagonal. Alternating tail
reflectors on the left (column `k`, pivot `k`) and on the right (row `k`, pivot `k + 1`); the
right reflector's axis vanishes on the columns `≤ k`, so the zeros already created survive. -/
theorem exists_unitary_mul_mul_unitary_apply_eq_zero (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U ∈ Matrix.unitaryGroup (Fin M) 𝕜, ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin M) (j : Fin N), (i : ℕ) ≠ j → (i : ℕ) + 1 ≠ j → (Uᴴ * A * V) i j = 0 := by
  suffices h : ∀ k : ℕ, ∃ U ∈ Matrix.unitaryGroup (Fin M) 𝕜, ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin M) (j : Fin N), ((i : ℕ) < k ∨ (j : ℕ) < k) → (i : ℕ) ≠ j → (i : ℕ) + 1 ≠ j →
        (Uᴴ * A * V) i j = 0 by
    obtain ⟨U, hU, V, hV, h⟩ := h N
    exact ⟨U, hU, V, hV, fun i j => h i j (Or.inr j.isLt)⟩
  intro k
  induction k with
  | zero => exact ⟨1, one_mem _, 1, one_mem _, fun i j hij => absurd hij (by simp)⟩
  | succ k ih =>
    obtain ⟨U, hU, V, hV, hB⟩ := ih
    by_cases hkN : k < N
    swap
    · refine ⟨U, hU, V, hV, fun i j hij => hB i j ?_⟩
      rcases hij with hi | hj
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (by have := j.isLt; omega)
      · exact Or.inr (by have := j.isLt; omega)
    obtain ⟨P, hPh, hPu, hPB⟩ := bidiag_left_step (Uᴴ * A * V) hkN hB
    have hUP : (U * P)ᴴ * A * V = P * (Uᴴ * A * V) := by
      rw [conjTranspose_mul, hPh.eq]
      simp only [Matrix.mul_assoc]
    by_cases hkM : k < M
    swap
    · refine ⟨U * P, mul_mem hU hPu, V, hV, fun i j hij hne1 hne2 => ?_⟩
      rw [hUP]
      refine hPB i j ?_ hne1 hne2
      rcases hij with hi | hj
      · exact Or.inl (by have := i.isLt; omega)
      · exact Or.inr hj
    obtain ⟨W, hWu, hWB⟩ := bidiag_right_step (P * (Uᴴ * A * V)) hkM hPB
    refine ⟨U * P, mul_mem hU hPu, V * W, mul_mem hV hWu, fun i j hij hne1 hne2 => ?_⟩
    rw [← Matrix.mul_assoc, hUP]
    exact hWB i j hij hne1 hne2

/-- **The Golub–Kahan bidiagonalization** ([quarteroni2000numerical] (5.57); [golub1989matrix]
§5.4.3): for `A : Matrix (Fin M) (Fin N) 𝕜` with `N ≤ M` there are unitary `U`, `V` with
`Uᴴ A V = (B; 0)`, zero below row `N` and upper bidiagonal on top. This is the first phase of the
Golub–Kahan–Reinsch computation of the singular value decomposition. -/
theorem exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal (h : N ≤ M)
    (A : Matrix (Fin M) (Fin N) 𝕜) :
    ∃ U ∈ Matrix.unitaryGroup (Fin M) 𝕜, ∃ V ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      (∀ (i : Fin M) (j : Fin N), N ≤ (i : ℕ) → (Uᴴ * A * V) i j = 0) ∧
        ((Uᴴ * A * V).submatrix (Fin.castLE h) id).IsUpperBidiagonal := by
  obtain ⟨U, hU, V, hV, hB⟩ := exists_unitary_mul_mul_unitary_apply_eq_zero A
  refine ⟨U, hU, V, hV, fun i j hi =>
    hB i j (by have := j.isLt; omega) (by have := j.isLt; omega), ?_⟩
  intro i j hij
  rw [submatrix_apply, id]
  rcases hij with hji | ⟨l, hil, hlj⟩
  · have h1 := Fin.lt_def.1 hji
    exact hB _ _ (by simp; omega) (by simp; omega)
  · have h1 := Fin.lt_def.1 hil
    have h2 := Fin.lt_def.1 hlj
    exact hB _ _ (by simp; omega) (by simp; omega)

end Bidiagonal

end Matrix
