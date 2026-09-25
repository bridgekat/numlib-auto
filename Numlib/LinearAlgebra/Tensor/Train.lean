/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Tensor.Unfolding

/-!
# Tensor trains

A tensor train ([golub2013matrix] §12.5.8, (12.5.25)–(12.5.29); Oseledets–Tyrtyshnikov 2009) with
mode sizes `n : ℕ → ℕ` and ranks `r : ℕ → ℕ`, `r 0 = r d = 1`, is given by cores
`G k : Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) R`: the book's carriages
`𝒢_k ∈ ℝ^{r_{k−1} × n_k × r_k}` read as matrix-valued functions of the middle index. The entry
`𝒯(i)` is the `1 × 1` matrix product `G 0 (i 0) ⋯ G (d − 1) (i (d − 1))`. The partial products are
defined by recursion on `d` with `Fin.castSucc`/`Fin.last`, which reduces definitionally.

## Main definitions

* `Tensor.ttPartial G d i`: the left partial product `G 0 (i 0) ⋯ G (d − 1) (i (d − 1))`.
* `Tensor.tensorTrain d h0 hd G`: the tensor train.

## Main statements

* `Tensor.exists_ttCore_of_rank`: one step of the TT-SVD, a core from a rank factorization.

## References

* [golub2013matrix], §12.5.8.
-/

universe u

open Matrix

namespace Tensor

variable {R : Type u} [CommSemiring R] {n r : ℕ → ℕ}

/-- The left partial products of a tensor train ([golub2013matrix] §12.5.8):
`ttPartial G d i = G 0 (i 0) * ⋯ * G (d − 1) (i (d − 1))`, an `r 0 × r d` matrix. -/
def ttPartial (G : ∀ k, Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) R) :
    ∀ d : ℕ, (∀ k : Fin d, Fin (n k)) → Matrix (Fin (r 0)) (Fin (r d)) R
  | 0, _ => 1
  | d + 1, i => ttPartial G d (fun k => i k.castSucc) * G d (i (Fin.last d))

variable (G : ∀ k, Fin (n k) → Matrix (Fin (r k)) (Fin (r (k + 1))) R)

@[simp]
theorem ttPartial_zero (i : ∀ k : Fin 0, Fin (n k)) : ttPartial G 0 i = 1 :=
  rfl

theorem ttPartial_succ (d : ℕ) (i : ∀ k : Fin (d + 1), Fin (n k)) :
    ttPartial G (d + 1) i = ttPartial G d (fun k => i k.castSucc) * G d (i (Fin.last d)) :=
  rfl

/-- The entries of the partial products: a sum over the rank index of the last contraction. -/
theorem ttPartial_succ_apply (d : ℕ) (i : ∀ k : Fin (d + 1), Fin (n k)) (p : Fin (r 0))
    (q : Fin (r (d + 1))) :
    ttPartial G (d + 1) i p q
      = ∑ s, ttPartial G d (fun k => i k.castSucc) p s * G d (i (Fin.last d)) s q :=
  mul_apply

/-- The tensor train ([golub2013matrix] (12.5.25)) with boundary ranks `r 0 = r d = 1`:
`𝒯(i) = 𝒢₁(i₁) 𝒢₂(i₂) ⋯ 𝒢_d(i_d)`, a `1 × 1` product. -/
def tensorTrain (d : ℕ) (h0 : r 0 = 1) (hd : r d = 1) :
    Tensor (fun k : Fin d => Fin (n k)) R :=
  of fun i => ttPartial G d i (Fin.cast h0.symm 0) (Fin.cast hd.symm 0)

theorem tensorTrain_apply (d : ℕ) (h0 : r 0 = 1) (hd : r d = 1) (i : ∀ k : Fin d, Fin (n k)) :
    tensorTrain G d h0 hd i = ttPartial G d i (Fin.cast h0.symm 0) (Fin.cast hd.symm 0) :=
  rfl

/-- One step of the TT-SVD construction ([golub2013matrix] (12.5.26)–(12.5.28), P12.5.11): a
matrix `C` whose rows are indexed by a previous rank index `k` and the next mode `i`, of rank at
most `s`, factors through a core: `C (k, i) c = (G i * C') k c` with `G i : p × s` (the book takes
`G' = U₃`, `C' = Σ₃ V₃ᵀ` from an SVD; any rank factorization works). -/
theorem exists_ttCore_of_rank {K : Type*} [Field K] {p m s : ℕ} {N : Type*} [Fintype N]
    (C : Matrix (Fin p × Fin m) N K) (hC : C.rank ≤ s) :
    ∃ (G : Fin m → Matrix (Fin p) (Fin s) K) (C' : Matrix (Fin s) N K),
      ∀ k i c, C (k, i) c = (G i * C') k c := by
  obtain ⟨G', C', h⟩ := (Matrix.rank_le_iff_exists_mul C s).1 hC
  refine ⟨fun i => Matrix.of fun k k' => G' (k, i) k', C', fun k i c => ?_⟩
  rw [h, mul_apply, mul_apply]
  rfl

end Tensor
