/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.UnitaryGroup`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Ordered products of a sequence of matrices

The products of the first `r` terms of a sequence `P : ℕ → Matrix ι ι α` of square matrices, in
the two orders in which a sequence of transformations accumulates:

* `Matrix.prodRev P r = P (r-1) * ⋯ * P 1 * P 0`, each new factor multiplying on the left — the
  accumulated transformation `Q_r` of `x_{k+1} = P_k x_k`, as in the backward error analysis of a
  sequence of Householder or Givens transformations ([higham2002accuracy] Lemma 19.3);
* `Matrix.prodFwd P r = P 0 * P 1 * ⋯ * P (r-1)`, each new factor multiplying on the right — the
  orthogonal factor `Q = Q₁ ⋯ Q_r` of a factorization built one reflector at a time
  ([golub2013matrix] §5.1.6–5.1.7, the WY representations).

Both are recursions on `r`, so statements about them are inductions on `r` with no `Fin` casts.
A product of members of a submonoid stays in it, so products of unitary or orthogonal matrices are
unitary or orthogonal (`Matrix.prodRev_mem_unitaryGroup`, `Matrix.prodRev_mem_orthogonalGroup`),
and the transpose of a forward product is the reverse product of the transposes
(`Matrix.transpose_prodFwd`).
-/

namespace Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring α]

/-- `P (r-1) * ⋯ * P 1 * P 0`: the product of the first `r` matrices of a sequence, each new one
multiplying on the left. -/
def prodRev (P : ℕ → Matrix ι ι α) : ℕ → Matrix ι ι α
  | 0 => 1
  | r + 1 => P r * prodRev P r

/-- `P 0 * P 1 * ⋯ * P (r-1)`: the product of the first `r` matrices of a sequence, each new one
multiplying on the right. -/
def prodFwd (P : ℕ → Matrix ι ι α) : ℕ → Matrix ι ι α
  | 0 => 1
  | r + 1 => prodFwd P r * P r

/-- The empty product is the identity. -/
@[simp]
theorem prodRev_zero (P : ℕ → Matrix ι ι α) : prodRev P 0 = 1 := rfl

/-- One more factor on the left. -/
theorem prodRev_succ (P : ℕ → Matrix ι ι α) (r : ℕ) : prodRev P (r + 1) = P r * prodRev P r :=
  rfl

/-- The empty product is the identity. -/
@[simp]
theorem prodFwd_zero (P : ℕ → Matrix ι ι α) : prodFwd P 0 = 1 := rfl

/-- One more factor on the right. -/
theorem prodFwd_succ (P : ℕ → Matrix ι ι α) (r : ℕ) : prodFwd P (r + 1) = prodFwd P r * P r :=
  rfl

/-- A reverse product of members of a submonoid is a member. -/
theorem prodRev_mem {S : Submonoid (Matrix ι ι α)} {P : ℕ → Matrix ι ι α} (hP : ∀ k, P k ∈ S)
    (r : ℕ) : prodRev P r ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih => exact S.mul_mem (hP r) ih

/-- A forward product of members of a submonoid is a member. -/
theorem prodFwd_mem {S : Submonoid (Matrix ι ι α)} {P : ℕ → Matrix ι ι α} (hP : ∀ k, P k ∈ S)
    (r : ℕ) : prodFwd P r ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih => exact S.mul_mem ih (hP r)

end Semiring

/-- The transpose of `prodFwd P r` is `prodRev Pᵀ r`. -/
theorem transpose_prodFwd [CommSemiring α] (P : ℕ → Matrix ι ι α) (r : ℕ) :
    (prodFwd P r)ᵀ = prodRev (fun k => (P k)ᵀ) r := by
  induction r with
  | zero => simp
  | succ r ih => rw [prodFwd_succ, transpose_mul, ih, prodRev_succ]

/-- The product of unitary matrices is unitary. -/
theorem prodRev_mem_unitaryGroup [CommRing α] [StarRing α] {P : ℕ → Matrix ι ι α}
    (hP : ∀ k, P k ∈ Matrix.unitaryGroup ι α) (r : ℕ) :
    prodRev P r ∈ Matrix.unitaryGroup ι α :=
  prodRev_mem hP r

/-- The product of unitary matrices is unitary. -/
theorem prodFwd_mem_unitaryGroup [CommRing α] [StarRing α] {P : ℕ → Matrix ι ι α}
    (hP : ∀ k, P k ∈ Matrix.unitaryGroup ι α) (r : ℕ) :
    prodFwd P r ∈ Matrix.unitaryGroup ι α :=
  prodFwd_mem hP r

/-- The product of orthogonal matrices is orthogonal. -/
theorem prodRev_mem_orthogonalGroup [CommRing α] {P : ℕ → Matrix ι ι α}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι α) (r : ℕ) :
    prodRev P r ∈ Matrix.orthogonalGroup ι α :=
  prodRev_mem hP r

/-- The product of orthogonal matrices is orthogonal. -/
theorem prodFwd_mem_orthogonalGroup [CommRing α] {P : ℕ → Matrix ι ι α}
    (hP : ∀ k, P k ∈ Matrix.orthogonalGroup ι α) (r : ℕ) :
    prodFwd P r ∈ Matrix.orthogonalGroup ι α :=
  prodFwd_mem hP r

end Matrix
