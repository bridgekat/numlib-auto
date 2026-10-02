/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Matrix.Mul`, beside `Matrix.col_mul_eq_mulVec_col`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Columns and rows of products

The columns of `B - M A` are `B.col q - M *ᵥ A.col q` and the rows of `B - A M` are
`B.row r - A.row r ᵥ* M` (`Matrix.col_sub_mul`, `Matrix.row_sub_mul_eq_sub_vecMul`): the form in
which a columnwise or rowwise error bound for one step of an elimination or orthogonal update is
read off a matrix statement. Both are definitional, like Mathlib's `Matrix.col_mul_eq_mulVec_col`
and `Matrix.row_mul_eq_vecMul_row`; over a commutative ring the row form is also
`B.row r - Mᵀ *ᵥ A.row r` (`Matrix.row_sub_mul`).

A matrix that acts on each column of `V` as a scalar is diagonalized by `V`:
`A V = V diag (γ)` when `A (V.col k) = γ k • V.col k`
(`Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col`), and dually `diag (γ) V = V A` when
`V.row k ᵥ* A = γ k • V.row k` (`Matrix.diagonal_mul_eq_mul_of_forall_vecMul_row`).

Selecting and inserting rows and columns commutes with multiplication in the expected way:
`P [A₁ | z | A₂] = [P A₁ | P z | P A₂]` for a column `z` inserted by `Fin.insertNth`
(`Matrix.mul_of_insertNth`), a row selection of the left factor is one of the product
(`Matrix.submatrix_id_mul`), and a submatrix applied to a vector is the matrix applied to the
vector's extension by zero (`Matrix.submatrix_mulVec_eq_comp_mulVec_extend`). A diagonal
congruence scales the entries, `(Dᴴ M D)ᵢⱼ = d̄ᵢ Mᵢⱼ dⱼ`
(`Matrix.star_diagonal_mul_mul_diagonal_apply`).
-/

namespace Matrix

variable {ι κ R : Type*} [Fintype ι]

/-- `(B - M A).col q = B.col q - M (A.col q)`. -/
theorem col_sub_mul [NonUnitalNonAssocRing R] (B : Matrix ι κ R) (M : Matrix ι ι R)
    (A : Matrix ι κ R) (q : κ) : (B - M * A).col q = B.col q - M *ᵥ A.col q :=
  rfl

/-- `(B - A M).row r = B.row r - A.row r ᵥ* M`. -/
theorem row_sub_mul_eq_sub_vecMul [NonUnitalNonAssocRing R] (B : Matrix κ ι R)
    (A : Matrix κ ι R) (M : Matrix ι ι R) (r : κ) :
    (B - A * M).row r = B.row r - A.row r ᵥ* M :=
  rfl

/-- `(B - A M).row r = B.row r - Mᵀ (A.row r)`, the `mulVec` form of
`Matrix.row_sub_mul_eq_sub_vecMul` over a commutative ring. -/
theorem row_sub_mul [NonUnitalCommRing R] (B : Matrix κ ι R) (A : Matrix κ ι R)
    (M : Matrix ι ι R) (r : κ) : (B - A * M).row r = B.row r - Mᵀ *ᵥ A.row r := by
  rw [row_sub_mul_eq_sub_vecMul, mulVec_transpose]

/-- A matrix whose action on each column of `V` is multiplication by `γ k` satisfies
`A V = V diag (γ)`. -/
theorem mul_eq_mul_diagonal_of_forall_mulVec_col [CommSemiring R] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι R} {V : Matrix ι κ R} {γ : κ → R} (h : ∀ k, A *ᵥ V.col k = γ k • V.col k) :
    A * V = V * diagonal γ := by
  ext j k
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [mul_diagonal, mul_comm (V j k)]
  exact hk

/-- A matrix whose action on each row of `V` (from the right) is multiplication by `γ k` satisfies
`diag (γ) V = V A`; the row twin of `Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col`. -/
theorem diagonal_mul_eq_mul_of_forall_vecMul_row [NonUnitalNonAssocSemiring R] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι ι R} {V : Matrix κ ι R} {γ : κ → R}
    (h : ∀ k, V.row k ᵥ* A = γ k • V.row k) : diagonal γ * V = V * A := by
  ext k j
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [diagonal_mul]
  exact hk.symm

/-- The entries of `Dᴴ M D` for a diagonal `D = diagonal d`: `star (d i) * M i j * d j`. -/
theorem star_diagonal_mul_mul_diagonal_apply [Semiring R] [StarRing R] [DecidableEq ι]
    (d : ι → R) (M : Matrix ι ι R) (i j : ι) :
    (star (diagonal d) * M * diagonal d) i j = star (d i) * M i j * d j := by
  rw [mul_diagonal, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul, Pi.star_apply]

/-- Multiplying a matrix with an inserted column: `P [A₁ | z | A₂] = [P A₁ | P z | P A₂]`. -/
theorem mul_of_insertNth {l : Type*} [NonUnitalNonAssocSemiring R] {m n : ℕ}
    (P : Matrix l (Fin m) R) (z : Fin m → R) (A : Matrix (Fin m) (Fin n) R) (k : Fin (n + 1)) :
    P * of (fun i => Fin.insertNth k (z i) (A i)) =
      of fun i => Fin.insertNth k ((P *ᵥ z) i) ((P * A) i) := by
  ext i j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove k j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply]

/-- Selecting rows of a left factor selects the rows of the product: the rewriting form of
Mathlib's `Matrix.submatrix_mul` with `e₂ = e₃ = id`. -/
theorem submatrix_id_mul [NonUnitalNonAssocSemiring R] {ι' ι'' : Type*} (X : Matrix ι' ι R)
    (Y : Matrix ι κ R) (e : ι'' → ι') : X.submatrix e id * Y = (X * Y).submatrix e id := by
  rw [submatrix_mul X Y e id id Function.bijective_id, submatrix_id_id]

/-- A submatrix applied to a vector: `(A.submatrix f g) x` is `A` applied to `x` extended by zero
along an injective `g`, restricted to the rows `f`. -/
theorem submatrix_mulVec_eq_comp_mulVec_extend {m m' n n' : Type*}
    [NonUnitalNonAssocSemiring R] [Fintype n] [Fintype n'] (B : Matrix m n R) (f : m' → m)
    {g : n' → n} (hg : Function.Injective g) (x : n' → R) :
    B.submatrix f g *ᵥ x = (B *ᵥ Function.extend g x 0) ∘ f := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
  exact Fintype.sum_of_injective g hg _ _ (fun k hk => by
    rw [Function.extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply, mul_zero]) fun j => by
    rw [hg.extend_apply]

end Matrix
