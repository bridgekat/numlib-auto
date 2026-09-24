/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Kronecker`, `Mathlib.LinearAlgebra.Matrix.Vec`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.Flat.Basic
import Numlib.LinearAlgebra.Matrix.Permutation

/-!
# The Kronecker product in positional layout, vectorization, and product families

Mathlib has the Kronecker product on product index types, `A ⊗ₖ B : Matrix (l × n) (m × p) R`, with
its algebra, and the column stacking `Matrix.vec A : n × m → R` with
`Matrix.kronecker_mulVec_vec : (B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ)`. Numerical texts read both
*positionally*: `B ⊗ C` is an `m₁ m₂ × n₁ n₂` array whose `(i₁, j₁)` block is `b_{i₁ j₁} C`, and
`vec X ∈ R^{nm}` stacks the columns of `X`. The positional layout is
`finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`, `(a, b) ↦ b + n a`, which is exactly the block-row
ordering of the books, and this file transports Mathlib's statements along it:
`Matrix.kroneckerFin`, `Matrix.vecFin`, and `Matrix.reshape` (MATLAB's `reshape`), with the typed
inverse `Matrix.unvec` of `Matrix.vec` beside them.

The perfect shuffle `Matrix.perfectShuffle p r` (`Numlib.LinearAlgebra.Matrix.Permutation`) is the
vec-permutation (commutation) matrix, `Π_{p,r} vec X = vec Xᵀ`
(`Matrix.perfectShuffle_mulVec_vecFin`), and conjugates `B ⊗ C` into `C ⊗ B`
(`Matrix.perfectShuffle_mul_kroneckerFin_mul_transpose`).

The elementary tensor `Matrix.kroneckerVec v w = v ⊗ w` of two vectors, on which a Kronecker product
acts factor by factor (`Matrix.kronecker_mulVec`), is the basic object of separation of variables
(`Numlib.LinearAlgebra.Matrix.KroneckerSum` builds the Kronecker sum on it).

Beyond two factors: the Kronecker product of a finite family `Matrix.piKronecker M`, indexed by the
product types `∀ i, μ i` (the matrix of the multilinear product of tensors), with its flattening to
the book's reversed-order `M_d ⊗ ⋯ ⊗ M_1` (`Matrix.piKronecker_reindex_finPiFinEquiv`); the
column-wise Khatri–Rao product and its family version; the Tracy–Singh product of block matrices as
a reindexed Kronecker product; and the algebraic facts of [golub2013matrix] §12.3.1 that Mathlib
lacks (the rank of a Kronecker product, Kronecker products of permutation and stochastic matrices).
Norms, eigenvalues, singular values and triangular factors of Kronecker products need the
factorization layer and are in `Numlib.LinearAlgebra.Matrix.Kronecker.Spectral`; this module stays
free of it.

## Main definitions

* `Matrix.kroneckerVec`: the elementary tensor `v ⊗ w`.
* `Matrix.kroneckerFin`, `Matrix.vecFin`, `Matrix.reshape`: the positional Kronecker product, column
  stacking and reshaping.
* `Matrix.unvec`: the inverse of `Matrix.vec`.
* `Matrix.piKronecker`, `Matrix.khatriRao`, `Matrix.piKhatriRao`, `Matrix.tracySingh`.

## Main statements

* `Matrix.kronecker_mulVec`: `(A ⊗ B)(v ⊗ w) = (A v) ⊗ (B w)`.
* `Matrix.kroneckerFin_mul_kroneckerFin`, `Matrix.inv_kroneckerFin`, `Matrix.kroneckerFin_assoc`,
  `Matrix.kroneckerFin_mulVec_vecFin`: [golub2013matrix] (1.3.2)–(1.3.4), (1.3.6).
* `Matrix.perfectShuffle_mul_kroneckerFin_mul_transpose`: [golub2013matrix] (1.3.5).
* `Matrix.piKronecker_mul_piKronecker`, `Matrix.khatriRao_transpose_mul_self`.
* `Matrix.rank_kronecker`: `rank (B ⊗ C) = rank B · rank C` over a field.

## References

* [golub2013matrix], §1.3.6–1.3.8, §12.3, §12.4.
-/

open scoped Kronecker Matrix

namespace Matrix

variable {R : Type*}

/-! ### Elementary tensors -/

section ElementaryTensor

variable {l m n p : Type*}

/-- The Kronecker product of two vectors, the elementary tensor `v ⊗ w`:
`kroneckerVec v w (i, j) = v i * w j`. -/
def kroneckerVec [Mul R] (v : m → R) (w : n → R) : m × n → R := fun q => v q.1 * w q.2

/-- The entries of an elementary tensor. -/
@[simp]
theorem kroneckerVec_apply [Mul R] (v : m → R) (w : n → R) (i : m) (j : n) :
    kroneckerVec v w (i, j) = v i * w j := rfl

/-- A scalar on the left factor of an elementary tensor scales the tensor. -/
theorem kroneckerVec_smul_left [Semigroup R] (c : R) (v : m → R) (w : n → R) :
    kroneckerVec (c • v) w = c • kroneckerVec v w := by
  funext q
  simp [kroneckerVec, mul_assoc]

/-- A scalar on the right factor of an elementary tensor scales the tensor. -/
theorem kroneckerVec_smul_right [CommSemigroup R] (c : R) (v : m → R) (w : n → R) :
    kroneckerVec v (c • w) = c • kroneckerVec v w := by
  funext q
  simp [kroneckerVec, mul_left_comm]

/-- An elementary tensor of two nonzero vectors is nonzero. -/
theorem kroneckerVec_ne_zero [MulZeroClass R] [NoZeroDivisors R] {v : m → R} {w : n → R}
    (hv : v ≠ 0) (hw : w ≠ 0) : kroneckerVec v w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  intro h
  exact mul_ne_zero hi hj (by simpa using congrFun h (i, j))

variable [CommSemiring R] [Fintype m] [Fintype n]

/-- The Kronecker product of matrices acts on an elementary tensor factor by factor:
`(A ⊗ B)(v ⊗ w) = (A v) ⊗ (B w)`. -/
theorem kronecker_mulVec (A : Matrix l m R) (B : Matrix p n R) (v : m → R) (w : n → R) :
    (A ⊗ₖ B) *ᵥ kroneckerVec v w = kroneckerVec (A *ᵥ v) (B *ᵥ w) := by
  funext q
  simp only [mulVec_apply_eq_sum, Fintype.sum_prod_type, kroneckerVec, kroneckerMap_apply]
  rw [Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The dot product of two elementary tensors factors:
`(v ⊗ w) · (v' ⊗ w') = (v · v') (w · w')`. -/
theorem kroneckerVec_dotProduct_kroneckerVec (v v' : m → R) (w w' : n → R) :
    kroneckerVec v w ⬝ᵥ kroneckerVec v' w' = (v ⬝ᵥ v') * (w ⬝ᵥ w') := by
  simp only [dotProduct, Fintype.sum_prod_type, kroneckerVec]
  rw [Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end ElementaryTensor

/-! ### The Kronecker product in positional layout -/

section KroneckerFin

variable {m₁ m₂ m₃ n₁ n₂ n₃ p₁ p₂ : ℕ}

/-- The Kronecker product in positional layout: `kroneckerFin A B` is the
`m₁ m₂ × n₁ n₂` array whose `(i₁, j₁)` block is `A i₁ j₁ • B`, row `(i₁, i₂)` sitting at position
`i₂ + m₂ i₁`. -/
def kroneckerFin [Mul R] (A : Matrix (Fin m₁) (Fin n₁) R) (B : Matrix (Fin m₂) (Fin n₂) R) :
    Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) R :=
  (A ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The entries of `kroneckerFin A B`: the `(i₁, j₁)` block is `A i₁ j₁ • B`. -/
@[simp]
theorem kroneckerFin_apply [Mul R] (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₂) (Fin n₂) R) (i₁ : Fin m₁) (i₂ : Fin m₂) (j₁ : Fin n₁) (j₂ : Fin n₂) :
    kroneckerFin A B (finProdFinEquiv (i₁, i₂)) (finProdFinEquiv (j₁, j₂)) = A i₁ j₁ * B i₂ j₂ := by
  simp [kroneckerFin]

/-- `(A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ` ([golub2013matrix] (1.3.1)). -/
theorem transpose_kroneckerFin [Mul R] (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₂) (Fin n₂) R) : (kroneckerFin A B)ᵀ = kroneckerFin Aᵀ Bᵀ :=
  rfl

/-- The mixed-product rule `(A ⊗ B)(C ⊗ D) = AC ⊗ BD` ([golub2013matrix] (1.3.2)). -/
theorem kroneckerFin_mul_kroneckerFin [CommSemiring R] (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₂) (Fin n₂) R) (C : Matrix (Fin n₁) (Fin p₁) R)
    (D : Matrix (Fin n₂) (Fin p₂) R) :
    kroneckerFin A B * kroneckerFin C D = kroneckerFin (A * C) (B * D) := by
  rw [kroneckerFin, kroneckerFin, kroneckerFin, submatrix_mul_equiv, mul_kronecker_mul]

/-- `(A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹` ([golub2013matrix] (1.3.3)); with Lean's convention for the inverse of a
singular matrix no hypothesis is needed. -/
theorem inv_kroneckerFin [CommRing R] (A : Matrix (Fin m₁) (Fin m₁) R)
    (B : Matrix (Fin m₂) (Fin m₂) R) : (kroneckerFin A B)⁻¹ = kroneckerFin A⁻¹ B⁻¹ := by
  rw [kroneckerFin, kroneckerFin, inv_submatrix_equiv, inv_kronecker]

/-- `I_m ⊗ I_n = I_{mn}`. -/
@[simp]
theorem kroneckerFin_one_one [MulZeroOneClass R] :
    kroneckerFin (1 : Matrix (Fin m₁) (Fin m₁) R) (1 : Matrix (Fin m₂) (Fin m₂) R) = 1 := by
  rw [kroneckerFin, one_kronecker_one, submatrix_one_equiv]

/-- The positional index of `(a, (b, c))` in `Fin (m₁ * (m₂ * m₃))` is that of `((a, b), c)` in
`Fin (m₁ * m₂ * m₃)`. -/
private theorem finCongr_symm_finProdFinEquiv_assoc (a : Fin m₁) (b : Fin m₂) (c : Fin m₃) :
    (finCongr (Nat.mul_assoc m₁ m₂ m₃)).symm (finProdFinEquiv (a, finProdFinEquiv (b, c)))
      = finProdFinEquiv (finProdFinEquiv (a, b), c) := by
  ext
  simp only [finCongr_symm, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
  ring

/-- Associativity of the positional Kronecker product ([golub2013matrix] (1.3.4)); the two sides
live on `Fin (m₁ * (m₂ * m₃))` and `Fin (m₁ * m₂ * m₃)`, identified by `Nat.mul_assoc`. -/
theorem kroneckerFin_assoc [Semigroup R] (A : Matrix (Fin m₁) (Fin n₁) R)
    (B : Matrix (Fin m₂) (Fin n₂) R) (C : Matrix (Fin m₃) (Fin n₃) R) :
    kroneckerFin A (kroneckerFin B C)
      = (kroneckerFin (kroneckerFin A B) C).submatrix (finCongr (Nat.mul_assoc m₁ m₂ m₃)).symm
          (finCongr (Nat.mul_assoc n₁ n₂ n₃)).symm := by
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective i'
  obtain ⟨⟨a', j'⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨b', c'⟩, rfl⟩ := finProdFinEquiv.surjective j'
  rw [submatrix_apply, finCongr_symm_finProdFinEquiv_assoc, finCongr_symm_finProdFinEquiv_assoc,
    kroneckerFin_apply, kroneckerFin_apply, kroneckerFin_apply, kroneckerFin_apply, mul_assoc]

end KroneckerFin

/-! ### Vectorization and reshaping -/

section Vec

variable {m n m₁ n₁ m₂ n₂ : ℕ}

/-- Column stacking in positional layout, `vec X = [X(:, 1); …; X(:, n)]`: entry `(i, j)` of `X`
sits at position `i + m j`. -/
def vecFin (X : Matrix (Fin m) (Fin n) R) : Fin (n * m) → R :=
  vec X ∘ finProdFinEquiv.symm

/-- Entry `(i, j)` of `X` sits at position `i + m j` of `vecFin X`. -/
@[simp]
theorem vecFin_apply (X : Matrix (Fin m) (Fin n) R) (j : Fin n) (i : Fin m) :
    vecFin X (finProdFinEquiv (j, i)) = X i j := by
  simp [vecFin]

/-- Column stacking is injective: a matrix is determined by `vec X`. -/
theorem vecFin_injective : Function.Injective (vecFin : Matrix (Fin m) (Fin n) R → _) :=
  fun X Y h => vec_inj.1 <| funext fun q => by
    simpa [vecFin] using congrFun h (finProdFinEquiv q)

/-- The reshaping identity `(B ⊗ C) vec X = vec (C X Bᵀ)` ([golub2013matrix] (1.3.6)). -/
theorem kroneckerFin_mulVec_vecFin [CommSemiring R] (B : Matrix (Fin m₁) (Fin n₁) R)
    (C : Matrix (Fin m₂) (Fin n₂) R) (X : Matrix (Fin n₂) (Fin n₁) R) :
    kroneckerFin B C *ᵥ vecFin X = vecFin (C * X * Bᵀ) := by
  rw [kroneckerFin, submatrix_mulVec_equiv, vecFin, vecFin, Equiv.symm_symm, Function.comp_assoc,
    Equiv.symm_comp_self, Function.comp_id, kronecker_mulVec_vec]

/-- MATLAB's `reshape(A, m₁, n₁)`: the `m₁ × n₁` matrix with the same column stacking as `A`. The
size condition is an argument, as a mismatch is an error in MATLAB. -/
def reshape (A : Matrix (Fin m) (Fin n) R) (m₁ n₁ : ℕ) (h : n₁ * m₁ = n * m) :
    Matrix (Fin m₁) (Fin n₁) R :=
  of fun i j => vecFin A (Fin.cast h (finProdFinEquiv (j, i)))

/-- `reshape` keeps the column stacking; with `vecFin_injective` this characterizes it. -/
theorem vecFin_reshape (A : Matrix (Fin m) (Fin n) R) (m₁ n₁ : ℕ) (h : n₁ * m₁ = n * m) :
    vecFin (reshape A m₁ n₁ h) = vecFin A ∘ Fin.cast h := by
  funext x
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective x
  rw [vecFin_apply, Function.comp_apply]
  rfl

variable {m' n' : Type*}

/-- The inverse of Mathlib's column stacking `Matrix.vec`: `unvec u i j = u (j, i)`. -/
def unvec (u : n' × m' → R) : Matrix m' n' R :=
  of fun i j => u (j, i)

/-- The entries of `unvec u`. -/
@[simp]
theorem unvec_apply (u : n' × m' → R) (i : m') (j : n') : unvec u i j = u (j, i) := rfl

/-- `unvec` is a left inverse of `vec`. -/
@[simp]
theorem unvec_vec (A : Matrix m' n' R) : unvec (vec A) = A := rfl

/-- `unvec` is a right inverse of `vec`. -/
@[simp]
theorem vec_unvec (u : n' × m' → R) : vec (unvec u) = u := rfl

/-- `Matrix.unvec` as a linear equivalence, with inverse `Matrix.vec`. -/
def unvecLinearEquiv (S : Type*) [Semiring S] [AddCommMonoid R] [Module S R] :
    (n' × m' → R) ≃ₗ[S] Matrix m' n' R where
  toFun := unvec
  invFun := vec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := vec_unvec
  right_inv := unvec_vec

/-- `unvec` of an elementary tensor is a rank-one matrix: `reshape(v ⊗ u, m, n) = u vᵀ`. -/
theorem unvec_kroneckerVec [CommMagma R] (v : n' → R) (u : m' → R) :
    unvec (kroneckerVec v u) = vecMulVec u v := by
  ext i j
  simp [vecMulVec_apply, mul_comm]

/-- The positional `reshape` is the typed inverse of `vec`, read through the positional layout. -/
theorem reshape_eq_unvec (A : Matrix (Fin m) (Fin n) R) (m₁ n₁ : ℕ) (h : n₁ * m₁ = n * m) :
    reshape A m₁ n₁ h = unvec ((vecFin A ∘ Fin.cast h) ∘ finProdFinEquiv) :=
  rfl

end Vec

/-! ### The perfect shuffle and the Kronecker product -/

section PerfectShuffle

variable {p r m₁ m₂ n₁ n₂ : ℕ}

/-- The perfect shuffle is the vec-permutation matrix: `Π_{p,r} vec X = vec Xᵀ` for an `r × p`
matrix `X`, whose `p` columns are the piles. -/
theorem perfectShuffle_mulVec_vecFin [NonAssocSemiring R] (X : Matrix (Fin r) (Fin p) R) :
    perfectShuffle p r *ᵥ vecFin X = vecFin Xᵀ := by
  funext x
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective x
  rw [perfectShuffle_mulVec_apply, vecFin_apply, vecFin_apply, transpose_apply]

/-- The Kronecker product commutes up to swapping both index pairs. -/
theorem kronecker_submatrix_swap [CommMagma R] {l m n q : Type*} (A : Matrix l m R)
    (B : Matrix n q R) : (A ⊗ₖ B).submatrix Prod.swap Prod.swap = B ⊗ₖ A := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  exact mul_comm _ _

/-- The perfect shuffle conjugates `B ⊗ C` into `C ⊗ B`: `Π_{m₁,m₂} (B ⊗ C) Π_{n₁,n₂}ᵀ = C ⊗ B`
([golub2013matrix] (1.3.5)). -/
theorem perfectShuffle_mul_kroneckerFin_mul_transpose [CommSemiring R]
    (B : Matrix (Fin m₁) (Fin n₁) R) (C : Matrix (Fin m₂) (Fin n₂) R) :
    perfectShuffle m₁ m₂ * kroneckerFin B C *
        (perfectShuffle n₁ n₂ : Matrix (Fin (n₂ * n₁)) (Fin (n₁ * n₂)) R)ᵀ
      = kroneckerFin C B := by
  rw [transpose_perfectShuffle, perfectShuffle, perfectShuffle, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  obtain ⟨⟨a₂, a₁⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b₂, b₁⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [submatrix_apply, submatrix_apply, id, id, Equiv.symm_symm, finPerfectShuffle_symm,
    finPerfectShuffle_apply, finPerfectShuffle_apply, kroneckerFin_apply, kroneckerFin_apply,
    mul_comm]

end PerfectShuffle

/-! ### Kronecker products of families -/

section Pi

variable {ι : Type*} [Fintype ι] {μ κ ν : ι → Type*}

/-- The Kronecker product of a finite family of matrices, on the product index types:
`piKronecker M a b = ∏ i, M i (a i) (b i)`. -/
def piKronecker [CommMonoid R] (M : ∀ i, Matrix (μ i) (κ i) R) :
    Matrix (∀ i, μ i) (∀ i, κ i) R :=
  of fun a b => ∏ i, M i (a i) (b i)

/-- The entries of a family Kronecker product. -/
@[simp]
theorem piKronecker_apply [CommMonoid R] (M : ∀ i, Matrix (μ i) (κ i) R) (a : ∀ i, μ i)
    (b : ∀ i, κ i) : piKronecker M a b = ∏ i, M i (a i) (b i) := rfl

/-- For two factors, `piKronecker` is the Kronecker product `M 0 ⊗ₖ M 1`. -/
theorem piKronecker_fin_two [CommMonoid R] {μ κ : Fin 2 → Type*} (M : ∀ i, Matrix (μ i) (κ i) R) :
    piKronecker M = (M 0 ⊗ₖ M 1).submatrix (piFinTwoEquiv μ) (piFinTwoEquiv κ) := by
  ext a b
  simp [Fin.prod_univ_two]

/-- The transpose of a family Kronecker product is the product of the transposes. -/
theorem transpose_piKronecker [CommMonoid R] (M : ∀ i, Matrix (μ i) (κ i) R) :
    (piKronecker M)ᵀ = piKronecker fun i => (M i)ᵀ :=
  rfl

/-- The conjugate transpose of a family Kronecker product is the product of the conjugate
transposes. -/
theorem conjTranspose_piKronecker [CommMonoid R] [StarMul R] (M : ∀ i, Matrix (μ i) (κ i) R) :
    (piKronecker M)ᴴ = piKronecker fun i => (M i)ᴴ := by
  ext a b
  simp [star_prod]

variable [CommSemiring R]

/-- The Kronecker product of identity matrices is the identity. -/
@[simp]
theorem piKronecker_one [∀ i, DecidableEq (μ i)] :
    piKronecker (fun i => (1 : Matrix (μ i) (μ i) R)) = 1 := by
  ext a b
  simp [one_apply, Finset.prod_boole, funext_iff]

variable [DecidableEq ι]

/-- The mixed-product rule for families: `(⊗ᵢ Nᵢ)(⊗ᵢ Mᵢ) = ⊗ᵢ (Nᵢ Mᵢ)`. -/
theorem piKronecker_mul_piKronecker [∀ i, Fintype (κ i)] (N : ∀ i, Matrix (μ i) (κ i) R)
    (M : ∀ i, Matrix (κ i) (ν i) R) :
    piKronecker N * piKronecker M = piKronecker fun i => N i * M i := by
  ext a b
  simp only [mul_apply, piKronecker_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- The family Kronecker product acts on an elementary tensor factor by factor. -/
theorem piKronecker_mulVec_prod [∀ i, Fintype (κ i)] (M : ∀ i, Matrix (μ i) (κ i) R)
    (z : ∀ i, κ i → R) :
    piKronecker M *ᵥ (fun b => ∏ i, z i (b i)) = fun a => ∏ i, (M i *ᵥ z i) (a i) := by
  funext a
  simp only [mulVec, dotProduct, piKronecker_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- A Kronecker product of matrices with orthonormal columns has orthonormal columns. -/
theorem conjTranspose_piKronecker_mul_piKronecker [StarRing R] [∀ i, Fintype (μ i)]
    [∀ i, DecidableEq (κ i)] {M : ∀ i, Matrix (μ i) (κ i) R} (h : ∀ i, (M i)ᴴ * M i = 1) :
    (piKronecker M)ᴴ * piKronecker M = 1 := by
  rw [conjTranspose_piKronecker, piKronecker_mul_piKronecker]
  simp only [h, piKronecker_one]

end Pi

section PiUnitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : ι → Type*} [CommRing R]

/-- A Kronecker product of unitary matrices is unitary. -/
theorem piKronecker_mem_unitaryGroup [StarRing R] [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]
    {U : ∀ i, Matrix (μ i) (μ i) R} (hU : ∀ i, U i ∈ unitaryGroup (μ i) R) :
    piKronecker U ∈ unitaryGroup (∀ i, μ i) R := by
  have h : ∀ i, U i * (U i)ᴴ = 1 := fun i => by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff.1 (hU i)
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_piKronecker,
    piKronecker_mul_piKronecker]
  simp only [h, piKronecker_one]

end PiUnitary

section PiFin

/-- The recursion of the little-endian flattening `finPiFinEquiv`: the last index carries the
largest weight. -/
private theorem val_finPiFinEquiv_snoc {d : ℕ} {s : Fin (d + 1) → ℕ}
    (i : ∀ k : Fin d, Fin (s k.castSucc)) (x : Fin (s (Fin.last d))) :
    (finPiFinEquiv (Fin.snoc (α := fun k => Fin (s k)) i x) : ℕ)
      = finPiFinEquiv i + (∏ k : Fin d, s k.castSucc) * x := by
  rw [finPiFinEquiv_apply, finPiFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [mul_comm (x : ℕ)]
  rfl

/-- The flattening of a family Kronecker product by `finPiFinEquiv` (the book's `col`) is the
positional Kronecker product with the *last* factor outermost; by induction the flattened
`piKronecker M` is `M_d ⊗ ⋯ ⊗ M_1`, reversed, because `finPiFinEquiv` is little-endian while
`finProdFinEquiv` is big-endian. The two index types agree up to `Fin.prod_univ_castSucc` and the
commutativity of the size product. -/
theorem piKronecker_reindex_finPiFinEquiv [CommMonoid R] {d : ℕ} {m n : Fin (d + 1) → ℕ}
    (M : ∀ k, Matrix (Fin (m k)) (Fin (n k)) R) :
    (piKronecker M).reindex finPiFinEquiv finPiFinEquiv
      = (kroneckerFin (M (Fin.last d))
            ((piKronecker fun k : Fin d => M k.castSucc).reindex finPiFinEquiv
              finPiFinEquiv)).submatrix
          (finCongr (by rw [Fin.prod_univ_castSucc, mul_comm]))
          (finCongr (by rw [Fin.prod_univ_castSucc, mul_comm])) := by
  have key : ∀ {s : Fin (d + 1) → ℕ}
      (h : ∏ k, s k = s (Fin.last d) * ∏ k : Fin d, s k.castSucc) (a : ∀ k, Fin (s k)),
      finCongr h (finPiFinEquiv a)
        = finProdFinEquiv (a (Fin.last d), finPiFinEquiv fun k : Fin d => a k.castSucc) := by
    intro s h a
    ext
    rw [finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
    conv_lhs => rw [← Fin.snoc_init_self a]
    exact val_finPiFinEquiv_snoc _ _
  ext I J
  obtain ⟨a, rfl⟩ := finPiFinEquiv.surjective I
  obtain ⟨b, rfl⟩ := finPiFinEquiv.surjective J
  simp only [reindex_apply, submatrix_apply, key, kroneckerFin_apply, Equiv.symm_apply_apply,
    piKronecker_apply]
  rw [Fin.prod_univ_castSucc, mul_comm]

end PiFin

/-! ### Khatri–Rao and Tracy–Singh products -/

section KhatriRao

variable {m n m₁ m₂ r : Type*}

/-- The column-wise Khatri–Rao product: column `j` of `khatriRao B C` is `b_j ⊗ c_j`. -/
def khatriRao [Mul R] (B : Matrix m₁ r R) (C : Matrix m₂ r R) : Matrix (m₁ × m₂) r R :=
  of fun ik j => B ik.1 j * C ik.2 j

/-- The entries of a Khatri–Rao product. -/
@[simp]
theorem khatriRao_apply [Mul R] (B : Matrix m₁ r R) (C : Matrix m₂ r R) (i : m₁) (k : m₂) (j : r) :
    khatriRao B C (i, k) j = B i j * C k j := rfl

/-- The Khatri–Rao product is a column submatrix of the Kronecker product. -/
theorem khatriRao_eq_submatrix_kronecker [Mul R] (B : Matrix m₁ r R) (C : Matrix m₂ r R) :
    khatriRao B C = (B ⊗ₖ C).submatrix id fun j => (j, j) :=
  rfl

/-- The Hadamard product is a submatrix of the Kronecker product. -/
theorem hadamard_eq_submatrix_kronecker [Mul R] (A B : Matrix m n R) :
    A ⊙ B = (A ⊗ₖ B).submatrix (fun i => (i, i)) fun j => (j, j) :=
  rfl

/-- The Gram matrix of a Khatri–Rao product ([golub2013matrix] (12.5.20)):
`(B ⊙ C)ᵀ (B ⊙ C) = (Bᵀ B) ∘ (Cᵀ C)`. -/
theorem khatriRao_transpose_mul_self [CommSemiring R] [Fintype m₁] [Fintype m₂]
    (B : Matrix m₁ r R) (C : Matrix m₂ r R) :
    (khatriRao B C)ᵀ * khatriRao B C = (Bᵀ * B) ⊙ (Cᵀ * C) := by
  ext j k
  simp only [mul_apply, transpose_apply, khatriRao_apply, hadamard_apply, Fintype.sum_prod_type,
    Fintype.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The conjugate-transpose twin of `Matrix.khatriRao_transpose_mul_self`. -/
theorem khatriRao_conjTranspose_mul_self [CommSemiring R] [StarRing R] [Fintype m₁] [Fintype m₂]
    (B : Matrix m₁ r R) (C : Matrix m₂ r R) :
    (khatriRao B C)ᴴ * khatriRao B C = (Bᴴ * B) ⊙ (Cᴴ * C) := by
  ext j k
  simp only [mul_apply, conjTranspose_apply, khatriRao_apply, hadamard_apply,
    Fintype.sum_prod_type, Fintype.sum_mul_sum, star_mul']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type*} [Fintype ι] {κ : ι → Type*}

/-- The Khatri–Rao product of a family: `piKhatriRao F a j = ∏ i, F i (a i) j`. -/
def piKhatriRao [CommMonoid R] (F : ∀ i, Matrix (κ i) r R) : Matrix (∀ i, κ i) r R :=
  of fun a j => ∏ i, F i (a i) j

/-- The entries of a family Khatri–Rao product. -/
@[simp]
theorem piKhatriRao_apply [CommMonoid R] (F : ∀ i, Matrix (κ i) r R) (a : ∀ i, κ i) (j : r) :
    piKhatriRao F a j = ∏ i, F i (a i) j := rfl

/-- For two factors, `piKhatriRao` is the binary Khatri–Rao product. -/
theorem piKhatriRao_fin_two [CommMonoid R] {κ : Fin 2 → Type*} (F : ∀ i, Matrix (κ i) r R) :
    piKhatriRao F = (khatriRao (F 0) (F 1)).submatrix (piFinTwoEquiv κ) id := by
  ext a j
  simp [Fin.prod_univ_two]

end KhatriRao

section TracySingh

variable {M₁ m₁ N₁ n₁ M₂ m₂ N₂ n₂ : Type*}

/-- The Tracy–Singh product of block matrices (outer index = block): block `(I₁, J₁)` of
`tracySingh B C` is the block matrix `[B_{I₁J₁} ⊗ C_{kl}]_{k,l}`. -/
def tracySingh [Mul R] (B : Matrix (M₁ × m₁) (N₁ × n₁) R) (C : Matrix (M₂ × m₂) (N₂ × n₂) R) :
    Matrix ((M₁ × M₂) × (m₁ × m₂)) ((N₁ × N₂) × (n₁ × n₂)) R :=
  of fun I J => B (I.1.1, I.2.1) (J.1.1, J.2.1) * C (I.1.2, I.2.2) (J.1.2, J.2.2)

/-- The Tracy–Singh product is a reindexed Kronecker product ([golub2013matrix] (12.3.6)). -/
theorem tracySingh_eq_reindex_kronecker [Mul R] (B : Matrix (M₁ × m₁) (N₁ × n₁) R)
    (C : Matrix (M₂ × m₂) (N₂ × n₂) R) :
    tracySingh B C
      = (B ⊗ₖ C).reindex (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _) :=
  rfl

end TracySingh

/-! ### Rank, permutation and stochastic matrices -/

section Rank

variable {K : Type*} [Field K]

/-- Over a field, the range of `f ⊗ g` has dimension `dim range f · dim range g`. -/
private theorem finrank_range_tensorProduct_map {M N P Q : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    [FiniteDimensional K P] [FiniteDimensional K Q] (f : M →ₗ[K] P) (g : N →ₗ[K] Q) :
    Module.finrank K (LinearMap.range (TensorProduct.map f g))
      = Module.finrank K (LinearMap.range f) * Module.finrank K (LinearMap.range g) := by
  have h : TensorProduct.map f g = TensorProduct.map (LinearMap.range f).subtype
      (LinearMap.range g).subtype ∘ₗ TensorProduct.map f.rangeRestrict g.rangeRestrict := by
    rw [← TensorProduct.map_comp, LinearMap.subtype_comp_rangeRestrict,
      LinearMap.subtype_comp_rangeRestrict]
  rw [h, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2
      (TensorProduct.map_surjective f.surjective_rangeRestrict g.surjective_rangeRestrict)),
    LinearMap.finrank_range_of_inj (TensorProduct.map_injective_of_flat_flat _ _
      (Submodule.injective_subtype _) (Submodule.injective_subtype _)),
    Module.finrank_tensorProduct]

/-- The rank of a Kronecker product is the product of the ranks ([golub2013matrix] §12.3.1). -/
theorem rank_kronecker {m₁ n₁ m₂ n₂ : Type*} [Finite m₁] [Fintype n₁] [Finite m₂] [Fintype n₂]
    (B : Matrix m₁ n₁ K) (C : Matrix m₂ n₂ K) : (B ⊗ₖ C).rank = B.rank * C.rank := by
  classical
  rw [B.rank_eq_finrank_range_toLin (Pi.basisFun K m₁) (Pi.basisFun K n₁),
    C.rank_eq_finrank_range_toLin (Pi.basisFun K m₂) (Pi.basisFun K n₂),
    (B ⊗ₖ C).rank_eq_finrank_range_toLin ((Pi.basisFun K m₁).tensorProduct (Pi.basisFun K m₂))
      ((Pi.basisFun K n₁).tensorProduct (Pi.basisFun K n₂)), toLin_kronecker]
  exact finrank_range_tensorProduct_map _ _

/-- The rank of a Hadamard product is at most the product of the ranks. -/
theorem rank_hadamard_le {m n : Type*} [Finite m] [Fintype n] (A B : Matrix m n K) :
    (A ⊙ B).rank ≤ A.rank * B.rank := by
  rw [hadamard_eq_submatrix_kronecker, ← rank_kronecker]
  exact rank_submatrix_le _ _ _

end Rank

section Permutation

variable {m n : Type*} [DecidableEq m] [DecidableEq n]

/-- The Kronecker product of permutation matrices is the permutation matrix of the product
permutation ([golub2013matrix] §12.3.1). -/
theorem permMatrix_kronecker_permMatrix [MulZeroOneClass R] (σ : Equiv.Perm m)
    (τ : Equiv.Perm n) :
    σ.permMatrix R ⊗ₖ τ.permMatrix R = Equiv.Perm.permMatrix R (σ.prodCongr τ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kroneckerMap_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Equiv.prodCongr_apply, Prod.map_apply, Prod.mk.injEq]
  rw [ite_zero_mul_ite_zero, one_mul]

variable [Fintype m] [Fintype n] [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- The Kronecker product of two row-stochastic matrices is row-stochastic
([golub2013matrix] §12.3.1). -/
theorem kronecker_mem_rowStochastic {B : Matrix m m R} {C : Matrix n n R}
    (hB : B ∈ rowStochastic R m) (hC : C ∈ rowStochastic R n) :
    B ⊗ₖ C ∈ rowStochastic R (m × n) := by
  rw [mem_rowStochastic_iff_sum] at hB hC ⊢
  refine ⟨fun i j => mul_nonneg (hB.1 _ _) (hC.1 _ _), fun i => ?_⟩
  simp only [Fintype.sum_prod_type, kroneckerMap_apply]
  rw [← Fintype.sum_mul_sum, hB.2, hC.2, one_mul]

/-- The Kronecker product of two column-stochastic matrices is column-stochastic. -/
theorem kronecker_mem_colStochastic {B : Matrix m m R} {C : Matrix n n R}
    (hB : B ∈ colStochastic R m) (hC : C ∈ colStochastic R n) :
    B ⊗ₖ C ∈ colStochastic R (m × n) := by
  rw [mem_colStochastic_iff_sum] at hB hC ⊢
  refine ⟨fun i j => mul_nonneg (hB.1 _ _) (hC.1 _ _), fun j => ?_⟩
  simp only [Fintype.sum_prod_type, kroneckerMap_apply]
  rw [← Fintype.sum_mul_sum, hB.2, hC.2, one_mul]

end Permutation

end Matrix
