/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.PlaneRotation`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith

/-!
# Plane embeddings and plane rotations

The **plane embedding** `Matrix.planeEmbed j k G` of a `2 × 2` matrix `G` is the `n × n` matrix
that agrees with the identity outside the rows and columns `j`, `k` and carries `G` on that block.
It acts on a vector or a matrix through the coordinates `j`, `k` alone, embeddings in one plane
compose as their `2 × 2` factors, and the embedding is unitary, orthogonal or of a given
determinant exactly when `G` is; all of this is proved once here, for any semiring.

The **plane rotation** `Matrix.planeRotation j k c s` is its instance `!![c, -s; s, c]` over `ℝ`:
for `c = cos θ` and `s = sin θ` it rotates the `(j, k)`-coordinate plane by the angle `θ` and
fixes its orthogonal complement. It is the Givens rotation of numerical linear algebra, and the
one-parameter family that every rotation-based algorithm is built from. The **Givens pair**
`Matrix.givensPair a b` is the cosine and sine of the rotation whose transpose sends `(a, b)` to
`(√(a² + b²), 0)`, the elementary step of every Givens `QR` factorization.

## Main definitions

* `Matrix.planeEmbed j k G`: the `2 × 2` matrix `G` placed in the `(j, k)` coordinate plane.
* `Matrix.planeRotation j k c s`: the rotation of the `(j, k)`-plane with cosine `c` and sine `s`.
* `Matrix.givensPair a b`: the pair `(c, s) = (a, b) / √(a² + b²)`, and `(1, 0)` when `a = b = 0`.

## Main results

* `Matrix.planeEmbed_mul_apply`, `Matrix.mul_planeEmbed_apply`, `Matrix.planeEmbed_mulVec_apply`:
  multiplying by an embedding on the left combines the rows `j`, `k`, on the right the columns
  `j`, `k`; every other entry is left alone.
* `Matrix.planeEmbed_mul_planeEmbed`, `Matrix.planeEmbed_transpose`,
  `Matrix.planeEmbed_conjTranspose`, `Matrix.det_planeEmbed`,
  `Matrix.planeEmbed_mem_unitaryGroup_iff`: the embedding is a multiplicative,
  transposition-preserving, determinant-preserving map, and it is unitary exactly when its
  `2 × 2` block is.
* `Matrix.transpose_planeRotation_mul_self`, `Matrix.planeRotation_mem_orthogonalGroup`: a plane
  rotation with `c ^ 2 + s ^ 2 = 1` is orthogonal.
* `Matrix.transpose_planeRotation_givensPair_mulVec`: the rotation built from the Givens pair of
  `(x j, x k)` annihilates the `k`-th entry of `x` and puts `√(x j ² + x k ²)` in the `j`-th.
* `Matrix.conj_planeRotation_apply_of_ne` and the entry formulas `conj_planeRotation_apply_jj`,
  `_kk`, `_jk`, `_col_j`, `_col_k`, `_row_j`, `_row_k`: the entries of the conjugate `Rᵀ M R` of
  an arbitrary square matrix `M` by a plane rotation `R`, entry by entry, which is the form in
  which an algorithm reads off what one rotation did.

## Implementation notes

The sign convention of the rotation is that of Jacobi's method: the rows `j`, `k` of the
rotation are `(c, -s)` and `(s, c)`, so that `Rᵀ` rotates counterclockwise. The Givens matrix
`G(i, k, θ)` of [quarteroni2000numerical] (5.43) carries `sin θ` in position `(i, k)`, so it is
`planeRotation i k (cos θ) (-sin θ)`, and the pair `(c, s)` of its (5.44) and (5.51) is
`(c, -s)` here; `givensPair` is written in the convention of this file. Nothing assumes
`c ^ 2 + s ^ 2 = 1` except the orthogonality statements, and nothing needs an order on the index
type; `j ≠ k` is a hypothesis of every lemma that needs one, the definition being degenerate at
`j = k`.

Consumers: Jacobi's eigenvalue algorithm (`Numlib/Eigen/Jacobi`), which conjugates a symmetric
matrix by a rotation chosen to annihilate one off-diagonal entry; the Givens `QR` factorization
of a Hessenberg matrix (`Numlib/LinearAlgebra/Matrix/QR`); and the complex Givens rotations of
the progressive `QR` factorization in `Numlib/Krylov/Hessenberg`, `Krylov.givensMatrix`, which
are `planeEmbed k (k + 1) !![conj c, conj s; -s, c]` (`Krylov.givensMatrix_eq_planeEmbed`).
-/

open Finset

namespace Matrix

variable {n R : Type*} [DecidableEq n]

/-! ### Embedding a `2 × 2` matrix in a coordinate plane -/

section PlaneEmbed

variable [Zero R] [One R]

/-- A `2 × 2` matrix `G` placed in the `(j, k)` coordinate plane: the identity outside the rows
and columns `j`, `k`, and `G` on that block, with `G 0 0` at `(j, j)`, `G 0 1` at `(j, k)`,
`G 1 0` at `(k, j)` and `G 1 1` at `(k, k)`. For `j = k` the definition is degenerate and no
lemma below assumes anything about it. -/
def planeEmbed (j k : n) (G : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  Matrix.of fun p q =>
    if p = j then (if q = j then G 0 0 else if q = k then G 0 1 else 0)
    else if p = k then (if q = j then G 1 0 else if q = k then G 1 1 else 0)
    else if p = q then 1 else 0

variable {j k : n} (G : Matrix (Fin 2) (Fin 2) R)

/-- The entries of a plane embedding, as a nested `if` on the row and then the column. -/
theorem planeEmbed_apply (p q : n) :
    planeEmbed j k G p q =
      if p = j then (if q = j then G 0 0 else if q = k then G 0 1 else 0)
      else if p = k then (if q = j then G 1 0 else if q = k then G 1 1 else 0)
      else if p = q then 1 else 0 := rfl

/-- Outside the rows `j`, `k` a plane embedding is the identity. -/
theorem planeEmbed_apply_of_ne_left {p : n} (hpj : p ≠ j) (hpk : p ≠ k) (q : n) :
    planeEmbed j k G p q = if p = q then 1 else 0 := by
  simp [planeEmbed_apply, hpj, hpk]

/-- Outside the columns `j`, `k` a plane embedding is the identity. -/
theorem planeEmbed_apply_of_ne_right (p : n) {q : n} (hqj : q ≠ j) (hqk : q ≠ k) :
    planeEmbed j k G p q = if p = q then 1 else 0 := by
  rw [planeEmbed_apply]
  split_ifs <;> simp_all

/-- The `2 × 2` block of a plane embedding is the embedded matrix: `![j, k]` indexes it. -/
theorem planeEmbed_apply_vecCons (hjk : j ≠ k) (a b : Fin 2) :
    planeEmbed j k G (![j, k] a) (![j, k] b) = G a b := by
  fin_cases a <;> fin_cases b <;> simp [planeEmbed_apply, hjk.symm]

/-- A plane embedding determines its `2 × 2` block. -/
theorem planeEmbed_injective (hjk : j ≠ k) :
    Function.Injective (planeEmbed j k : Matrix (Fin 2) (Fin 2) R → Matrix n n R) := by
  intro G G' h
  ext a b
  rw [← planeEmbed_apply_vecCons G hjk a b, ← planeEmbed_apply_vecCons G' hjk a b, h]

/-- The embedding of the identity is the identity. -/
theorem planeEmbed_one (hjk : j ≠ k) : planeEmbed j k (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext p q
  simp only [planeEmbed_apply, one_apply]
  split_ifs <;> simp_all

/-- An embedding is the identity exactly when its `2 × 2` block is. -/
theorem planeEmbed_eq_one_iff (hjk : j ≠ k) : planeEmbed j k G = 1 ↔ G = 1 :=
  ⟨fun h => planeEmbed_injective hjk (h.trans (planeEmbed_one hjk).symm),
    fun h => h ▸ planeEmbed_one hjk⟩

/-- Transposition commutes with the embedding. -/
theorem planeEmbed_transpose (hjk : j ≠ k) : (planeEmbed j k G)ᵀ = planeEmbed j k Gᵀ := by
  ext p q
  simp only [transpose_apply, planeEmbed_apply]
  split_ifs <;> subst_vars <;> simp_all

end PlaneEmbed

/-- Conjugate transposition commutes with the embedding. -/
theorem planeEmbed_conjTranspose [NonAssocSemiring R] [StarRing R] {j k : n} (hjk : j ≠ k)
    (G : Matrix (Fin 2) (Fin 2) R) : (planeEmbed j k G)ᴴ = planeEmbed j k Gᴴ := by
  ext p q
  simp only [conjTranspose_apply, planeEmbed_apply]
  split_ifs <;> subst_vars <;> simp_all

/-! ### The action of a plane embedding on rows and columns -/

section Mul

variable [Fintype n] [NonAssocSemiring R] {j k : n} (G : Matrix (Fin 2) (Fin 2) R)

omit [DecidableEq n] in
/-- A sum all of whose terms outside the pair `{j, k}` vanish. -/
private theorem sum_eq_add_of_ne (hjk : j ≠ k) (f : n → R) (hf : ∀ r, r ≠ j → r ≠ k → f r = 0) :
    ∑ r, f r = f j + f k := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({j, k} : Finset n))
    (fun r _ hr => hf r (fun h => hr (by simp [h])) fun h => hr (by simp [h])),
    Finset.sum_pair hjk]

/-- The row `p` of an embedding against a vector: rows `j`, `k` combine the entries `j`, `k`. -/
private theorem sum_planeEmbed_mul (hjk : j ≠ k) (f : n → R) (p : n) :
    ∑ r, planeEmbed j k G p r * f r =
      if p = j then G 0 0 * f j + G 0 1 * f k
      else if p = k then G 1 0 * f j + G 1 1 * f k
      else f p := by
  by_cases hpj : p = j
  · subst hpj
    rw [ite_eq_left rfl, sum_eq_add_of_ne hjk _ fun r hrj hrk => by
      simp [planeEmbed_apply, hrj, hrk]]
    simp [planeEmbed_apply, hjk.symm]
  by_cases hpk : p = k
  · subst hpk
    rw [ite_eq_right hpj, ite_eq_left rfl, sum_eq_add_of_ne hjk _ fun r hrj hrk => by
      simp [planeEmbed_apply, hrj, hrk, hpj]]
    simp [planeEmbed_apply, hjk.symm]
  · rw [ite_eq_right hpj, ite_eq_right hpk]
    simp [planeEmbed_apply_of_ne_left G hpj hpk, ite_mul, Finset.sum_ite_eq]

/-- A vector against the column `q` of an embedding: columns `j`, `k` combine the entries `j`,
`k`. -/
private theorem sum_mul_planeEmbed (hjk : j ≠ k) (f : n → R) (q : n) :
    ∑ r, f r * planeEmbed j k G r q =
      if q = j then f j * G 0 0 + f k * G 1 0
      else if q = k then f j * G 0 1 + f k * G 1 1
      else f q := by
  by_cases hqj : q = j
  · subst hqj
    rw [ite_eq_left rfl, sum_eq_add_of_ne hjk _ fun r hrj hrk => by
      simp [planeEmbed_apply, hrj, hrk]]
    simp [planeEmbed_apply, hjk.symm]
  by_cases hqk : q = k
  · subst hqk
    rw [ite_eq_right hqj, ite_eq_left rfl, sum_eq_add_of_ne hjk _ fun r hrj hrk => by
      simp [planeEmbed_apply, hrj, hrk]]
    simp [planeEmbed_apply, hjk.symm]
  · rw [ite_eq_right hqj, ite_eq_right hqk]
    simp [planeEmbed_apply_of_ne_right G _ hqj hqk, mul_ite, Finset.sum_ite_eq']

/-- Left multiplication by an embedded `2 × 2` matrix combines the rows `j` and `k` and leaves
the other rows alone ([quarteroni2000numerical] Program 34). -/
theorem planeEmbed_mul_apply (hjk : j ≠ k) (M : Matrix n n R) (p q : n) :
    (planeEmbed j k G * M) p q =
      if p = j then G 0 0 * M j q + G 0 1 * M k q
      else if p = k then G 1 0 * M j q + G 1 1 * M k q
      else M p q := by
  rw [mul_apply]
  exact sum_planeEmbed_mul G hjk (fun r => M r q) p

/-- Right multiplication by an embedded `2 × 2` matrix combines the columns `j` and `k` and
leaves the other columns alone ([quarteroni2000numerical] Program 35). -/
theorem mul_planeEmbed_apply (hjk : j ≠ k) (M : Matrix n n R) (p q : n) :
    (M * planeEmbed j k G) p q =
      if q = j then M p j * G 0 0 + M p k * G 1 0
      else if q = k then M p j * G 0 1 + M p k * G 1 1
      else M p q := by
  rw [mul_apply]
  exact sum_mul_planeEmbed G hjk (fun r => M p r) q

/-- An embedded `2 × 2` matrix acts on a vector through its `j`-th and `k`-th entries alone. -/
theorem planeEmbed_mulVec_apply (hjk : j ≠ k) (x : n → R) (p : n) :
    (planeEmbed j k G *ᵥ x) p =
      if p = j then G 0 0 * x j + G 0 1 * x k
      else if p = k then G 1 0 * x j + G 1 1 * x k
      else x p :=
  sum_planeEmbed_mul G hjk x p

/-- Away from the plane an embedded `2 × 2` matrix leaves the entries of a vector alone. -/
theorem planeEmbed_mulVec_apply_of_ne (hjk : j ≠ k) (x : n → R) {p : n} (hpj : p ≠ j)
    (hpk : p ≠ k) : (planeEmbed j k G *ᵥ x) p = x p := by
  rw [planeEmbed_mulVec_apply G hjk, ite_eq_right hpj, ite_eq_right hpk]

/-- A row vector against an embedded `2 × 2` matrix, the transpose of
`Matrix.planeEmbed_mulVec_apply`. -/
theorem vecMul_planeEmbed_apply (hjk : j ≠ k) (x : n → R) (q : n) :
    (x ᵥ* planeEmbed j k G) q =
      if q = j then x j * G 0 0 + x k * G 1 0
      else if q = k then x j * G 0 1 + x k * G 1 1
      else x q :=
  sum_mul_planeEmbed G hjk x q

/-- Two embeddings in the same plane compose as their `2 × 2` factors. -/
theorem planeEmbed_mul_planeEmbed (hjk : j ≠ k) (G' : Matrix (Fin 2) (Fin 2) R) :
    planeEmbed j k G * planeEmbed j k G' = planeEmbed j k (G * G') := by
  ext p q
  rw [planeEmbed_mul_apply G hjk]
  simp only [planeEmbed_apply, mul_apply, Fin.sum_univ_two]
  split_ifs <;> simp_all [hjk.symm]

end Mul

/-! ### Determinant and unitarity -/

section CommRing

variable [Fintype n] [CommRing R] {j k : n} (G : Matrix (Fin 2) (Fin 2) R)

/-- The `(j, k)`-plane, indexed by `Fin 2`. -/
private def planeEquiv (hjk : j ≠ k) : Fin 2 ≃ {i : n // i = j ∨ i = k} where
  toFun a := ![⟨j, Or.inl rfl⟩, ⟨k, Or.inr rfl⟩] a
  invFun i := if (i : n) = j then 0 else 1
  left_inv a := by fin_cases a <;> simp [hjk.symm]
  right_inv := by
    rintro ⟨i, hi | hi⟩ <;> subst hi <;> simp [hjk.symm]

/-- The determinant of an embedding is the determinant of its `2 × 2` block: the embedding is
block triangular with blocks `G` and an identity. -/
theorem det_planeEmbed (hjk : j ≠ k) : (planeEmbed j k G).det = G.det := by
  rw [twoBlockTriangular_det (planeEmbed j k G) (fun i => i = j ∨ i = k) fun i hi l hl => by
    rw [planeEmbed_apply_of_ne_left G (fun h => hi (Or.inl h)) fun h => hi (Or.inr h)]
    exact ite_eq_right fun h : i = l => hi (h ▸ hl)]
  have hone : toSquareBlockProp (planeEmbed j k G) (fun i => ¬(i = j ∨ i = k)) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    rw [toSquareBlockProp_def, of_apply, one_apply,
      planeEmbed_apply_of_ne_left G (fun h => ha (Or.inl h)) fun h => ha (Or.inr h)]
    simp [Subtype.ext_iff]
  rw [hone, det_one, mul_one, ← det_submatrix_equiv_self (planeEquiv hjk)]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [planeEquiv, toSquareBlockProp_def, planeEmbed_apply, hjk.symm]

/-- An embedded `2 × 2` matrix is unitary exactly when the `2 × 2` matrix is; this is what gives
`Krylov.givensMatrix` of `Numlib/Krylov/Hessenberg.lean` its unitarity. -/
theorem planeEmbed_mem_unitaryGroup_iff [StarRing R] (hjk : j ≠ k) :
    planeEmbed j k G ∈ unitaryGroup n R ↔ G ∈ unitaryGroup (Fin 2) R := by
  rw [mem_unitaryGroup_iff', mem_unitaryGroup_iff', star_eq_conjTranspose, star_eq_conjTranspose,
    planeEmbed_conjTranspose hjk, planeEmbed_mul_planeEmbed _ hjk, planeEmbed_eq_one_iff _ hjk]

end CommRing

/-! ### Plane rotations -/

/-- The rotation of the `(j,k)`-plane with cosine `c` and sine `s`: the identity matrix with its
`j`-th and `k`-th rows replaced by `(c, -s)` and `(s, c)` in the columns `j` and `k`; the Givens
matrix `G(i, k, θ)` of [quarteroni2000numerical] (5.43) is `planeRotation i k (cos θ) (-sin θ)`. -/
def planeRotation (j k : n) (c s : ℝ) : Matrix n n ℝ := planeEmbed j k !![c, -s; s, c]

variable {j k : n} {c s : ℝ}

/-- The entries of a plane rotation, written so that each column is a linear combination of
Kronecker deltas. -/
theorem planeRotation_apply (hjk : j ≠ k) (t q : n) :
    planeRotation j k c s t q =
      if q = j then (if t = j then c else 0) + (if t = k then s else 0)
      else if q = k then (if t = j then -s else 0) + (if t = k then c else 0)
      else if t = q then 1 else 0 := by
  rw [planeRotation, planeEmbed_apply]
  split_ifs <;> simp_all [hjk.symm]

/-- The transpose of a plane rotation is the rotation by the opposite angle. -/
theorem planeRotation_transpose (hjk : j ≠ k) :
    (planeRotation j k c s)ᵀ = planeRotation j k c (-s) := by
  rw [planeRotation, planeEmbed_transpose _ hjk, planeRotation]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp

variable [Fintype n]

/-- Multiplying on the right by a plane rotation combines the `j`-th and `k`-th columns. -/
theorem mul_planeRotation_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    (M * planeRotation j k c s) p q =
      if q = j then c * M p j + s * M p k
      else if q = k then -s * M p j + c * M p k
      else M p q := by
  rw [planeRotation, mul_planeEmbed_apply _ hjk]
  split_ifs <;> simp <;> ring

/-- Multiplying on the left by the transpose of a plane rotation combines the `j`-th and `k`-th
rows. -/
theorem transpose_planeRotation_mul_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    ((planeRotation j k c s)ᵀ * M) p q =
      if p = j then c * M j q + s * M k q
      else if p = k then -s * M j q + c * M k q
      else M p q := by
  rw [planeRotation_transpose hjk, planeRotation, planeEmbed_mul_apply _ hjk]
  split_ifs <;> simp

/-- The transpose of a plane rotation acts on a vector through its `j`-th and `k`-th entries. -/
theorem transpose_planeRotation_mulVec_apply (hjk : j ≠ k) (x : n → ℝ) (p : n) :
    ((planeRotation j k c s)ᵀ *ᵥ x) p =
      if p = j then c * x j + s * x k
      else if p = k then -s * x j + c * x k
      else x p := by
  rw [planeRotation_transpose hjk, planeRotation, planeEmbed_mulVec_apply _ hjk]
  split_ifs <;> simp

/-- A plane rotation is orthogonal. -/
theorem transpose_planeRotation_mul_self (hjk : j ≠ k) (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRotation j k c s)ᵀ * planeRotation j k c s = 1 := by
  rw [planeRotation_transpose hjk, planeRotation, planeRotation, planeEmbed_mul_planeEmbed _ hjk,
    planeEmbed_eq_one_iff _ hjk]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [mul_apply, Fin.sum_univ_two] <;> nlinarith [hcs]

/-- A plane rotation with `c ^ 2 + s ^ 2 = 1` belongs to the orthogonal group. -/
theorem planeRotation_mem_orthogonalGroup (hjk : j ≠ k) (hcs : c ^ 2 + s ^ 2 = 1) :
    planeRotation j k c s ∈ orthogonalGroup n ℝ :=
  (mem_orthogonalGroup_iff' n ℝ).2 (transpose_planeRotation_mul_self hjk hcs)

/-! ### Conjugation by a plane rotation -/

/-- Conjugating by a plane rotation leaves every entry outside the `j`-th and `k`-th rows and
columns alone. -/
theorem conj_planeRotation_apply_of_ne (hjk : j ≠ k) (M : Matrix n n ℝ) {p q : n}
    (hpj : p ≠ j) (hpk : p ≠ k) (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p q = M p q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk,
    hpj, hpk, hqj, hqk]

/-- The `(j,j)` entry of a matrix conjugated by a plane rotation. -/
theorem conj_planeRotation_apply_jj (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j j
      = c * (c * M j j + s * M j k) + s * (c * M k j + s * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk]
  ring

/-- The `(k,k)` entry of a matrix conjugated by a plane rotation. -/
theorem conj_planeRotation_apply_kk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k k
      = -s * (-s * M j j + c * M j k) + c * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- The `(j,k)` entry of a matrix conjugated by a plane rotation: the entry the Jacobi angle is
chosen to annihilate. -/
theorem conj_planeRotation_apply_jk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j k
      = c * (-s * M j j + c * M j k) + s * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- The `(p,j)` entry after a plane rotation, for `p` outside the rotated plane. -/
theorem conj_planeRotation_apply_col_j (hjk : j ≠ k) (M : Matrix n n ℝ) {p : n}
    (hpj : p ≠ j) (hpk : p ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p j = c * M p j + s * M p k := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hpj, hpk]

/-- The `(p,k)` entry after a plane rotation, for `p` outside the rotated plane. -/
theorem conj_planeRotation_apply_col_k (hjk : j ≠ k) (M : Matrix n n ℝ) {p : n}
    (hpj : p ≠ j) (hpk : p ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p k = -s * M p j + c * M p k := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hpj, hpk,
    Ne.symm hjk]

/-- The `(j,q)` entry after a plane rotation, for `q` outside the rotated plane. -/
theorem conj_planeRotation_apply_row_j (hjk : j ≠ k) (M : Matrix n n ℝ) {q : n}
    (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j q = c * M j q + s * M k q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hqj, hqk]

/-- The `(k,q)` entry after a plane rotation, for `q` outside the rotated plane. -/
theorem conj_planeRotation_apply_row_k (hjk : j ≠ k) (M : Matrix n n ℝ) {q : n}
    (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k q = -s * M j q + c * M k q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hqj, hqk,
    Ne.symm hjk]

/-! ### The Givens pair -/

/-- The cosine and sine `(c, s) = (a, b) / √(a² + b²)` of the rotation whose transpose sends
`(a, b)` to `(√(a² + b²), 0)`, and `(1, 0)` when `a = b = 0`: [quarteroni2000numerical] (5.44)
and (5.51), `c = x_i/α`, `s = -x_k/α`, read in the sign convention of `Matrix.planeRotation`
(their `s` is `-s` here), and Program 33 up to the choice of branch. -/
noncomputable def givensPair (a b : ℝ) : ℝ × ℝ :=
  if a = 0 ∧ b = 0 then (1, 0) else (a / √(a ^ 2 + b ^ 2), b / √(a ^ 2 + b ^ 2))

/-- The Givens pair when not both entries vanish. -/
theorem givensPair_of_not (a b : ℝ) (h : ¬(a = 0 ∧ b = 0)) :
    givensPair a b = (a / √(a ^ 2 + b ^ 2), b / √(a ^ 2 + b ^ 2)) := by
  rw [givensPair, ite_eq_right h]

/-- The Givens pair of `(0, 0)` is `(1, 0)`. -/
@[simp]
theorem givensPair_zero_zero : givensPair 0 0 = (1, 0) := by simp [givensPair]

/-- `a ^ 2 + b ^ 2 > 0` unless both vanish. -/
private theorem sq_add_sq_pos_of_not {a b : ℝ} (h : ¬(a = 0 ∧ b = 0)) : 0 < a ^ 2 + b ^ 2 := by
  rcases not_and_or.1 h with ha | hb
  · have := sq_pos_of_ne_zero ha; positivity
  · have := sq_pos_of_ne_zero hb; positivity

/-- The Givens pair lies on the unit circle. -/
theorem givensPair_sq_add_sq (a b : ℝ) :
    (givensPair a b).1 ^ 2 + (givensPair a b).2 ^ 2 = 1 := by
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [givensPair_of_not a b h]
    have hpos := sq_add_sq_pos_of_not h
    simp only [div_pow, Real.sq_sqrt hpos.le]
    rw [← add_div, div_self hpos.ne']

/-- The Givens pair rotates `(a, b)` onto the first axis: `c a + s b = √(a² + b²)` and
`-s a + c b = 0`, which is [quarteroni2000numerical] (5.51). -/
theorem givensPair_fst_mul_add_snd_mul (a b : ℝ) :
    (givensPair a b).1 * a + (givensPair a b).2 * b = √(a ^ 2 + b ^ 2) ∧
      -(givensPair a b).2 * a + (givensPair a b).1 * b = 0 := by
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [givensPair_of_not a b h]
    have hpos := sq_add_sq_pos_of_not h
    have hs : √(a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    refine ⟨?_, by ring⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← sq, ← sq,
      div_eq_iff hs, Real.mul_self_sqrt hpos.le]

/-- [quarteroni2000numerical] (5.44): the transpose of the rotation built from the Givens pair of
`(x j, x k)` annihilates the `k`-th entry of `x`, puts `√(x j ² + x k ²)` in the `j`-th, and
leaves every other entry alone. -/
theorem transpose_planeRotation_givensPair_mulVec (hjk : j ≠ k) (x : n → ℝ) :
    ((planeRotation j k (givensPair (x j) (x k)).1 (givensPair (x j) (x k)).2)ᵀ *ᵥ x) k = 0 ∧
      ((planeRotation j k (givensPair (x j) (x k)).1 (givensPair (x j) (x k)).2)ᵀ *ᵥ x) j =
        √(x j ^ 2 + x k ^ 2) ∧
      ∀ q, q ≠ j → q ≠ k →
        ((planeRotation j k (givensPair (x j) (x k)).1 (givensPair (x j) (x k)).2)ᵀ *ᵥ x) q =
          x q := by
  obtain ⟨h1, h2⟩ := givensPair_fst_mul_add_snd_mul (x j) (x k)
  refine ⟨?_, ?_, fun q hqj hqk => ?_⟩
  · rw [transpose_planeRotation_mulVec_apply hjk, ite_eq_right hjk.symm, ite_eq_left rfl, h2]
  · rw [transpose_planeRotation_mulVec_apply hjk, ite_eq_left rfl, h1]
  · rw [transpose_planeRotation_mulVec_apply hjk, ite_eq_right hqj, ite_eq_right hqk]

end Matrix
