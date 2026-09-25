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
import Mathlib.Basic.Sign.Defs
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

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

The **hyperbolic rotation** `Matrix.hyperbolicRotation j k c s = planeEmbed j k !![c, -s; -s, c]`
with `c² − s² = 1` is the indefinite counterpart of `planeRotation`: it is `J`-orthogonal
(`H J Hᵀ = J`, `Matrix.IsJOrthogonal`) for any signature `J = diagonal ε` with `ε j = 1`,
`ε k = −1`, and the **hyperbolic pair** `Matrix.hyperbolicPair a b` ([golub2013matrix] (6.5.13))
makes it annihilate the `k`-th entry of `x` when `|x k| < |x j|` — and nothing does when
`|x j| ≤ |x k|`, `x k ≠ 0`. `J`-orthogonality with Mathlib's symplectic form is membership in
`Matrix.symplecticGroup` (`Matrix.isJOrthogonal_iff_mem_symplecticGroup`).

## Main definitions

* `Matrix.planeEmbed j k G`: the `2 × 2` matrix `G` placed in the `(j, k)` coordinate plane.
* `Matrix.planeRotation j k c s`: the rotation of the `(j, k)`-plane with cosine `c` and sine `s`.
* `Matrix.givensPair a b`: the pair `(c, s) = (a, b) / √(a² + b²)`, and `(1, 0)` when `a = b = 0`.
* `Matrix.IsJOrthogonal J H`: `H J Hᵀ = J` ([golub2013matrix] (6.5.11), "`S`-orthogonal").
* `Matrix.hyperbolicRotation j k c s`, `Matrix.hyperbolicPair a b`: the hyperbolic rotation and
  the pair `(c, s)` that makes it introduce a zero ([golub2013matrix] §6.5.4).

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

/-! ### `J`-orthogonal matrices and hyperbolic rotations -/

section JOrthogonal

variable [CommRing R]

/-- **`J`-orthogonality** ([golub2013matrix] (6.5.11), "`S`-orthogonal"; Higham, "J-orthogonal
matrices", SIAM Review 2003): `H J Hᵀ = J`. For `J = 1` it is membership in the orthogonal group
(`Matrix.isJOrthogonal_one_iff_mem_orthogonalGroup`), for Mathlib's symplectic form `J l R`
membership in the symplectic group (`Matrix.isJOrthogonal_iff_mem_symplecticGroup`). -/
def IsJOrthogonal (J H : Matrix n n R) : Prop := H * J * Hᵀ = J

/-- The identity is `J`-orthogonal. -/
theorem isJOrthogonal_one (J : Matrix n n R) : IsJOrthogonal J 1 := by
  simp [IsJOrthogonal]

omit [DecidableEq n] in
/-- **Products of `J`-orthogonal matrices are `J`-orthogonal** ([golub2013matrix] §6.5.4). -/
theorem IsJOrthogonal.mul {J H₁ H₂ : Matrix n n R} (h₁ : IsJOrthogonal J H₁)
    (h₂ : IsJOrthogonal J H₂) : IsJOrthogonal J (H₁ * H₂) := by
  unfold IsJOrthogonal at *
  calc H₁ * H₂ * J * (H₁ * H₂)ᵀ = H₁ * (H₂ * J * H₂ᵀ) * H₁ᵀ := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h₂, h₁]

/-- For an involutive signature, `H J Hᵀ = J` gives `Hᵀ J H = J`: `J Hᵀ J` is a right, hence a
left, inverse of `H`. -/
private theorem transpose_mul_mul_eq_of_isJOrthogonal {J H : Matrix n n R} (hJ : J * J = 1)
    (h : IsJOrthogonal J H) : Hᵀ * J * H = J := by
  have h1 : H * (J * Hᵀ * J) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [IsJOrthogonal] at h
    rw [h, hJ]
  have h2 : J * Hᵀ * J * H = 1 := mul_eq_one_comm.1 h1
  calc Hᵀ * J * H = J * J * (Hᵀ * J * H) := by rw [hJ, Matrix.one_mul]
    _ = J * (J * Hᵀ * J * H) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, Matrix.mul_one]

/-- For an involutive signature (`J * J = 1`), the transpose of a `J`-orthogonal matrix is
`J`-orthogonal: `H J Hᵀ = J` gives `Hᵀ J H = J`, the form of [golub2013matrix] P6.5.5. -/
theorem IsJOrthogonal.transpose {J H : Matrix n n R} (hJ : J * J = 1) (h : IsJOrthogonal J H) :
    IsJOrthogonal J Hᵀ := by
  change Hᵀ * J * Hᵀᵀ = J
  rw [transpose_transpose]
  exact transpose_mul_mul_eq_of_isJOrthogonal hJ h

/-- For an involutive signature, `H` is `J`-orthogonal iff `Hᵀ` is. -/
theorem isJOrthogonal_transpose_iff {J H : Matrix n n R} (hJ : J * J = 1) :
    IsJOrthogonal J Hᵀ ↔ IsJOrthogonal J H :=
  ⟨fun h => by simpa using h.transpose hJ, fun h => h.transpose hJ⟩

/-- For `J = 1`, `J`-orthogonality is orthogonality. -/
theorem isJOrthogonal_one_iff_mem_orthogonalGroup {H : Matrix n n R} :
    IsJOrthogonal 1 H ↔ H ∈ Matrix.orthogonalGroup n R := by
  rw [IsJOrthogonal, Matrix.mul_one, mem_orthogonalGroup_iff]

/-- **The bridge to Mathlib's symplectic group**: for Mathlib's `J l R`, `J`-orthogonality is
membership in `Matrix.symplecticGroup l R`, whose carrier is literally `A J Aᵀ = J`. -/
theorem isJOrthogonal_iff_mem_symplecticGroup {l : Type*} [DecidableEq l] [Fintype l]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    IsJOrthogonal (Matrix.J l R) A ↔ A ∈ Matrix.symplecticGroup l R :=
  SymplecticGroup.mem_iff.symm

end JOrthogonal

section Hyperbolic

/-- **The hyperbolic rotation** ([golub2013matrix] §6.5.4, `H_k(θ)`): `!![c, -s; -s, c]` in the
`(j, k)`-plane. With `c = cosh θ`, `s = sinh θ` it is `J`-orthogonal for the signature that is
`+1` at `j` and `-1` at `k` (`Matrix.isJOrthogonal_hyperbolicRotation`). -/
def hyperbolicRotation (j k : n) (c s : ℝ) : Matrix n n ℝ := planeEmbed j k !![c, -s; -s, c]

omit [Fintype n] in
/-- A hyperbolic rotation is symmetric. -/
theorem hyperbolicRotation_transpose {j k : n} (hjk : j ≠ k) (c s : ℝ) :
    (hyperbolicRotation j k c s)ᵀ = hyperbolicRotation j k c s := by
  rw [hyperbolicRotation, planeEmbed_transpose _ hjk]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

/-- **Hyperbolic rotations are `J`-orthogonal** ([golub2013matrix] §6.5.4, "the `S`-orthogonality
of this matrix follows from `cosh(θ)² − sinh(θ)² = 1`"): for a signature `ε` with `ε j = 1` and
`ε k = -1`, and `c² - s² = 1`, `H (diagonal ε) Hᵀ = diagonal ε`. -/
theorem isJOrthogonal_hyperbolicRotation {j k : n} (hjk : j ≠ k) {ε : n → ℝ} (hj : ε j = 1)
    (hk : ε k = -1) {c s : ℝ} (hcs : c ^ 2 - s ^ 2 = 1) :
    IsJOrthogonal (diagonal ε) (hyperbolicRotation j k c s) := by
  rw [IsJOrthogonal, hyperbolicRotation_transpose hjk, Matrix.mul_assoc]
  ext p q
  rw [hyperbolicRotation, planeEmbed_mul_apply _ hjk]
  simp only [diagonal_mul, planeEmbed_apply, diagonal_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
  by_cases hpj : p = j
  · subst hpj
    by_cases hqp : q = p
    · subst hqp
      simp [hjk.symm, hj, hk]
      linear_combination hcs
    by_cases hqk : q = k
    · subst hqk
      simp [hqp, hjk, hj, hk]
      ring
    · simp [hqp, hqk, Ne.symm hqp]
  by_cases hpk : p = k
  · subst hpk
    by_cases hqj : q = j
    · subst hqj
      simp [hjk.symm, hj, hk]
      ring
    by_cases hqp : q = p
    · subst hqp
      simp [hj, hk, hqj]
      nlinarith [hcs]
    · simp [hqp, hqj, Ne.symm hqp]
  · by_cases hqj : q = j
    · subst hqj
      simp [hpj, hpk]
    by_cases hqk : q = k
    · subst hqk
      simp [hpj, hpk]
    · by_cases hpq : p = q
      · subst hpq
        simp [hpj, hpk]
      · simp [hpj, hpk, hpq]

end Hyperbolic

/-- **The hyperbolic pair** ([golub2013matrix] (6.5.13)): `(c, s) = (c, c τ)` with `τ = b / a`,
`c = 1 / √(1 - τ²)`; meaningful when `|b| < |a|`. The hyperbolic counterpart of
`Matrix.givensPair`. -/
noncomputable def hyperbolicPair (a b : ℝ) : ℝ × ℝ :=
  (1 / √(1 - (b / a) ^ 2), 1 / √(1 - (b / a) ^ 2) * (b / a))

/-- The ratio `τ = b / a` of a hyperbolic pair has `τ² < 1` when `|b| < |a|`. -/
private theorem one_sub_div_sq_pos {a b : ℝ} (h : |b| < |a|) : 0 < 1 - (b / a) ^ 2 := by
  have ha : a ≠ 0 := fun ha => by
    rw [ha, abs_zero] at h
    exact absurd h (not_lt.2 (abs_nonneg b))
  have hab : b ^ 2 < a ^ 2 := sq_lt_sq.2 h
  rw [div_pow, sub_pos, div_lt_one (by positivity)]
  exact hab

/-- **The hyperbolic pair is hyperbolic** ([golub2013matrix] (6.5.13)): `c² - s² = 1`, `c > 0`. -/
theorem hyperbolicPair_sq_sub_sq {a b : ℝ} (h : |b| < |a|) :
    (hyperbolicPair a b).1 ^ 2 - (hyperbolicPair a b).2 ^ 2 = 1 ∧ 0 < (hyperbolicPair a b).1 := by
  have hpos := one_sub_div_sq_pos h
  have hr : 0 < √(1 - (b / a) ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : √(1 - (b / a) ^ 2) ^ 2 = 1 - (b / a) ^ 2 := Real.sq_sqrt hpos.le
  refine ⟨?_, by simp only [hyperbolicPair]; positivity⟩
  simp only [hyperbolicPair]
  generalize b / a = τ at hpos hsq ⊢
  rw [mul_pow, div_pow, one_pow, hsq]
  field_simp [hpos.ne']

/-- **Hyperbolic rotations introduce zeros** ([golub2013matrix] §6.5.4, (6.5.13)): if
`|x k| < |x j|` and `(c, s)` is the hyperbolic pair of `(x j, x k)`, the hyperbolic rotation
annihilates the `k`-th entry of `x` and puts `sign (x j) √(x j² - x k²)` in the `j`-th; the other
entries are unchanged (`Matrix.planeEmbed_mulVec_apply_of_ne`). -/
theorem hyperbolicRotation_hyperbolicPair_mulVec {j k : n} (hjk : j ≠ k)
    {x : n → ℝ} (h : |x k| < |x j|) :
    (hyperbolicRotation j k (hyperbolicPair (x j) (x k)).1 (hyperbolicPair (x j) (x k)).2 *ᵥ x) k
        = 0 ∧
      (hyperbolicRotation j k (hyperbolicPair (x j) (x k)).1 (hyperbolicPair (x j) (x k)).2 *ᵥ x) j
        = SignType.sign (x j) * √(x j ^ 2 - x k ^ 2) := by
  have ha : x j ≠ 0 := fun ha => by
    rw [ha, abs_zero] at h
    exact absurd h (not_lt.2 (abs_nonneg _))
  have hD : 0 < x j ^ 2 - x k ^ 2 := sub_pos.2 (sq_lt_sq.2 h)
  have hsqrt : √(1 - (x k / x j) ^ 2) = √(x j ^ 2 - x k ^ 2) / |x j| := by
    rw [show 1 - (x k / x j) ^ 2 = (x j ^ 2 - x k ^ 2) / |x j| ^ 2 by
      rw [sq_abs]; field_simp, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  have hr : 0 < √(x j ^ 2 - x k ^ 2) := Real.sqrt_pos.2 hD
  have hrr : √(x j ^ 2 - x k ^ 2) ^ 2 = x j ^ 2 - x k ^ 2 := Real.sq_sqrt hD.le
  rw [hyperbolicRotation, planeEmbed_mulVec_apply _ hjk, planeEmbed_mulVec_apply _ hjk]
  simp only [hjk.symm, ite_true, ite_false, hyperbolicPair, hsqrt, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · rw [abs_of_neg hneg, sign_neg hneg, SignType.coe_neg_one]
      field_simp
      linear_combination hrr
    · rw [abs_of_pos hpos, sign_pos hpos, SignType.coe_one]
      field_simp
      linear_combination -hrr

/-- **The hyperbolic pair may not exist** ([golub2013matrix] §6.5.4, "there is no real solution
to `−s x₁ + c x₂ = 0` if `|x₂| > |x₁|`"): if `|x₁| ≤ |x₂|` and `x₂ ≠ 0` no `c² - s² = 1` solves
it (the book states the strict inequality; equality fails as well). -/
theorem not_exists_hyperbolic_of_abs_le {x₁ x₂ : ℝ} (h : |x₁| ≤ |x₂|) (hx₂ : x₂ ≠ 0) :
    ¬ ∃ c s : ℝ, c ^ 2 - s ^ 2 = 1 ∧ -s * x₁ + c * x₂ = 0 := by
  rintro ⟨c, s, hcs, hz⟩
  have h12 : x₁ ^ 2 ≤ x₂ ^ 2 := sq_le_sq.2 h
  have hx : 0 < x₂ ^ 2 := by positivity
  have hsq : c ^ 2 * x₂ ^ 2 = s ^ 2 * x₁ ^ 2 := by
    have : c * x₂ = s * x₁ := by linarith
    rw [← mul_pow, ← mul_pow, this]
  nlinarith [mul_le_mul_of_nonneg_left h12 (sq_nonneg s)]

end Matrix
