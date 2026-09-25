/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.QR`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.PlaneRotation

/-!
# Householder reflectors and the QR factorization

A **Householder reflector** `Matrix.householder w = 1 - 2 w wᴴ` is the reflection in the hyperplane
orthogonal to a unit vector `w`; it is Hermitian, involutive and therefore unitary. Its defining
property is that one reflector annihilates every entry of a vector but one
(`Matrix.householder_mulVec_eq_smul_single`), and an induction over the columns then triangularizes
any matrix by a product of reflectors (`Matrix.exists_unitary_mul_upperTriangular`).

The same factorization is reached from the other end by orthonormalizing the columns:
`Matrix.exists_qr` factors a matrix with linearly independent columns as `X = Q R` with `Qᴴ Q = 1`
and `R` upper triangular of positive diagonal, taking `Q` to be
`InnerProductSpace.gramSchmidtNormed` of the columns and `R i j = ⟪Q i, X j⟫`.  The two routes meet
at `Matrix.qr_unique`: the factorization with a positive diagonal is unique, so a product of
reflectors, classical Gram–Schmidt and modified Gram–Schmidt all compute the same `Q` and the same
`R`.

The second half of the file is the Householder and Givens machinery of the eigenvalue algorithms
of [quarteroni2000numerical] §5.6 and §5.8: the **tail reflector** `Matrix.householderTail x p`,
which keeps the coordinates before a pivot `p` and annihilates those after it; the **Householder
reduction to Hessenberg form** `Matrix.hessenbergReduce`, a unitary similarity `Qᴴ A Q` by `N - 2`
tail reflectors, tridiagonal for a Hermitian `A`; and the **Givens `QR` factorization of a
Hessenberg matrix** `Matrix.hessenbergGivensQR`, by `N - 1` plane rotations, whose `Q` is again
Hessenberg. The tail reflectors alternating on the two sides also give the Golub–Kahan
bidiagonalization, which is in `Numlib/LinearAlgebra/Matrix/Bidiagonal`.

Nothing here is numerical: no stability, no operation count, no pivoting.

This serves [saad2003iterative], §1.7 — the reflector (1.20), its defining conditions (1.21)–(1.26),
the factorization (1.19), the triangularization (1.27)–(1.28) and Algorithm 1.3 —
[kress1998numerical], §5, and [quarteroni2000numerical], §5.6.1–5.6.3, §5.6.5 and §5.8.3.

## Main definitions

* `Matrix.householder`: the reflector `1 - 2 w wᴴ` in the hyperplane orthogonal to `w`.
* `Matrix.reflector`: the reflector `1 - (2 / vᴴ v) v vᴴ` of an unnormalized axis `v`, the
  `P = I - β v vᵀ` of [golub2013matrix] (5.1.1).
* `Matrix.phase`: the unit-modulus phase of a scalar, `1` at zero; [saad2003iterative] `sign`.
* `Matrix.householderAxis`, `Matrix.householderVec`: the axis `x + sign(x i) ‖x‖ eᵢ` of the
  reflector that annihilates every entry of `x` but the `i`-th, and its normalization.
* `Matrix.householderTail`: the axis of the reflector acting on the coordinates from a pivot on.
* `Matrix.hessenbergReduce`, `Matrix.hessenbergQ`: the Householder reduction to Hessenberg form
  and its unitary matrix, built from `Matrix.hessenbergStep`.
* `Matrix.hessenbergGivensQR`: the Givens `QR` factorization of a real Hessenberg matrix.
* `Matrix.IsQR A Q R`: the full QR factorization `A = Q R` of an `M × N` matrix, `Q` unitary and `R`
  upper trapezoidal ([quarteroni2000numerical] Definition 3.1); `Matrix.firstColumns`,
  `Matrix.firstRows`: the reduced factors `Q̃ = Q(1:m, 1:n)`, `R̃ = R(1:n, 1:n)` of (3.48).
* `Matrix.IsThinQR A Q R`: the thin factorization `A = Q R`, `Qᴴ Q = 1`, `R` upper triangular
  ([golub2013matrix] (5.2.2)); `Matrix.IsPivotedQR A Q R σ`: QR with column pivoting,
  `A Π = Q R`.

## Main results

* `Matrix.householder_mulVec_eq_smul_single`: one reflector annihilates every entry of a vector but
  one; `Matrix.householder_tail_mulVec` is the same for the tail of a vector.
* `Matrix.reflector_mulVec_eq_of_sq`: the reflector of `x + α eᵢ`, `ᾱ α = ‖x‖²`, `ᾱ xᵢ` real,
  sends `x` to `-α eᵢ` — the defining property with either sign ([golub2013matrix] (5.1.2));
  `Matrix.reflector_eq_householder`, `Matrix.reflector_mem_unitaryGroup`.
* `Matrix.conj_one_sub_smul_vecMulVec_eq_sub`: `P B P = B - v wᴴ - w vᴴ` for Hermitian `B`, the
  rank-two form of a two-sided reflection ([golub2013matrix] §8.3.1), over any field with a star.
* `Matrix.householder_mul_eq_sub_vecMulVec`, `Matrix.mul_householder_eq_sub_vecMulVec`: applying
  a reflector is a rank-one update.
* `Matrix.exists_unitary_mul_upperTriangular`: a product of reflectors triangularizes any matrix;
  `Matrix.exists_unitary_mul_isUpperTriangular` is its form on any finite linear order.
* `Matrix.exists_qr`: the Gram–Schmidt factorization `X = Q R` of a matrix with linearly independent
  columns, and its converse `Matrix.linearIndependent_of_qr`.
* `Matrix.qr_unique`: the factorization with a positive diagonal is unique, so all three
  constructions compute the same pair.
* `Matrix.exists_isQR`, `Matrix.IsQR.reduced`: the full QR factorization exists, from the
  Householder triangularization, and yields the reduced factorization `A = Q̃ R̃`,
  `Q̃ᴴ Q̃ = 1`, `R̃` upper triangular ([quarteroni2000numerical] Property 3.3), whose columns
  span the column space of `A` when `A` has full column rank
  (`Matrix.IsQR.span_firstColumns_eq`). Uniqueness, which Property 3.3 also claims, holds only
  with a normalization of the diagonal of `R̃` (`Matrix.qr_unique`).
* `Matrix.exists_isThinQR`, `Matrix.IsThinQR.unique`, `Matrix.IsQR.isThinQR`: the thin
  factorization ([golub2013matrix] Theorem 5.2.3); `Matrix.IsQR.span_col_prefix_eq`: the leading
  columns of `A` and `Q` span the same spaces ((5.2.1)).
* `Matrix.prod_one_sub_vecMulVec_of_orthonormal`: the product of the deflations
  `1 - qᵢ qᵢᴴ` of pairwise orthogonal vectors is `1 - ∑ qᵢ qᵢᴴ`, the identity behind modified
  Gram–Schmidt ([golub2013matrix] §5.2.8).
* `Matrix.hessenbergReduce_eq_conj`, `Matrix.isUpperHessenberg_hessenbergReduce`,
  `Matrix.exists_unitary_conj_isUpperHessenberg`: the Householder reduction is a unitary
  similarity to upper Hessenberg form, tridiagonal for Hermitian input
  (`Matrix.isTridiagonal_hessenbergReduce_of_isHermitian`).
* `Matrix.hessenbergGivensQR_spec`: the Givens factorization of a Hessenberg matrix is a `QR`
  factorization with a Hessenberg `Q`.
* `Matrix.norm_det_le_prod_sqrt_sum_norm_sq`: **Hadamard's determinant inequality**, a corollary
  of the triangularization, with `Matrix.norm_det_le_of_forall_norm_le` its entrywise form.

## Implementation notes

The algorithms of §5.6 step through the columns, so they are stated on `Fin N` with the step
index in `ℕ`: a step whose pivot lies beyond `N` is the identity (`Matrix.householderTail` is `0`
there), which is what makes the folds total and the invariants inductions on `ℕ` without `Fin`
casts. The existence statements are transported to any finite linear order.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### The Euclidean length of a vector of scalars -/

/-- The Euclidean inner square of a vector of scalars: `star x ⬝ᵥ x = ‖x‖²`. -/
private theorem star_dotProduct_self (x : n → 𝕜) :
    star x ⬝ᵥ x = ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2 := by
  rw [← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

private theorem ofReal_norm_toLp_ne_zero {x : n → 𝕜} (hx : x ≠ 0) :
    ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ≠ 0 := by
  have hne : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := by simpa using hx
  simpa using norm_ne_zero_iff.2 hne

private theorem norm_toLp_pos {x : n → 𝕜} (hx : x ≠ 0) :
    (0 : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ := by
  have hne : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := by simpa using hx
  exact norm_pos_iff.2 hne

/-- The vector `v` scaled to unit Euclidean length. -/
private noncomputable def normalize (v : n → 𝕜) : n → 𝕜 :=
  ((‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ : 𝕜))⁻¹ • v

private theorem star_dotProduct_normalize_self {v : n → 𝕜} (hv : v ≠ 0) :
    star (normalize v) ⬝ᵥ normalize v = 1 := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [normalize, star_smul, smul_dotProduct, dotProduct_smul, RCLike.star_def, RCLike.conj_inv,
    RCLike.conj_ofReal, smul_eq_mul, smul_eq_mul, star_dotProduct_self]
  field_simp

private theorem normalize_apply_eq_zero {v : n → 𝕜} {r : n} (h : v r = 0) :
    normalize v r = 0 := by simp [normalize, h]

/-! ### Householder reflectors -/

variable [DecidableEq n]

/-- The Householder reflector `1 - 2 w wᴴ`, the reflection in the hyperplane orthogonal to `w` when
`w` is a unit vector, and the identity when `w = 0`. -/
def householder (w : n → 𝕜) : Matrix n n 𝕜 := 1 - (2 : 𝕜) • vecMulVec w (star w)

omit [Fintype n] in
/-- The entries of a Householder reflector. -/
theorem householder_apply (w : n → 𝕜) (i j : n) :
    householder w i j = (if i = j then 1 else 0) - 2 * (w i * star (w j)) := by
  simp [householder, one_apply, vecMulVec_apply]

omit [Fintype n] in
/-- The reflector of the zero axis is the identity. -/
@[simp]
theorem householder_zero : householder (0 : n → 𝕜) = 1 := by simp [householder]

omit [Fintype n] in
/-- A Householder reflector is Hermitian, whatever the axis. -/
theorem isHermitian_householder (w : n → 𝕜) : IsHermitian (householder w) := by
  ext i j
  simp only [conjTranspose_apply, householder_apply, star_sub, star_mul', RCLike.star_def,
    map_ofNat, apply_ite (starRingEnd 𝕜), map_one, map_zero, starRingEnd_self_apply]
  by_cases h : i = j
  · subst h
    ring
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
    ring

/-- The reflector acts by `x ↦ x - 2 ⟪w, x⟫ w`. -/
theorem householder_mulVec (w x : n → 𝕜) :
    householder w *ᵥ x = x - (2 * (star w ⬝ᵥ x)) • w := by
  funext i
  have h : ∀ j, householder w i j * x j
      = (if i = j then x j else 0) - 2 * (star (w j) * x j) * w i := by
    intro j
    rw [householder_apply]
    by_cases hij : i = j <;> simp [hij] <;> ring
  have hsum2 : ∑ j : n, 2 * (star (w j) * x j) * w i = (2 * (star w ⬝ᵥ x)) * w i := by
    simp only [dotProduct, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [mulVec, dotProduct, Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, hsum2]
  simp

/-- A unit vector gives an involutive reflector. -/
theorem householder_mul_self {w : n → 𝕜} (hw : star w ⬝ᵥ w = 1) :
    householder w * householder w = 1 := by
  have hP : vecMulVec w (star w) * vecMulVec w (star w) = vecMulVec w (star w) := by
    rw [vecMulVec_mul_vecMulVec]
    congr 1
    rw [show (star w : n → 𝕜) ⬝ᵥ w = 1 from hw, one_smul]
  have h2 : ((2 : 𝕜) • vecMulVec w (star w)) * ((2 : 𝕜) • vecMulVec w (star w))
      = (4 : 𝕜) • vecMulVec w (star w) := by
    rw [smul_mul_smul_comm, hP]
    norm_num
  simp only [householder, sub_mul, mul_sub, one_mul, mul_one, h2]
  module

/-- The reflector of a unit vector is unitary. -/
theorem householder_mem_unitaryGroup {w : n → 𝕜} (hw : star w ⬝ᵥ w = 1) :
    householder w ∈ Matrix.unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hs : (star (householder w) : Matrix n n 𝕜) = householder w := isHermitian_householder w
  rw [hs, householder_mul_self hw]

/-- The reflector built from an unnormalized axis `v` sends `x` to `x - (2 ⟪v, x⟫ / ⟪v, v⟫) v`. -/
private theorem householder_normalize_mulVec {v : n → 𝕜} (hv : v ≠ 0) (x : n → 𝕜) :
    householder (normalize v) *ᵥ x = x - (2 * (star v ⬝ᵥ x) / (star v ⬝ᵥ v)) • v := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [householder_mulVec, normalize, star_smul, smul_dotProduct, RCLike.star_def, RCLike.conj_inv,
    RCLike.conj_ofReal, smul_eq_mul, smul_smul, star_dotProduct_self]
  congr 2
  field_simp

/-! ### The reflector that annihilates a column below one entry -/

/-- The unit-modulus phase of a scalar, and `1` at zero: the `sign` of [saad2003iterative] (1.22).
-/
noncomputable def phase (z : 𝕜) : 𝕜 := if z = 0 then 1 else ((‖z‖ : 𝕜))⁻¹ * z

/-- The phase of `0` is `1`, by convention. -/
@[simp]
theorem phase_zero : phase (0 : 𝕜) = 1 := by simp [phase]

/-- The phase has modulus one. -/
@[simp]
theorem norm_phase (z : 𝕜) : ‖phase z‖ = 1 := by
  rw [phase]
  by_cases h : z = 0
  · simp [h]
  · rw [ite_eq_right h, norm_mul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- The defining property of the phase: `conj (sign z) * z = |z|`, a nonnegative real.  This is what
makes the denominator of [saad2003iterative] (1.22) bounded away from zero. -/
theorem conj_phase_mul_self (z : 𝕜) : starRingEnd 𝕜 (phase z) * z = ((‖z‖ : 𝕜)) := by
  rw [phase]
  by_cases h : z = 0
  · simp [h]
  · rw [ite_eq_right h, map_mul, RCLike.conj_inv, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    have hz : ((‖z‖ : 𝕜)) ≠ 0 := by simpa using norm_ne_zero_iff.2 h
    field_simp

/-- [saad2003iterative] (1.22): the axis `x + sign(x i) ‖x‖ e_i` of the reflector that annihilates
every entry of `x` but the `i`-th. -/
noncomputable def householderAxis (x : n → 𝕜) (i : n) : n → 𝕜 :=
  x + (phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)))
    • (Pi.single i 1 : n → 𝕜)

/-- [saad2003iterative] (1.22): the unit vector whose reflector annihilates every entry of `x` but
the `i`-th. -/
noncomputable def householderVec (x : n → 𝕜) (i : n) : n → 𝕜 := normalize (householderAxis x i)

/-- Away from the pivot the reflector's axis agrees with the vector it is built from. -/
theorem householderAxis_apply_of_ne (x : n → 𝕜) {r i : n} (h : r ≠ i) :
    householderAxis x i r = x r := by
  simp [householderAxis, Pi.single_eq_of_ne h]

/-- The reflector's axis inherits the vanishing of `x` away from the pivot, which is what lets a
reflector act on a trailing block of coordinates only. -/
theorem householderVec_apply_eq_zero {x : n → 𝕜} {r i : n} (hri : r ≠ i) (h : x r = 0) :
    householderVec x i r = 0 :=
  normalize_apply_eq_zero (by rw [householderAxis_apply_of_ne x hri, h])

omit [Fintype n] in
private theorem star_single_one (i : n) :
    star (Pi.single i 1 : n → 𝕜) = (Pi.single i 1 : n → 𝕜) := by
  funext r
  rcases eq_or_ne r i with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

/-- `⟪v, x⟫` for the Householder axis `v` is the nonnegative real `‖x‖² + ‖x‖ |x i|`. -/
private theorem star_householderAxis_dotProduct (x : n → 𝕜) (i : n) :
    star (householderAxis x i) ⬝ᵥ x
      = (((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2
          + ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ * ‖x i‖ : ℝ)) : 𝕜) := by
  rw [householderAxis, star_add, add_dotProduct, star_smul, smul_dotProduct, star_single_one,
    single_dotProduct, star_dotProduct_self, RCLike.star_def, map_mul, RCLike.conj_ofReal,
    smul_eq_mul]
  push_cast
  linear_combination
    ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) * conj_phase_mul_self (x i)

/-- `⟪v, v⟫ = 2 ⟪v, x⟫` for the Householder axis `v`: the sign choice is exactly what makes the two
agree up to the factor two. -/
private theorem star_householderAxis_dotProduct_self (x : n → 𝕜) (i : n) :
    star (householderAxis x i) ⬝ᵥ householderAxis x i
      = 2 * (star (householderAxis x i) ⬝ᵥ x) := by
  have hself : star (householderAxis x i) ⬝ᵥ (Pi.single i 1 : n → 𝕜)
      = starRingEnd 𝕜 (householderAxis x i i) := by
    rw [dotProduct_single, mul_one]
    rfl
  have hval : householderAxis x i i
      = x i + phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) := by
    simp [householderAxis]
  have h1 : phase (x i) * starRingEnd 𝕜 (x i) = ((‖x i‖ : 𝕜)) := by
    have h := congrArg (starRingEnd 𝕜) (conj_phase_mul_self (x i))
    rwa [map_mul, starRingEnd_self_apply, RCLike.conj_ofReal] at h
  have h2 : phase (x i) * starRingEnd 𝕜 (phase (x i)) = 1 := by
    rw [RCLike.mul_conj, norm_phase]
    norm_num
  nth_rewrite 2 [householderAxis]
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hself, hval, star_householderAxis_dotProduct,
    map_add, map_mul, RCLike.conj_ofReal]
  push_cast
  linear_combination ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) * h1
    + ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2 * h2

/-- The Householder axis `x + sign(x_i) ‖x‖₂ e_i` is nonzero when `x` is. -/
theorem householderAxis_ne_zero {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    householderAxis x i ≠ 0 := by
  intro h
  have hd := star_householderAxis_dotProduct x i
  rw [h] at hd
  simp only [star_zero, zero_dotProduct] at hd
  have hpos : (0 : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2
      + ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ * ‖x i‖ := by
    have := norm_toLp_pos hx
    positivity
  rw [eq_comm, RCLike.ofReal_eq_zero] at hd
  exact hpos.ne' hd

/-- The unit Householder vector really is a unit vector. -/
theorem star_dotProduct_householderVec_self {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    star (householderVec x i) ⬝ᵥ householderVec x i = 1 :=
  star_dotProduct_normalize_self (householderAxis_ne_zero hx i)

/-- The reflector that annihilates a nonzero vector below its `i`-th entry is unitary. -/
theorem householder_householderVec_mem_unitaryGroup {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    householder (householderVec x i) ∈ Matrix.unitaryGroup n 𝕜 :=
  householder_mem_unitaryGroup (star_dotProduct_householderVec_self hx i)

/-- [saad2003iterative] (1.21)–(1.22): the Householder reflector in the hyperplane orthogonal to `w
= (x + sign(x i) ‖x‖ e_i) / ‖x + sign(x i) ‖x‖ e_i‖` sends `x` to `(- sign(x i) ‖x‖) e_i`, so a
single reflector annihilates every entry of `x` but the `i`-th. -/
theorem householder_mulVec_eq_smul_single {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    householder (householderVec x i) *ᵥ x
      = (-(phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜))))
        • (Pi.single i 1 : n → 𝕜) := by
  have hv := householderAxis_ne_zero hx i
  have hd : star (householderAxis x i) ⬝ᵥ householderAxis x i
      = 2 * (star (householderAxis x i) ⬝ᵥ x) := star_householderAxis_dotProduct_self x i
  have hvv : star (householderAxis x i) ⬝ᵥ householderAxis x i ≠ 0 := by
    rw [star_dotProduct_self]
    exact pow_ne_zero 2 (ofReal_norm_toLp_ne_zero hv)
  rw [householderVec, householder_normalize_mulVec hv, ← hd, div_self hvv, one_smul,
    householderAxis]
  module

/-! ### Householder reflectors of an unnormalized axis -/

/-- **The Householder reflector of an axis** `v`, not necessarily of unit length:
`reflector v = 1 - (2 / vᴴ v) v vᴴ` ([golub2013matrix] (5.1.1) `P = I - β v vᵀ`, `β = 2 / vᵀ v`;
[higham2002accuracy] (19.1)). It is the identity at `v = 0` (`2 / 0 = 0`), and the
normalization-free form of `Matrix.householder` (`Matrix.reflector_eq_householder`). -/
noncomputable def reflector (v : n → 𝕜) : Matrix n n 𝕜 :=
  1 - (2 / (star v ⬝ᵥ v)) • vecMulVec v (star v)

/-- The reflector of the zero axis is the identity. -/
@[simp]
theorem reflector_zero : reflector (0 : n → 𝕜) = 1 := by simp [reflector]

/-- For a nonzero axis the reflector is the Householder reflector of the normalized axis. -/
theorem reflector_eq_householder {v : n → 𝕜} (hv : v ≠ 0) :
    reflector v =
      householder (((‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ : 𝕜))⁻¹ • v) := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [reflector, householder, star_dotProduct_self, star_smul, vecMulVec_smul, smul_vecMulVec,
    smul_smul, smul_smul, RCLike.star_def, RCLike.conj_inv, RCLike.conj_ofReal]
  congr 2
  field_simp

/-- A reflector is Hermitian. -/
theorem isHermitian_reflector (v : n → 𝕜) : (reflector v).IsHermitian := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [reflector_zero]
    exact isHermitian_one
  · rw [reflector_eq_householder hv]
    exact isHermitian_householder _

/-- A reflector is involutive. -/
theorem reflector_mul_self (v : n → 𝕜) : reflector v * reflector v = 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [reflector_zero, Matrix.one_mul]
  · rw [reflector_eq_householder hv]
    exact householder_mul_self (star_dotProduct_normalize_self hv)

/-- **A reflector is unitary** ([golub2013matrix] §5.1.2, "Householder matrices are symmetric and
orthogonal"), whatever the axis. -/
theorem reflector_mem_unitaryGroup (v : n → 𝕜) : reflector v ∈ Matrix.unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hs : (star (reflector v) : Matrix n n 𝕜) = reflector v := isHermitian_reflector v
  rw [hs, reflector_mul_self]

/-- Over `ℝ` a reflector is orthogonal. -/
theorem reflector_mem_orthogonalGroup (v : n → ℝ) : reflector v ∈ Matrix.orthogonalGroup n ℝ :=
  reflector_mem_unitaryGroup v

/-- Over `ℝ` the reflector is `1 - (2 / vᵀ v) v vᵀ`. -/
theorem reflector_eq_one_sub_smul_vecMulVec (v : n → ℝ) :
    reflector v = 1 - (2 / (v ⬝ᵥ v)) • vecMulVec v v := by
  simp [reflector]

/-- The reflector acts by `x ↦ x - (2 vᴴ x / vᴴ v) v`. -/
theorem reflector_mulVec (v x : n → 𝕜) :
    reflector v *ᵥ x = x - (2 / (star v ⬝ᵥ v) * (star v ⬝ᵥ x)) • v := by
  rw [reflector, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

/-- **The defining property of a reflector, with either sign** ([golub2013matrix] (5.1.2) and
its complex form §5.1.13): if `ᾱ α = ‖x‖₂²` and `ᾱ xᵢ` is real (`α = ± phase (x i) ‖x‖₂`), then
the reflector of the axis `v = x + α eᵢ` sends `x` to `-α eᵢ`. Indeed `vᴴ x = ‖x‖² + ᾱ xᵢ` and
`vᴴ v = 2 (‖x‖² + ᾱ xᵢ)`, so `P x = x - v`. Over `ℝ`: `α = ±‖x‖₂`, `P x = ∓‖x‖₂ eᵢ`. -/
theorem reflector_mulVec_eq_of_sq {x : n → 𝕜} {i : n} {α : 𝕜}
    (hα : star α * α = ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2)
    (hreal : star (star α * x i) = star α * x i)
    (hv : x + α • Pi.single i 1 ≠ 0) :
    reflector (x + α • Pi.single i 1) *ᵥ x = -α • Pi.single i 1 := by
  set v := x + α • (Pi.single i 1 : n → 𝕜) with hvdef
  have hxx : star x ⬝ᵥ x = ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2 :=
    star_dotProduct_self x
  have hsingle : star (Pi.single i 1 : n → 𝕜) = Pi.single i 1 := by
    funext r
    rcases eq_or_ne r i with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  have hvx : star v ⬝ᵥ x = star x ⬝ᵥ x + star α * x i := by
    rw [hvdef, star_add, add_dotProduct, star_smul, smul_dotProduct, hsingle, single_dotProduct,
      one_mul, smul_eq_mul]
  have hvv : star v ⬝ᵥ v = 2 * (star v ⬝ᵥ x) := by
    have hvi : star v ⬝ᵥ (Pi.single i 1 : n → 𝕜) = star (x i) + star α := by
      rw [dotProduct_single, mul_one, hvdef]
      simp
    have hreal' : star α * x i = α * star (x i) := by
      rw [← hreal, star_mul', star_star, mul_comm]
    rw [show star v ⬝ᵥ v = star v ⬝ᵥ x + α * (star v ⬝ᵥ (Pi.single i 1 : n → 𝕜)) by
      rw [hvdef, dotProduct_add, dotProduct_smul, smul_eq_mul]]
    rw [hvi, hvx, hxx]
    linear_combination hα - hreal'
  have hvv0 : star v ⬝ᵥ v ≠ 0 := by
    rw [star_dotProduct_self]
    exact pow_ne_zero 2 (ofReal_norm_toLp_ne_zero hv)
  have hvx0 : star v ⬝ᵥ x ≠ 0 := fun h0 => hvv0 (by rw [hvv, h0, mul_zero])
  rw [reflector_mulVec, hvv, show 2 / (2 * (star v ⬝ᵥ x)) * (star v ⬝ᵥ x) = 1 by
    field_simp, one_smul, hvdef]
  module

/-! ### Reflectors as rank-one updates, and the coordinates they fix -/

section RankOne

variable {m : Type*}

/-- [quarteroni2000numerical] (5.49): applying a reflector on the left is the rank-one update
`P M = M - 2 w (wᴴ M)`, never a matrix product. -/
theorem householder_mul_eq_sub_vecMulVec (w : n → 𝕜) (M : Matrix n m 𝕜) :
    householder w * M = M - (2 : 𝕜) • vecMulVec w (star w ᵥ* M) := by
  rw [householder, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul]

/-- [quarteroni2000numerical] (5.50): applying a reflector on the right is the rank-one update
`M P = M - 2 (M w) wᴴ`. -/
theorem mul_householder_eq_sub_vecMulVec (M : Matrix m n 𝕜) (w : n → 𝕜) :
    M * householder w = M - (2 : 𝕜) • vecMulVec (M *ᵥ w) (star w) := by
  rw [householder, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec]

/-- A reflector fixes the coordinates where its axis vanishes: this is the block form
`P = diag (I, R)` of [quarteroni2000numerical] (5.41), without blocks. -/
theorem householder_mulVec_apply_of_apply_eq_zero {w : n → 𝕜} {i : n} (hw : w i = 0)
    (x : n → 𝕜) : (householder w *ᵥ x) i = x i := by
  rw [householder_mulVec, Pi.sub_apply, Pi.smul_apply, hw, smul_zero, sub_zero]

/-- A reflector fixes every vector orthogonal to its axis. -/
theorem householder_mulVec_eq_self_of_dotProduct_eq_zero {w x : n → 𝕜} (h : star w ⬝ᵥ x = 0) :
    householder w *ᵥ x = x := by
  rw [householder_mulVec, h, mul_zero, zero_smul, sub_zero]

/-- A reflector fixes every vector that vanishes on the support of its axis. -/
theorem householder_mulVec_eq_self_of_apply_eq_zero {w x : n → 𝕜}
    (h : ∀ r, w r ≠ 0 → x r = 0) : householder w *ᵥ x = x := by
  refine householder_mulVec_eq_self_of_dotProduct_eq_zero (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : w r = 0
  · rw [Pi.star_apply, hr, star_zero, zero_mul]
  · rw [h r hr, mul_zero]

/-- The columns of `P M` are the images of the columns of `M`. -/
theorem householder_mul_apply (w : n → 𝕜) (M : Matrix n m 𝕜) (i : n) (j : m) :
    (householder w * M) i j = (householder w *ᵥ fun r => M r j) i := rfl

/-- Left multiplication by a reflector leaves the rows where its axis vanishes alone. -/
theorem householder_mul_apply_of_apply_eq_zero {w : n → 𝕜} {i : n} (hw : w i = 0)
    (M : Matrix n m 𝕜) (j : m) : (householder w * M) i j = M i j := by
  rw [householder_mul_apply, householder_mulVec_apply_of_apply_eq_zero hw]

/-- Right multiplication by a reflector leaves the columns where its axis vanishes alone. -/
theorem mul_householder_apply_of_apply_eq_zero {w : n → 𝕜} {j : n} (hw : w j = 0)
    (M : Matrix m n 𝕜) (i : m) : (M * householder w) i j = M i j := by
  rw [mul_householder_eq_sub_vecMulVec, sub_apply, smul_apply, vecMulVec_apply, Pi.star_apply, hw,
    star_zero, mul_zero, smul_zero, sub_zero]

/-- A row vector against the reflector of the conjugate axis is the reflector applied to it:
`x P̄ = P x` for `P = householder u`, which is how a reflector acts on the rows of a matrix. -/
theorem vecMul_householder_star (x u : n → 𝕜) :
    x ᵥ* householder (star u) = householder u *ᵥ x := by
  rw [householder_mulVec, householder, vecMul_sub, vecMul_one, vecMul_smul, vecMul_vecMulVec,
    star_star, dotProduct_comm, smul_smul]

/-- The rows of `M P̄` are the images of the rows of `M` under `P`. -/
theorem mul_householder_star_apply (M : Matrix m n 𝕜) (u : n → 𝕜) (i : m) (j : n) :
    (M * householder (star u)) i j = (householder u *ᵥ M i) j := by
  rw [← vecMul_householder_star]
  rfl

omit [DecidableEq n] in
/-- The conjugate of a unit axis is a unit axis. -/
theorem star_dotProduct_star_self {u : n → 𝕜} (hu : star u ⬝ᵥ u = 1) :
    star (star u) ⬝ᵥ star u = 1 := by
  rw [star_star, dotProduct_comm, hu]

end RankOne

/-! ### The two-sided reflection as a rank-two update -/

section ConjReflector

variable {R : Type*} [Field R] [StarRing R]

omit [DecidableEq n] in
/-- A Hermitian quadratic form takes self-adjoint values: `star (vᴴ B v) = vᴴ B v`. -/
theorem star_dotProduct_mulVec_self_of_conjTranspose_eq {B : Matrix n n R} (hB : Bᴴ = B)
    (v : n → R) : star (star v ⬝ᵥ (B *ᵥ v)) = star v ⬝ᵥ (B *ᵥ v) := by
  conv_rhs => rw [star_dotProduct, star_mulVec, hB, ← dotProduct_mulVec]

/-- **The two-sided reflection as a symmetric rank-two update** ([golub2013matrix] §8.3.1): for
a Hermitian `B` (`Bᴴ = B`), an axis `v` and a self-adjoint `β` (no normalization is needed, and
`β = 0` is allowed), with `P = 1 - β v vᴴ`, `p = β B v` and `w = p - (β vᴴ p / 2) v`,
`P B P = B - v wᴴ - w vᴴ`. Over `ℝ` it is the book's `P B P = B - v wᵀ - w vᵀ`. -/
theorem conj_one_sub_smul_vecMulVec_eq_sub (h2 : (2 : R) ≠ 0) {B : Matrix n n R} (hB : Bᴴ = B)
    (v : n → R) {β : R} (hβ : star β = β) {p w : n → R} (hp : p = β • (B *ᵥ v))
    (hw : w = p - ((β * (star v ⬝ᵥ p)) / 2) • v) :
    (1 - β • vecMulVec v (star v)) * B * (1 - β • vecMulVec v (star v)) =
      B - vecMulVec v (star w) - vecMulVec w (star v) := by
  set s := star v ⬝ᵥ (B *ᵥ v) with hs
  have hss : star s = s := star_dotProduct_mulVec_self_of_conjTranspose_eq hB v
  have e1 : vecMulVec v (star v) * B = vecMulVec v (star (B *ᵥ v)) := by
    rw [vecMulVec_mul, star_mulVec, hB]
  have e2 : B * vecMulVec v (star v) = vecMulVec (B *ᵥ v) (star v) := mul_vecMulVec _ _ _
  have e3 : vecMulVec v (star (B *ᵥ v)) * vecMulVec v (star v) = s • vecMulVec v (star v) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, star_mulVec, hB, ← dotProduct_mulVec]
  have hexp : (1 - β • vecMulVec v (star v)) * B * (1 - β • vecMulVec v (star v)) =
      B - β • vecMulVec v (star (B *ᵥ v)) - β • vecMulVec (B *ᵥ v) (star v) +
        (β * β * s) • vecMulVec v (star v) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, e1, e2, e3,
      smul_smul]
    module
  rw [hexp]
  subst hw hp
  ext i j
  simp only [sub_apply, add_apply, smul_apply, vecMulVec_apply, Pi.star_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, star_sub, star_mul', hβ, dotProduct_smul, ← hs, star_div₀,
    star_ofNat, hss]
  field_simp
  ring

end ConjReflector

/-! ### Triangularization by a product of reflectors -/

section Triangular

variable {N M : ℕ}

/-- One step of [saad2003iterative] Algorithm 1.3: a reflector supported on the rows from `k` on
annihilates the `k`-th column below the diagonal without disturbing the columns already cleared. -/
private theorem triangular_step (X : Matrix (Fin N) (Fin M) 𝕜) (k : ℕ)
    {P : Matrix (Fin N) (Fin N) 𝕜} (hP : P ∈ Matrix.unitaryGroup (Fin N) 𝕜)
    (hT : ∀ (i : Fin N) (j : Fin M), (j : ℕ) < k → (j : ℕ) < (i : ℕ) → (P * X) i j = 0) :
    ∃ P' ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin N) (j : Fin M), (j : ℕ) < k + 1 → (j : ℕ) < (i : ℕ) → (P' * X) i j = 0 := by
  by_cases hkM : k < M
  swap
  · exact ⟨P, hP, fun i j hj hij => hT i j (by have := j.isLt; omega) hij⟩
  by_cases hkN : k < N
  swap
  · refine ⟨P, hP, fun i j hj hij => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · exact hT i j hj' hij
    · exact absurd i.isLt (by omega)
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin N, (κ : ℕ) = k := ⟨⟨k, hkN⟩, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin M, (μ : ℕ) = k := ⟨⟨k, hkM⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin N → 𝕜, ∀ r : Fin N,
      y r = if k ≤ (r : ℕ) then (P * X) r μ else 0 :=
    ⟨fun r => if k ≤ (r : ℕ) then (P * X) r μ else 0, fun _ => rfl⟩
  by_cases hy0 : y = 0
  · refine ⟨P, hP, fun i j hj hij => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · exact hT i j hj' hij
    · have hjμ : j = μ := Fin.ext (by omega)
      subst hjμ
      have h2 := hy i
      rw [ite_eq_left (show k ≤ (i : ℕ) by omega)] at h2
      rw [← h2, hy0]
      rfl
  · have hwzero : ∀ r : Fin N, (r : ℕ) < k → householderVec y κ r = 0 := by
      intro r hr
      refine householderVec_apply_eq_zero (fun hrk => ?_) ?_
      · rw [hrk] at hr; omega
      · rw [hy r, ite_eq_right (by omega)]
    have hstar0 : ∀ z : Fin N → 𝕜, (∀ r : Fin N, k ≤ (r : ℕ) → z r = 0) →
        star (householderVec y κ) ⬝ᵥ z = 0 := by
      intro z hz
      rw [dotProduct]
      refine Finset.sum_eq_zero fun r _ => ?_
      rcases lt_or_ge (r : ℕ) k with hr | hr
      · rw [Pi.star_apply, hwzero r hr, star_zero, zero_mul]
      · rw [hz r hr, mul_zero]
    have hfix : ∀ z : Fin N → 𝕜, (∀ r : Fin N, k ≤ (r : ℕ) → z r = 0) →
        householder (householderVec y κ) *ᵥ z = z := by
      intro z hz
      rw [householder_mulVec, hstar0 z hz, mul_zero, zero_smul, sub_zero]
    refine ⟨householder (householderVec y κ) * P,
      mul_mem (householder_householderVec_mem_unitaryGroup hy0 κ) hP, fun i j hj hij => ?_⟩
    have hcol : ∀ j : Fin M, (householder (householderVec y κ) * P * X) i j
        = (householder (householderVec y κ) *ᵥ fun r => (P * X) r j) i := fun j =>
      (congrFun₂ (Matrix.mul_assoc (householder (householderVec y κ)) P X) i j).trans rfl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · rw [hcol j, hfix _ fun r hr => hT r j hj' (by omega)]
      exact hT i j hj' hij
    · have hjμ : j = μ := Fin.ext (by omega)
      subst hjμ
      have hsplit : (fun r => (P * X) r j)
          = (fun r : Fin N => if (r : ℕ) < k then (P * X) r j else 0) + y := by
        funext r
        rw [Pi.add_apply, hy r]
        by_cases hr : (r : ℕ) < k
        · rw [ite_eq_left hr, ite_eq_right (by omega), add_zero]
        · rw [ite_eq_right hr, ite_eq_left (by omega), zero_add]
      have hine : i ≠ κ := fun h => by rw [h] at hij; omega
      rw [hcol j, hsplit, mulVec_add, hfix _ fun r hr => ite_eq_right (by omega),
        householder_mulVec_eq_smul_single hy0 κ]
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ite_eq_right (show ¬((i : ℕ) < k) by omega),
        Pi.single_eq_of_ne hine, mul_zero, add_zero]

/-- [saad2003iterative] (1.27)–(1.28) and Algorithm 1.3: every matrix is carried to upper triangular
form (in the rectangular sense, zero strictly below the diagonal) by a unitary matrix, namely a
product of at most as many Householder reflectors as the matrix has columns. -/
theorem exists_unitary_mul_upperTriangular (X : Matrix (Fin N) (Fin M) 𝕜) :
    ∃ P ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin N) (j : Fin M), (j : ℕ) < (i : ℕ) → (P * X) i j = 0 := by
  suffices h : ∀ k : ℕ, ∃ P ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin N) (j : Fin M), (j : ℕ) < k → (j : ℕ) < (i : ℕ) → (P * X) i j = 0 by
    obtain ⟨P, hP, hT⟩ := h M
    exact ⟨P, hP, fun i j hij => hT i j j.isLt hij⟩
  intro k
  induction k with
  | zero => exact ⟨1, one_mem _, fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨P, hP, hT⟩ := ih
    exact triangular_step X k hP hT

/-- A square matrix indexed by a linearly ordered finite type is triangularized by a unitary
matrix: `Matrix.exists_unitary_mul_upperTriangular` transported from `Fin N` to `n` along
`monoEquivOfFin`. -/
theorem exists_unitary_mul_isUpperTriangular [LinearOrder n] (X : Matrix n n 𝕜) :
    ∃ U ∈ Matrix.unitaryGroup n 𝕜, (U * X).IsUpperTriangular := by
  obtain ⟨e, -⟩ : ∃ e : Fin (Fintype.card n) ≃o n, True := ⟨monoEquivOfFin n rfl, trivial⟩
  obtain ⟨P, hP, hT⟩ := exists_unitary_mul_upperTriangular (X.submatrix e.toEquiv e.toEquiv)
  refine ⟨P.submatrix e.toEquiv.symm e.toEquiv.symm, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hP,
      submatrix_one_equiv]
  · intro i j hij
    have hX : X = (X.submatrix e.toEquiv e.toEquiv).submatrix e.toEquiv.symm e.toEquiv.symm := by
      rw [submatrix_submatrix]
      ext i j
      simp
    rw [hX, submatrix_mul_equiv, submatrix_apply]
    refine hT _ _ ?_
    change (e.symm j : ℕ) < e.symm i
    exact e.symm.lt_iff_lt.mpr hij

end Triangular

/-! ### The reflector that annihilates the tail of a vector -/

section Tail

variable {N : ℕ}

/-- The axis of the reflector that keeps the coordinates `i < p` of `x`, sends the `p`-th
coordinate to `±‖(x_i)_{i ≥ p}‖` and annihilates those beyond; it is `0` (the reflector is the
identity) when `p ≥ N` or when the tail already vanishes. This is the vector `w^{(k)}` of
[quarteroni2000numerical] (5.42) with `p = k + 1` (the book counts from `1`), and it is what
`Matrix.householderVec` becomes when a reflector must act on trailing coordinates only. -/
noncomputable def householderTail (x : Fin N → 𝕜) (p : ℕ) : Fin N → 𝕜 :=
  if h : p < N then householderVec (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) ⟨p, h⟩
  else 0

variable (x : Fin N → 𝕜) {p : ℕ}

/-- The tail axis for a pivot inside the range. -/
theorem householderTail_of_lt (h : p < N) :
    householderTail x p =
      householderVec (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) ⟨p, h⟩ :=
  dite_eq_left h

/-- The tail axis for a pivot beyond the range is zero. -/
theorem householderTail_of_le (h : N ≤ p) : householderTail x p = 0 :=
  dite_eq_right (not_lt.2 h)

/-- The tail axis vanishes before the pivot. -/
theorem householderTail_apply_of_lt {i : Fin N} (hi : (i : ℕ) < p) :
    householderTail x p i = 0 := by
  by_cases h : p < N
  · rw [householderTail_of_lt x h]
    refine householderVec_apply_eq_zero (fun hip => ?_) (ite_eq_right (not_le.2 hi))
    rw [hip] at hi
    exact lt_irrefl _ hi
  · rw [householderTail_of_le x (not_lt.1 h), Pi.zero_apply]

/-- The Householder vector of the zero vector is zero, so its reflector is the identity. -/
theorem householderVec_zero (i : n) : householderVec (0 : n → 𝕜) i = 0 := by
  have h : householderAxis (0 : n → 𝕜) i = 0 := by
    rw [householderAxis, Pi.zero_apply, phase_zero, one_mul, WithLp.toLp_zero, norm_zero,
      RCLike.ofReal_zero, zero_smul, add_zero]
  rw [householderVec, h, normalize, smul_zero]

/-- The reflector of a tail axis is unitary: the axis is a unit vector or zero. -/
theorem householder_householderTail_mem_unitaryGroup (p : ℕ) :
    householder (householderTail x p) ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  by_cases h : p < N
  · rw [householderTail_of_lt x h]
    by_cases ht : (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) = 0
    · rw [ht, householderVec_zero, householder_zero]
      exact one_mem _
    · exact householder_householderVec_mem_unitaryGroup ht _
  · rw [householderTail_of_le x (not_lt.1 h), householder_zero]
    exact one_mem _

/-- The reflector of the conjugate of a tail axis is unitary as well. -/
theorem householder_star_householderTail_mem_unitaryGroup (p : ℕ) :
    householder (star (householderTail x p)) ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  by_cases h : p < N
  · rw [householderTail_of_lt x h]
    by_cases ht : (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) = 0
    · rw [ht, householderVec_zero, star_zero, householder_zero]
      exact one_mem _
    · exact householder_mem_unitaryGroup
        (star_dotProduct_star_self (star_dotProduct_householderVec_self ht _))
  · rw [householderTail_of_le x (not_lt.1 h), star_zero, householder_zero]
    exact one_mem _

/-- [quarteroni2000numerical] (5.41)–(5.42): the reflector of the tail axis with pivot `p` keeps
the coordinates before `p`, sends the `p`-th to `-sign(x_p) ‖(x_i)_{i ≥ p}‖` and annihilates
the rest. -/
theorem householder_tail_mulVec (p : ℕ) (i : Fin N) :
    (householder (householderTail x p) *ᵥ x) i =
      if (i : ℕ) < p then x i
      else if (i : ℕ) = p then
        -(phase (x i) * ((‖(WithLp.toLp 2 (fun r : Fin N => if p ≤ (r : ℕ) then x r else 0) :
          EuclideanSpace 𝕜 (Fin N))‖ : 𝕜)))
      else 0 := by
  by_cases h : p < N
  swap
  · rw [householderTail_of_le x (not_lt.1 h), householder_zero, one_mulVec,
      ite_eq_left (by have := i.isLt; omega)]
  obtain ⟨t, ht⟩ : ∃ t : Fin N → 𝕜, t = fun r : Fin N => if p ≤ (r : ℕ) then x r else 0 :=
    ⟨_, rfl⟩
  have htp : ∀ r : Fin N, p ≤ (r : ℕ) → t r = x r := fun r hr => by
    rw [ht]
    exact ite_eq_left hr
  have htp' : ∀ r : Fin N, (r : ℕ) < p → t r = 0 := fun r hr => by
    rw [ht]
    exact ite_eq_right (not_le.2 hr)
  rw [householderTail_of_lt x h, ← ht]
  by_cases ht0 : t = 0
  · have hx0 : ∀ r : Fin N, p ≤ (r : ℕ) → x r = 0 := fun r hr => by
      rw [← htp r hr, ht0, Pi.zero_apply]
    rw [ht0, householderVec_zero, householder_zero, one_mulVec]
    split_ifs with h1 h2
    · rfl
    · rw [hx0 i (by omega)]
      simp
    · exact hx0 i (by omega)
  · have hw : ∀ r : Fin N, (r : ℕ) < p → householderVec t ⟨p, h⟩ r = 0 := fun r hr =>
      householderVec_apply_eq_zero (fun hrp => by rw [hrp] at hr; exact lt_irrefl _ hr) (htp' r hr)
    have hfix : householder (householderVec t ⟨p, h⟩) *ᵥ (x - t) = x - t :=
      householder_mulVec_eq_self_of_apply_eq_zero fun r hr => by
        rw [Pi.sub_apply, htp r (not_lt.1 fun hrp => hr (hw r hrp)), sub_self]
    have key : householder (householderVec t ⟨p, h⟩) *ᵥ x =
        (x - t) + (-(phase (t ⟨p, h⟩) * ((‖(WithLp.toLp 2 t : EuclideanSpace 𝕜 (Fin N))‖ : 𝕜))))
          • (Pi.single (⟨p, h⟩ : Fin N) 1 : Fin N → 𝕜) := by
      calc householder (householderVec t ⟨p, h⟩) *ᵥ x
          = householder (householderVec t ⟨p, h⟩) *ᵥ ((x - t) + t) := by rw [sub_add_cancel]
        _ = _ := by rw [mulVec_add, hfix, householder_mulVec_eq_smul_single ht0]
    rw [key, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with h1 h2
    · rw [htp' i h1, sub_zero, Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (i : ℕ) ≠ p by omega)),
        mul_zero, add_zero]
    · have hi : i = ⟨p, h⟩ := Fin.ext h2
      subst hi
      rw [htp _ le_rfl, sub_self, zero_add, Pi.single_eq_same, mul_one]
    · rw [htp i (by omega), sub_self, zero_add,
        Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (i : ℕ) ≠ p by omega)), mul_zero]

/-- The tail reflector keeps the coordinates before the pivot. -/
theorem householder_householderTail_mulVec_apply_of_lt {i : Fin N} (hi : (i : ℕ) < p) :
    (householder (householderTail x p) *ᵥ x) i = x i := by
  rw [householder_tail_mulVec, ite_eq_left hi]

/-- The tail reflector annihilates the coordinates after the pivot. -/
theorem householder_householderTail_mulVec_apply_of_gt {i : Fin N} (hi : p < (i : ℕ)) :
    (householder (householderTail x p) *ᵥ x) i = 0 := by
  rw [householder_tail_mulVec, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The tail reflector sends the pivot coordinate to `-sign(x_p) ‖(x_i)_{i ≥ p}‖`. -/
theorem householder_householderTail_mulVec_apply_self (h : p < N) :
    (householder (householderTail x p) *ᵥ x) ⟨p, h⟩ =
      -(phase (x ⟨p, h⟩) * ((‖(WithLp.toLp 2 (fun r : Fin N => if p ≤ (r : ℕ) then x r else 0) :
        EuclideanSpace 𝕜 (Fin N))‖ : 𝕜))) := by
  rw [householder_tail_mulVec, ite_eq_right (lt_irrefl p), ite_eq_left rfl]

/-- The pivot coordinate after the tail reflector has the Euclidean length of the tail. -/
theorem norm_householder_householderTail_mulVec_apply_self (h : p < N) :
    ‖(householder (householderTail x p) *ᵥ x) ⟨p, h⟩‖ =
      ‖(WithLp.toLp 2 (fun r : Fin N => if p ≤ (r : ℕ) then x r else 0) :
        EuclideanSpace 𝕜 (Fin N))‖ := by
  rw [householder_householderTail_mulVec_apply_self x h, norm_neg, norm_mul, norm_phase, one_mul,
    RCLike.norm_ofReal, abs_norm]

end Tail

/-! ### Uniqueness of the QR factorization -/

section Unique

open scoped ComplexOrder

variable {M : ℕ}

/-- In the `RCLike` order a positive scalar is the cast of a positive real. -/
private theorem pos_iff_exists_ofReal {z : 𝕜} : 0 < z ↔ ∃ r : ℝ, 0 < r ∧ z = (r : 𝕜) := by
  constructor
  · intro hz
    obtain ⟨hre, him⟩ := RCLike.pos_iff.1 hz
    exact ⟨RCLike.re z, hre, RCLike.ext (by simp) (by simp [him])⟩
  · rintro ⟨r, hr, rfl⟩
    exact RCLike.pos_iff.2 ⟨by simpa using hr, by simp⟩

private theorem pos_mul_inv {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) : 0 < b * a⁻¹ := by
  obtain ⟨ra, hra, rfl⟩ := pos_iff_exists_ofReal.1 ha
  obtain ⟨rb, hrb, rfl⟩ := pos_iff_exists_ofReal.1 hb
  refine pos_iff_exists_ofReal.2 ⟨rb * ra⁻¹, by positivity, ?_⟩
  rw [RCLike.ofReal_mul, RCLike.ofReal_inv]

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
private theorem upperTriangular_mul_diag {A B : Matrix (Fin M) (Fin M) 𝕜}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (j : Fin M) :
    (A * B) j j = A j j * B j j := by
  rw [mul_apply]
  refine Finset.sum_eq_single j (fun r _ hr => ?_) fun h => absurd (Finset.mem_univ j) h
  rcases lt_or_gt_of_ne hr with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

/-- A unitary upper triangular matrix with positive diagonal is the identity.  This is the
flag-uniqueness argument of `Numlib.Analysis.InnerProductSpace.GramSchmidt` at matrix level, and it
is what makes the QR factorization with a positive diagonal unique. -/
private theorem eq_one_of_isUpperTriangular_of_unitary {S : Matrix (Fin M) (Fin M) 𝕜}
    (hS : S.IsUpperTriangular) (hu : Sᴴ * S = 1) (hd : ∀ j, 0 < S j j) : S = 1 := by
  have key : ∀ m : ℕ, ∀ j : Fin M, (j : ℕ) = m →
      ∀ i : Fin M, S i j = if i = j then 1 else 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hjm
      have habove : ∀ i : Fin M, (i : ℕ) < (j : ℕ) → S i j = 0 := by
        intro i hi
        have h1 : (Sᴴ * S) i j = 0 := by
          rw [hu, one_apply, ite_eq_right fun h => by rw [h] at hi; omega]
        rw [mul_apply] at h1
        have h2 : ∀ r : Fin M, Sᴴ i r * S r j = if r = i then S i j else 0 := by
          intro r
          rw [conjTranspose_apply, ih (i : ℕ) (by omega) i rfl r]
          by_cases hr : r = i
          · subst hr; simp
          · simp [hr]
        rw [Finset.sum_congr rfl fun r _ => h2 r,
          Finset.sum_ite_eq' Finset.univ i fun _ => S i j] at h1
        simpa using h1
      have hcol : ∀ r : Fin M, r ≠ j → S r j = 0 := by
        intro r hr
        rcases lt_or_gt_of_ne hr with h | h
        · exact habove r h
        · exact hS h
      have hdiag : star (S j j) * S j j = 1 := by
        have h1 : (Sᴴ * S) j j = 1 := by rw [hu, one_apply, ite_eq_left rfl]
        rw [mul_apply] at h1
        have h2 : ∀ r : Fin M, Sᴴ j r * S r j = if r = j then star (S j j) * S j j else 0 := by
          intro r
          rw [conjTranspose_apply]
          by_cases hr : r = j
          · subst hr; simp
          · rw [hcol r hr, mul_zero, ite_eq_right hr]
        rw [Finset.sum_congr rfl fun r _ => h2 r,
          Finset.sum_ite_eq' Finset.univ j fun _ => star (S j j) * S j j] at h1
        simpa using h1
      have hjj : S j j = 1 := by
        obtain ⟨r, hr, hrz⟩ := pos_iff_exists_ofReal.1 (hd j)
        rw [hrz] at hdiag ⊢
        rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← RCLike.ofReal_one,
          RCLike.ofReal_inj] at hdiag
        have hr1 : r = 1 := by nlinarith
        rw [hr1, RCLike.ofReal_one]
      intro i
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl]
        exact hjj
      · rw [ite_eq_right hij]
        exact hcol i hij
  ext i j
  rw [key (j : ℕ) j rfl i, one_apply]

/-- Uniqueness of the QR factorization with a positive diagonal: this is what identifies the
reflector product of `Matrix.exists_unitary_mul_upperTriangular` with the Gram–Schmidt factorization
of `Matrix.exists_qr`, and either of them with the modified Gram–Schmidt one, with no need to
compare the constructions. -/
theorem qr_unique {N : ℕ} {X Q₁ Q₂ : Matrix (Fin N) (Fin M) 𝕜}
    {R₁ R₂ : Matrix (Fin M) (Fin M) 𝕜} (hX₁ : X = Q₁ * R₁) (hX₂ : X = Q₂ * R₂)
    (hQ₁ : Q₁ᴴ * Q₁ = 1) (hQ₂ : Q₂ᴴ * Q₂ = 1)
    (hR₁ : R₁.IsUpperTriangular) (hR₂ : R₂.IsUpperTriangular)
    (hd₁ : ∀ j, 0 < R₁.diag j) (hd₂ : ∀ j, 0 < R₂.diag j) :
    Q₁ = Q₂ ∧ R₁ = R₂ := by
  have hd₁' : ∀ j, 0 < R₁ j j := hd₁
  have hd₂' : ∀ j, 0 < R₂ j j := hd₂
  have hdet : IsUnit R₁.det := by
    rw [det_of_isUpperTriangular hR₁, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (hd₁' j).ne'
  have : Invertible R₁ := invertibleOfIsUnitDet R₁ hdet
  have hRR : R₁ᴴ * R₁ = R₂ᴴ * R₂ := by
    have h1 : Xᴴ * X = R₁ᴴ * R₁ := by
      rw [hX₁, conjTranspose_mul]
      calc R₁ᴴ * Q₁ᴴ * (Q₁ * R₁) = R₁ᴴ * (Q₁ᴴ * Q₁ * R₁) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R₁ᴴ * R₁ := by rw [hQ₁, Matrix.one_mul]
    have h2 : Xᴴ * X = R₂ᴴ * R₂ := by
      rw [hX₂, conjTranspose_mul]
      calc R₂ᴴ * Q₂ᴴ * (Q₂ * R₂) = R₂ᴴ * (Q₂ᴴ * Q₂ * R₂) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R₂ᴴ * R₂ := by rw [hQ₂, Matrix.one_mul]
    rw [← h1, h2]
  have hinvUT : (R₁⁻¹).IsUpperTriangular := blockTriangular_inv_of_blockTriangular hR₁
  have hSUT : (R₂ * R₁⁻¹).IsUpperTriangular := hR₂.mul hinvUT
  have hinvdiag : ∀ j, (R₁⁻¹) j j = (R₁ j j)⁻¹ := by
    intro j
    have h1 : R₁ j j * (R₁⁻¹) j j = 1 := by
      rw [← upperTriangular_mul_diag hR₁ hinvUT j, mul_nonsing_inv R₁ hdet, one_apply_eq]
    calc (R₁⁻¹) j j = (R₁ j j)⁻¹ * (R₁ j j * (R₁⁻¹) j j) := by
          rw [← mul_assoc, inv_mul_cancel₀ (hd₁' j).ne', one_mul]
      _ = (R₁ j j)⁻¹ := by rw [h1, mul_one]
  have hSd : ∀ j, 0 < (R₂ * R₁⁻¹) j j := fun j => by
    rw [upperTriangular_mul_diag hR₂ hinvUT j, hinvdiag j]
    exact pos_mul_inv (hd₁' j) (hd₂' j)
  have hSu : (R₂ * R₁⁻¹)ᴴ * (R₂ * R₁⁻¹) = 1 := by
    have h : (R₂ * R₁⁻¹)ᴴ * (R₂ * R₁⁻¹) = (R₁⁻¹)ᴴ * (R₂ᴴ * R₂ * R₁⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    have h2 : (R₁⁻¹)ᴴ * (R₁ᴴ * R₁ * R₁⁻¹) = (R₁ * R₁⁻¹)ᴴ * (R₁ * R₁⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    rw [h, ← hRR, h2, mul_nonsing_inv R₁ hdet, conjTranspose_one, mul_one]
  have hS1 : R₂ * R₁⁻¹ = 1 := eq_one_of_isUpperTriangular_of_unitary hSUT hSu hSd
  have hR : R₂ = R₁ := by
    calc R₂ = R₂ * (R₁⁻¹ * R₁) := by rw [nonsing_inv_mul R₁ hdet, mul_one]
      _ = R₂ * R₁⁻¹ * R₁ := by rw [mul_assoc]
      _ = R₁ := by rw [hS1, one_mul]
  refine ⟨?_, hR.symm⟩
  calc Q₁ = Q₁ * (R₁ * R₁⁻¹) := by rw [mul_nonsing_inv R₁ hdet, Matrix.mul_one]
    _ = Q₁ * R₁ * R₁⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = Q₂ * R₂ * R₁⁻¹ := by rw [← hX₁, hX₂]
    _ = Q₂ * (R₂ * R₁⁻¹) := Matrix.mul_assoc _ _ _
    _ = Q₂ := by rw [hS1, Matrix.mul_one]

end Unique

/-! ### The Gram–Schmidt factorization -/

section GramSchmidt

open InnerProductSpace
open scoped ComplexOrder

variable {ι E : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `⟪gramSchmidt f j, f j⟫ = ‖gramSchmidt f j‖²`: the Gram–Schmidt vector is the orthogonal
component of `f j`.  (This is the index-general form of the same lemma in
`Numlib.Analysis.InnerProductSpace.GramSchmidt`, which is stated for `ℕ`.) -/
private theorem inner_gramSchmidt_self (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidt 𝕜 f j) (f j) = ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' 𝕜 f j]
  rw [inner_add_right, inner_sum, inner_self_eq_norm_sq_to_K]
  convert add_zero _
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 f (Finset.mem_Iio.1 hi).ne', mul_zero]

private theorem inner_gramSchmidtNormed_self (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) = ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) := by
  rw [gramSchmidtNormed, inner_smul_left, inner_gramSchmidt_self, RCLike.conj_inv,
    RCLike.conj_ofReal]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) 0 with h | h
  · simp [h]
  · rw [sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- [saad2003iterative] (1.19): a matrix whose columns are linearly independent factors as `X = Q R`
with orthonormal columns in `Q` and `R` upper triangular of positive diagonal.  The factors are the
Gram–Schmidt orthonormalization of the columns and the matrix `R i j = ⟪Q i, X j⟫` of the
coefficients, which is [saad2003iterative] Algorithm 1.1; Algorithm 1.2 (modified Gram–Schmidt)
computes the same pair, by `Matrix.qr_unique`. -/
theorem exists_qr {N M : ℕ} (X : Matrix (Fin N) (Fin M) 𝕜) (hX : LinearIndependent 𝕜 Xᵀ) :
    ∃ (Q : Matrix (Fin N) (Fin M) 𝕜) (R : Matrix (Fin M) (Fin M) 𝕜),
      X = Q * R ∧ Qᴴ * Q = 1 ∧ R.IsUpperTriangular ∧ ∀ j, 0 < R.diag j := by
  set f : Fin M → EuclideanSpace 𝕜 (Fin N) := fun j => WithLp.toLp 2 (Xᵀ j) with hf_def
  have hf : LinearIndependent 𝕜 f := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    refine Fintype.linearIndependent_iff.1 hX g ?_ i
    funext r
    have h0 := congrArg (fun z : EuclideanSpace 𝕜 (Fin N) => WithLp.ofLp z r) hg
    simpa [hf_def] using h0
  have hgne : ∀ j : Fin M, gramSchmidt 𝕜 f j ≠ 0 := fun j => gramSchmidt_ne_zero j hf
  have hnne : ∀ j : Fin M, ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ≠ 0 := fun j => by
    simpa using norm_ne_zero_iff.2 (hgne j)
  have hon : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := gramSchmidtNormed_orthonormal hf
  have htri : ∀ i j : Fin M, j < i → inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) = 0 := by
    intro i j hji
    rw [gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular 𝕜 f hji, mul_zero]
  have hexp : ∀ j : Fin M, f j = ∑ i : Fin M,
      inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i := by
    intro j
    have hsum : ∑ i : Fin M, inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i
        = ∑ i ∈ Finset.Iic j,
            inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
      rw [htri i j (by simpa using hi), zero_smul]
    have hterm : ∀ i : Fin M,
        inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i
          = (inner 𝕜 (gramSchmidt 𝕜 f i) (f j) / ((‖gramSchmidt 𝕜 f i‖ : 𝕜)) ^ 2)
            • gramSchmidt 𝕜 f i := by
      intro i
      rw [gramSchmidtNormed, inner_smul_left, RCLike.conj_inv, RCLike.conj_ofReal, smul_smul]
      congr 1
      field_simp [hnne i]
    have hdiagterm : inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) • gramSchmidtNormed 𝕜 f j
        = gramSchmidt 𝕜 f j := by
      rw [inner_gramSchmidtNormed_self, gramSchmidtNormed, smul_smul,
        mul_inv_cancel₀ (hnne j), one_smul]
    rw [hsum, ← Finset.Iio_insert, Finset.sum_insert (by simp), hdiagterm,
      show (∑ i ∈ Finset.Iio j,
            inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i)
          = ∑ i ∈ Finset.Iio j,
            (inner 𝕜 (gramSchmidt 𝕜 f i) (f j) / ((‖gramSchmidt 𝕜 f i‖ : 𝕜)) ^ 2)
              • gramSchmidt 𝕜 f i from Finset.sum_congr rfl fun i _ => hterm i]
    exact gramSchmidt_def'' 𝕜 f j
  refine ⟨Matrix.of fun r j => WithLp.ofLp (gramSchmidtNormed 𝕜 f j) r,
    Matrix.of fun i j => inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j), ?_, ?_, ?_, ?_⟩
  · ext r j
    have h : X r j = ∑ i : Fin M, inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j)
        * WithLp.ofLp (gramSchmidtNormed 𝕜 f i) r := by
      have h0 := congrArg (fun z : EuclideanSpace 𝕜 (Fin N) => WithLp.ofLp z r) (hexp j)
      simpa [hf_def] using h0
    rw [mul_apply, h]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.of_apply, Matrix.of_apply, mul_comm]
  · ext i j
    have h : ∑ r : Fin N, starRingEnd 𝕜 (WithLp.ofLp (gramSchmidtNormed 𝕜 f i) r)
          * WithLp.ofLp (gramSchmidtNormed 𝕜 f j) r
        = inner 𝕜 (gramSchmidtNormed 𝕜 f i) (gramSchmidtNormed 𝕜 f j) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      exact Finset.sum_congr rfl fun r _ => by simp [mul_comm]
    rw [mul_apply]
    simp only [conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
    rw [h, orthonormal_iff_ite.1 hon i j, one_apply]
  · intro i j hji
    exact htri i j hji
  · intro j
    rw [diag_apply, Matrix.of_apply, inner_gramSchmidtNormed_self]
    exact pos_iff_exists_ofReal.2 ⟨‖gramSchmidt 𝕜 f j‖, norm_pos_iff.2 (hgne j), rfl⟩

/-- The converse of `Matrix.exists_qr`: a factorization with orthonormal columns and an invertible
upper triangular factor forces the columns of `X` to be linearly independent. -/
theorem linearIndependent_of_qr {N M : ℕ} {X Q : Matrix (Fin N) (Fin M) 𝕜}
    {R : Matrix (Fin M) (Fin M) 𝕜} (hX : X = Q * R) (hQ : Qᴴ * Q = 1)
    (hR : R.IsUpperTriangular) (hd : ∀ j, 0 < R.diag j) : LinearIndependent 𝕜 Xᵀ := by
  have hd' : ∀ j, 0 < R j j := hd
  have hdet : IsUnit R.det := by
    rw [det_of_isUpperTriangular hR, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (hd' j).ne'
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have hXc : X *ᵥ c = 0 := by
    funext r
    have h0 := congrFun hc r
    simpa [mulVec, dotProduct, mul_comm] using h0
  have hQRc : Q *ᵥ (R *ᵥ c) = 0 := by
    rw [mulVec_mulVec, ← hX, hXc]
  have hRc : R *ᵥ c = 0 := by
    have h1 : Qᴴ *ᵥ (Q *ᵥ (R *ᵥ c)) = R *ᵥ c := by
      rw [mulVec_mulVec, hQ, one_mulVec]
    rw [hQRc, mulVec_zero] at h1
    exact h1.symm
  have h2 : c = 0 := by
    rw [← nonsing_inv_mulVec_mulVec ((isUnit_iff_isUnit_det R).2 hdet) c, hRc, mulVec_zero]
  exact fun i => congrFun h2 i

end GramSchmidt

/-! ### The full QR factorization and its reduced form -/

section FullQR

variable {M N : ℕ}

/-- **The full QR factorization**, [quarteroni2000numerical] Definition 3.1: `A = Q R` with `Q`
unitary (`M × M`) and `R` upper trapezoidal (`M × N`, zero below the diagonal, so that its rows from
the `N`-th on vanish when `N ≤ M`). -/
structure IsQR (A : Matrix (Fin M) (Fin N) 𝕜) (Q : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) : Prop where
  /-- The orthogonal factor is unitary. -/
  mem_unitaryGroup : Q ∈ Matrix.unitaryGroup (Fin M) 𝕜
  /-- The triangular factor vanishes below the diagonal. -/
  apply_eq_zero : ∀ (i : Fin M) (j : Fin N), (j : ℕ) < i → R i j = 0
  /-- The factors multiply to `A`. -/
  mul_eq : Q * R = A

/-- **Every matrix has a full QR factorization**, by Householder triangularization
(`Matrix.exists_unitary_mul_upperTriangular`): `P A = R` with `P` unitary, so `A = Pᴴ R`. -/
theorem exists_isQR (A : Matrix (Fin M) (Fin N) 𝕜) : ∃ Q R, IsQR A Q R := by
  obtain ⟨P, hP, hPA⟩ := exists_unitary_mul_upperTriangular A
  refine ⟨star P, P * A, Unitary.star_mem hP, hPA, ?_⟩
  rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hP, Matrix.one_mul]

variable {α : Type*} {m' n' : Type*}

/-- The first `N` columns of a matrix with `M ≥ N` columns, the `Q̃ = Q(1:m, 1:n)` of
[quarteroni2000numerical] (3.48). -/
def firstColumns (Q : Matrix m' (Fin M) α) (h : N ≤ M) : Matrix m' (Fin N) α :=
  Q.submatrix id (Fin.castLE h)

/-- The first `N` rows of a matrix with `M ≥ N` rows, the `R̃ = R(1:n, 1:n)` of
[quarteroni2000numerical] (3.48). -/
def firstRows (R : Matrix (Fin M) n' α) (h : N ≤ M) : Matrix (Fin N) n' α :=
  R.submatrix (Fin.castLE h) id

/-- The entries of the first columns. -/
@[simp]
theorem firstColumns_apply (Q : Matrix m' (Fin M) α) (h : N ≤ M) (i : m') (j : Fin N) :
    firstColumns Q h i j = Q i (Fin.castLE h j) := rfl

/-- The entries of the first rows. -/
@[simp]
theorem firstRows_apply (R : Matrix (Fin M) n' α) (h : N ≤ M) (i : Fin N) (j : n') :
    firstRows R h i j = R (Fin.castLE h i) j := rfl

variable {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
variable {R : Matrix (Fin M) (Fin N) 𝕜}

/-- The rows of the trapezoidal factor from the `N`-th on vanish. -/
theorem IsQR.apply_eq_zero_of_le (h : IsQR A Q R) {i : Fin M} (hi : N ≤ i) (j : Fin N) :
    R i j = 0 :=
  h.apply_eq_zero i j (j.2.trans_le hi)

/-- The product of the reduced factors is `A`: the trailing rows of `R` are zero, so only the
first `N` columns of `Q` contribute ([quarteroni2000numerical] (3.47)). -/
theorem IsQR.firstColumns_mul_firstRows (h : IsQR A Q R) (hNM : N ≤ M) :
    firstColumns Q hNM * firstRows R hNM = A := by
  rw [← h.mul_eq]
  ext i j
  simp only [mul_apply, firstColumns_apply, firstRows_apply]
  refine Finset.sum_bij_ne_zero (fun k _ _ => Fin.castLE hNM k) (fun _ _ _ => Finset.mem_univ _)
    (fun _ _ _ _ _ _ hk => Fin.castLE_injective hNM hk) (fun k _ hk => ?_) fun _ _ _ => rfl
  by_cases hkN : (k : ℕ) < N
  · exact ⟨⟨k, hkN⟩, Finset.mem_univ _, by simpa using hk, Fin.ext rfl⟩
  · exact absurd (by rw [h.apply_eq_zero_of_le (not_lt.1 hkN), mul_zero]) hk

/-- The reduced orthogonal factor has orthonormal columns: `Q̃ᴴ Q̃ = 1`, being a block of
`Qᴴ Q = 1`. -/
theorem IsQR.conjTranspose_firstColumns_mul_self (h : IsQR A Q R) (hNM : N ≤ M) :
    (firstColumns Q hNM)ᴴ * firstColumns Q hNM = 1 := by
  have hQ : star Q * Q = 1 := Unitary.star_mul_self_of_mem h.mem_unitaryGroup
  ext i j
  have := congrFun (congrFun hQ (Fin.castLE hNM i)) (Fin.castLE hNM j)
  simp only [mul_apply, star_apply] at this
  simp only [mul_apply, conjTranspose_apply, firstColumns_apply, this, one_apply, Fin.castLE_inj]

/-- The reduced triangular factor is upper triangular. -/
theorem IsQR.isUpperTriangular_firstRows (h : IsQR A Q R) (hNM : N ≤ M) :
    (firstRows R hNM).IsUpperTriangular := fun _ _ hij =>
  h.apply_eq_zero _ _ hij

/-- **The reduced QR factorization**, [quarteroni2000numerical] Property 3.3 and (3.47)–(3.48):
from a full factorization `A = Q R`, `N ≤ M`, the first `N` columns `Q̃` of `Q` and the first `N`
rows `R̃` of `R` satisfy `A = Q̃ R̃`, `Q̃ᴴ Q̃ = 1` and `R̃` upper triangular. -/
theorem IsQR.reduced (h : IsQR A Q R) (hNM : N ≤ M) :
    firstColumns Q hNM * firstRows R hNM = A ∧
      (firstColumns Q hNM)ᴴ * firstColumns Q hNM = 1 ∧ (firstRows R hNM).IsUpperTriangular :=
  ⟨h.firstColumns_mul_firstRows hNM, h.conjTranspose_firstColumns_mul_self hNM,
    h.isUpperTriangular_firstRows hNM⟩

/-- For `A` of full column rank the reduced triangular factor is nonsingular: `A = Q̃ R̃` is
injective on vectors, hence so is `R̃`. -/
theorem IsQR.isUnit_firstRows_of_linearIndependent (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) : IsUnit (firstRows R hNM) := by
  rw [← mulVec_injective_iff_isUnit]
  have hinj : Function.Injective A.mulVec := mulVec_injective_iff.2 hA
  rw [← h.firstColumns_mul_firstRows hNM] at hinj
  intro x y hxy
  apply hinj
  simp only [← mulVec_mulVec, hxy]

/-- The diagonal of the reduced triangular factor is nowhere zero when `A` has full column rank. -/
theorem IsQR.firstRows_diag_ne_zero_of_linearIndependent (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) (i : Fin N) : firstRows R hNM i i ≠ 0 :=
  (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular (h.isUpperTriangular_firstRows hNM)).1
    (h.isUnit_firstRows_of_linearIndependent hNM hA) i

/-- [quarteroni2000numerical] Property 3.3, the range clause: for `A` of full column rank the
columns of `Q̃` span the column space of `A`, since `A = Q̃ R̃` with `R̃` nonsingular. -/
theorem IsQR.span_firstColumns_eq (h : IsQR A Q R) (hNM : N ≤ M) (hA : LinearIndependent 𝕜 Aᵀ) :
    Submodule.span 𝕜 (Set.range (firstColumns Q hNM)ᵀ) = Submodule.span 𝕜 (Set.range Aᵀ) := by
  have hR := h.isUnit_firstRows_of_linearIndependent hNM hA
  rw [show Set.range Aᵀ = Set.range A.col from rfl,
    show Set.range (firstColumns Q hNM)ᵀ = Set.range (firstColumns Q hNM).col from rfl,
    ← range_mulVecLin, ← range_mulVecLin, ← h.firstColumns_mul_firstRows hNM,
    mulVecLin_mul, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (mulVec_surjective_iff_isUnit.2 hR)

end FullQR

/-! ### The thin and the pivoted QR factorizations -/

section ThinQR

variable {m : Type*} [Fintype m] {M N : ℕ}

/-- **The thin (reduced) QR factorization** ([golub2013matrix] (5.2.2), Theorem 5.2.3): `A = Q R`
with `A : Matrix m (Fin N) 𝕜`, `Q : Matrix m (Fin N) 𝕜` of orthonormal columns (`Qᴴ Q = 1`) and
`R` upper triangular `N × N`. No sign condition: uniqueness (`Matrix.IsThinQR.unique`) asks for a
positive diagonal. The specification of classical and modified Gram–Schmidt; the full
factorization `Matrix.IsQR` gives one (`Matrix.IsQR.isThinQR`). -/
structure IsThinQR (A : Matrix m (Fin N) 𝕜) (Q : Matrix m (Fin N) 𝕜)
    (R : Matrix (Fin N) (Fin N) 𝕜) : Prop where
  /-- The factors multiply to `A`. -/
  mul_eq : Q * R = A
  /-- The columns of `Q` are orthonormal. -/
  conjTranspose_mul_self : Qᴴ * Q = 1
  /-- The triangular factor is upper triangular. -/
  isUpperTriangular : R.IsUpperTriangular

open scoped ComplexOrder in
/-- **Existence of the thin QR factorization** with a positive diagonal, for linearly independent
columns: `Matrix.exists_qr` repackaged. -/
theorem exists_isThinQR (A : Matrix (Fin M) (Fin N) 𝕜) (hA : LinearIndependent 𝕜 Aᵀ) :
    ∃ Q R, IsThinQR A Q R ∧ ∀ j, 0 < R j j := by
  obtain ⟨Q, R, hX, hQ, hR, hd⟩ := exists_qr A hA
  exact ⟨Q, R, ⟨hX.symm, hQ, hR⟩, hd⟩

open scoped ComplexOrder in
/-- **Uniqueness of the thin QR factorization** with a positive diagonal ([golub2013matrix]
Theorem 5.2.3): `Matrix.qr_unique` repackaged. -/
theorem IsThinQR.unique {A Q₁ Q₂ : Matrix (Fin M) (Fin N) 𝕜} {R₁ R₂ : Matrix (Fin N) (Fin N) 𝕜}
    (h₁ : IsThinQR A Q₁ R₁) (h₂ : IsThinQR A Q₂ R₂) (hd₁ : ∀ j, 0 < R₁ j j)
    (hd₂ : ∀ j, 0 < R₂ j j) : Q₁ = Q₂ ∧ R₁ = R₂ :=
  qr_unique h₁.mul_eq.symm h₂.mul_eq.symm h₁.conjTranspose_mul_self h₂.conjTranspose_mul_self
    h₁.isUpperTriangular h₂.isUpperTriangular hd₁ hd₂

/-- The reduced factors of a full QR factorization form a thin one (`Matrix.IsQR.reduced`
repackaged). -/
theorem IsQR.isThinQR {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
    {R : Matrix (Fin M) (Fin N) 𝕜} (h : IsQR A Q R) (hNM : N ≤ M) :
    IsThinQR A (firstColumns Q hNM) (firstRows R hNM) :=
  ⟨(h.reduced hNM).1, (h.reduced hNM).2.1, (h.reduced hNM).2.2⟩

/-- **The leading columns of `A` and `Q` span the same spaces** ([golub2013matrix] (5.2.1)): if
`A = Q R` is a full QR factorization of `A` with linearly independent columns, then for every
`k ≤ N` the first `k` columns of `A` and of `Q` span the same subspace, and the diagonal entries
of `R` are nonzero. The inclusion is `a_j = ∑_{i ≤ j} r_ij q_i` ((5.2.3)); equality is the
dimension count. -/
theorem IsQR.span_col_prefix_eq {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
    {R : Matrix (Fin M) (Fin N) 𝕜} (h : IsQR A Q R) (hA : LinearIndependent 𝕜 Aᵀ) (hNM : N ≤ M)
    {k : ℕ} (hk : k ≤ N) :
    Submodule.span 𝕜 (Set.range fun j : Fin k => A.col (Fin.castLE hk j)) =
        Submodule.span 𝕜 (Set.range fun i : Fin k => Q.col (Fin.castLE (hk.trans hNM) i)) ∧
      ∀ (i : Fin M) (j : Fin N), (i : ℕ) = j → R i j ≠ 0 := by
  refine ⟨Submodule.eq_of_le_of_finrank_le ?_ ?_, fun i j hij => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    have hcol : A.col (Fin.castLE hk c) = ∑ i : Fin M, R i (Fin.castLE hk c) • Q.col i := by
      funext r
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      change A r _ = ∑ i, R i _ * Q r i
      rw [← h.mul_eq, mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    change A.col (Fin.castLE hk c) ∈ _
    rw [hcol]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, congrArg _ (Fin.ext rfl)⟩)
    · rw [h.apply_eq_zero i _ (by simp only [Fin.val_castLE]; omega), zero_smul]
      exact Submodule.zero_mem _
  · have hli : LinearIndependent 𝕜 fun j : Fin k => A.col (Fin.castLE hk j) :=
      hA.comp _ (Fin.castLE_injective hk)
    rw [finrank_span_eq_card hli]
    exact (finrank_range_le_card _).trans (by simp)
  · have := h.firstRows_diag_ne_zero_of_linearIndependent hNM hA j
    rwa [firstRows_apply, show Fin.castLE hNM j = i from Fin.ext hij.symm] at this

/-- **QR factorization with column pivoting** ([golub2013matrix] §5.4.2): `A Π = Q R` with
`Π` the permutation matrix of `σ`, i.e. column `k` of `A Π` is column `σ k` of `A`. A structure
rather than an abbreviation, so that its rank-revealing refinements are dot notation on it. -/
structure IsPivotedQR (A : Matrix (Fin M) (Fin N) 𝕜) (Q : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) (σ : Equiv.Perm (Fin N)) : Prop where
  /-- The column-permuted matrix has the full QR factorization `Q R`. -/
  isQR : IsQR (A.submatrix id σ) Q R

end ThinQR

/-! ### The projector of modified Gram–Schmidt -/

section GramSchmidtProjector

variable {R : Type*} [CommRing R] [StarRing R]

/-- **The projector identity behind modified Gram–Schmidt** ([golub2013matrix] §5.2.8): for
pairwise orthogonal vectors `q i` (`q iᴴ q j = 0` for `i ≠ j`), the product of the deflations
`1 - q i q iᴴ` is `1 - ∑ i, q i q iᴴ`, since the cross terms vanish. So the successive deflations
of modified Gram–Schmidt compute, in exact arithmetic, the vectors `a - ∑ i (q iᴴ a) q i` of
classical Gram–Schmidt. -/
theorem prod_one_sub_vecMulVec_of_orthonormal :
    ∀ {k : ℕ} (q : Fin k → n → R), (∀ i j, i ≠ j → star (q i) ⬝ᵥ q j = 0) →
      (List.ofFn fun i => 1 - vecMulVec (q i) (star (q i))).prod =
        1 - ∑ i, vecMulVec (q i) (star (q i))
  | 0, q, _ => by simp
  | k + 1, q, hq => by
    rw [List.ofFn_succ, List.prod_cons,
      prod_one_sub_vecMulVec_of_orthonormal (fun i => q i.succ)
        (fun i j hij => hq _ _ (fun h => hij (Fin.succ_injective _ h))),
      Fin.sum_univ_succ]
    have h0 : vecMulVec (q 0) (star (q 0)) * ∑ i : Fin k, vecMulVec (q i.succ) (star (q i.succ))
        = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [vecMulVec_mul_vecMulVec, hq 0 i.succ (Fin.succ_ne_zero i).symm, zero_smul,
        vecMulVec_zero]
    have e : ∀ P S : Matrix n n R, (1 - P) * (1 - S) = 1 - (P + S) + P * S := fun P S => by
      noncomm_ring
    rw [e, h0, add_zero]

end GramSchmidtProjector


/-! ### Reduction to Hessenberg form by Householder reflectors -/

section HessenbergReduction

variable {N : ℕ}

/-- The reflector of step `k` of the Householder reduction to Hessenberg form: the tail reflector
of column `k` of `A` with pivot `k + 1`, [quarteroni2000numerical] (5.41) with `x` the `k`-th
column of `A^{(k-1)}`; the identity when `k ≥ N`. -/
noncomputable def hessenbergReflector (A : Matrix (Fin N) (Fin N) 𝕜) (k : ℕ) :
    Matrix (Fin N) (Fin N) 𝕜 :=
  if h : k < N then householder (householderTail (fun i => A i ⟨k, h⟩) (k + 1)) else 1

variable (A : Matrix (Fin N) (Fin N) 𝕜) {k : ℕ}

/-- The reflector of a step inside the range. -/
theorem hessenbergReflector_of_lt (h : k < N) :
    hessenbergReflector A k = householder (householderTail (fun i => A i ⟨k, h⟩) (k + 1)) :=
  dite_eq_left h

/-- The reflector of a step beyond the range is the identity. -/
theorem hessenbergReflector_of_le (h : N ≤ k) : hessenbergReflector A k = 1 :=
  dite_eq_right (not_lt.2 h)

/-- The reflectors of the reduction are Hermitian. -/
theorem isHermitian_hessenbergReflector (k : ℕ) : (hessenbergReflector A k).IsHermitian := by
  unfold hessenbergReflector
  split_ifs
  · exact isHermitian_householder _
  · exact isHermitian_one

/-- The reflectors of the reduction are unitary. -/
theorem hessenbergReflector_mem_unitaryGroup (k : ℕ) :
    hessenbergReflector A k ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  unfold hessenbergReflector
  split_ifs
  · exact householder_householderTail_mem_unitaryGroup _ _
  · exact one_mem _

/-- [quarteroni2000numerical] (5.45): one step of the Householder reduction to Hessenberg form,
`A^{(k)} = P_{(k)}ᵀ A^{(k-1)} P_{(k)}`, the reflector being Hermitian and involutive so that
`Pᴴ A P = P A P`. -/
noncomputable def hessenbergStep (A : Matrix (Fin N) (Fin N) 𝕜) (k : ℕ) :
    Matrix (Fin N) (Fin N) 𝕜 :=
  hessenbergReflector A k * A * hessenbergReflector A k

/-- The matrices `A^{(k)}` of the Householder reduction: `A^{(0)} = A` and `A^{(k+1)}` is the
step `k` applied to `A^{(k)}`. -/
noncomputable def hessenbergIter (A : Matrix (Fin N) (Fin N) 𝕜) : ℕ → Matrix (Fin N) (Fin N) 𝕜
  | 0 => A
  | k + 1 => hessenbergStep (hessenbergIter A k) k

/-- The accumulated product `Q_{(k)} = P_{(0)} ⋯ P_{(k-1)}` of the reflectors of the Householder
reduction. -/
noncomputable def hessenbergQIter (A : Matrix (Fin N) (Fin N) 𝕜) : ℕ → Matrix (Fin N) (Fin N) 𝕜
  | 0 => 1
  | k + 1 => hessenbergQIter A k * hessenbergReflector (hessenbergIter A k) k

/-- **The Householder reduction to Hessenberg form** ([quarteroni2000numerical] §5.6.2,
Program 29): the matrix `H = A^{(N-2)}` after the `N - 2` similarity steps of
`Matrix.hessenbergStep`. -/
noncomputable def hessenbergReduce (A : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  hessenbergIter A (N - 2)

/-- The unitary matrix `Q = P_{(0)} ⋯ P_{(N-3)}` of the Householder reduction, so that
`hessenbergReduce A = Qᴴ A Q` (`Matrix.hessenbergReduce_eq_conj`). -/
noncomputable def hessenbergQ (A : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  hessenbergQIter A (N - 2)

/-- The reduction starts at `A`. -/
@[simp]
theorem hessenbergIter_zero : hessenbergIter A 0 = A := rfl

/-- One step of the reduction, by definition. -/
theorem hessenbergIter_succ (k : ℕ) :
    hessenbergIter A (k + 1) = hessenbergStep (hessenbergIter A k) k := rfl

/-- The accumulated reflector product starts at the identity. -/
@[simp]
theorem hessenbergQIter_zero : hessenbergQIter A 0 = 1 := rfl

/-- One step of the accumulated reflector product, by definition. -/
theorem hessenbergQIter_succ (k : ℕ) :
    hessenbergQIter A (k + 1) =
      hessenbergQIter A k * hessenbergReflector (hessenbergIter A k) k := rfl

/-- The accumulated reflector product is unitary. -/
theorem hessenbergQIter_mem_unitaryGroup (k : ℕ) :
    hessenbergQIter A k ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  induction k with
  | zero => exact one_mem _
  | succ k ih => exact mul_mem ih (hessenbergReflector_mem_unitaryGroup _ _)

/-- [quarteroni2000numerical] (5.45): `A^{(k)} = Q_{(k)}ᴴ A Q_{(k)}`. -/
theorem hessenbergIter_eq_conj (k : ℕ) :
    hessenbergIter A k = (hessenbergQIter A k)ᴴ * A * hessenbergQIter A k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hessenbergIter_succ, hessenbergStep, hessenbergQIter_succ, conjTranspose_mul,
      (isHermitian_hessenbergReflector _ _).eq, ih]
    simp only [Matrix.mul_assoc]

/-- The matrix `Q` of the Householder reduction is unitary. -/
theorem hessenbergQ_mem_unitaryGroup : hessenbergQ A ∈ Matrix.unitaryGroup (Fin N) 𝕜 :=
  hessenbergQIter_mem_unitaryGroup A _

/-- The matrix `Q` of the Householder reduction of a real matrix is orthogonal. -/
theorem hessenbergQ_mem_orthogonalGroup (A : Matrix (Fin N) (Fin N) ℝ) :
    hessenbergQ A ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  hessenbergQ_mem_unitaryGroup A

/-- [quarteroni2000numerical] (5.45): the Householder reduction is a unitary similarity,
`H = Qᴴ A Q`. -/
theorem hessenbergReduce_eq_conj : hessenbergReduce A = (hessenbergQ A)ᴴ * A * hessenbergQ A :=
  hessenbergIter_eq_conj A _

/-- The invariant of the reduction: step `k` clears column `k` below the first subdiagonal by the
tail reflector, and leaves the columns already cleared alone, because the reflector's axis
vanishes on the rows `≤ k` where those columns live. -/
private theorem hessenbergStep_apply_eq_zero {B : Matrix (Fin N) (Fin N) 𝕜} {k : ℕ}
    (hB : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → B i j = 0) (i j : Fin N)
    (hj : (j : ℕ) < k + 1) (hij : (j : ℕ) + 1 < (i : ℕ)) : hessenbergStep B k i j = 0 := by
  by_cases hk : k < N
  swap
  · rw [hessenbergStep, hessenbergReflector_of_le B (not_lt.1 hk), one_mul, mul_one]
    exact hB i j (by have := i.isLt; omega) hij
  rw [hessenbergStep, hessenbergReflector_of_lt B hk,
    mul_householder_apply_of_apply_eq_zero (householderTail_apply_of_lt _ (by omega)),
    householder_mul_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · rw [householder_mulVec_eq_self_of_apply_eq_zero fun r hr => hB r j hjk ?_]
    · exact hB i j hjk hij
    · by_contra hcon
      exact hr (householderTail_apply_of_lt _ (by omega))
  · have hjκ : j = ⟨k, hk⟩ := Fin.ext hjk
    subst hjκ
    exact householder_householderTail_mulVec_apply_of_gt _ hij

/-- After `k` steps of the reduction the columns `j < k` vanish below the first subdiagonal. -/
theorem hessenbergIter_apply_eq_zero (k : ℕ) (i j : Fin N) (hj : (j : ℕ) < k)
    (hij : (j : ℕ) + 1 < (i : ℕ)) : hessenbergIter A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    rw [hessenbergIter_succ]
    exact hessenbergStep_apply_eq_zero (fun i j => ih i j) i j hj hij

/-- **The Householder reduction produces an upper Hessenberg matrix**
([quarteroni2000numerical] §5.6.2): after `N - 2` steps every column vanishes below the first
subdiagonal. -/
theorem isUpperHessenberg_hessenbergReduce : (hessenbergReduce A).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff_fin]
  intro i j hij
  exact hessenbergIter_apply_eq_zero A (N - 2) i j (by have := i.isLt; omega) hij

/-- The Householder reduction of a Hermitian matrix is Hermitian, being a unitary conjugate of it
([quarteroni2000numerical] Remark 5.4). -/
theorem isHermitian_hessenbergReduce (hA : A.IsHermitian) : (hessenbergReduce A).IsHermitian := by
  rw [hessenbergReduce_eq_conj]
  exact isHermitian_conjTranspose_mul_mul _ hA

/-- [quarteroni2000numerical] Remark 5.4: the Householder reduction of a Hermitian matrix is
tridiagonal. -/
theorem isTridiagonal_hessenbergReduce_of_isHermitian (hA : A.IsHermitian) :
    (hessenbergReduce A).IsTridiagonal :=
  (isUpperHessenberg_hessenbergReduce A).isTridiagonal_of_isHermitian
    (isHermitian_hessenbergReduce A hA)

/-- [quarteroni2000numerical] Remark 5.4, the real case: the Householder reduction of a symmetric
real matrix is symmetric, hence (`Matrix.IsUpperHessenberg.isTridiagonal_of_isSymm`)
tridiagonal. -/
theorem isSymm_hessenbergReduce {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) :
    (hessenbergReduce A).IsSymm := by
  have h : (hessenbergReduce A).IsHermitian :=
    isHermitian_hessenbergReduce A (by rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial])
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

/-- **Every square matrix is unitarily similar to an upper Hessenberg matrix**
([quarteroni2000numerical] §5.6.2): the existence form of the Householder reduction, transported
from `Fin N` to any finite linearly ordered index type along `monoEquivOfFin`. -/
theorem exists_unitary_conj_isUpperHessenberg [LinearOrder n] (A : Matrix n n 𝕜) :
    ∃ Q ∈ Matrix.unitaryGroup n 𝕜, (Qᴴ * A * Q).IsUpperHessenberg := by
  obtain ⟨e, -⟩ : ∃ e : Fin (Fintype.card n) ≃o n, True := ⟨monoEquivOfFin n rfl, trivial⟩
  obtain ⟨A', hA'⟩ : ∃ A', A' = A.submatrix e.toEquiv e.toEquiv := ⟨_, rfl⟩
  have hA : A = A'.submatrix e.toEquiv.symm e.toEquiv.symm := by
    rw [hA', submatrix_submatrix]
    ext i j
    simp
  refine ⟨(hessenbergQ A').submatrix e.toEquiv.symm e.toEquiv.symm, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp (hessenbergQ_mem_unitaryGroup _), submatrix_one_equiv]
  · rintro i j ⟨l, hjl, hli⟩
    rw [hA, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
      ← hessenbergReduce_eq_conj, submatrix_apply]
    exact isUpperHessenberg_hessenbergReduce _ _ _
      ⟨e.symm l, e.symm.lt_iff_lt.mpr hjl, e.symm.lt_iff_lt.mpr hli⟩

end HessenbergReduction

/-! ### The Givens QR factorization of a Hessenberg matrix -/

section GivensQR

variable {N : ℕ}

/-- The rotation of step `j` of the Givens `QR` factorization of a Hessenberg matrix: the
rotation of the `(j, j + 1)`-plane by the Givens pair of the entries `(j, j)` and `(j + 1, j)` of
`R`, whose transpose annihilates the latter ([quarteroni2000numerical] (5.47), `G_j^{(k)}`). -/
noncomputable def hessenbergGivensRotation (R : Matrix (Fin N) (Fin N) ℝ) (j : ℕ)
    (h : j + 1 < N) : Matrix (Fin N) (Fin N) ℝ :=
  planeRotation (⟨j, by omega⟩ : Fin N) ⟨j + 1, h⟩
    (givensPair (R ⟨j, by omega⟩ ⟨j, by omega⟩) (R ⟨j + 1, h⟩ ⟨j, by omega⟩)).1
    (givensPair (R ⟨j, by omega⟩ ⟨j, by omega⟩) (R ⟨j + 1, h⟩ ⟨j, by omega⟩)).2

/-- The rotations of the Givens factorization are orthogonal. -/
theorem hessenbergGivensRotation_mem_orthogonalGroup (R : Matrix (Fin N) (Fin N) ℝ) (j : ℕ)
    (h : j + 1 < N) : hessenbergGivensRotation R j h ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  planeRotation_mem_orthogonalGroup (Fin.ne_of_val_ne (by simp)) (givensPair_sq_add_sq _ _)

/-- One step of the Givens `QR` factorization of a Hessenberg matrix, on the pair `(Q, R)`: rotate
the rows `j`, `j + 1` of `R` so as to annihilate the entry `(j + 1, j)`, and accumulate the rotation
into `Q` ([quarteroni2000numerical] (5.47), Program 31); no step when `j + 1 ≥ N`. -/
noncomputable def hessenbergGivensStep (QR : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)
    (j : ℕ) : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ :=
  if h : j + 1 < N then
    (QR.1 * hessenbergGivensRotation QR.2 j h, (hessenbergGivensRotation QR.2 j h)ᵀ * QR.2)
  else QR

/-- The pairs `(Q, R)` of the Givens factorization after `j` steps, starting from `(1, H)`. -/
noncomputable def hessenbergGivensIter (H : Matrix (Fin N) (Fin N) ℝ) :
    ℕ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ
  | 0 => (1, H)
  | j + 1 => hessenbergGivensStep (hessenbergGivensIter H j) j

/-- **The Givens `QR` factorization of an upper Hessenberg matrix** ([quarteroni2000numerical]
(5.47)–(5.48), Program 31): the pair `(Q, R)` after the `N - 1` rotations in the planes
`(j, j + 1)`, `Q = G_0 ⋯ G_{N-2}` and `R = G_{N-2}ᵀ ⋯ G_0ᵀ H`. Its properties are
`Matrix.hessenbergGivensQR_spec`. -/
noncomputable def hessenbergGivensQR (H : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ :=
  hessenbergGivensIter H (N - 1)

/-- The invariant of the Givens fold after `j` steps: `Q` is orthogonal, `Q R = H`, `R` is
Hessenberg and upper triangular in the columns `< j`, and `Q` is Hessenberg and agrees with the
identity beyond row `j` and beyond column `j`. -/
private structure GivensInvariant (H : Matrix (Fin N) (Fin N) ℝ) (j : ℕ)
    (Q R : Matrix (Fin N) (Fin N) ℝ) : Prop where
  orth : Q ∈ Matrix.orthogonalGroup (Fin N) ℝ
  mul : Q * R = H
  hessR : ∀ i l : Fin N, (l : ℕ) + 1 < (i : ℕ) → R i l = 0
  colsR : ∀ i l : Fin N, (l : ℕ) < j → (l : ℕ) < (i : ℕ) → R i l = 0
  hessQ : ∀ i l : Fin N, (l : ℕ) + 1 < (i : ℕ) → Q i l = 0
  rowsQ : ∀ i l : Fin N, j < (i : ℕ) → Q i l = if i = l then 1 else 0
  colsQ : ∀ i l : Fin N, j < (l : ℕ) → Q i l = if i = l then 1 else 0

private theorem givensInvariant_zero {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg) :
    GivensInvariant H 0 1 H where
  orth := one_mem _
  mul := Matrix.one_mul H
  hessR := isUpperHessenberg_iff_fin.1 hH
  colsR := fun _ _ hl => absurd hl (Nat.not_lt_zero _)
  hessQ := fun _ _ hil => one_apply_ne (Fin.ne_of_val_ne (by omega))
  rowsQ := fun _ _ _ => one_apply
  colsQ := fun _ _ _ => one_apply

private theorem givensInvariant_step {H : Matrix (Fin N) (Fin N) ℝ} {j : ℕ}
    {Q R : Matrix (Fin N) (Fin N) ℝ} (hinv : GivensInvariant H j Q R) :
    GivensInvariant H (j + 1) (hessenbergGivensStep (Q, R) j).1
      (hessenbergGivensStep (Q, R) j).2 := by
  unfold hessenbergGivensStep
  split_ifs with h
  swap
  · exact
      { orth := hinv.orth
        mul := hinv.mul
        hessR := hinv.hessR
        colsR := fun i l hl hli => hinv.colsR i l (by have := i.isLt; omega) hli
        hessQ := hinv.hessQ
        rowsQ := fun i l hi => hinv.rowsQ i l (by omega)
        colsQ := fun i l hl => hinv.colsQ i l (by omega) }
  obtain ⟨a, ha⟩ : ∃ a : Fin N, a = ⟨j, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin N, b = ⟨j + 1, h⟩ := ⟨_, rfl⟩
  have hav : (a : ℕ) = j := by rw [ha]
  have hbv : (b : ℕ) = j + 1 := by rw [hb]
  have hab : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hG : hessenbergGivensRotation R j h = planeRotation a b
      (givensPair (R a a) (R b a)).1 (givensPair (R a a) (R b a)).2 := by
    rw [ha, hb]; rfl
  have hRb : ∀ l : Fin N, (l : ℕ) < j → R b l = 0 := fun l hl => hinv.hessR b l (by omega)
  have hRa : ∀ l : Fin N, (l : ℕ) < j → R a l = 0 := fun l hl => hinv.colsR a l hl (by omega)
  have hGG : hessenbergGivensRotation R j h * (hessenbergGivensRotation R j h)ᵀ = 1 :=
    (mem_orthogonalGroup_iff (Fin N) ℝ).1 (hessenbergGivensRotation_mem_orthogonalGroup R j h)
  refine
    { orth := mul_mem hinv.orth (hessenbergGivensRotation_mem_orthogonalGroup R j h)
      mul := ?_
      hessR := ?_
      colsR := ?_
      hessQ := ?_
      rowsQ := ?_
      colsQ := ?_ }
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (hessenbergGivensRotation R j h), hGG,
      Matrix.one_mul, hinv.mul]
  · intro i l hil
    dsimp only
    rw [hG, transpose_planeRotation_mul_apply hab]
    by_cases hia : i = a
    · have hiv : (i : ℕ) = a := by rw [hia]
      rw [ite_eq_left hia, hinv.hessR a l (by omega), hinv.hessR b l (by omega)]
      ring
    by_cases hib : i = b
    · have hiv : (i : ℕ) = b := by rw [hib]
      rw [ite_eq_right hia, ite_eq_left hib, hRa l (by omega), hRb l (by omega)]
      ring
    · rw [ite_eq_right hia, ite_eq_right hib]
      exact hinv.hessR i l hil
  · intro i l hl hli
    dsimp only
    rw [hG, transpose_planeRotation_mul_apply hab]
    by_cases hia : i = a
    · have hiv : (i : ℕ) = a := by rw [hia]
      rw [ite_eq_left hia, hRa l (by omega), hRb l (by omega)]
      ring
    by_cases hib : i = b
    · rw [ite_eq_right hia, ite_eq_left hib]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlj | hlj
      · rw [hRa l hlj, hRb l hlj]
        ring
      · have hla : l = a := Fin.ext (by omega)
        rw [hla]
        exact (givensPair_fst_mul_add_snd_mul (R a a) (R b a)).2
    · rw [ite_eq_right hia, ite_eq_right hib]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlj | hlj
      · exact hinv.colsR i l hlj hli
      · have hia' : (i : ℕ) ≠ j := fun hij => hia (Fin.ext (by omega))
        have hib' : (i : ℕ) ≠ j + 1 := fun hij => hib (Fin.ext (by omega))
        exact hinv.hessR i l (by omega)
  · intro i l hil
    dsimp only
    rw [hG, mul_planeRotation_apply hab]
    by_cases hla : l = a
    · rw [ite_eq_left hla, hinv.rowsQ i a (by omega), hinv.rowsQ i b (by omega),
        ite_eq_right (Fin.ne_of_val_ne (by omega : (i : ℕ) ≠ a)),
        ite_eq_right (Fin.ne_of_val_ne (by omega : (i : ℕ) ≠ b))]
      ring
    by_cases hlb : l = b
    · rw [ite_eq_right hla, ite_eq_left hlb, hinv.rowsQ i a (by omega),
        hinv.rowsQ i b (by omega), ite_eq_right (Fin.ne_of_val_ne (by omega : (i : ℕ) ≠ a)),
        ite_eq_right (Fin.ne_of_val_ne (by omega : (i : ℕ) ≠ b))]
      ring
    · rw [ite_eq_right hla, ite_eq_right hlb]
      exact hinv.hessQ i l hil
  · intro i l hi
    dsimp only
    rw [hG, mul_planeRotation_apply hab]
    have hia : i ≠ a := Fin.ne_of_val_ne (by omega)
    have hib : i ≠ b := Fin.ne_of_val_ne (by omega)
    by_cases hla : l = a
    · rw [ite_eq_left hla, hinv.rowsQ i a (by omega), hinv.rowsQ i b (by omega),
        ite_eq_right hia, ite_eq_right hib, hla, ite_eq_right hia]
      ring
    by_cases hlb : l = b
    · rw [ite_eq_right hla, ite_eq_left hlb, hinv.rowsQ i a (by omega),
        hinv.rowsQ i b (by omega), ite_eq_right hia, ite_eq_right hib, hlb, ite_eq_right hib]
      ring
    · rw [ite_eq_right hla, ite_eq_right hlb]
      exact hinv.rowsQ i l (by omega)
  · intro i l hl
    dsimp only
    rw [hG, mul_planeRotation_apply hab, ite_eq_right (Fin.ne_of_val_ne (by omega : (l : ℕ) ≠ a)),
      ite_eq_right (Fin.ne_of_val_ne (by omega : (l : ℕ) ≠ b))]
    exact hinv.colsQ i l (by omega)

private theorem givensInvariant_iter {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg)
    (j : ℕ) : GivensInvariant H j (hessenbergGivensIter H j).1 (hessenbergGivensIter H j).2 := by
  induction j with
  | zero => exact givensInvariant_zero hH
  | succ j ih => exact givensInvariant_step ih

/-- **The Givens `QR` factorization of a Hessenberg matrix** ([quarteroni2000numerical]
(5.47)–(5.48), §5.6.3): for `H` upper Hessenberg, the pair `(Q, R) = hessenbergGivensQR H` has `Q`
orthogonal, `R` upper triangular, `H = Q R`, and `Q` itself upper Hessenberg. -/
theorem hessenbergGivensQR_spec {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg) :
    (hessenbergGivensQR H).1 ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      (hessenbergGivensQR H).2.IsUpperTriangular ∧
      H = (hessenbergGivensQR H).1 * (hessenbergGivensQR H).2 ∧
      (hessenbergGivensQR H).1.IsUpperHessenberg := by
  have hinv := givensInvariant_iter hH (N - 1)
  refine ⟨hinv.orth, fun i l hli => ?_, hinv.mul.symm, isUpperHessenberg_iff_fin.2 hinv.hessQ⟩
  have hli' : (l : ℕ) < i := hli
  exact hinv.colsR i l (by have := i.isLt; omega) hli'

end GivensQR

/-! ### Hadamard's determinant inequality -/

section Hadamard

/-- A unitary matrix preserves the Euclidean length of a vector, in the form
`∑ i, ‖(U *ᵥ v) i‖² = ∑ i, ‖v i‖²`: both sides are `star w ⬝ᵥ w` read as a real number, and
`Uᴴ U = 1`. -/
theorem sum_norm_sq_mulVec_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ Matrix.unitaryGroup n 𝕜) (v : n → 𝕜) :
    ∑ i, ‖(U *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have key : ∀ w : n → 𝕜, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : 𝕜) := by
    intro w
    rw [dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by simpa using RCLike.conj_mul (w i)
  have h : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.1 hU, vecMul_one]
  rw [key, key] at h
  exact_mod_cast h

/-- The determinant of a unitary matrix has modulus one. -/
theorem norm_det_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    ‖U.det‖ = 1 := by
  have h1 : ‖star U.det * U.det‖ = 1 := by
    rw [_root_.Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hU), norm_one]
  rw [norm_mul, norm_star] at h1
  nlinarith [norm_nonneg U.det]

variable [LinearOrder n]

/-- **Hadamard's determinant inequality**: the modulus of a determinant is at most the product of
the Euclidean lengths of the columns. Triangularize by a unitary matrix
(`Matrix.exists_unitary_mul_isUpperTriangular`); the determinant of `U X` is that of `X` up to a
unit-modulus factor, it is the product of the diagonal of the triangular factor, and each diagonal
entry is bounded by the length of its column, which `U` has not changed. -/
theorem norm_det_le_prod_sqrt_sum_norm_sq (X : Matrix n n 𝕜) :
    ‖X.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖X i j‖ ^ 2) := by
  obtain ⟨U, hU, hT⟩ := exists_unitary_mul_isUpperTriangular X
  have hcol : ∀ j, ∑ i, ‖(U * X) i j‖ ^ 2 = ∑ i, ‖X i j‖ ^ 2 := fun j =>
    sum_norm_sq_mulVec_of_mem_unitaryGroup hU _
  have hX : ‖X.det‖ = ‖(U * X).det‖ := by
    rw [det_mul, norm_mul, norm_det_of_mem_unitaryGroup hU, one_mul]
  rw [hX, det_of_isUpperTriangular hT, norm_prod]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [← hcol j]
  calc ‖(U * X) j j‖ = Real.sqrt (‖(U * X) j j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ‖(U * X) i j‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖(U * X) i j‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_univ j))

/-- **Hadamard's inequality in entrywise form**: a matrix of order `m` whose entries have modulus
at most `c` has `‖det‖ ≤ m^{m/2} c^m`. -/
theorem norm_det_le_of_forall_norm_le {X : Matrix n n 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖X i j‖ ≤ c) :
    ‖X.det‖ ≤ (Real.sqrt (Fintype.card n) * c) ^ Fintype.card n := by
  refine (norm_det_le_prod_sqrt_sum_norm_sq X).trans ?_
  calc ∏ j, Real.sqrt (∑ i, ‖X i j‖ ^ 2)
      ≤ ∏ _j : n, Real.sqrt (Fintype.card n * c ^ 2) := by
        refine Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) fun j _ => Real.sqrt_le_sqrt ?_
        calc ∑ i, ‖X i j‖ ^ 2 ≤ ∑ _i : n, c ^ 2 :=
              Finset.sum_le_sum fun i _ => by nlinarith [h i j, norm_nonneg (X i j)]
          _ = Fintype.card n * c ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Real.sqrt (Fintype.card n) * c) ^ Fintype.card n := by
        rw [Finset.prod_const, Finset.card_univ, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

end Hadamard

end Matrix
