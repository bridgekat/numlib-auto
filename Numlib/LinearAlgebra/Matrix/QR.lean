/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.QR`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.Analysis.InnerProductSpace.GramSchmidt

/-!
# Householder reflectors and the QR factorization

A **Householder reflector** `Matrix.householder w = 1 - 2 w wᴴ` is the reflection in the
hyperplane orthogonal to a unit vector `w`; it is Hermitian, involutive and therefore unitary.
Its defining property is that one reflector annihilates every entry of a vector but one
(`Matrix.householder_mulVec_eq_smul_single`), and an induction over the columns then
triangularizes any matrix by a product of reflectors
(`Matrix.exists_unitary_mul_upperTriangular`).

The same factorization is reached from the other end by orthonormalizing the columns:
`Matrix.exists_qr` factors a matrix with linearly independent columns as `X = Q R` with
`Qᴴ Q = 1` and `R` upper triangular of positive diagonal, taking `Q` to be
`InnerProductSpace.gramSchmidtNormed` of the columns and `R i j = ⟪Q i, X j⟫`.  The two routes
meet at `Matrix.qr_unique`: the factorization with a positive diagonal is unique, so a product
of reflectors, classical Gram–Schmidt and modified Gram–Schmidt all compute the same `Q` and the
same `R`.

Nothing here is numerical: no stability, no operation count, no pivoting.

This serves [Saad, *Iterative Methods for Sparse Linear Systems*][saad2003iterative], §1.7 — the
reflector (1.20), its defining conditions (1.21)–(1.26), the factorization (1.19), the
triangularization (1.27)–(1.28) and Algorithm 1.3 — and [Kress, *Numerical
Analysis*][kress1998numerical], §5.

## Main definitions

* `Matrix.householder`: the reflector `1 - 2 w wᴴ` in the hyperplane orthogonal to `w`.
* `Matrix.phase`: the unit-modulus phase of a scalar, `1` at zero; Saad's `sign`.
* `Matrix.householderAxis`, `Matrix.householderVec`: the axis `x + sign(x i) ‖x‖ eᵢ` of the
  reflector that annihilates every entry of `x` but the `i`-th, and its normalization.

## Main results

* `Matrix.householder_mulVec_eq_smul_single`: one reflector annihilates every entry of a vector
  but one.
* `Matrix.exists_unitary_mul_upperTriangular`: a product of reflectors triangularizes any matrix.
* `Matrix.exists_qr`: the Gram–Schmidt factorization `X = Q R` of a matrix with linearly
  independent columns, and its converse `Matrix.linearIndependent_of_qr`.
* `Matrix.qr_unique`: the factorization with a positive diagonal is unique, so all three
  constructions compute the same pair.
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

/-- The Householder reflector `1 - 2 w wᴴ`, the reflection in the hyperplane orthogonal to `w`
when `w` is a unit vector, and the identity when `w = 0`. -/
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

/-- The reflector built from an unnormalized axis `v` sends `x` to
`x - (2 ⟪v, x⟫ / ⟪v, v⟫) v`. -/
private theorem householder_normalize_mulVec {v : n → 𝕜} (hv : v ≠ 0) (x : n → 𝕜) :
    householder (normalize v) *ᵥ x = x - (2 * (star v ⬝ᵥ x) / (star v ⬝ᵥ v)) • v := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [householder_mulVec, normalize, star_smul, smul_dotProduct, RCLike.star_def, RCLike.conj_inv,
    RCLike.conj_ofReal, smul_eq_mul, smul_smul, star_dotProduct_self]
  congr 2
  field_simp

/-! ### The reflector that annihilates a column below one entry -/

/-- The unit-modulus phase of a scalar, and `1` at zero: the `sign` of Saad's (1.22). -/
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

/-- The defining property of the phase: `conj (sign z) * z = |z|`, a nonnegative real.  This is
what makes the denominator of Saad's (1.22) bounded away from zero. -/
theorem conj_phase_mul_self (z : 𝕜) : starRingEnd 𝕜 (phase z) * z = ((‖z‖ : 𝕜)) := by
  rw [phase]
  by_cases h : z = 0
  · simp [h]
  · rw [ite_eq_right h, map_mul, RCLike.conj_inv, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    have hz : ((‖z‖ : 𝕜)) ≠ 0 := by simpa using norm_ne_zero_iff.2 h
    field_simp

/-- Saad's (1.22): the axis `x + sign(x i) ‖x‖ e_i` of the reflector that annihilates every entry
of `x` but the `i`-th. -/
noncomputable def householderAxis (x : n → 𝕜) (i : n) : n → 𝕜 :=
  x + (phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)))
    • (Pi.single i 1 : n → 𝕜)

/-- Saad's (1.22): the unit vector whose reflector annihilates every entry of `x` but the
`i`-th. -/
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

/-- `⟪v, v⟫ = 2 ⟪v, x⟫` for the Householder axis `v`: the sign choice is exactly what makes the
two agree up to the factor two. -/
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

private theorem householderAxis_ne_zero {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
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

/-- Saad's (1.21)–(1.22): the Householder reflector in the hyperplane orthogonal to
`w = (x + sign(x i) ‖x‖ e_i) / ‖x + sign(x i) ‖x‖ e_i‖` sends `x` to `(- sign(x i) ‖x‖) e_i`, so
a single reflector annihilates every entry of `x` but the `i`-th. -/
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

/-! ### Triangularization by a product of reflectors -/

section Triangular

variable {N M : ℕ}

/-- One step of [Saad, *Iterative Methods*][saad2003iterative] Algorithm 1.3: a reflector
supported on the rows from `k` on annihilates the
`k`-th column below the diagonal without disturbing the columns already cleared. -/
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

/-- Saad's (1.27)–(1.28) and Algorithm 1.3: every matrix is carried to upper triangular form (in
the rectangular sense, zero strictly below the diagonal) by a unitary matrix, namely a product of
at most as many Householder reflectors as the matrix has columns. -/
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

end Triangular

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
flag-uniqueness argument of `Numlib.Analysis.InnerProductSpace.GramSchmidt` at matrix level, and
it is what makes the QR factorization with a positive diagonal unique. -/
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
reflector product of `Matrix.exists_unitary_mul_upperTriangular` with the Gram–Schmidt
factorization of `Matrix.exists_qr`, and either of them with the modified Gram–Schmidt one, with
no need to compare the constructions. -/
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

/-- Saad's (1.19): a matrix whose columns are linearly independent factors as `X = Q R` with
orthonormal columns in `Q` and `R` upper triangular of positive diagonal.  The factors are the
Gram–Schmidt orthonormalization of the columns and the matrix `R i j = ⟪Q i, X j⟫` of the
coefficients, which is Saad's Algorithm 1.1; Algorithm 1.2 (modified Gram–Schmidt) computes the
same pair, by `Matrix.qr_unique`. -/
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

/-- The converse of `Matrix.exists_qr`: a factorization with orthonormal columns and an
invertible upper triangular factor forces the columns of `X` to be linearly independent. -/
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
    have := congrArg (fun v => R⁻¹ *ᵥ v) hRc
    simpa [mulVec_mulVec, nonsing_inv_mul R hdet] using this
  exact fun i => congrFun h2 i

end GramSchmidt

end Matrix
