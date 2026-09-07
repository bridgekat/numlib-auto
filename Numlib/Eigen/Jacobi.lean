/-
Upstreaming candidate for its first half: `Matrix.offDiagNormSq` and `Matrix.planeRotation` are
general matrix material with no numerical-analysis-specific content.
Natural home: `Mathlib.LinearAlgebra.Matrix.PlaneRotation`.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Jacobi's eigenvalue algorithm

Jacobi's method drives a real symmetric matrix towards a diagonal one by a sequence of plane
rotations, each chosen to annihilate one off-diagonal entry. The quantity it decreases is the
**off-diagonal mass** `N(A)² = ∑_{i ≠ j} |a_ij|²`, and the whole of the classical analysis is the
identity `N(UᵀAU)² = N(A)² - 2 a_jk²` for the rotation `U` that annihilates `a_jk`
([kress1998numerical], Lemma 7.13), together with the observation that the largest off-diagonal
entry carries at least a fraction `1/(n² - n)` of the mass.

## Main definitions

* `Matrix.offDiagNormSq`: [kress1998numerical] `N(A)²`.
* `Matrix.planeRotation`: the rotation of the `(j,k)`-plane by a given cosine and sine.
* `Matrix.jacobiRotation`, `Matrix.jacobiStep`: the rotation annihilating `a_jk`, and the similarity
  it induces.
* `Matrix.classicalJacobiIterate`: the classical method, annihilating a largest off-diagonal entry
  at each step.

## Main results

* `Matrix.offDiagNormSq_jacobiStep`: `N(UᵀAU)² = N(A)² - 2 a_jk²`.
* `Matrix.offDiagNormSq_classicalJacobiIterate_le`: the geometric decay `N(A_ν)² ≤ (1 - 2/(n² -
  n))^ν N(A)²`.
* `Matrix.tendsto_offDiagNormSq_classicalJacobiIterate`: the off-diagonal mass tends to `0`.
* `Matrix.charpoly_classicalJacobiIterate`: every iterate is orthogonally similar to `A`, so the
  eigenvalues never move.
* `Matrix.tendsto_classicalJacobiIterate`: the iterates converge to a diagonal matrix with the
  characteristic polynomial of `A`.

## Implementation notes

The method is stated for **real symmetric** matrices, which is what a plane rotation with a real
angle can diagonalize: for a complex Hermitian matrix a rotation with one real parameter cannot
annihilate a complex `a_jk`, and one needs a phase as well.

The rotation angle is parametrized by its tangent `t`, the root `t = θ + √(θ²+1)` of `t² - 2θt - 1 =
0` with `θ = (a_kk - a_jj)/(2 a_jk)`, rather than by the angle itself: the annihilation identity is
then a polynomial identity in `c` and `s`, provable by `linear_combination`, and no trigonometry is
needed. The numerically preferable root, the one of smaller modulus, differs only in stability and
not in the statements proved here.
-/

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The off-diagonal mass -/

section OffDiag

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **off-diagonal mass** of a matrix, `N(A)² = ∑_{i ≠ j} ‖a_ij‖²`; [kress1998numerical] writes
it `N(A)²`. Jacobi's method is the statement that a plane rotation annihilating `a_jk` decreases it
by exactly `2 ‖a_jk‖²`. -/
noncomputable def offDiagNormSq (A : Matrix n n 𝕜) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2

/-- The off-diagonal mass is a sum of squares, hence nonnegative. -/
theorem offDiagNormSq_nonneg (A : Matrix n n 𝕜) : 0 ≤ offDiagNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The off-diagonal mass and the diagonal mass make up the squared Frobenius norm `∑ i, ∑ j,
‖a_ij‖²` ([kress1998numerical], Lemma 7.8). -/
theorem offDiagNormSq_add_sum_diag_sq (A : Matrix n n 𝕜) :
    offDiagNormSq A + ∑ i, ‖A i i‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [offDiagNormSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- The off-diagonal mass vanishes exactly for diagonal matrices. -/
theorem offDiagNormSq_eq_zero_iff {A : Matrix n n 𝕜} :
    offDiagNormSq A = 0 ↔ ∀ i j, i ≠ j → A i j = 0 := by
  rw [offDiagNormSq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  constructor
  · intro h i j hij
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 (h i (Finset.mem_univ i))
      j (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)
    simpa using h1
  · intro h i _
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [h i j (Finset.mem_erase.1 hj).1.symm]
    simp

end OffDiag

/-! ### Plane rotations -/

section PlaneRotation

/-- The rotation of the `(j,k)`-plane with cosine `c` and sine `s`: the identity matrix with its
`j`-th and `k`-th rows replaced by `(c, -s)` and `(s, c)` in the columns `j` and `k`. -/
def planeRotation (j k : n) (c s : ℝ) : Matrix n n ℝ := Matrix.of fun p q =>
  if p = j then (if q = j then c else if q = k then -s else 0)
  else if p = k then (if q = j then s else if q = k then c else 0)
  else if p = q then 1 else 0

variable {j k : n} {c s : ℝ}

omit [Fintype n] in
/-- The entries of a plane rotation, written so that each column is a linear combination of
Kronecker deltas. -/
theorem planeRotation_apply (hjk : j ≠ k) (t q : n) :
    planeRotation j k c s t q =
      if q = j then (if t = j then c else 0) + (if t = k then s else 0)
      else if q = k then (if t = j then -s else 0) + (if t = k then c else 0)
      else if t = q then 1 else 0 := by
  have hkj : k ≠ j := hjk.symm
  unfold planeRotation
  simp only [Matrix.of_apply]
  by_cases htj : t = j
  · by_cases hqj : q = j
    · simp [htj, hqj, hjk]
    · by_cases hqk : q = k
      · simp [htj, hqk, hjk]
      · simp [htj, hqj, hqk, Ne.symm hqj]
  · by_cases htk : t = k
    · by_cases hqj : q = j
      · simp [htk, hqj, hkj]
      · by_cases hqk : q = k
        · simp [htk, hqk, hkj]
        · simp [htk, hqj, hqk, Ne.symm hqk]
    · by_cases hqj : q = j
      · simp [htj, htk, hqj]
      · by_cases hqk : q = k
        · simp [htj, htk, hqk]
        · simp [htj, htk, hqj, hqk]

/-- Multiplying on the right by a plane rotation combines the `j`-th and `k`-th columns. -/
theorem mul_planeRotation_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    (M * planeRotation j k c s) p q =
      if q = j then c * M p j + s * M p k
      else if q = k then -s * M p j + c * M p k
      else M p q := by
  rw [Matrix.mul_apply]
  simp only [planeRotation_apply hjk]
  split_ifs with h1 h2
  · simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq', mul_comm]
  · simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq', mul_comm]
  · simp [mul_ite, Finset.sum_ite_eq']

/-- Multiplying on the left by the transpose of a plane rotation combines the `j`-th and `k`-th
rows. -/
theorem transpose_planeRotation_mul_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    ((planeRotation j k c s)ᵀ * M) p q =
      if p = j then c * M j q + s * M k q
      else if p = k then -s * M j q + c * M k q
      else M p q := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, planeRotation_apply hjk]
  split_ifs with h1 h2
  · simp [add_mul, Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']
  · simp [add_mul, Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq']
  · simp [ite_mul, Finset.sum_ite_eq']

/-- A plane rotation is orthogonal. -/
theorem transpose_planeRotation_mul_self (hjk : j ≠ k) (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRotation j k c s)ᵀ * planeRotation j k c s = 1 := by
  have hkj : k ≠ j := hjk.symm
  ext p q
  rw [transpose_planeRotation_mul_apply hjk]
  simp only [planeRotation_apply hjk, Matrix.one_apply, hjk, hkj, ite_true, ite_false,
    add_zero, zero_add]
  split_ifs <;> simp_all <;> nlinarith [hcs]

end PlaneRotation

/-! ### Frobenius mass and orthogonal conjugation -/

section Frobenius

omit [DecidableEq n] in
/-- The trace of `AᵀA` is the squared Frobenius norm of `A`. -/
theorem trace_transpose_mul_self (A : Matrix n n ℝ) :
    (Aᵀ * A).trace = ∑ i, ∑ q, (A i q) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

/-- Over the reals the off-diagonal mass is the sum of the squares of the off-diagonal entries, the
norm bars being redundant. -/
theorem offDiagNormSq_real (A : Matrix n n ℝ) :
    offDiagNormSq A = ∑ i, ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2 := by
  simp [offDiagNormSq, Real.norm_eq_abs, sq_abs]

/-- The real form of `Matrix.offDiagNormSq_add_sum_diag_sq`: the off-diagonal and the diagonal
masses make up the squared Frobenius norm. -/
theorem offDiagNormSq_add_sum_diag_sq_real (A : Matrix n n ℝ) :
    offDiagNormSq A + ∑ i, (A i i) ^ 2 = ∑ i, ∑ q, (A i q) ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using offDiagNormSq_add_sum_diag_sq A

/-- The Frobenius mass is invariant under conjugation by an orthogonal matrix. -/
theorem sum_sq_conj_eq (A U : Matrix n n ℝ) (hU : Uᵀ * U = 1) :
    ∑ i, ∑ q, ((Uᵀ * A * U) i q) ^ 2 = ∑ i, ∑ q, (A i q) ^ 2 := by
  have hU' : U * Uᵀ = 1 := _root_.mul_eq_one_comm.1 hU
  have key : (Uᵀ * A * U)ᵀ * (Uᵀ * A * U) = Uᵀ * (Aᵀ * A) * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Uᵀ * (Aᵀ * U) * (Uᵀ * A * U)
        = Uᵀ * Aᵀ * (U * Uᵀ) * A * U := by noncomm_ring
      _ = Uᵀ * (Aᵀ * A) * U := by rw [hU']; noncomm_ring
  rw [← trace_transpose_mul_self, ← trace_transpose_mul_self, key, Matrix.trace_mul_cycle,
    ← Matrix.mul_assoc, hU', Matrix.one_mul]

end Frobenius

/-! ### The Jacobi rotation -/

section Jacobi

variable (A : Matrix n n ℝ) (j k : n)

/-- The tangent of the Jacobi angle: the root of `t² - 2θt - 1 = 0` of **smaller modulus**, where
`θ = (a_kk - a_jj)/(2 a_jk)`, namely `θ - √(θ²+1)` for `θ ≥ 0` and `θ + √(θ²+1)` for `θ < 0`. It
is `0` when `a_jk` already vanishes, so that the rotation is then the identity.

The two roots have product `-1`, so exactly one of them has `|t| ≤ 1`, and that is the one
[kress1998numerical] Lemma 7.13 prescribes: its `cos 2φ = 1/√(1 + tan² 2φ)` is positive, which is
`|φ| ≤ π/4`. **The choice is not a matter of numerical stability alone.** With the other root the
rotation angle lies in `(0, π/2)` and a step at a pair with `a_kk > a_jj` and `|a_jk|` small is
close to an interchange of the two coordinates, so `A_{ν+1} - A_ν` does not tend to `0` and the
iterates need not converge at all — `Matrix.abs_jacobiTan_le_one` is exactly what
`Matrix.dist_jacobiStep_le` needs. -/
noncomputable def jacobiTan : ℝ :=
  if A j k = 0 then 0
  else if 0 ≤ (A k k - A j j) / (2 * A j k) then
    (A k k - A j j) / (2 * A j k) - Real.sqrt (((A k k - A j j) / (2 * A j k)) ^ 2 + 1)
  else (A k k - A j j) / (2 * A j k) + Real.sqrt (((A k k - A j j) / (2 * A j k)) ^ 2 + 1)

/-- The cosine of the Jacobi angle. -/
noncomputable def jacobiCos : ℝ := 1 / Real.sqrt (1 + jacobiTan A j k ^ 2)

/-- The sine of the Jacobi angle. -/
noncomputable def jacobiSin : ℝ := jacobiTan A j k * jacobiCos A j k

/-- The **Jacobi rotation** of `A` in the `(j,k)`-plane: the plane rotation whose angle is chosen so
that the similarity it induces annihilates the entry `a_jk` ([kress1998numerical], Lemma 7.13). -/
noncomputable def jacobiRotation : Matrix n n ℝ :=
  planeRotation j k (jacobiCos A j k) (jacobiSin A j k)

/-- One **Jacobi step**: the orthogonal similarity of `A` by its Jacobi rotation. -/
noncomputable def jacobiStep : Matrix n n ℝ :=
  (jacobiRotation A j k)ᵀ * A * jacobiRotation A j k

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine and sine are the cosine and the sine of an angle: `c² + s² = 1`. -/
theorem jacobiCos_sq_add_jacobiSin_sq : jacobiCos A j k ^ 2 + jacobiSin A j k ^ 2 = 1 := by
  have hpos : (0 : ℝ) < 1 + jacobiTan A j k ^ 2 := by positivity
  have hsq : Real.sqrt (1 + jacobiTan A j k ^ 2) ^ 2 = 1 + jacobiTan A j k ^ 2 :=
    Real.sq_sqrt hpos.le
  have hne : Real.sqrt (1 + jacobiTan A j k ^ 2) ≠ 0 := by positivity
  rw [jacobiSin, jacobiCos]
  field_simp
  linarith [hsq]

omit [Fintype n] [DecidableEq n] in
/-- The defining quadratic `t² = 2θ t + 1` of the Jacobi tangent. -/
theorem jacobiTan_sq (h : A j k ≠ 0) :
    jacobiTan A j k ^ 2
      = 2 * ((A k k - A j j) / (2 * A j k)) * jacobiTan A j k + 1 := by
  have hnn : (0 : ℝ) ≤ ((A k k - A j j) / (2 * A j k)) ^ 2 + 1 := by positivity
  have hsq := Real.sq_sqrt hnn
  simp only [jacobiTan, h, ite_false]
  split_ifs <;> nlinarith [hsq]

omit [Fintype n] [DecidableEq n] in
/-- **The Jacobi angle is at most `π/4`**: the root of smaller modulus has `|t| ≤ 1`. This is what
keeps a Jacobi step close to the identity when the annihilated entry is small, and hence what makes
the classical method converge as a sequence of matrices and not merely in off-diagonal mass. -/
theorem abs_jacobiTan_le_one : |jacobiTan A j k| ≤ 1 := by
  rw [jacobiTan]
  split_ifs with h hθ
  · simp
  · set θ := (A k k - A j j) / (2 * A j k) with hθdef
    have hnn : (0 : ℝ) ≤ θ ^ 2 + 1 := by positivity
    have hsq := Real.sq_sqrt hnn
    have hle : θ ≤ Real.sqrt (θ ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq]
    have hge : Real.sqrt (θ ^ 2 + 1) ≤ θ + 1 := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq, hθ]
    rw [abs_le]
    constructor <;> linarith
  · set θ := (A k k - A j j) / (2 * A j k) with hθdef
    have hθ' : θ < 0 := lt_of_not_ge hθ
    have hnn : (0 : ℝ) ≤ θ ^ 2 + 1 := by positivity
    have hsq := Real.sq_sqrt hnn
    have hle : -θ ≤ Real.sqrt (θ ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq]
    have hge : Real.sqrt (θ ^ 2 + 1) ≤ 1 - θ := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq, hθ']
    rw [abs_le]
    constructor <;> linarith

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi tangent annihilates the off-diagonal entry. -/
theorem jacobiTan_annihilate :
    (1 - jacobiTan A j k ^ 2) * A j k + jacobiTan A j k * (A k k - A j j) = 0 := by
  by_cases h : A j k = 0
  · simp [jacobiTan, h]
  · have ht := jacobiTan_sq A j k h
    have hθ : A k k - A j j = 2 * ((A k k - A j j) / (2 * A j k)) * A j k := by
      field_simp
    rw [hθ]
    linear_combination (-(A j k)) * ht

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi angle annihilates the off-diagonal entry: this is the equation `b_jk = 0`. -/
theorem jacobi_annihilate :
    (jacobiCos A j k ^ 2 - jacobiSin A j k ^ 2) * A j k
      + jacobiCos A j k * jacobiSin A j k * (A k k - A j j) = 0 := by
  have h := jacobiTan_annihilate A j k
  rw [jacobiSin]
  linear_combination (jacobiCos A j k ^ 2) * h

/-- A Jacobi rotation is orthogonal, so a Jacobi step is an orthogonal similarity. -/
theorem transpose_jacobiRotation_mul_self (hjk : j ≠ k) :
    (jacobiRotation A j k)ᵀ * jacobiRotation A j k = 1 :=
  transpose_planeRotation_mul_self hjk (jacobiCos_sq_add_jacobiSin_sq A j k)

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine is positive. -/
theorem jacobiCos_pos : 0 < jacobiCos A j k := by
  have h : (0 : ℝ) < 1 + jacobiTan A j k ^ 2 := by positivity
  rw [jacobiCos]
  positivity

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine is at most one. -/
theorem jacobiCos_le_one : jacobiCos A j k ≤ 1 := by
  nlinarith [jacobiCos_sq_add_jacobiSin_sq A j k, jacobiCos_pos A j k,
    sq_nonneg (jacobiSin A j k)]

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi sine is at most one in modulus. -/
theorem abs_jacobiSin_le_one : |jacobiSin A j k| ≤ 1 := by
  have h := jacobiCos_sq_add_jacobiSin_sq A j k
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (jacobiCos A j k), sq_nonneg (jacobiSin A j k + 1),
    sq_nonneg (jacobiSin A j k - 1)]

end Jacobi

/-! ### One Jacobi step -/

section Step

variable {c s : ℝ} {j k : n}

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

variable (A : Matrix n n ℝ)

/-- **The Jacobi step annihilates the chosen off-diagonal entry** ([kress1998numerical], Lemma
7.13). -/
theorem jacobiStep_apply_eq_zero (hA : A.IsSymm) (hjk : j ≠ k) : jacobiStep A j k j k = 0 := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_jk hjk, hsym]
  linear_combination jacobi_annihilate A j k

/-- The `(j,j)` entry after a Jacobi step. -/
theorem jacobiStep_apply_jj (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k j j = jacobiCos A j k ^ 2 * A j j
      + 2 * (jacobiCos A j k * jacobiSin A j k) * A j k + jacobiSin A j k ^ 2 * A k k := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_jj hjk, hsym]
  ring

/-- The `(k,k)` entry after a Jacobi step. -/
theorem jacobiStep_apply_kk (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k k k = jacobiSin A j k ^ 2 * A j j
      - 2 * (jacobiCos A j k * jacobiSin A j k) * A j k + jacobiCos A j k ^ 2 * A k k := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_kk hjk, hsym]
  ring

/-- A Jacobi step leaves every diagonal entry outside the rotated plane alone. -/
theorem jacobiStep_apply_diag_of_ne (hjk : j ≠ k) {i : n} (hij : i ≠ j) (hik : i ≠ k) :
    jacobiStep A j k i i = A i i := by
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_of_ne hjk A hij hik hij hik]

omit [Fintype n] [DecidableEq n] in
/-- The algebraic core of [kress1998numerical] Lemma 7.13: a rotation that annihilates the
off-diagonal entry `w` of a symmetric two-by-two block moves exactly `2w²` of mass onto the
diagonal. -/
private theorem sq_add_sq_of_rotation {u v w : ℝ} (h1 : c ^ 2 + s ^ 2 = 1)
    (h2 : (c ^ 2 - s ^ 2) * w + c * s * (v - u) = 0) :
    (c ^ 2 * u + 2 * (c * s) * w + s ^ 2 * v) ^ 2
        + (s ^ 2 * u - 2 * (c * s) * w + c ^ 2 * v) ^ 2
      = u ^ 2 + v ^ 2 + 2 * w ^ 2 := by
  linear_combination (-2 * ((c ^ 2 - s ^ 2) * w + c * s * (v - u))) * h2
    + ((c ^ 2 + s ^ 2 + 1) * (u ^ 2 + v ^ 2 + 2 * w ^ 2)) * h1

private theorem sum_split (hjk : j ≠ k) (f : n → ℝ) :
    ∑ i, f i = f j + f k + ∑ i ∈ (Finset.univ.erase j).erase k, f i := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ j),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩), add_assoc]

/-- A Jacobi step moves exactly `2 a_jk²` of mass onto the diagonal. -/
theorem sum_diag_sq_jacobiStep (hA : A.IsSymm) (hjk : j ≠ k) :
    ∑ i, (jacobiStep A j k i i) ^ 2 = ∑ i, (A i i) ^ 2 + 2 * (A j k) ^ 2 := by
  have htail : ∑ i ∈ (Finset.univ.erase j).erase k, (jacobiStep A j k i i) ^ 2
      = ∑ i ∈ (Finset.univ.erase j).erase k, (A i i) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hik, hi'⟩ := Finset.mem_erase.1 hi
    obtain ⟨hij, -⟩ := Finset.mem_erase.1 hi'
    rw [jacobiStep_apply_diag_of_ne A hjk hij hik]
  have hpoly := sq_add_sq_of_rotation (jacobiCos_sq_add_jacobiSin_sq A j k)
    (jacobi_annihilate A j k)
  rw [sum_split hjk (fun i => (jacobiStep A j k i i) ^ 2), sum_split hjk (fun i => (A i i) ^ 2),
    htail, jacobiStep_apply_jj A hA hjk, jacobiStep_apply_kk A hA hjk]
  linarith [hpoly]

/-- **[kress1998numerical], Lemma 7.13**: a Jacobi step decreases the off-diagonal mass by exactly
twice the square of the annihilated entry. The Frobenius mass is unchanged by the orthogonal
similarity, and the two-by-two block moves `2 a_jk²` of it onto the diagonal. -/
theorem offDiagNormSq_jacobiStep (hA : A.IsSymm) (hjk : j ≠ k) :
    offDiagNormSq (jacobiStep A j k) = offDiagNormSq A - 2 * (A j k) ^ 2 := by
  have hF : ∑ i, ∑ q, ((jacobiStep A j k) i q) ^ 2 = ∑ i, ∑ q, (A i q) ^ 2 := by
    rw [jacobiStep]
    exact sum_sq_conj_eq A _ (transpose_jacobiRotation_mul_self A j k hjk)
  have h1 := offDiagNormSq_add_sum_diag_sq_real (jacobiStep A j k)
  have h2 := offDiagNormSq_add_sum_diag_sq_real A
  have hD := sum_diag_sq_jacobiStep A hA hjk
  linarith

/-- A Jacobi step preserves symmetry, being an orthogonal similarity. -/
theorem isSymm_jacobiStep {A : Matrix n n ℝ} (hA : A.IsSymm) (j k : n) :
    (jacobiStep A j k).IsSymm := by
  rw [Matrix.IsSymm, jacobiStep, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hA, ← Matrix.mul_assoc]

/-- **The `(j,j)` entry moves by `t a_jk`**: with the angle of `Matrix.jacobiTan` the diagonal entry
changes by the tangent times the annihilated entry, so by at most `|a_jk|`. -/
theorem jacobiStep_apply_jj_sub (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k j j - A j j = jacobiTan A j k * A j k := by
  have hcs := jacobiCos_sq_add_jacobiSin_sq A j k
  have hann := jacobiTan_annihilate A j k
  rw [jacobiSin] at hcs
  rw [jacobiStep_apply_jj A hA hjk, jacobiSin]
  linear_combination (A j j + jacobiTan A j k * A j k) * hcs
    + (jacobiTan A j k * jacobiCos A j k ^ 2) * hann

/-- **The `(k,k)` entry moves by `-t a_jk`**, the mirror of `Matrix.jacobiStep_apply_jj_sub`. -/
theorem jacobiStep_apply_kk_sub (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k k k - A k k = -(jacobiTan A j k * A j k) := by
  have hcs := jacobiCos_sq_add_jacobiSin_sq A j k
  have hann := jacobiTan_annihilate A j k
  rw [jacobiSin] at hcs
  rw [jacobiStep_apply_kk A hA hjk, jacobiSin]
  linear_combination (A k k - jacobiTan A j k * A j k) * hcs
    - (jacobiTan A j k * jacobiCos A j k ^ 2) * hann

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

/-- Every off-diagonal entry is at most `√(N(A))` in modulus, being one term of the sum defining
the off-diagonal mass. -/
theorem abs_le_sqrt_offDiagNormSq (A : Matrix n n ℝ) {p q : n} (hpq : p ≠ q) :
    |A p q| ≤ Real.sqrt (offDiagNormSq A) := by
  have h : (A p q) ^ 2 ≤ offDiagNormSq A := by
    rw [offDiagNormSq_real]
    calc (A p q) ^ 2 ≤ ∑ q' ∈ Finset.univ.erase p, (A p q') ^ 2 :=
          Finset.single_le_sum (f := fun q' => (A p q') ^ 2) (fun i _ => sq_nonneg _)
            (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩)
      _ ≤ ∑ i, ∑ q' ∈ Finset.univ.erase i, (A i q') ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ q' ∈ Finset.univ.erase i, (A i q') ^ 2)
            (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ p)
  calc |A p q| = Real.sqrt ((A p q) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (offDiagNormSq A) := Real.sqrt_le_sqrt h

/-- **A Jacobi step moves no entry by more than `2 √(N(A))`.** Every entry it changes is a
combination of off-diagonal entries of `A` with coefficients at most one, or the annihilated entry
times the tangent, and `Matrix.abs_jacobiTan_le_one` keeps the latter below `|a_jk|`. This is the
estimate the convergence of the *matrix* sequence rests on, and it fails for the other root of the
Jacobi quadratic. -/
theorem abs_jacobiStep_sub_le (hA : A.IsSymm) (hjk : j ≠ k) (p q : n) :
    |jacobiStep A j k p q - A p q| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
  have hnn : (0 : ℝ) ≤ Real.sqrt (offDiagNormSq A) := Real.sqrt_nonneg _
  have hc1 : jacobiCos A j k ≤ 1 := jacobiCos_le_one A j k
  have hc0 : 0 < jacobiCos A j k := jacobiCos_pos A j k
  have hs1 : |jacobiSin A j k| ≤ 1 := abs_jacobiSin_le_one A j k
  have ht1 : |jacobiTan A j k| ≤ 1 := abs_jacobiTan_le_one A j k
  have hcc : |jacobiCos A j k - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have htwo : ∀ x y u v : ℝ, |x| ≤ 1 → |y| ≤ 1 → |u| ≤ Real.sqrt (offDiagNormSq A) →
      |v| ≤ Real.sqrt (offDiagNormSq A) → |x * u + y * v| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro x y u v hx hy hu hv
    calc |x * u + y * v| ≤ |x * u| + |y * v| := abs_add_le _ _
      _ = |x| * |u| + |y| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * Real.sqrt (offDiagNormSq A) + 1 * Real.sqrt (offDiagNormSq A) :=
          add_le_add (mul_le_mul hx hu (abs_nonneg _) zero_le_one)
            (mul_le_mul hy hv (abs_nonneg _) zero_le_one)
      _ = 2 * Real.sqrt (offDiagNormSq A) := by ring
  have hone : ∀ u : ℝ, |u| ≤ Real.sqrt (offDiagNormSq A) →
      |u| ≤ 2 * Real.sqrt (offDiagNormSq A) := fun u hu => by linarith
  -- the four entries of the rotated block
  have cjj : |jacobiStep A j k j j - A j j| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [jacobiStep_apply_jj_sub A hA hjk, abs_mul]
    have h := abs_le_sqrt_offDiagNormSq A hjk
    nlinarith [abs_nonneg (jacobiTan A j k), abs_nonneg (A j k)]
  have ckk : |jacobiStep A j k k k - A k k| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [jacobiStep_apply_kk_sub A hA hjk, abs_neg, abs_mul]
    have h := abs_le_sqrt_offDiagNormSq A hjk
    nlinarith [abs_nonneg (jacobiTan A j k), abs_nonneg (A j k)]
  have cjk : |jacobiStep A j k j k - A j k| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [jacobiStep_apply_eq_zero A hA hjk, zero_sub, abs_neg]
    exact hone _ (abs_le_sqrt_offDiagNormSq A hjk)
  have ckj : |jacobiStep A j k k j - A k j| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [(isSymm_jacobiStep hA j k).apply j k, jacobiStep_apply_eq_zero A hA hjk, zero_sub,
      abs_neg, hA.apply j k]
    exact hone _ (abs_le_sqrt_offDiagNormSq A hjk)
  have cjq : ∀ q' : n, q' ≠ j → q' ≠ k →
      |jacobiStep A j k j q' - A j q'| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro q' hqj hqk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_row_j hjk A hqj hqk]
    have hexp : jacobiCos A j k * A j q' + jacobiSin A j k * A k q' - A j q'
        = (jacobiCos A j k - 1) * A j q' + jacobiSin A j k * A k q' := by ring
    rw [hexp]
    exact htwo _ _ _ _ hcc hs1 (abs_le_sqrt_offDiagNormSq A (Ne.symm hqj))
      (abs_le_sqrt_offDiagNormSq A (Ne.symm hqk))
  have ckq : ∀ q' : n, q' ≠ j → q' ≠ k →
      |jacobiStep A j k k q' - A k q'| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro q' hqj hqk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_row_k hjk A hqj hqk]
    have hexp : -jacobiSin A j k * A j q' + jacobiCos A j k * A k q' - A k q'
        = -jacobiSin A j k * A j q' + (jacobiCos A j k - 1) * A k q' := by ring
    rw [hexp]
    refine htwo _ _ _ _ ?_ hcc (abs_le_sqrt_offDiagNormSq A (Ne.symm hqj))
      (abs_le_sqrt_offDiagNormSq A (Ne.symm hqk))
    rwa [abs_neg]
  have cpj : ∀ p' : n, p' ≠ j → p' ≠ k →
      |jacobiStep A j k p' j - A p' j| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro p' hpj hpk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_col_j hjk A hpj hpk]
    have hexp : jacobiCos A j k * A p' j + jacobiSin A j k * A p' k - A p' j
        = (jacobiCos A j k - 1) * A p' j + jacobiSin A j k * A p' k := by ring
    rw [hexp]
    exact htwo _ _ _ _ hcc hs1 (abs_le_sqrt_offDiagNormSq A hpj)
      (abs_le_sqrt_offDiagNormSq A hpk)
  have cpk : ∀ p' : n, p' ≠ j → p' ≠ k →
      |jacobiStep A j k p' k - A p' k| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro p' hpj hpk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_col_k hjk A hpj hpk]
    have hexp : -jacobiSin A j k * A p' j + jacobiCos A j k * A p' k - A p' k
        = -jacobiSin A j k * A p' j + (jacobiCos A j k - 1) * A p' k := by ring
    rw [hexp]
    refine htwo _ _ _ _ ?_ hcc (abs_le_sqrt_offDiagNormSq A hpj)
      (abs_le_sqrt_offDiagNormSq A hpk)
    rwa [abs_neg]
  by_cases hpj : p = j
  · by_cases hqj : q = j
    · rw [hpj, hqj]; exact cjj
    · by_cases hqk : q = k
      · rw [hpj, hqk]; exact cjk
      · rw [hpj]; exact cjq q hqj hqk
  · by_cases hpk : p = k
    · by_cases hqj : q = j
      · rw [hpk, hqj]; exact ckj
      · by_cases hqk : q = k
        · rw [hpk, hqk]; exact ckk
        · rw [hpk]; exact ckq q hqj hqk
    · by_cases hqj : q = j
      · rw [hqj]; exact cpj p hpj hpk
      · by_cases hqk : q = k
        · rw [hqk]; exact cpk p hpj hpk
        · rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_of_ne hjk A hpj hpk hqj hqk,
            sub_self, abs_zero]
          positivity

end Step

/-! ### The classical Jacobi method -/

section ClassicalJacobi

/-- A matrix with at most one index has no off-diagonal entries, so no off-diagonal mass. This is
the degenerate case that the geometric decay below has to dispose of separately, the factor `1/(n² -
n)` being meaningless there. -/
theorem offDiagNormSq_eq_zero_of_card_le_one (h : Fintype.card n ≤ 1) (A : Matrix n n ℝ) :
    offDiagNormSq A = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun q hq => ?_
  have hcard : (Finset.univ.erase i).card = 0 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  rw [Finset.card_eq_zero] at hcard
  simp [hcard] at hq

variable [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
/-- With at least two indices there is a pair of distinct ones at which `A` attains its largest
off-diagonal modulus: the choice the classical method makes at every step. -/
theorem exists_maxOffDiagPair (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) :
    ∃ p : n × n, p.1 ≠ p.2 ∧ ∀ q : n × n, q.1 ≠ q.2 → |A q.1 q.2| ≤ |A p.1 p.2| := by
  classical
  have hnt : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne n
  have hne : (Finset.univ.filter fun p : n × n => p.1 ≠ p.2).Nonempty :=
    ⟨(a, b), by simp [hab]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _ (fun p : n × n => |A p.1 p.2|) hne
  exact ⟨p, (Finset.mem_filter.1 hp).2,
    fun q hq => hmax q (Finset.mem_filter.2 ⟨Finset.mem_univ q, hq⟩)⟩

omit [DecidableEq n] in
private theorem exists_maxOffDiagPair_aux (A : Matrix n n ℝ) :
    ∃ p : n × n, 2 ≤ Fintype.card n →
      p.1 ≠ p.2 ∧ ∀ q : n × n, q.1 ≠ q.2 → |A q.1 q.2| ≤ |A p.1 p.2| := by
  by_cases hn : 2 ≤ Fintype.card n
  · obtain ⟨p, hp⟩ := exists_maxOffDiagPair A hn
    exact ⟨p, fun _ => hp⟩
  · exact ⟨(Classical.arbitrary n, Classical.arbitrary n), fun h => absurd h hn⟩

/-- A pair of distinct indices at which `A` has a largest off-diagonal entry in absolute value. When
the index type has fewer than two elements no such pair exists and the value is junk; the two facts
about it, `Matrix.maxOffDiagPair_ne` and `Matrix.abs_le_abs_maxOffDiagPair`, both assume `2 ≤
Fintype.card n`. -/
noncomputable def maxOffDiagPair (A : Matrix n n ℝ) : n × n :=
  (exists_maxOffDiagPair_aux A).choose

omit [DecidableEq n] in
/-- The two indices of `Matrix.maxOffDiagPair` are distinct, so the pair really is off the diagonal.
-/
theorem maxOffDiagPair_ne (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) :
    (maxOffDiagPair A).1 ≠ (maxOffDiagPair A).2 :=
  ((exists_maxOffDiagPair_aux A).choose_spec hn).1

omit [DecidableEq n] in
/-- `Matrix.maxOffDiagPair` really is a maximizing pair: no off-diagonal entry has larger modulus.
-/
theorem abs_le_abs_maxOffDiagPair (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) (q : n × n)
    (hq : q.1 ≠ q.2) :
    |A q.1 q.2| ≤ |A (maxOffDiagPair A).1 (maxOffDiagPair A).2| :=
  ((exists_maxOffDiagPair_aux A).choose_spec hn).2 q hq

/-- The **classical Jacobi method**: each step annihilates a largest off-diagonal entry of the
current matrix ([kress1998numerical], Section 7.3). -/
noncomputable def classicalJacobiIterate (A : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => A
  | ν + 1 => jacobiStep (classicalJacobiIterate A ν)
      (maxOffDiagPair (classicalJacobiIterate A ν)).1
      (maxOffDiagPair (classicalJacobiIterate A ν)).2

/-- The method starts at the given matrix. -/
@[simp]
theorem classicalJacobiIterate_zero (A : Matrix n n ℝ) : classicalJacobiIterate A 0 = A := rfl

/-- One step of the classical method is a Jacobi step at a largest off-diagonal entry. -/
theorem classicalJacobiIterate_succ (A : Matrix n n ℝ) (ν : ℕ) :
    classicalJacobiIterate A (ν + 1)
      = jacobiStep (classicalJacobiIterate A ν) (maxOffDiagPair (classicalJacobiIterate A ν)).1
        (maxOffDiagPair (classicalJacobiIterate A ν)).2 := rfl

/-- Every iterate of the classical method is symmetric, each step being an orthogonal similarity. -/
theorem isSymm_classicalJacobiIterate {A : Matrix n n ℝ} (hA : A.IsSymm) :
    ∀ ν, (classicalJacobiIterate A ν).IsSymm
  | 0 => hA
  | ν + 1 => isSymm_jacobiStep (isSymm_classicalJacobiIterate hA ν) _ _

/-- The largest off-diagonal entry carries at least a fraction `1/(n² - n)` of the off-diagonal
mass, since the mass is a sum of `n² - n` terms each at most its square. -/
theorem offDiagNormSq_le_mul_sq (A : Matrix n n ℝ) {j k : n}
    (hmax : ∀ q : n × n, q.1 ≠ q.2 → |A q.1 q.2| ≤ |A j k|) :
    offDiagNormSq A ≤ ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) * (A j k) ^ 2 := by
  have hcard : (1 : ℕ) ≤ Fintype.card n := Fintype.card_pos
  have hrow : ∀ i : n, ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2
      ≤ ((Fintype.card n : ℝ) - 1) * (A j k) ^ 2 := by
    intro i
    have hle : ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2
        ≤ ∑ _q ∈ Finset.univ.erase i, (A j k) ^ 2 := by
      refine Finset.sum_le_sum fun q hq => ?_
      have h := hmax (i, q) (Ne.symm (Finset.mem_erase.1 hq).1)
      nlinarith [sq_abs (A i q), sq_abs (A j k), abs_nonneg (A i q), abs_nonneg (A j k)]
    refine hle.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub hcard, Nat.cast_one]
  rw [offDiagNormSq_real]
  refine (Finset.sum_le_sum fun i _ => hrow i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- One step of the classical method multiplies the off-diagonal mass by at most `1 - 2/(n² - n)`.
-/
theorem offDiagNormSq_jacobiStep_maxOffDiagPair_le {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ Fintype.card n) :
    offDiagNormSq (jacobiStep A (maxOffDiagPair A).1 (maxOffDiagPair A).2)
      ≤ (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) * offDiagNormSq A := by
  have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
  have hb := offDiagNormSq_le_mul_sq A (abs_le_abs_maxOffDiagPair A hn)
  rw [offDiagNormSq_jacobiStep A hA (maxOffDiagPair_ne A hn)]
  have hkey : offDiagNormSq A / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)
      ≤ (A (maxOffDiagPair A).1 (maxOffDiagPair A).2) ^ 2 := (div_le_iff₀ hd).2 (by linarith)
  have hexp : (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) * offDiagNormSq A
      = offDiagNormSq A
        - 2 * (offDiagNormSq A / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) := by
    field_simp
  rw [hexp]
  linarith

/-- **[kress1998numerical], proof of Theorem 7.14**: the off-diagonal mass of the classical Jacobi
iterates decays geometrically, `N(A_ν)² ≤ (1 - 2/(n² - n))^ν N(A)²`. -/
theorem offDiagNormSq_classicalJacobiIterate_le {A : Matrix n n ℝ} (hA : A.IsSymm) (ν : ℕ) :
    offDiagNormSq (classicalJacobiIterate A ν)
      ≤ (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) ^ ν * offDiagNormSq A := by
  rcases lt_or_ge (Fintype.card n) 2 with hn | hn
  · rw [offDiagNormSq_eq_zero_of_card_le_one (by omega),
      offDiagNormSq_eq_zero_of_card_le_one (by omega) A, mul_zero]
  · have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
    have hd : (2 : ℝ) ≤ (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
    have hρ : 0 ≤ 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) := by
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    induction ν with
    | zero => simp
    | succ ν ih =>
      rw [classicalJacobiIterate_succ, pow_succ, mul_assoc, mul_comm _ (offDiagNormSq A),
        ← mul_assoc]
      refine (offDiagNormSq_jacobiStep_maxOffDiagPair_le (isSymm_classicalJacobiIterate hA ν)
        hn).trans ?_
      calc (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n))
            * offDiagNormSq (classicalJacobiIterate A ν)
          ≤ (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n))
              * ((1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) ^ ν * offDiagNormSq A) :=
            mul_le_mul_of_nonneg_left ih hρ
        _ = _ := by ring

omit [Nonempty n] in
/-- Every Jacobi step is an orthogonal similarity, so it leaves the characteristic polynomial — and
with it the eigenvalues — alone. -/
theorem charpoly_jacobiStep (A : Matrix n n ℝ) {j k : n} (hjk : j ≠ k) :
    (jacobiStep A j k).charpoly = A.charpoly := by
  have hU : (jacobiRotation A j k)ᵀ * jacobiRotation A j k = 1 :=
    transpose_jacobiRotation_mul_self A j k hjk
  have hU' : jacobiRotation A j k * (jacobiRotation A j k)ᵀ = 1 := _root_.mul_eq_one_comm.1 hU
  rw [jacobiStep, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hU',
    Matrix.mul_one]

/-- The classical Jacobi iterates are all orthogonally similar to `A`, so they all have its
characteristic polynomial: the method moves the mass of the matrix onto the diagonal without
changing the eigenvalues. -/
theorem charpoly_classicalJacobiIterate {A : Matrix n n ℝ} (hn : 2 ≤ Fintype.card n) :
    ∀ ν, (classicalJacobiIterate A ν).charpoly = A.charpoly
  | 0 => rfl
  | ν + 1 => by
    rw [classicalJacobiIterate_succ,
      charpoly_jacobiStep _ (maxOffDiagPair_ne (classicalJacobiIterate A ν) hn)]
    exact charpoly_classicalJacobiIterate hn ν

/-- **The classical Jacobi method drives the off-diagonal mass to zero** (the first half of
[kress1998numerical], Theorem 7.14): the iterates converge to a diagonal matrix, and by
`Matrix.charpoly_classicalJacobiIterate` they all carry the characteristic polynomial of `A`. -/
theorem tendsto_offDiagNormSq_classicalJacobiIterate {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ Fintype.card n) :
    Filter.Tendsto (fun ν => offDiagNormSq (classicalJacobiIterate A ν)) Filter.atTop (nhds 0) := by
  have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
  have hρ0 : 0 ≤ 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) := by
    rw [sub_nonneg, div_le_one hd]
    nlinarith
  have hρ1 : 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) < 1 :=
    sub_lt_self _ (by positivity)
  refine squeeze_zero (fun ν => offDiagNormSq_nonneg _)
    (fun ν => offDiagNormSq_classicalJacobiIterate_le hA ν) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (offDiagNormSq A)

/-- **[kress1998numerical], Theorem 7.14**: the classical Jacobi iterates converge, and the limit is
a diagonal matrix carrying the characteristic polynomial of `A` — a diagonal matrix whose diagonal
is the multiset of eigenvalues of `A`.

[kress1998numerical] proves only that the off-diagonal mass tends to `0`
(`Matrix.tendsto_offDiagNormSq_classicalJacobiIterate`); convergence of the matrix sequence is a
separate theorem, usually attributed to Forsythe and Henrici, and is normally proved by showing
that the limit points lie in the finite set of diagonal matrices with the right spectrum. None of
that is needed here: `Matrix.abs_jacobiStep_sub_le` bounds a step by `2 √(N(A_ν))`, and
`Matrix.offDiagNormSq_classicalJacobiIterate_le` makes `N(A_ν)` decay geometrically, so the steps
are bounded by a geometric series and the sequence is Cauchy outright. -/
theorem tendsto_classicalJacobiIterate {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ Fintype.card n) :
    ∃ Λ : Matrix n n ℝ, Matrix.IsDiag Λ ∧ Matrix.charpoly Λ = A.charpoly ∧
      Filter.Tendsto (classicalJacobiIterate A) Filter.atTop (nhds Λ) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) := ⟨_, rfl⟩
  have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one hd]
    nlinarith
  have hρ1 : ρ < 1 := by
    rw [hρ]
    exact sub_lt_self _ (by positivity)
  have hr1 : Real.sqrt ρ < 1 := by
    have h := Real.sqrt_lt_sqrt hρ0 hρ1
    rwa [Real.sqrt_one] at h
  have hsp : ∀ m : ℕ, Real.sqrt (ρ ^ m) = Real.sqrt ρ ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hρ0 m), ih, pow_succ]
  have hstep : ∀ (p q : n) (ν : ℕ),
      dist (classicalJacobiIterate A ν p q) (classicalJacobiIterate A (ν + 1) p q)
        ≤ (2 * Real.sqrt (offDiagNormSq A)) * Real.sqrt ρ ^ ν := by
    intro p q ν
    rw [Real.dist_eq, abs_sub_comm, classicalJacobiIterate_succ]
    refine (abs_jacobiStep_sub_le _ (isSymm_classicalJacobiIterate hA ν)
      (maxOffDiagPair_ne _ hn) p q).trans ?_
    have hle : offDiagNormSq (classicalJacobiIterate A ν) ≤ ρ ^ ν * offDiagNormSq A := by
      rw [hρ]
      exact offDiagNormSq_classicalJacobiIterate_le hA ν
    calc 2 * Real.sqrt (offDiagNormSq (classicalJacobiIterate A ν))
        ≤ 2 * Real.sqrt (ρ ^ ν * offDiagNormSq A) := by
          have h := Real.sqrt_le_sqrt hle
          linarith
      _ = 2 * (Real.sqrt ρ ^ ν * Real.sqrt (offDiagNormSq A)) := by
          rw [Real.sqrt_mul (pow_nonneg hρ0 ν), hsp]
      _ = (2 * Real.sqrt (offDiagNormSq A)) * Real.sqrt ρ ^ ν := by ring
  have hcs : ∀ p q : n, ∃ l : ℝ,
      Filter.Tendsto (fun ν => classicalJacobiIterate A ν p q) Filter.atTop (nhds l) :=
    fun p q => cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric _ _ hr1 (hstep p q))
  choose Λ hΛ using hcs
  have htend : Filter.Tendsto (classicalJacobiIterate A) Filter.atTop (nhds (Matrix.of Λ)) :=
    tendsto_pi_nhds.2 fun p => tendsto_pi_nhds.2 fun q => hΛ p q
  refine ⟨Matrix.of Λ, ?_, ?_, htend⟩
  · have hoff : Filter.Tendsto (fun ν => offDiagNormSq (classicalJacobiIterate A ν))
        Filter.atTop (nhds (offDiagNormSq (Matrix.of Λ))) := by
      simp only [offDiagNormSq_real]
      exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun q _ => (hΛ i q).pow 2
    have hzero : offDiagNormSq (Matrix.of Λ) = 0 :=
      tendsto_nhds_unique hoff (tendsto_offDiagNormSq_classicalJacobiIterate hA hn)
    exact fun i j hij => offDiagNormSq_eq_zero_iff.1 hzero i j hij
  · refine Polynomial.funext fun x => ?_
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
    have hcont : Continuous fun M : Matrix n n ℝ => (Matrix.scalar n x - M).det :=
      (continuous_const.sub continuous_id).matrix_det
    have hdet : Filter.Tendsto
        (fun ν => (Matrix.scalar n x - classicalJacobiIterate A ν).det) Filter.atTop
        (nhds ((Matrix.scalar n x - Matrix.of Λ).det)) := by
      simpa [Function.comp_def] using (hcont.continuousAt (x := Matrix.of Λ)).tendsto.comp htend
    have hconst : ∀ ν, (Matrix.scalar n x - classicalJacobiIterate A ν).det
        = (Matrix.scalar n x - A).det := by
      intro ν
      rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, charpoly_classicalJacobiIterate hn ν]
    simp only [hconst] at hdet
    exact tendsto_nhds_unique hdet tendsto_const_nhds

end ClassicalJacobi

end Matrix
