/-
Upstreaming candidate for its first half: `Matrix.offDiagNormSq` and `Matrix.planeRotation` are
general matrix material with no numerical-analysis-specific content.
Natural home: `Mathlib.LinearAlgebra.Matrix.PlaneRotation`.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Jacobi's eigenvalue algorithm

Jacobi's method drives a real symmetric matrix towards a diagonal one by a sequence of plane
rotations, each chosen to annihilate one off-diagonal entry. The quantity it decreases is the
**off-diagonal mass** `N(A)² = ∑_{i ≠ j} |a_ij|²`, and the whole of the classical analysis is the
identity `N(UᵀAU)² = N(A)² - 2 a_jk²` for the rotation `U` that annihilates `a_jk`
(Kress, *Numerical Analysis*[^kress], Lemma 7.13), together with the observation that the largest
off-diagonal entry carries at least a fraction `1/(n² - n)` of the mass.

## Main definitions

* `Matrix.offDiagNormSq`: Kress's `N(A)²`.
* `Matrix.planeRotation`: the rotation of the `(j,k)`-plane by a given cosine and sine.
* `Matrix.jacobiRotation`, `Matrix.jacobiStep`: the rotation annihilating `a_jk`, and the
  similarity it induces.
* `Matrix.classicalJacobiIterate`: the classical method, annihilating a largest off-diagonal
  entry at each step.

## Main results

* `Matrix.offDiagNormSq_jacobiStep`: `N(UᵀAU)² = N(A)² - 2 a_jk²`.
* `Matrix.offDiagNormSq_classicalJacobiIterate_le`: the geometric decay
  `N(A_ν)² ≤ (1 - 2/(n² - n))^ν N(A)²`.
* `Matrix.tendsto_offDiagNormSq_classicalJacobiIterate`: the off-diagonal mass tends to `0`.
* `Matrix.charpoly_classicalJacobiIterate`: every iterate is orthogonally similar to `A`, so the
  eigenvalues never move.

## Implementation notes

The method is stated for **real symmetric** matrices, which is what a plane rotation with a real
angle can diagonalize: for a complex Hermitian matrix a rotation with one real parameter cannot
annihilate a complex `a_jk`, and one needs a phase as well.

The rotation angle is parametrized by its tangent `t`, the root `t = θ + √(θ²+1)` of
`t² - 2θt - 1 = 0` with `θ = (a_kk - a_jj)/(2 a_jk)`, rather than by the angle itself: the
annihilation identity is then a polynomial identity in `c` and `s`, provable by
`linear_combination`, and no trigonometry is needed. The numerically preferable root, the one of
smaller modulus, differs only in stability and not in the statements proved here.

## References

[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181,
  Springer, 1998.
-/

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The off-diagonal mass -/

section OffDiag

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **off-diagonal mass** of a matrix, `N(A)² = ∑_{i ≠ j} ‖a_ij‖²`; Kress writes it `N(A)²`.
Jacobi's method is the statement that a plane rotation annihilating `a_jk` decreases it by
exactly `2 ‖a_jk‖²`. -/
noncomputable def offDiagNormSq (A : Matrix n n 𝕜) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2

theorem offDiagNormSq_nonneg (A : Matrix n n 𝕜) : 0 ≤ offDiagNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The off-diagonal mass and the diagonal mass make up the squared Frobenius norm
`∑ i, ∑ j, ‖a_ij‖²` (Kress, *Numerical Analysis*, Lemma 7.8). -/
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
theorem trace_transpose_mul_self (A : Matrix n n ℝ) :
    (Aᵀ * A).trace = ∑ i, ∑ q, (A i q) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

theorem offDiagNormSq_real (A : Matrix n n ℝ) :
    offDiagNormSq A = ∑ i, ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2 := by
  simp [offDiagNormSq, Real.norm_eq_abs, sq_abs]

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

/-- The tangent of the Jacobi angle: the root `t = θ + √(θ² + 1)` of `t² - 2θt - 1 = 0`, where
`θ = (a_kk - a_jj)/(2 a_jk)`. It is `0` when `a_jk` already vanishes, so that the rotation is
then the identity. -/
noncomputable def jacobiTan : ℝ :=
  if A j k = 0 then 0
  else (A k k - A j j) / (2 * A j k) + Real.sqrt (((A k k - A j j) / (2 * A j k)) ^ 2 + 1)

/-- The cosine of the Jacobi angle. -/
noncomputable def jacobiCos : ℝ := 1 / Real.sqrt (1 + jacobiTan A j k ^ 2)

/-- The sine of the Jacobi angle. -/
noncomputable def jacobiSin : ℝ := jacobiTan A j k * jacobiCos A j k

/-- The **Jacobi rotation** of `A` in the `(j,k)`-plane: the plane rotation whose angle is chosen
so that the similarity it induces annihilates the entry `a_jk`
(Kress, *Numerical Analysis*, Lemma 7.13). -/
noncomputable def jacobiRotation : Matrix n n ℝ :=
  planeRotation j k (jacobiCos A j k) (jacobiSin A j k)

/-- One **Jacobi step**: the orthogonal similarity of `A` by its Jacobi rotation. -/
noncomputable def jacobiStep : Matrix n n ℝ :=
  (jacobiRotation A j k)ᵀ * A * jacobiRotation A j k

omit [Fintype n] [DecidableEq n] in
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
  nlinarith [hsq]

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

theorem transpose_jacobiRotation_mul_self (hjk : j ≠ k) :
    (jacobiRotation A j k)ᵀ * jacobiRotation A j k = 1 :=
  transpose_planeRotation_mul_self hjk (jacobiCos_sq_add_jacobiSin_sq A j k)

end Jacobi

/-! ### One Jacobi step -/

section Step

variable {c s : ℝ} {j k : n}

theorem conj_planeRotation_apply_of_ne (hjk : j ≠ k) (M : Matrix n n ℝ) {p q : n}
    (hpj : p ≠ j) (hpk : p ≠ k) (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p q = M p q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk,
    hpj, hpk, hqj, hqk]

theorem conj_planeRotation_apply_jj (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j j
      = c * (c * M j j + s * M j k) + s * (c * M k j + s * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk]
  ring

theorem conj_planeRotation_apply_kk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k k
      = -s * (-s * M j j + c * M j k) + c * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

theorem conj_planeRotation_apply_jk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j k
      = c * (-s * M j j + c * M j k) + s * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

variable (A : Matrix n n ℝ)

/-- **The Jacobi step annihilates the chosen off-diagonal entry**
(Kress, *Numerical Analysis*, Lemma 7.13). -/
theorem jacobiStep_apply_eq_zero (hA : A.IsSymm) (hjk : j ≠ k) : jacobiStep A j k j k = 0 := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_jk hjk, hsym]
  linear_combination jacobi_annihilate A j k

theorem jacobiStep_apply_jj (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k j j = jacobiCos A j k ^ 2 * A j j
      + 2 * (jacobiCos A j k * jacobiSin A j k) * A j k + jacobiSin A j k ^ 2 * A k k := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_jj hjk, hsym]
  ring

theorem jacobiStep_apply_kk (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k k k = jacobiSin A j k ^ 2 * A j j
      - 2 * (jacobiCos A j k * jacobiSin A j k) * A j k + jacobiCos A j k ^ 2 * A k k := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_kk hjk, hsym]
  ring

theorem jacobiStep_apply_diag_of_ne (hjk : j ≠ k) {i : n} (hij : i ≠ j) (hik : i ≠ k) :
    jacobiStep A j k i i = A i i := by
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_of_ne hjk A hij hik hij hik]

omit [Fintype n] [DecidableEq n] in
/-- The algebraic core of Kress's Lemma 7.13: a rotation that annihilates the off-diagonal
entry `w` of a symmetric two-by-two block moves exactly `2w²` of mass onto the diagonal. -/
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

/-- **Kress, *Numerical Analysis*, Lemma 7.13**: a Jacobi step decreases the off-diagonal mass
by exactly twice the square of the annihilated entry. The Frobenius mass is unchanged by the
orthogonal similarity, and the two-by-two block moves `2 a_jk²` of it onto the diagonal. -/
theorem offDiagNormSq_jacobiStep (hA : A.IsSymm) (hjk : j ≠ k) :
    offDiagNormSq (jacobiStep A j k) = offDiagNormSq A - 2 * (A j k) ^ 2 := by
  have hF : ∑ i, ∑ q, ((jacobiStep A j k) i q) ^ 2 = ∑ i, ∑ q, (A i q) ^ 2 := by
    rw [jacobiStep]
    exact sum_sq_conj_eq A _ (transpose_jacobiRotation_mul_self A j k hjk)
  have h1 := offDiagNormSq_add_sum_diag_sq_real (jacobiStep A j k)
  have h2 := offDiagNormSq_add_sum_diag_sq_real A
  have hD := sum_diag_sq_jacobiStep A hA hjk
  linarith

end Step

/-! ### The classical Jacobi method -/

section ClassicalJacobi

theorem isSymm_jacobiStep {A : Matrix n n ℝ} (hA : A.IsSymm) (j k : n) :
    (jacobiStep A j k).IsSymm := by
  rw [Matrix.IsSymm, jacobiStep, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hA, ← Matrix.mul_assoc]

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

/-- A pair of distinct indices at which `A` has a largest off-diagonal entry in absolute value.
When the index type has fewer than two elements no such pair exists and the value is junk; the
two facts about it, `Matrix.maxOffDiagPair_ne` and `Matrix.abs_le_abs_maxOffDiagPair`, both
assume `2 ≤ Fintype.card n`. -/
noncomputable def maxOffDiagPair (A : Matrix n n ℝ) : n × n :=
  (exists_maxOffDiagPair_aux A).choose

omit [DecidableEq n] in
theorem maxOffDiagPair_ne (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) :
    (maxOffDiagPair A).1 ≠ (maxOffDiagPair A).2 :=
  ((exists_maxOffDiagPair_aux A).choose_spec hn).1

omit [DecidableEq n] in
theorem abs_le_abs_maxOffDiagPair (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) (q : n × n)
    (hq : q.1 ≠ q.2) :
    |A q.1 q.2| ≤ |A (maxOffDiagPair A).1 (maxOffDiagPair A).2| :=
  ((exists_maxOffDiagPair_aux A).choose_spec hn).2 q hq

/-- The **classical Jacobi method**: each step annihilates a largest off-diagonal entry of the
current matrix (Kress, *Numerical Analysis*, Section 7.3). -/
noncomputable def classicalJacobiIterate (A : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => A
  | ν + 1 => jacobiStep (classicalJacobiIterate A ν)
      (maxOffDiagPair (classicalJacobiIterate A ν)).1
      (maxOffDiagPair (classicalJacobiIterate A ν)).2

@[simp]
theorem classicalJacobiIterate_zero (A : Matrix n n ℝ) : classicalJacobiIterate A 0 = A := rfl

theorem classicalJacobiIterate_succ (A : Matrix n n ℝ) (ν : ℕ) :
    classicalJacobiIterate A (ν + 1)
      = jacobiStep (classicalJacobiIterate A ν) (maxOffDiagPair (classicalJacobiIterate A ν)).1
        (maxOffDiagPair (classicalJacobiIterate A ν)).2 := rfl

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

/-- One step of the classical method multiplies the off-diagonal mass by at most
`1 - 2/(n² - n)`. -/
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

/-- **Kress, *Numerical Analysis*, proof of Theorem 7.14**: the off-diagonal mass of the classical
Jacobi iterates decays geometrically, `N(A_ν)² ≤ (1 - 2/(n² - n))^ν N(A)²`. -/
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
/-- Every Jacobi step is an orthogonal similarity, so it leaves the characteristic polynomial —
and with it the eigenvalues — alone. -/
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
Kress, *Numerical Analysis*, Theorem 7.14): the iterates converge to a diagonal matrix, and by
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

end ClassicalJacobi

end Matrix
