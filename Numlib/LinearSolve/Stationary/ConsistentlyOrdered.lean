import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.LinearSolve.Stationary.Splitting

/-!
# Consistently ordered matrices and Young's theory of SOR

The relation between the eigenvalues of the Jacobi iteration matrix `B` and those of the SOR
iteration matrix `G_ω` for a *consistently ordered* matrix (Saad[^saad-iterative] §4.2.5;
Kress[^kress] §4.2).

Write `A = D - E - F` for the splitting of `A` into its diagonal part and the negatives of its
strictly lower and strictly upper parts, and put `L = D⁻¹ E`, `U = D⁻¹ F`, so that the Jacobi
iteration matrix is `B = L + U`.  Following Kress, `A` is *consistently ordered*
(`Matrix.IsConsistentlyOrdered`) when the spectrum of the scaled matrix
`C(α) = α L + α⁻¹ U` is the same for every `α ≠ 0`.  This is the property the proofs use;
Saad's combinatorial definition — a labelling `c` of the indices with `c j = c i - 1` for every
nonzero entry below the diagonal and `c j = c i + 1` above it — implies it
(`Matrix.isConsistentlyOrdered_of_labelling`), and tridiagonal matrices are the basic example
(`Matrix.IsTridiagonal.isConsistentlyOrdered`).

The main theorem (`Matrix.IsConsistentlyOrdered.mem_spectrum_jacobi_iff_sor`) is that for `ω ≠ 0`
and `λ ≠ 0` linked to `μ` by `(λ + ω - 1)² = λ ω² μ²`, the number `μ` is an eigenvalue of `B`
exactly when `λ` is an eigenvalue of `G_ω`.  Its proof is the identity

`λ 1 - G_ω = (D - ω E)⁻¹ D ((λ + ω - 1) 1 - ω (λ L + U))`

together with `λ L + U = α (α L + α⁻¹ U)` for a square root `α` of `λ`, which turns the pencil
into a resolvent of `C(α)`.  At `ω = 1` the relation reads `λ = μ²`, whence
`ρ(G_GS) = ρ(B)²` (`Matrix.IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq`):
Gauss–Seidel converges twice as fast as Jacobi.

For a consistently ordered matrix whose Jacobi eigenvalues are *real*, the same relation gives
Young's closed formula for the SOR spectral radius
(`Matrix.IsConsistentlyOrdered.spectralRadius_sor_eq`): with `t = ω ρ(B)/2` and
`d = t² - (ω - 1)`, it is `(t + √d)²` when `d ≥ 0` and `ω - 1` when `d < 0`, which is what
`Matrix.youngRadius` computes.  Minimizing that over `0 < ω < 2` gives the optimal relaxation
parameter `ω_opt = 2/(1 + √(1 - ρ(B)²))` (`Matrix.optimalRelaxation`), where the discriminant
vanishes and the radius is `ω_opt - 1`
(`Matrix.IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor`).

Everything is stated over `ℂ`, where square roots exist; real matrices enter through
`Matrix.complexify`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
-/

namespace Matrix

open Stationary

open scoped NNReal ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Parts

variable {𝕜 : Type*} [Field 𝕜]

/-- The strictly lower part `L = D⁻¹ E` of the Jacobi iteration matrix, for the splitting
`A = D - E - F` into the diagonal part and the negatives of the strict triangular parts. -/
noncomputable def jacobiLower (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  -(diagPart A)⁻¹ * strictLower A

/-- The strictly upper part `U = D⁻¹ F` of the Jacobi iteration matrix, for the splitting
`A = D - E - F` into the diagonal part and the negatives of the strict triangular parts. -/
noncomputable def jacobiUpper (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  -(diagPart A)⁻¹ * strictUpper A

/-- The Jacobi iteration matrix is `B = L + U`. -/
theorem jacobiLower_add_jacobiUpper (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    jacobiLower A + jacobiUpper A = (jacobiSplitting A h).iterationOperator := by
  rw [jacobiSplitting_iterationOperator, jacobiLower, jacobiUpper, ← mul_add]

/-- Entries of `L`: the strictly lower triangle of `A`, scaled row by row. -/
theorem jacobiLower_apply {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i j : n) :
    jacobiLower A i j = -((A i i)⁻¹ * strictLower A i j) := by
  rw [jacobiLower, inv_diagPart h, neg_mul, neg_apply, diagonal_mul]

/-- Entries of `U`: the strictly upper triangle of `A`, scaled row by row. -/
theorem jacobiUpper_apply {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i j : n) :
    jacobiUpper A i j = -((A i i)⁻¹ * strictUpper A i j) := by
  rw [jacobiUpper, inv_diagPart h, neg_mul, neg_apply, diagonal_mul]

/-- `L` vanishes outside the strict lower triangle of the nonzero pattern of `A`. -/
theorem jacobiLower_eq_zero {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) {i j : n}
    (hji : ¬ j < i) : jacobiLower A i j = 0 := by simp [jacobiLower_apply h, hji]

/-- `U` vanishes outside the strict upper triangle of the nonzero pattern of `A`. -/
theorem jacobiUpper_eq_zero {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) {i j : n}
    (hij : ¬ i < j) : jacobiUpper A i j = 0 := by simp [jacobiUpper_apply h, hij]

/-- `D L = -E'`, where `E' = strictLower A` is the strictly lower part of `A` itself. -/
theorem diagPart_mul_jacobiLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    diagPart A * jacobiLower A = -strictLower A := by
  rw [jacobiLower, neg_mul, mul_neg, ← mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mul]

/-- `D U = -F'`, where `F' = strictUpper A` is the strictly upper part of `A` itself. -/
theorem diagPart_mul_jacobiUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    diagPart A * jacobiUpper A = -strictUpper A := by
  rw [jacobiUpper, neg_mul, mul_neg, ← mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mul]

/-- The SOR iteration matrix `(D - ω E)⁻¹ (ω F + (1 - ω) D)` as a function of the relaxation
parameter alone, so that it can be compared across values of `ω`.  It agrees with
`(Matrix.sorSplitting A h hω).iterationOperator` whenever `ω ≠ 0`
(`Matrix.sorSplitting_iterationOperator`), and at `ω = 0` it takes the junk value that the matrix
inverse supplies there. -/
noncomputable def sorIterationMatrix (A : Matrix n n 𝕜) (ω : 𝕜) : Matrix n n 𝕜 :=
  (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A)

/-- The SOR splitting has `Matrix.sorIterationMatrix` as its iteration operator. -/
theorem sorSplitting_iterationOperator_eq (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) : (sorSplitting A h hω).iterationOperator = sorIterationMatrix A ω :=
  sorSplitting_iterationOperator A h hω

end Parts

section Def

/-- Kress's definition of a *consistently ordered* matrix: the spectrum of the scaled matrix
`C(α) = α L + α⁻¹ U` does not depend on `α ≠ 0`, where `L` and `U` are the strictly lower and
strictly upper parts `Matrix.jacobiLower`, `Matrix.jacobiUpper` of the Jacobi iteration matrix
`B = L + U`.  This is the property that Young's theory uses; the combinatorial conditions of
`Matrix.isConsistentlyOrdered_of_labelling` and `Matrix.IsTridiagonal.isConsistentlyOrdered`
are sufficient for it. -/
def IsConsistentlyOrdered (A : Matrix n n ℂ) : Prop :=
  ∀ α : ℂ, α ≠ 0 →
    spectrum ℂ (α • jacobiLower A + α⁻¹ • jacobiUpper A) =
      spectrum ℂ (jacobiLower A + jacobiUpper A)

/-- Consistent ordering follows from a similarity: it is enough that `C(α)` be conjugate to
`C(1) = B` by a unit for each `α ≠ 0`. -/
theorem isConsistentlyOrdered_of_conj {A : Matrix n n ℂ}
    (h : ∀ α : ℂ, α ≠ 0 → ∃ u : (Matrix n n ℂ)ˣ,
      α • jacobiLower A + α⁻¹ • jacobiUpper A =
        (u : Matrix n n ℂ) * (jacobiLower A + jacobiUpper A) *
          ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)) :
    A.IsConsistentlyOrdered := fun α hα => by
  obtain ⟨u, hu⟩ := h α hα
  rw [hu, spectrum.units_conjugate]

/-- The diagonal matrix of a nowhere-vanishing family, as a unit. -/
private noncomputable def diagonalUnits (d : n → ℂ) (hd : ∀ i, d i ≠ 0) : (Matrix n n ℂ)ˣ where
  val := diagonal d
  inv := diagonal fun i => (d i)⁻¹
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun i => mul_inv_cancel₀ (hd i))
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun i => inv_mul_cancel₀ (hd i))

/-- Saad's combinatorial definition implies Kress's: a labelling `c` of the indices such that
`c i = c j + 1` for every nonzero entry `A i j` strictly below the diagonal and `c j = c i + 1`
for every nonzero entry strictly above it makes `A` consistently ordered, the similarity being
by the diagonal matrix `diag (α ^ c i)`. -/
theorem isConsistentlyOrdered_of_labelling {A : Matrix n n ℂ} (h : IsUnit (diagPart A))
    (c : n → ℕ) (hlow : ∀ i j, j < i → A i j ≠ 0 → c i = c j + 1)
    (hupp : ∀ i j, i < j → A i j ≠ 0 → c j = c i + 1) :
    A.IsConsistentlyOrdered := by
  refine isConsistentlyOrdered_of_conj fun α hα => ?_
  obtain ⟨u, hval, hinv⟩ : ∃ u : (Matrix n n ℂ)ˣ,
      (u : Matrix n n ℂ) = diagonal (fun i => α ^ c i) ∧
        ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = diagonal fun i => (α ^ c i)⁻¹ :=
    ⟨diagonalUnits _ fun i => pow_ne_zero (c i) hα, rfl, rfl⟩
  refine ⟨u, ?_⟩
  rw [hval, hinv, mul_assoc]
  ext i j
  rw [diagonal_mul, mul_diagonal, add_apply, add_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [jacobiLower_eq_zero h (asymm hij)]
    rcases eq_or_ne (A i j) 0 with hA | hA
    · rw [jacobiUpper_apply h, strictUpper_apply, ite_eq_left hij, hA]; ring
    · rw [hupp i j hij hA, pow_succ]
      have hpow : α ^ c i ≠ 0 := pow_ne_zero _ hα
      field_simp
      ring
  · rw [jacobiLower_eq_zero h (lt_irrefl i), jacobiUpper_eq_zero h (lt_irrefl i)]
    ring
  · rw [jacobiUpper_eq_zero h (asymm hij)]
    rcases eq_or_ne (A i j) 0 with hA | hA
    · rw [jacobiLower_apply h, strictLower_apply, ite_eq_left hij, hA]; ring
    · rw [hlow i j hij hA, pow_succ]
      have hpow : α ^ c j ≠ 0 := pow_ne_zero _ hα
      field_simp
      ring

omit [DecidableEq n] in
/-- The number of indices strictly below `i`: the labelling that makes a tridiagonal matrix
consistently ordered. -/
private def indexRank (i : n) : ℕ := (Finset.univ.filter (· < i)).card

omit [DecidableEq n] in
/-- Consecutive indices have consecutive ranks: if nothing lies strictly between `j` and `i` then
`indexRank i = indexRank j + 1`. -/
private theorem indexRank_eq_succ {i j : n} (hji : j < i) (hcov : ¬ ∃ k, j < k ∧ k < i) :
    indexRank i = indexRank j + 1 := by
  have hset : Finset.univ.filter (· < i) = insert j (Finset.univ.filter (· < j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rcases lt_trichotomy k j with hlt | rfl | hgt
      · exact Or.inr hlt
      · exact Or.inl rfl
      · exact absurd ⟨k, hgt, hk⟩ hcov
    · rintro (rfl | hlt)
      · exact hji
      · exact hlt.trans hji
  rw [indexRank, indexRank, hset, Finset.card_insert_of_notMem (by simp)]

/-- A tridiagonal matrix with invertible diagonal is consistently ordered: the number of indices
below `i` is a labelling in the sense of `Matrix.isConsistentlyOrdered_of_labelling`, because a
nonzero off-diagonal entry of a tridiagonal matrix joins two neighbouring indices. -/
theorem IsTridiagonal.isConsistentlyOrdered {A : Matrix n n ℂ} (h : IsUnit (diagPart A))
    (hA : A.IsTridiagonal) : A.IsConsistentlyOrdered := by
  refine isConsistentlyOrdered_of_labelling h indexRank (fun i j hji hA' => ?_)
    fun i j hij hA' => ?_
  · exact indexRank_eq_succ hji fun hk => hA' (hA i j (Or.inl hk))
  · exact indexRank_eq_succ hij fun hk => hA' (hA i j (Or.inr hk))

end Def

section Blocks

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The block sign matrix `diag (1, -1)`, as a unit; conjugating by it turns a block
anti-diagonal matrix into its negative. -/
private def blockSignUnits : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ where
  val := fromBlocks 1 0 0 (-1)
  inv := fromBlocks 1 0 0 (-1)
  val_inv := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]
  inv_val := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]

/-- Saad's Proposition 4.12: the spectrum of a block anti-diagonal matrix is symmetric about the
origin.  Conjugating by `diag (1, -1)` turns such a matrix into its negative. -/
theorem neg_mem_spectrum_fromBlocks_zero_zero (B₁₂ : Matrix p q ℂ) (B₂₁ : Matrix q p ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (fromBlocks 0 B₁₂ B₂₁ 0)) :
    -μ ∈ spectrum ℂ (fromBlocks 0 B₁₂ B₂₁ 0) := by
  obtain ⟨u, hval, hinv⟩ : ∃ u : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ,
      (u : Matrix (p ⊕ q) (p ⊕ q) ℂ) = fromBlocks 1 0 0 (-1) ∧
        ((u⁻¹ : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ) : Matrix (p ⊕ q) (p ⊕ q) ℂ) =
          fromBlocks 1 0 0 (-1) :=
    ⟨blockSignUnits, rfl, rfl⟩
  have hconj : (u : Matrix (p ⊕ q) (p ⊕ q) ℂ) * fromBlocks 0 B₁₂ B₂₁ 0 *
      ((u⁻¹ : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ) : Matrix (p ⊕ q) (p ⊕ q) ℂ) =
      -fromBlocks 0 B₁₂ B₂₁ 0 := by
    rw [hval, hinv, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
    simp
  have hspec : spectrum ℂ (-fromBlocks 0 B₁₂ B₂₁ (0 : Matrix q q ℂ)) =
      spectrum ℂ (fromBlocks 0 B₁₂ B₂₁ 0) := by
    rw [← hconj, spectrum.units_conjugate]
  rw [← Set.mem_neg, spectrum.neg_eq, hspec]
  exact hμ

end Blocks

section SOR

omit [LinearOrder n] in
/-- Multiplication by a nonzero scalar does not affect invertibility. -/
private theorem isUnit_smul_iff {c : ℂ} (hc : c ≠ 0) (M : Matrix n n ℂ) :
    IsUnit (c • M) ↔ IsUnit M := by
  have hc' : IsUnit (algebraMap ℂ (Matrix n n ℂ) c) := (isUnit_iff_ne_zero.mpr hc).map _
  have hsm : c • M = algebraMap ℂ (Matrix n n ℂ) c * M := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [hsm, ← hc'.unit_spec, Units.isUnit_units_mul]

/-- `D + ω L'` is a unit, being `ω` times the `M` factor of the SOR splitting. -/
private theorem isUnit_diagPart_add_smul_strictLower {A : Matrix n n ℂ} (h : IsUnit (diagPart A))
    {ω : ℂ} (hω : ω ≠ 0) : IsUnit (diagPart A + ω • strictLower A) := by
  have hm : diagPart A + ω • strictLower A = ω • (sorSplitting A h hω).m := by
    change _ = ω • (ω⁻¹ • diagPart A + strictLower A)
    rw [smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
  rw [hm, isUnit_smul_iff hω]
  exact (sorSplitting A h hω).isUnit

/-- The pencil identity behind Young's theory: `λ 1 - G_ω` is `(D - ω E)⁻¹ D` times the pencil
`(λ + ω - 1) 1 - ω (λ L + U)`, in which the parameter `λ` appears only in front of `L`. -/
theorem smul_one_sub_sor_iterationOperator (A : Matrix n n ℂ) (h : IsUnit (diagPart A)) {ω : ℂ}
    (hω : ω ≠ 0) (l : ℂ) :
    l • (1 : Matrix n n ℂ) - (sorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictLower A)⁻¹ * diagPart A *
        ((l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A)) := by
  have hM := isUnit_diagPart_add_smul_strictLower h hω
  have hMinv : (diagPart A + ω • strictLower A)⁻¹ * (diagPart A + ω • strictLower A) = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM)
  have hinner : diagPart A *
      ((l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A)) =
      l • (diagPart A + ω • strictLower A) - ((1 - ω) • diagPart A - ω • strictUpper A) := by
    rw [mul_sub, mul_smul_comm, mul_one, mul_smul_comm, mul_add, mul_smul_comm,
      diagPart_mul_jacobiLower h, diagPart_mul_jacobiUpper h]
    module
  have hexpand : (diagPart A + ω • strictLower A)⁻¹ *
      (l • (diagPart A + ω • strictLower A) - ((1 - ω) • diagPart A - ω • strictUpper A)) =
      l • (1 : Matrix n n ℂ) -
        (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) := by
    rw [mul_sub, mul_smul_comm, hMinv]
  rw [sorSplitting_iterationOperator, mul_assoc, hinner, hexpand]

/-- The eigenvalues of the SOR iteration matrix are exactly the values of `λ` at which the pencil
`(λ + ω - 1) 1 - ω (λ L + U)` becomes singular. -/
theorem mem_spectrum_sor_iff (A : Matrix n n ℂ) (h : IsUnit (diagPart A)) {ω : ℂ} (hω : ω ≠ 0)
    (l : ℂ) :
    l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator ↔
      ¬ IsUnit ((l + ω - 1) • (1 : Matrix n n ℂ) -
        ω • (l • jacobiLower A + jacobiUpper A)) := by
  have hM := isUnit_diagPart_add_smul_strictLower h hω
  have hMinv : IsUnit ((diagPart A + ω • strictLower A)⁻¹) := by
    rw [isUnit_iff_isUnit_det, det_nonsing_inv]
    exact ((isUnit_iff_isUnit_det _).mp hM).ringInverse
  have hu : IsUnit ((diagPart A + ω • strictLower A)⁻¹ * diagPart A) := hMinv.mul h
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    smul_one_sub_sor_iterationOperator A h hω l, ← hu.unit_spec, Units.isUnit_units_mul]

/-- For a consistently ordered matrix the spectrum of the Jacobi iteration matrix is symmetric
about the origin: the case `α = -1` of consistent ordering says that `B` and `-B` have the same
spectrum. -/
theorem IsConsistentlyOrdered.neg_mem_spectrum_jacobi_iff {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) {μ : ℂ} :
    -μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator ↔
      μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator := by
  have hneg : ((-1 : ℂ) • jacobiLower A + (-1 : ℂ)⁻¹ • jacobiUpper A) =
      -(jacobiLower A + jacobiUpper A) := by
    rw [inv_neg, inv_one]; module
  have hspec := hA (-1) (by norm_num)
  rw [hneg] at hspec
  rw [← jacobiLower_add_jacobiUpper A h, ← Set.mem_neg, spectrum.neg_eq, hspec]

/-- **Young's eigenvalue relation** (Saad, *Iterative Methods*, Thm 4.16; Kress,
*Numerical Analysis*, (4.8)): for a consistently ordered matrix, `ω ≠ 0` and `λ ≠ 0` bound to `μ`
by `(λ + ω - 1)² = λ ω² μ²`, the number `μ` is an eigenvalue of the Jacobi iteration matrix `B`
if and only if `λ` is an eigenvalue of the SOR iteration matrix `G_ω`. -/
theorem IsConsistentlyOrdered.mem_spectrum_jacobi_iff_sor {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) {ω : ℂ} (hω : ω ≠ 0) {l μ : ℂ}
    (hl : l ≠ 0) (hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2) :
    μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator ↔
      l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator := by
  obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
  have hα : α ≠ 0 := by
    rintro rfl
    exact hl (by simpa using hα2.symm)
  have hωα : ω * α ≠ 0 := mul_ne_zero hω hα
  set ν : ℂ := (l + ω - 1) / (ω * α) with hν
  have e1 : ω * α * ν = l + ω - 1 := by rw [hν]; field_simp
  have e2 : ω * α * α = ω * l := by rw [mul_assoc, ← sq, hα2]
  have e3 : ω * α * α⁻¹ = ω := by field_simp
  have hmat : (l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A) =
      (ω * α) • (ν • (1 : Matrix n n ℂ) - (α • jacobiLower A + α⁻¹ • jacobiUpper A)) := by
    have hl' : (l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A) =
        (l + ω - 1) • (1 : Matrix n n ℂ) - (ω * l) • jacobiLower A - ω • jacobiUpper A := by
      module
    have hr' : (ω * α) • (ν • (1 : Matrix n n ℂ) - (α • jacobiLower A + α⁻¹ • jacobiUpper A)) =
        (ω * α * ν) • (1 : Matrix n n ℂ) - (ω * α * α) • jacobiLower A -
          (ω * α * α⁻¹) • jacobiUpper A := by
      module
    rw [hl', hr', e1, e2, e3]
  have hkey : l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator ↔
      ν ∈ spectrum ℂ (α • jacobiLower A + α⁻¹ • jacobiUpper A) := by
    rw [mem_spectrum_sor_iff A h hω l, hmat, isUnit_smul_iff hωα, spectrum.mem_iff,
      Algebra.algebraMap_eq_smul_one]
  rw [hkey, hA α hα, jacobiLower_add_jacobiUpper A h]
  have hν2 : ν ^ 2 = μ ^ 2 := by
    rw [hν, div_pow, mul_pow, hα2, hrel]
    field_simp
  have hsq : (ν - μ) * (ν + μ) = 0 := by linear_combination hν2
  rcases mul_eq_zero.mp hsq with hz | hz
  · rw [sub_eq_zero] at hz; rw [hz]
  · rw [eq_neg_of_add_eq_zero_left hz, hA.neg_mem_spectrum_jacobi_iff h]

/-- **Gauss–Seidel converges twice as fast as Jacobi** (Kress, *Numerical Analysis*, Cor 4.16):
for a consistently ordered matrix the spectral radius of the Gauss–Seidel iteration matrix is the
square of that of the Jacobi iteration matrix.  This is the case `ω = 1` of
`Matrix.IsConsistentlyOrdered.mem_spectrum_jacobi_iff_sor`, where the eigenvalue relation reads
`λ = μ²`. -/
theorem IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator =
      spectralRadius ℂ (jacobiSplitting A h).iterationOperator ^ 2 := by
  have hgs : gaussSeidelSplitting A h = sorSplitting A h (one_ne_zero (α := ℂ)) :=
    (sorSplitting_one A h).symm
  have hB2 : spectralRadius ℂ (jacobiSplitting A h).iterationOperator ^ 2 =
      ⨆ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, ((‖μ‖₊ : ℝ≥0∞) ^ 2) :=
    ENNReal.iSup₂_pow_of_ne_zero _ two_ne_zero
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun l hl => ?_
    rcases eq_or_ne l 0 with rfl | hl0
    · simp
    · obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
      have hmem : μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator := by
        rw [hA.mem_spectrum_jacobi_iff_sor h one_ne_zero hl0 (by rw [hμ]; ring), ← hgs]
        exact hl
      rw [hB2]
      refine le_iSup₂_of_le μ hmem ?_
      rw [← hμ]
      simp
  · rw [hB2]
    refine iSup₂_le fun μ hμ => ?_
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp
    · have hl0 : μ ^ 2 ≠ 0 := pow_ne_zero _ hμ0
      have hmem : μ ^ 2 ∈ spectrum ℂ (gaussSeidelSplitting A h).iterationOperator := by
        rw [hgs, ← hA.mem_spectrum_jacobi_iff_sor h one_ne_zero hl0 (by ring)]
        exact hμ
      refine le_iSup₂_of_le (μ ^ 2) hmem ?_
      simp

end SOR

section Young

/-- The modulus of the dominant root of Young's quadratic `(λ + ω - 1)² = λ ω² μ²`, as a function
of the relaxation parameter `ω` and of the modulus `r` of the Jacobi eigenvalue `μ`.

Writing `t = ω r / 2` and `d = t² - (ω - 1)`, the two roots are `(t ± √d)²` when `d ≥ 0` and a
conjugate pair of modulus `ω - 1` when `d < 0`.  Since `Real.sqrt` of a negative number is `0`,
the maximum below is `(t + √d)²` in the first case and `ω - 1` in the second, so it covers both:
see `Matrix.youngRadius_of_le` and `Matrix.youngRadius_of_lt`. -/
noncomputable def youngRadius (ω r : ℝ) : ℝ :=
  max ((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2) (ω - 1)

/-- When the discriminant is nonnegative the two roots of Young's quadratic are real and the
larger one is `(ω r/2 + √((ω r/2)² - (ω - 1)))²`. -/
theorem youngRadius_of_le {ω r : ℝ} (ht : 0 ≤ ω * r) (h : ω - 1 ≤ (ω * r / 2) ^ 2) :
    youngRadius ω r = (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 := by
  refine max_eq_left ?_
  have hd : 0 ≤ (ω * r / 2) ^ 2 - (ω - 1) := by linarith
  have hs := Real.sq_sqrt hd
  nlinarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1)), ht]

/-- When the discriminant is negative the two roots of Young's quadratic are a conjugate pair of
modulus `ω - 1`. -/
theorem youngRadius_of_lt {ω r : ℝ} (h : (ω * r / 2) ^ 2 < ω - 1) : youngRadius ω r = ω - 1 := by
  rw [youngRadius, Real.sqrt_eq_zero_of_nonpos (by linarith), add_zero]
  exact max_eq_right h.le

/-- Young's radius is nonnegative: the first branch of the maximum is a square. -/
theorem youngRadius_nonneg {ω r : ℝ} : 0 ≤ youngRadius ω r :=
  le_max_of_le_left (sq_nonneg _)

/-- Young's radius is nondecreasing in the modulus of the Jacobi eigenvalue: a larger Jacobi
eigenvalue gives a larger SOR eigenvalue. -/
theorem youngRadius_mono {ω : ℝ} (hω : 0 ≤ ω) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    youngRadius ω r₁ ≤ youngRadius ω r₂ := by
  refine max_le_max ?_ le_rfl
  have h1 : 0 ≤ ω * r₁ / 2 := by positivity
  have h2 : ω * r₁ / 2 ≤ ω * r₂ / 2 := by
    have := mul_le_mul_of_nonneg_left h hω
    linarith
  have hsq : (ω * r₁ / 2) ^ 2 - (ω - 1) ≤ (ω * r₂ / 2) ^ 2 - (ω - 1) := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  nlinarith [Real.sqrt_nonneg ((ω * r₁ / 2) ^ 2 - (ω - 1)),
    Real.sqrt_nonneg ((ω * r₂ / 2) ^ 2 - (ω - 1))]

/-- **The modulus bound of Young's quadratic.**  Any root `λ` of `(λ + ω - 1)² = λ (2t)²` has
modulus at most `max ((t + √(t² - (ω - 1)))², ω - 1)`.  Writing `λ = z²` and choosing the sign of
`z` so that `λ + ω - 1 = 2 t z`, the number `w = z - t` satisfies `w² = t² - (ω - 1)`; its real
part is bounded by `√(t² - (ω-1))` when that is real, and vanishes when it is not. -/
private theorem norm_le_young_aux {ω t : ℝ} (ht : 0 ≤ t) {l : ℂ}
    (hrel : (l + (ω : ℂ) - 1) ^ 2 = l * (2 * (t : ℂ)) ^ 2) :
    ‖l‖ ≤ max ((t + Real.sqrt (t ^ 2 - (ω - 1))) ^ 2) (ω - 1) := by
  obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
  obtain ⟨z, hz2, hzrel⟩ : ∃ z : ℂ, z ^ 2 = l ∧ l + (ω : ℂ) - 1 = 2 * t * z := by
    have hfac : (l + (ω : ℂ) - 1 - 2 * t * z₀) * (l + (ω : ℂ) - 1 + 2 * t * z₀) = 0 := by
      linear_combination hrel - 4 * (t : ℂ) ^ 2 * hz₀
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact ⟨z₀, hz₀, by linear_combination hc⟩
    · exact ⟨-z₀, by linear_combination hz₀, by linear_combination hc⟩
  have hw2 : (z - (t : ℂ)) ^ 2 = ((t ^ 2 - (ω - 1) : ℝ) : ℂ) := by
    push_cast
    linear_combination hz2 + hzrel
  have hwnorm : ‖z - (t : ℂ)‖ ^ 2 = |t ^ 2 - (ω - 1)| := by
    rw [← norm_pow, hw2, Complex.norm_real, Real.norm_eq_abs]
  have hwre : (z - (t : ℂ)).re ^ 2 - (z - (t : ℂ)).im ^ 2 = t ^ 2 - (ω - 1) := by
    have hre := congrArg Complex.re hw2
    simpa [pow_two, Complex.mul_re] using hre
  have hwim : (z - (t : ℂ)).re * (z - (t : ℂ)).im = 0 := by
    have him := congrArg Complex.im hw2
    simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at him
    linarith
  have hsum : (z - (t : ℂ)).re ^ 2 + (z - (t : ℂ)).im ^ 2 = |t ^ 2 - (ω - 1)| := by
    rw [← hwnorm, Complex.sq_norm, Complex.normSq_apply]; ring
  have hznorm : ‖z‖ ^ 2 = t ^ 2 + 2 * t * (z - (t : ℂ)).re + |t ^ 2 - (ω - 1)| := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] at hsum ⊢
    nlinarith [hsum]
  have hlz : ‖l‖ = ‖z‖ ^ 2 := by rw [← hz2, norm_pow]
  rcases le_or_gt 0 (t ^ 2 - (ω - 1)) with hdpos | hdneg
  · refine le_trans (le_of_eq hlz) (le_max_of_le_left ?_)
    have habs : |t ^ 2 - (ω - 1)| = t ^ 2 - (ω - 1) := abs_of_nonneg hdpos
    have hsq := Real.sq_sqrt hdpos
    have hre2 : (z - (t : ℂ)).re ^ 2 ≤ t ^ 2 - (ω - 1) := by
      nlinarith [sq_nonneg (z - (t : ℂ)).im, hsum, habs]
    have hrele : (z - (t : ℂ)).re ≤ Real.sqrt (t ^ 2 - (ω - 1)) := by
      nlinarith [Real.sqrt_nonneg (t ^ 2 - (ω - 1)),
        sq_nonneg ((z - (t : ℂ)).re - Real.sqrt (t ^ 2 - (ω - 1))),
        sq_nonneg ((z - (t : ℂ)).re + Real.sqrt (t ^ 2 - (ω - 1)))]
    rw [hznorm, habs]
    nlinarith [Real.sqrt_nonneg (t ^ 2 - (ω - 1))]
  · refine le_trans (le_of_eq hlz) (le_max_of_le_right ?_)
    have hre0 : (z - (t : ℂ)).re = 0 := by
      rcases mul_eq_zero.mp hwim with hc | hc
      · exact hc
      · nlinarith [sq_nonneg (z - (t : ℂ)).re]
    rw [hznorm, hre0, abs_of_neg hdneg]
    linarith

/-- The square of a real complex number is the square of its modulus. -/
private theorem sq_eq_sq_norm_of_im_eq_zero {μ : ℂ} (h : μ.im = 0) :
    μ ^ 2 = ((‖μ‖ : ℝ) : ℂ) ^ 2 := by
  have hre : μ = ((μ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
  have hnorm : ‖μ‖ = |μ.re| := by
    conv_lhs => rw [hre]
    rw [Complex.norm_real, Real.norm_eq_abs]
  conv_lhs => rw [hre]
  rw [hnorm, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]

/-- Any eigenvalue `λ` of the SOR iteration matrix attached by Young's relation to a *real*
Jacobi eigenvalue `μ` of modulus at most `r` satisfies `‖λ‖ ≤ youngRadius ω r`. -/
theorem norm_le_youngRadius {ω r : ℝ} (hω : 0 ≤ ω) {l μ : ℂ} (hμim : μ.im = 0) (hμ : ‖μ‖ ≤ r)
    (hrel : (l + (ω : ℂ) - 1) ^ 2 = l * (ω : ℂ) ^ 2 * μ ^ 2) :
    ‖l‖ ≤ youngRadius ω r := by
  have hμsq : μ ^ 2 = ((‖μ‖ : ℝ) : ℂ) ^ 2 := sq_eq_sq_norm_of_im_eq_zero hμim
  have ht : 0 ≤ ω * ‖μ‖ / 2 := by positivity
  have hrel' : (l + (ω : ℂ) - 1) ^ 2 = l * (2 * ((ω * ‖μ‖ / 2 : ℝ) : ℂ)) ^ 2 := by
    rw [hrel, hμsq]
    push_cast
    ring
  refine le_trans (norm_le_young_aux ht hrel') ?_
  have hmono := youngRadius_mono hω (norm_nonneg μ) hμ
  rw [youngRadius] at hmono
  exact hmono

/-- **Young's radius is attained.**  For every `ω ≥ 0` and `r ≥ 0` there is a root `λ` of
`(λ + ω - 1)² = λ ω² r²` with `‖λ‖ = youngRadius ω r`. -/
theorem exists_norm_eq_youngRadius {ω r : ℝ} (hω : 0 ≤ ω) (hr : 0 ≤ r) :
    ∃ l : ℂ, (l + (ω : ℂ) - 1) ^ 2 = l * (ω : ℂ) ^ 2 * ((r : ℝ) : ℂ) ^ 2 ∧
      ‖l‖ = youngRadius ω r := by
  have ht : 0 ≤ ω * r := mul_nonneg hω hr
  have h2t : ω * r = 2 * (ω * r / 2) := by ring
  rcases le_or_gt (ω - 1) ((ω * r / 2) ^ 2) with hcase | hcase
  · have hd : 0 ≤ (ω * r / 2) ^ 2 - (ω - 1) := by linarith
    have hs2 := Real.sq_sqrt hd
    have hs0 := Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1))
    have hE : (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 + (ω - 1) =
        2 * (ω * r / 2) * (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) := by
      linear_combination hs2
    have hreal : ((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 + (ω - 1)) ^ 2 =
        (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 * ω ^ 2 * r ^ 2 := by
      rw [hE]
      ring
    refine ⟨(((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 : ℝ) : ℂ), ?_, ?_⟩
    · calc ((((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 : ℝ) : ℂ) + (ω : ℂ) - 1) ^ 2
          = ((((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 + (ω - 1)) ^ 2 : ℝ) : ℂ) :=
            by push_cast; ring
        _ = (((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 * ω ^ 2 * r ^ 2 : ℝ) : ℂ) :=
            by rw [hreal]
        _ = (((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 : ℝ) : ℂ) * (ω : ℂ) ^ 2 *
              ((r : ℝ) : ℂ) ^ 2 := by push_cast; ring
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        youngRadius_of_le ht hcase]
  · have hd : 0 < (ω - 1) - (ω * r / 2) ^ 2 := by linarith
    have hs2 := Real.sq_sqrt hd.le
    have hsc : ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ) ^ 2 =
        (ω : ℂ) - 1 - (((ω * r / 2 : ℝ)) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hs2]
      push_cast
      ring
    refine ⟨(((ω * r / 2 : ℝ) : ℂ) +
      Complex.I * ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ)) ^ 2, ?_, ?_⟩
    · have hE : ((((ω * r / 2 : ℝ)) : ℂ) +
          Complex.I * ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ)) ^ 2 + (ω : ℂ) - 1 =
          2 * (((ω * r / 2 : ℝ)) : ℂ) * ((((ω * r / 2 : ℝ)) : ℂ) +
            Complex.I * ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ)) := by
        linear_combination ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ) ^ 2 * Complex.I_sq -
          hsc
      rw [hE]
      push_cast
      ring
    · rw [norm_pow, Complex.sq_norm, Complex.normSq_apply, youngRadius_of_lt hcase]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero,
        zero_add, add_zero, sub_zero]
      linear_combination hs2

/-- The coercion `ℝ≥0 → ℝ≥0∞` of a norm is its `ENNReal.ofReal`; the form in which the suprema
defining a spectral radius are compared with real bounds. -/
private theorem coe_nnnorm_eq_ofReal (z : ℂ) : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

omit [LinearOrder n] in
/-- A complex square matrix on a nonempty index type has a nonempty spectrum: its characteristic
polynomial has positive degree, hence a root. -/
private theorem spectrum_nonempty [Nonempty n] (M : Matrix n n ℂ) : (spectrum ℂ M).Nonempty := by
  have hdeg : M.charpoly.degree ≠ 0 := by
    rw [Matrix.charpoly_degree_eq_dim]
    have : 0 < Fintype.card n := Fintype.card_pos
    exact_mod_cast this.ne'
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root M.charpoly hdeg
  exact ⟨μ, Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ⟩

omit [LinearOrder n] in
/-- The spectral radius of a complex matrix with nonempty spectrum is attained. -/
private theorem exists_norm_eq_spectralRadius (M : Matrix n n ℂ) (hne : (spectrum ℂ M).Nonempty) :
    ∃ μ₀ ∈ spectrum ℂ M, spectralRadius ℂ M = ENNReal.ofReal ‖μ₀‖ ∧
      ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ ‖μ₀‖ := by
  classical
  have hfin := M.finite_spectrum
  obtain ⟨μ₁, hμ₁⟩ := hne
  have hne' : hfin.toFinset.Nonempty := ⟨μ₁, hfin.mem_toFinset.mpr hμ₁⟩
  obtain ⟨μ₀, hmem₀, hsup⟩ := Finset.exists_mem_eq_sup' hne' fun μ => ‖μ‖
  have hmem₀' : μ₀ ∈ spectrum ℂ M := hfin.mem_toFinset.mp hmem₀
  have hmax : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ ‖μ₀‖ := fun μ hμ => by
    rw [← hsup]
    exact Finset.le_sup' (fun μ => ‖μ‖) (hfin.mem_toFinset.mpr hμ)
  refine ⟨μ₀, hmem₀', le_antisymm (iSup₂_le fun μ hμ => ?_)
    (le_iSup₂_of_le μ₀ hmem₀' ?_), hmax⟩
  · rw [coe_nnnorm_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal (hmax μ hμ)
  · rw [coe_nnnorm_eq_ofReal]

/-- Every nonzero eigenvalue of the SOR iteration matrix of a consistently ordered matrix comes
from an eigenvalue of the Jacobi matrix through Young's relation. -/
theorem IsConsistentlyOrdered.exists_mem_spectrum_jacobi {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) {ω : ℂ} (hω : ω ≠ 0) {l : ℂ}
    (hl : l ≠ 0) (hmem : l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator) :
    ∃ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator,
      (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2 := by
  obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
  have hα : α ≠ 0 := by
    rintro rfl
    exact hl (by simpa using hα2.symm)
  have hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * ((l + ω - 1) / (ω * α)) ^ 2 := by
    rw [div_pow, mul_pow, ← hα2]
    field_simp
  exact ⟨(l + ω - 1) / (ω * α),
    (hA.mem_spectrum_jacobi_iff_sor h hω hl hrel).mpr hmem, hrel⟩

/-- **Young's formula for the SOR spectral radius** (Kress, *Numerical Analysis*, Thm 4.15;
Saad, *Iterative Methods*, (4.47)).  For a consistently ordered matrix whose Jacobi iteration
matrix has real eigenvalues, the spectral radius of the SOR iteration matrix at a relaxation
parameter `ω > 0` is `Matrix.youngRadius ω ρ(B)`: it is `ω - 1` while the discriminant
`(ω ρ(B)/2)² - (ω - 1)` is negative and `(ω ρ(B)/2 + √((ω ρ(B)/2)² - (ω - 1)))²` otherwise.

The upper bound is `Matrix.norm_le_youngRadius` applied to the Jacobi eigenvalue attached to each
SOR eigenvalue by `Matrix.IsConsistentlyOrdered.exists_mem_spectrum_jacobi`, together with the
monotonicity of `youngRadius` in the modulus of that eigenvalue; the lower bound is
`Matrix.exists_norm_eq_youngRadius` applied to a Jacobi eigenvalue of maximal modulus. -/
theorem IsConsistentlyOrdered.spectralRadius_sor_eq {A : Matrix n n ℂ} [Nonempty n]
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0) {ω : ℝ}
    (hω : 0 < ω) :
    spectralRadius ℂ (sorIterationMatrix A (ω : ℂ)) =
      ENNReal.ofReal (youngRadius ω
        (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal) := by
  rw [← sorSplitting_iterationOperator_eq A h (Complex.ofReal_ne_zero.mpr hω.ne')]
  obtain ⟨μ₀, hμ₀, hρ, hmax⟩ :=
    exists_norm_eq_spectralRadius _ (spectrum_nonempty (jacobiSplitting A h).iterationOperator)
  have htoReal : (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal = ‖μ₀‖ := by
    rw [hρ, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [htoReal]
  refine le_antisymm (iSup₂_le fun l hl => ?_) ?_
  · rcases eq_or_ne l 0 with rfl | hl0
    · simp
    · obtain ⟨μ, hμmem, hrel⟩ :=
        hA.exists_mem_spectrum_jacobi h (Complex.ofReal_ne_zero.mpr hω.ne') hl0 hl
      rw [coe_nnnorm_eq_ofReal]
      exact ENNReal.ofReal_le_ofReal
        (norm_le_youngRadius hω.le (hreal μ hμmem) (hmax μ hμmem) hrel)
  · obtain ⟨l, hrelr, hnorm⟩ := exists_norm_eq_youngRadius hω.le (norm_nonneg μ₀)
    rcases eq_or_ne l 0 with rfl | hl0
    · rw [← hnorm]
      simp
    · have hrel : (l + (ω : ℂ) - 1) ^ 2 = l * (ω : ℂ) ^ 2 * μ₀ ^ 2 := by
        rw [hrelr, sq_eq_sq_norm_of_im_eq_zero (hreal μ₀ hμ₀)]
      have hmem : l ∈ spectrum ℂ
          (sorSplitting A h (Complex.ofReal_ne_zero.mpr hω.ne')).iterationOperator :=
        (hA.mem_spectrum_jacobi_iff_sor h (Complex.ofReal_ne_zero.mpr hω.ne') hl0 hrel).mp hμ₀
      refine le_iSup₂_of_le l hmem ?_
      rw [coe_nnnorm_eq_ofReal, hnorm]

/-- The optimal relaxation parameter `ω_opt = 2 / (1 + √(1 - r²))` of Young's theory, as a
function of the spectral radius `r` of the Jacobi iteration matrix.  It is the value of `ω` at
which the discriminant of Young's quadratic vanishes. -/
noncomputable def optimalRelaxation (r : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 - r ^ 2))

section Optimal

variable {r : ℝ}

/-- The three facts about `√(1 - r²)` that every computation with the optimal parameter needs:
its square is `1 - r²`, it is positive, and it is at most `1`. -/
private theorem sqrt_one_sub_sq_facts (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 ∧ 0 < Real.sqrt (1 - r ^ 2) ∧
      Real.sqrt (1 - r ^ 2) ≤ 1 := by
  have hpos : 0 < 1 - r ^ 2 := by nlinarith
  have hsq := Real.sq_sqrt hpos.le
  refine ⟨hsq, ?_, ?_⟩
  · exact Real.sqrt_pos.mpr hpos
  · nlinarith [Real.sqrt_nonneg (1 - r ^ 2)]

/-- The optimal relaxation parameter is at least `1`: over-relaxation never hurts. -/
theorem one_le_optimalRelaxation (hr0 : 0 ≤ r) (hr1 : r < 1) : 1 ≤ optimalRelaxation r := by
  obtain ⟨-, hq0, hq1⟩ := sqrt_one_sub_sq_facts hr0 hr1
  rw [optimalRelaxation, le_div_iff₀ (by linarith)]
  linarith

/-- The optimal relaxation parameter lies below `2`, so it is admissible for Kahan's condition. -/
theorem optimalRelaxation_lt_two (hr0 : 0 ≤ r) (hr1 : r < 1) : optimalRelaxation r < 2 := by
  obtain ⟨-, hq0, -⟩ := sqrt_one_sub_sq_facts hr0 hr1
  rw [optimalRelaxation, div_lt_iff₀ (by linarith)]
  linarith

/-- The defining property of the optimal parameter: the discriminant of Young's quadratic
vanishes there, `(ω_opt r / 2)² = ω_opt - 1`. -/
theorem sq_optimalRelaxation (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (optimalRelaxation r * r / 2) ^ 2 = optimalRelaxation r - 1 := by
  obtain ⟨hq2, hq0, -⟩ := sqrt_one_sub_sq_facts hr0 hr1
  have h1q : (0 : ℝ) < 1 + Real.sqrt (1 - r ^ 2) := by linarith
  have hA : (optimalRelaxation r * r / 2) ^ 2 = r ^ 2 / (1 + Real.sqrt (1 - r ^ 2)) ^ 2 := by
    rw [optimalRelaxation]
    field_simp
  have hB : optimalRelaxation r - 1 =
      (1 - Real.sqrt (1 - r ^ 2)) / (1 + Real.sqrt (1 - r ^ 2)) := by
    rw [optimalRelaxation]
    field_simp
    ring
  rw [hA, hB, div_eq_div_iff (by positivity) h1q.ne']
  linear_combination (1 + Real.sqrt (1 - r ^ 2)) * hq2

/-- Young's radius at the optimal parameter is `ω_opt - 1`. -/
theorem youngRadius_optimalRelaxation (hr0 : 0 ≤ r) (hr1 : r < 1) :
    youngRadius (optimalRelaxation r) r = optimalRelaxation r - 1 := by
  have hc1 := one_le_optimalRelaxation hr0 hr1
  have hsq := sq_optimalRelaxation hr0 hr1
  have hnn : 0 ≤ optimalRelaxation r * r := mul_nonneg (by linarith) hr0
  have hzero : (optimalRelaxation r * r / 2) ^ 2 - (optimalRelaxation r - 1) = 0 := by
    rw [hsq]; ring
  rw [youngRadius_of_le hnn (by linarith), hzero, Real.sqrt_zero, add_zero, hsq]

/-- **The optimal relaxation parameter minimizes Young's radius on `(0, 2)`.**  For `ω ≥ ω_opt`
the radius is `ω - 1`, which increases; for `ω ≤ ω_opt` the discriminant is nonnegative and the
dominant root `(ω r/2 + √d)²` is at least `(ω_opt r/2)² = ω_opt - 1`, because
`√d ≥ ω_opt r/2 - ω r/2` reduces to `(2 - ω_opt)(ω_opt - ω) ≥ 0`. -/
theorem youngRadius_optimalRelaxation_le (hr0 : 0 ≤ r) (hr1 : r < 1) {ω : ℝ}
    (hω0 : 0 < ω) : youngRadius (optimalRelaxation r) r ≤ youngRadius ω r := by
  have hc1 := one_le_optimalRelaxation hr0 hr1
  have hc2 := optimalRelaxation_lt_two hr0 hr1
  have hsq := sq_optimalRelaxation hr0 hr1
  have hcpos : 0 < optimalRelaxation r := by linarith
  have hr2 : optimalRelaxation r ^ 2 * r ^ 2 = 4 * (optimalRelaxation r - 1) := by
    linear_combination 4 * hsq
  rw [youngRadius_optimalRelaxation hr0 hr1]
  rcases le_or_gt ω (optimalRelaxation r) with hle | hgt
  · -- `ω ≤ ω_opt`: the discriminant is nonnegative
    have hfac : 0 ≤ (optimalRelaxation r - ω) *
        (optimalRelaxation r - (optimalRelaxation r - 1) * ω) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hid : optimalRelaxation r ^ 2 * ((ω * r / 2) ^ 2 - (ω - 1)) =
        (optimalRelaxation r - ω) *
          (optimalRelaxation r - (optimalRelaxation r - 1) * ω) := by
      linear_combination (ω ^ 2 / 4) * hr2
    have hd : 0 ≤ (ω * r / 2) ^ 2 - (ω - 1) := by nlinarith [pow_pos hcpos 2]
    rw [youngRadius_of_le (by positivity) (by linarith)]
    -- the dominant root is at least `(ω_opt r / 2)²`
    have hkey : optimalRelaxation r * r / 2 ≤
        ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) := by
      rcases le_or_gt (optimalRelaxation r * r / 2) (ω * r / 2) with h1 | h1
      · linarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1))]
      · have hpos : 0 < optimalRelaxation r * r / 2 - ω * r / 2 := by linarith
        have hfac2 : 0 ≤ (2 - optimalRelaxation r) * (optimalRelaxation r - ω) :=
          mul_nonneg (by linarith) (by linarith)
        have hid2 : optimalRelaxation r * ((ω * r / 2) ^ 2 - (ω - 1) -
            (optimalRelaxation r * r / 2 - ω * r / 2) ^ 2) =
            (2 - optimalRelaxation r) * (optimalRelaxation r - ω) := by
          linear_combination ((2 * ω - optimalRelaxation r) / 4) * hr2
        have hsqle : (optimalRelaxation r * r / 2 - ω * r / 2) ^ 2 ≤
            (ω * r / 2) ^ 2 - (ω - 1) := by nlinarith
        have hmono := Real.sqrt_le_sqrt hsqle
        rw [Real.sqrt_sq hpos.le] at hmono
        linarith
    have hnn : 0 ≤ optimalRelaxation r * r / 2 := by positivity
    nlinarith [hsq]
  · -- `ω ≥ ω_opt`: the radius is at least `ω - 1`
    exact le_trans (by linarith) (le_max_right _ _)

/-- **SOR converges for every `0 < ω < 2`** when the Jacobi spectral radius is `< 1`. -/
theorem youngRadius_lt_one (hr0 : 0 ≤ r) (hr1 : r < 1) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    youngRadius ω r < 1 := by
  rw [youngRadius, max_lt_iff]
  refine ⟨?_, by linarith⟩
  have ht0 : 0 ≤ ω * r / 2 := by positivity
  have ht : ω * r / 2 < 1 := by nlinarith
  have hdlt : (ω * r / 2) ^ 2 - (ω - 1) < (1 - ω * r / 2) ^ 2 := by nlinarith
  have hs : Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) < 1 - ω * r / 2 := by
    rcases le_or_gt ((ω * r / 2) ^ 2 - (ω - 1)) 0 with hle | hgt
    · rw [Real.sqrt_eq_zero_of_nonpos hle]; linarith
    · calc Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) < Real.sqrt ((1 - ω * r / 2) ^ 2) :=
            Real.sqrt_lt_sqrt hgt.le hdlt
        _ = 1 - ω * r / 2 := Real.sqrt_sq (by linarith)
  nlinarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1))]

end Optimal

section Matrices

variable {A : Matrix n n ℂ} [Nonempty n]

omit [LinearOrder n] [Nonempty n] in
/-- A spectral radius below `1` is finite, so its real value is below `1` too. -/
private theorem toReal_spectralRadius_lt_one {M : Matrix n n ℂ}
    (hlt : spectralRadius ℂ M < 1) : (spectralRadius ℂ M).toReal < 1 := by
  have hne : spectralRadius ℂ M ≠ ⊤ := (hlt.trans_le le_top).ne
  rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top]
  exact hlt

/-- **The optimal relaxation parameter** (Saad, *Iterative Methods*, (4.47); Kress,
*Numerical Analysis*, Thm 4.15).  For a consistently ordered matrix whose Jacobi iteration matrix
has real eigenvalues and spectral radius `< 1`, the parameter
`ω_opt = 2/(1 + √(1 - ρ(B)²))` minimizes the SOR spectral radius over `0 < ω < 2`.  The value
there is `ω_opt - 1` (`Matrix.IsConsistentlyOrdered.spectralRadius_sor_optimalRelaxation`), and
SOR converges for every `0 < ω < 2`
(`Matrix.IsConsistentlyOrdered.spectralRadius_sor_lt_one`). -/
theorem IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1) :
    IsMinOn (fun ω : ℝ => spectralRadius ℂ (sorIterationMatrix A (ω : ℂ))) (Set.Ioo 0 2)
      (optimalRelaxation
        (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal) := by
  set r := (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := toReal_spectralRadius_lt_one hlt
  have hc1 := one_le_optimalRelaxation hr0 hr1
  have hc2 := optimalRelaxation_lt_two hr0 hr1
  rw [isMinOn_iff]
  intro ω hω
  rw [hA.spectralRadius_sor_eq h hreal (by linarith : (0:ℝ) < optimalRelaxation r),
    hA.spectralRadius_sor_eq h hreal hω.1]
  exact ENNReal.ofReal_le_ofReal (youngRadius_optimalRelaxation_le hr0 hr1 hω.1)

/-- At the optimal parameter the SOR spectral radius is `ω_opt - 1`. -/
theorem IsConsistentlyOrdered.spectralRadius_sor_optimalRelaxation
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1) :
    spectralRadius ℂ (sorIterationMatrix A
        ((optimalRelaxation
          (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal : ℝ) : ℂ)) =
      ENNReal.ofReal (optimalRelaxation
        (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal - 1) := by
  set r := (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := toReal_spectralRadius_lt_one hlt
  have hc1 := one_le_optimalRelaxation hr0 hr1
  rw [hA.spectralRadius_sor_eq h hreal (by linarith : (0:ℝ) < optimalRelaxation r),
    youngRadius_optimalRelaxation hr0 hr1]

/-- SOR converges for every `0 < ω < 2` when the Jacobi spectral radius is `< 1`. -/
theorem IsConsistentlyOrdered.spectralRadius_sor_lt_one
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) : spectralRadius ℂ (sorIterationMatrix A (ω : ℂ)) < 1 := by
  set r := (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := toReal_spectralRadius_lt_one hlt
  rw [hA.spectralRadius_sor_eq h hreal hω0]
  calc ENNReal.ofReal (youngRadius ω r) < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (youngRadius_lt_one hr0 hr1 hω0 hω2)
    _ = 1 := ENNReal.ofReal_one

end Matrices

end Young

end Matrix
