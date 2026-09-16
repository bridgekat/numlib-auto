import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Eigen.Pencil
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Jordan
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Basics

/-!
# Quarteroni–Sacco–Saleri §1.7: eigenvalues and eigenvectors

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.7. An eigenvalue of `A ∈ ℂ^{n×n}` is a `μ ∈ spectrum ℂ A`, an
eigenvector a nonzero `x` with `A *ᵥ x = μ • x`, the eigenspace
`Module.End.eigenspace A.mulVecLin μ` (the kernel of `A - μ I`); the algebraic multiplicity is
`A.charpoly.rootMultiplicity μ` and the geometric one the dimension of the eigenspace. The
spectral radius of a complex matrix is `spectralRadius ℂ A`; that of a real matrix is the
backbone's `Matrix.complexSpectralRadius A = spectralRadius ℂ (complexify A)`
(`Numlib/LinearAlgebra/Matrix/Complexify`), since the real spectrum may miss the complex
eigenvalues the book counts.

## Contents

* `mem_spectrum_iff_exists_mulVec_eq_smul`, `vecMul_eq_smul_iff_conjTranspose_mulVec` — the
  definition of eigenvalue, right and left eigenvectors, the Rayleigh quotient.
* `mem_spectrum_iff_isRoot_charpoly`, `equation_1_6`, `spectrum_transpose`,
  `star_mem_spectrum_complexify_iff`, `cayleyHamilton` — the characteristic equation and its
  consequences.
* `equation_1_7`, `spectralRadius_conjTranspose`, `spectralRadius_smul`, `spectralRadius_pow`,
  `exercise_1_8` — the spectral radius and its rules, the spectral mapping theorem.
* `spectrum_of_blockTriangular`, `spectrum_of_isTriangular` — block triangular and triangular
  matrices.
* `finrank_eigenspace_eq`, `finrank_eigenspace_le_rootMultiplicity`, `IsDefective`,
  `definition_1_13` — the two multiplicities, defective matrices, invariant subspaces.

## Conventions

Matrices are `Matrix (Fin n) (Fin n) ℂ` (or `ℝ` where the book says "real entries"), and the
book's standing assumption that the order `n` is positive is the `[NeZero n]` of the statements
that need a nonempty spectrum. Mathlib's `spectrum ℂ A` is the set of `μ` with `μ I - A` not
invertible; the book's characteristic polynomial `det (A - λ I)` differs from Mathlib's
`A.charpoly = det (λ I - A)` by the sign `(-1)^n`, and the roots agree. The book's `xᴴ A x` is
`star x ⬝ᵥ (A *ᵥ x)` and its `yᴴ A` is `star y ᵥ* A`.
-/

open Finset Matrix Polynomial
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter01

variable {n : ℕ}

/-! ### Eigenvalues, eigenvectors, the Rayleigh quotient -/

/-- **§1.7, the definition.** `λ ∈ ℂ` is an *eigenvalue* of the square matrix `A` when there is
a nonnull `x ∈ ℂⁿ` with `A x = λ x`; `x` is an *eigenvector* for `λ`, and the set of eigenvalues
is the *spectrum* `σ(A)`. This is membership in Mathlib's `spectrum ℂ A` (backbone
`Matrix.mem_spectrum_iff_exists_mulVec_eq_smul`). -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ x : Fin n → ℂ, x ≠ 0 ∧ A *ᵥ x = μ • x :=
  Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ

/-- **§1.7, left eigenvectors and the Rayleigh quotient.** `y` is a *left eigenvector* of `A` for
`λ` when `yᴴ A = λ yᴴ`, which is the same as `Aᴴ y = conj λ • y`, that is, as `y` being a (right)
eigenvector of `Aᴴ` for `conj λ`; and the eigenvalue of an eigenvector `x` is recovered by the
Rayleigh quotient `λ = xᴴ A x / (xᴴ x)`. -/
theorem vecMul_eq_smul_iff_conjTranspose_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (y : Fin n → ℂ) :
    (star y ᵥ* A = μ • star y ↔ Aᴴ *ᵥ y = star μ • y) ∧
      ∀ x : Fin n → ℂ, x ≠ 0 → A *ᵥ x = μ • x → (star x ⬝ᵥ (A *ᵥ x)) / (star x ⬝ᵥ x) = μ := by
  refine ⟨?_, fun x hx hAx => ?_⟩
  · have h1 : star (Aᴴ *ᵥ y) = star y ᵥ* A := by rw [star_mulVec, conjTranspose_conjTranspose]
    have h2 : star (star μ • y) = μ • star y := by rw [star_smul, star_star]
    rw [← h1, ← h2, star_inj]
  · have h0 : star x ⬝ᵥ x ≠ 0 := by
      open scoped ComplexOrder in
      exact fun h => hx (dotProduct_star_self_eq_zero.1 h)
    rw [hAx, dotProduct_smul, smul_eq_mul, mul_div_cancel_right₀ _ h0]

/-! ### The characteristic equation -/

/-- **§1.7, the characteristic equation.** The eigenvalues of `A ∈ ℂ^{n×n}` are the solutions of
`p_A(λ) = det (A - λ I) = 0`, `p_A` the *characteristic polynomial*: `μ ∈ σ(A)` iff `μ` is a root
of Mathlib's `A.charpoly = det (λ I - A)` (`Matrix.mem_spectrum_iff_isRoot_charpoly`; the two
polynomials differ by the sign `(-1)^n`), iff `det (A - μ I) = 0`. Since `p_A` has degree `n`,
there are exactly `n` eigenvalues counted with multiplicity: `A.charpoly.natDegree = n` and
`A.charpoly.roots.card = n`. -/
theorem mem_spectrum_iff_isRoot_charpoly (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    (μ ∈ spectrum ℂ A ↔ A.charpoly.IsRoot μ) ∧ (μ ∈ spectrum ℂ A ↔ (A - μ • 1).det = 0) ∧
      A.charpoly.natDegree = n ∧ A.charpoly.roots.card = n := by
  refine ⟨Matrix.mem_spectrum_iff_isRoot_charpoly, ?_, ?_, ?_⟩
  · rw [Matrix.mem_spectrum_iff_exists_mulVec_eq_smul, ← Matrix.exists_mulVec_eq_zero_iff]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  · rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  · rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim,
      Fintype.card_fin]

/-- **(1.6).** `det A = ∏ᵢ λᵢ` and `tr A = ∑ᵢ λᵢ`, the eigenvalues counted with their algebraic
multiplicity, that is, over the multiset of roots of the characteristic polynomial
(`Matrix.det_eq_prod_roots_charpoly`, `Matrix.trace_eq_sum_roots_charpoly`); consequently a
matrix is singular iff it has a null eigenvalue (clauses 1 and 6 of `nonsingular_tfae`). -/
theorem equation_1_6 (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det = A.charpoly.roots.prod ∧ A.trace = A.charpoly.roots.sum ∧
      (¬ IsUnit A ↔ (0 : ℂ) ∈ spectrum ℂ A) :=
  ⟨det_eq_prod_roots_charpoly A, trace_eq_sum_roots_charpoly A,
    ((nonsingular_tfae A).out 1 6).not.trans not_not⟩

/-- **§1.7, the spectra of `Aᵀ` and `Aᴴ`.** Since `det (Aᵀ - λ I) = det (A - λ I)`,
`σ(Aᵀ) = σ(A)` (`Matrix.spectrum_transpose`); and `σ(Aᴴ) = conj σ(A)` (the characteristic
polynomial of `Aᴴ` has the conjugate coefficients; `spectrum.map_star`), so `λ` is an eigenvalue
of `A` iff `conj λ` is an eigenvalue of `Aᴴ`. -/
theorem spectrum_transpose (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ Aᵀ = spectrum ℂ A ∧ spectrum ℂ Aᴴ = star '' spectrum ℂ A ∧
      ∀ μ : ℂ, star μ ∈ spectrum ℂ Aᴴ ↔ μ ∈ spectrum ℂ A := by
  have h : spectrum ℂ Aᴴ = star '' spectrum ℂ A := by
    rw [← star_eq_conjTranspose, spectrum.map_star, Set.image_star]
  exact ⟨Matrix.spectrum_transpose A, h, fun μ => by rw [h, Set.image_star, Set.star_mem_star]⟩

/-- **§1.7, real matrices.** If `A` has real entries, `p_A` has real coefficients, so the complex
eigenvalues of `A` occur in conjugate pairs: `conj μ ∈ σ(A) ↔ μ ∈ σ(A)`, the spectrum being that
of the complexification (backbone `Matrix.star_mem_spectrum_complexify_iff`); and the conjugate
eigenvalues have the same algebraic multiplicity
(`Matrix.rootMultiplicity_charpoly_complexify_star`). -/
theorem star_mem_spectrum_complexify_iff (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) :
    (star μ ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℂ (complexify A)) ∧
      (complexify A).charpoly.rootMultiplicity (star μ) =
        (complexify A).charpoly.rootMultiplicity μ :=
  ⟨Matrix.star_mem_spectrum_complexify_iff A μ, rootMultiplicity_charpoly_complexify_star A μ⟩

/-- **§1.7, the Cayley–Hamilton theorem.** `p_A(A) = 0`: a matrix annihilates its own
characteristic polynomial (`Matrix.aeval_self_charpoly`). -/
theorem cayleyHamilton (A : Matrix (Fin n) (Fin n) ℂ) : aeval A A.charpoly = 0 :=
  aeval_self_charpoly A

/-! ### The spectral radius, (1.7) -/

section SpectralRadius

open scoped Matrix.Norms.L2Operator

/-- **(1.7).** The *spectral radius* `ρ(A) = max_{λ ∈ σ(A)} |λ|` is Mathlib's
`spectralRadius ℂ A = ⨆ λ ∈ σ(A), ‖λ‖₊` (in `ℝ≥0∞`); for a matrix of positive order the maximum
is attained at some eigenvalue (`spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty`) and is
finite. For a real matrix the book's `ρ(A)` is the backbone's `Matrix.complexSpectralRadius A`,
the spectral radius of the complexification, since `spectrum ℝ A` may miss the complex
eigenvalues. -/
theorem equation_1_7 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ A = ⨆ μ ∈ spectrum ℂ A, (‖μ‖₊ : ℝ≥0∞) ∧
      (∃ μ ∈ spectrum ℂ A, (‖μ‖₊ : ℝ≥0∞) = spectralRadius ℂ A) ∧ spectralRadius ℂ A ≠ ⊤ ∧
      B.complexSpectralRadius = spectralRadius ℂ (complexify B) := by
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact ⟨rfl, spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A), spectrum.spectralRadius_ne_top A,
    rfl⟩

end SpectralRadius

/-- **§1.7, `ρ(Aᴴ) = ρ(A)`.** Since `λ ∈ σ(A)` iff `conj λ ∈ σ(Aᴴ)` and `|conj λ| = |λ|`,
`ρ(Aᴴ) = ρ(A)`; also `ρ(Aᵀ) = ρ(A)`, the spectra being equal. -/
theorem spectralRadius_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ Aᴴ = spectralRadius ℂ A ∧ spectralRadius ℂ Aᵀ = spectralRadius ℂ A :=
  ⟨by rw [← star_eq_conjTranspose, spectralRadius_star],
    by rw [spectralRadius, spectralRadius, (Chapter01.spectrum_transpose A).1]⟩

/-- **§1.7, `ρ(α A) = |α| ρ(A)`** for every `α ∈ ℂ` (backbone `spectralRadius_smul`), and for a
real matrix and a real scalar with the complex spectral radius
(`Matrix.complexSpectralRadius_smul`). -/
theorem spectralRadius_smul (α : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ (α • A) = ‖α‖₊ * spectralRadius ℂ A ∧
      (c • B).complexSpectralRadius = ‖c‖₊ * B.complexSpectralRadius :=
  ⟨_root_.spectralRadius_smul α A, complexSpectralRadius_smul c B⟩

/-- **§1.7, `ρ(Aᵏ) = ρ(A)ᵏ`** for every `k ∈ ℕ` and every matrix of positive order (the spectral
mapping theorem for powers; backbone `spectralRadius_pow_of_nonempty`), for a complex and for a
real matrix. -/
theorem spectralRadius_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) :
    spectralRadius ℂ (A ^ k) = spectralRadius ℂ A ^ k ∧
      (B ^ k).complexSpectralRadius = B.complexSpectralRadius ^ k := by
  refine ⟨spectralRadius_pow_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A) k, ?_⟩
  rw [complexSpectralRadius, complexSpectralRadius, complexify_pow]
  exact spectralRadius_pow_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (complexify B)) k

/-- **Exercise 8.** If `P(A) = ∑ₖ cₖ Aᵏ` is a polynomial in the square matrix `A` of positive
order, the eigenvalues of `P(A)` are the values `P(λ)` at the eigenvalues `λ` of `A`:
`σ(P(A)) = P(σ(A))` (Mathlib's `spectrum.map_polynomial_aeval_of_nonempty`); in particular
`ρ(A²) = ρ(A)²`. -/
theorem exercise_1_8 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) (P : ℂ[X]) :
    spectrum ℂ (aeval A P) = (fun μ => P.eval μ) '' spectrum ℂ A ∧
      spectralRadius ℂ (A ^ 2) = spectralRadius ℂ A ^ 2 :=
  ⟨spectrum.map_polynomial_aeval_of_nonempty A P
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A),
    (Chapter01.spectralRadius_pow A 0 2).1⟩

/-! ### Block triangular matrices -/

/-- **§1.7, block triangular matrices.** If `A` is block upper triangular with diagonal blocks
`A₁₁, …, A_kk` — `Matrix.BlockTriangular A b` for a block map `b` into a linear order, the
diagonal blocks being `A.toSquareBlock b k` — then `p_A = p_{A₁₁} ⋯ p_{A_kk}`
(`Matrix.BlockTriangular.charpoly`), so the spectrum of `A` is the union of the spectra of the
diagonal blocks. -/
theorem spectrum_of_blockTriangular {α : Type*} [LinearOrder α] {A : Matrix (Fin n) (Fin n) ℂ}
    {b : Fin n → α} (hA : A.BlockTriangular b) :
    A.charpoly = ∏ k ∈ univ.image b, (A.toSquareBlock b k).charpoly ∧
      spectrum ℂ A = ⋃ k ∈ univ.image b, spectrum ℂ (A.toSquareBlock b k) := by
  refine ⟨hA.charpoly, Set.ext fun μ => ?_⟩
  simp only [Set.mem_iUnion, Matrix.mem_spectrum_iff_isRoot_charpoly, hA.charpoly, isRoot_prod,
    exists_prop]

/-- **§1.7, triangular matrices.** The eigenvalues of a triangular matrix are its diagonal
entries: `σ(A) = {aᵢᵢ}` for an upper or a lower triangular `A`
(`Matrix.charpoly_of_isUpperTriangular`, and its transpose). -/
theorem spectrum_of_isTriangular (U L : Matrix (Fin n) (Fin n) ℂ) :
    (U.IsUpperTriangular → spectrum ℂ U = Set.range fun i => U i i) ∧
      (L.IsLowerTriangular → spectrum ℂ L = Set.range fun i => L i i) := by
  have key : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.IsUpperTriangular →
      spectrum ℂ T = Set.range fun i => T i i := fun T hT => by
    ext μ
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_of_isUpperTriangular T hT,
      IsRoot.def, eval_prod, Finset.prod_eq_zero_iff, mem_univ, true_and, eval_sub, eval_X,
      eval_C, sub_eq_zero, Set.mem_range]
    exact exists_congr fun i => eq_comm
  refine ⟨key U, fun hL => ?_⟩
  have hLt : Lᵀ.IsUpperTriangular := fun _ _ hij => hL (OrderDual.toDual_lt_toDual.2 hij)
  rw [← Matrix.spectrum_transpose, key Lᵀ hLt]
  rfl

/-! ### Geometric and algebraic multiplicity, defective matrices -/

/-- **§1.7, the eigenspace and the geometric multiplicity.** The *eigenspace* of `λ` — the
eigenvectors for `λ` together with the null vector — is `ker (A - λ I)`
(`Module.End.eigenspace A.mulVecLin λ`, backbone `Matrix.eigenspace_mulVecLin_eq_ker`), and its
dimension, the *geometric multiplicity* of `λ`, is `n - rank (A - λ I)` (rank–nullity,
`Matrix.rank_add_finrank_ker_mulVecLin`). -/
theorem finrank_eigenspace_eq (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.eigenspace A.mulVecLin μ = LinearMap.ker (A - μ • 1).mulVecLin ∧
      Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ) = n - (A - μ • 1).rank := by
  refine ⟨eigenspace_mulVecLin_eq_ker A μ, ?_⟩
  have h := rank_add_finrank_ker_mulVecLin (A - μ • 1)
  rw [Fintype.card_fin] at h
  rw [eigenspace_mulVecLin_eq_ker]
  omega

/-- **§1.7, the two multiplicities.** The geometric multiplicity of an eigenvalue can never be
greater than its *algebraic multiplicity*, its multiplicity as a root of the characteristic
polynomial (backbone `Matrix.finrank_eigenspace_le_rootMultiplicity_charpoly`). -/
theorem finrank_eigenspace_le_rootMultiplicity (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ) ≤ A.charpoly.rootMultiplicity μ :=
  finrank_eigenspace_le_rootMultiplicity_charpoly A μ

/-- **§1.7, defective matrices.** An eigenvalue is *defective* when its geometric multiplicity is
strictly less than its algebraic one, and a matrix is *defective* when it has at least one
defective eigenvalue. -/
def IsDefective (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ μ ∈ spectrum ℂ A,
    Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ) < A.charpoly.rootMultiplicity μ

/-- **Definition 1.13.** A subspace `S ⊆ ℂⁿ` is *invariant* with respect to the square matrix `A`
when `A S ⊆ S`, that is, `S.map A.mulVecLin ≤ S`; and every eigenspace of `A` is invariant with
respect to `A`, since `A x = λ x` gives `A (A x) = λ (A x)`. -/
theorem definition_1_13 (A : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) (μ : ℂ) :
    (S.map A.mulVecLin ≤ S ↔ ∀ x ∈ S, A *ᵥ x ∈ S) ∧
      (Module.End.eigenspace A.mulVecLin μ).map A.mulVecLin ≤
        Module.End.eigenspace A.mulVecLin μ := by
  refine ⟨Submodule.map_le_iff_le_comap, Submodule.map_le_iff_le_comap.2 fun x hx => ?_⟩
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff, hx, map_smul, hx]

end QuarteroniSaccoSaleri.Chapter01
