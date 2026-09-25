import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Eigen.PowerMethod
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hamiltonian
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# Hamiltonian eigenvalue problems

Hamiltonian and symplectic eigenvalue problems ([golub2013matrix] §7.8.1): the eigenvalue
pairings, orthogonal symplectic transformations, the stable invariant subspace and the algebraic
Riccati equation.

Matrices are real, indexed by `l ⊕ l`, and `J` is Mathlib's `Matrix.J l ℝ = fromBlocks 0 (-1) 1 0`,
which is **minus** the book's `J = [0 I; -I 0]`; every notion used here is invariant under
`J ↦ -J`. The structures themselves live in `Numlib/LinearAlgebra/Matrix/Hamiltonian`
(`Matrix.IsHamiltonian`, `Matrix.IsSkewHamiltonian`, the block characterization of orthogonal
symplectic matrices); this module is the eigenvalue theory on top.

## Main results

* The eigenvalue pairings of [golub2013matrix] §7.8.1 (3)–(4): the characteristic polynomial of a
  Hamiltonian matrix is even, `χ_M(-X) = χ_M` (`Matrix.IsHamiltonian.charpoly_comp_neg`, over any
  commutative ring, so the pairing `λ ↔ -λ` holds with multiplicities), hence
  `Matrix.IsHamiltonian.neg_mem_spectrum`; the eigenvalues of a symplectic matrix pair as
  `λ ↔ λ⁻¹` (`Matrix.inv_mem_spectrum_of_mem_symplecticGroup`). Spectra of real matrices are those
  of the complexifications.
* Orthogonal symplectic transformations: `diag(P, P)` for orthogonal `P`
  (`Matrix.fromBlocks_diagonal_mem_symplecticGroup`), plane rotations in the coordinates `inl i`,
  `inr i` (`Matrix.planeRotation_inl_inr_mem_symplecticGroup`), and the
  Householder–Givens–Householder reduction of a vector to a multiple of the first coordinate vector
  (`Matrix.exists_orthogonalSymplectic_mulVec_eq`).
* **The stable invariant subspace is Lagrangian**
  (`Matrix.IsHamiltonian.isLagrangian_stable_invariant`):
  if `M X₀ = X₀ T₁` with `T₁` stable, then `X₀ᵀ J X₀ = 0`, because `W = X₀ᵀ J X₀` solves a
  Sylvester equation `T₁ᵀ W + W T₁ = 0` whose coefficients have spectra in opposite half-planes.
  This is the key lemma of the real Hamiltonian–Schur form (7.8.1), proved in the invariant-subspace
  form of Paige–Van Loan (1981) rather than the book's deflation sketch.
* **The algebraic Riccati equation** (`Matrix.riccati_of_hamiltonianSchur`, (7.8.2)): from a
  Hamiltonian–Schur decomposition with nonsingular `Q₁`, `X = Q₂ Q₁⁻¹` is symmetric, solves
  `G + X A + Aᵀ X - X F X = 0`, and `A - F X = Q₁ T Q₁⁻¹`. The symmetry of `X` comes from the
  orthogonality condition `(Q₁ᵀ Q₂)ᵀ = Q₁ᵀ Q₂`, not from `Q₁ᵀ Q₁ + Q₂ᵀ Q₂ = I` as the book says.

* **The real Hamiltonian–Schur form** (`Matrix.exists_orthogonalSymplectic_hamiltonianSchur`,
  (7.8.1)): without eigenvalues on the imaginary axis, `Qᵀ M Q = [[T, R], [0, -Tᵀ]]` with `Q`
  orthogonal symplectic and `T` quasi upper triangular with stable eigenvalues. The real stable
  invariant subspace has dimension `n`: the complexified stable and unstable spectral subspaces are
  complementary (`Krylov.isCompl_iSup_maxGenEigenspace`) and conjugation-closed, so their real
  points span `ℝ^{2n}`, and each is isotropic (the Lagrangian lemma, applied to `M` and to `-M`), so
  neither exceeds `n`. An orthonormal basis `[Q₁; -Q₂]` completes to `[[Q₁, Q₂], [-Q₂, Q₁]]`, and
  the real Schur form of the stable block (`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`),
  applied as `diag(U, U)`, finishes.

The skew-Hamiltonian Schur form and the condensed forms (7.8.3)–(7.8.4) of Paige–Van Loan and Van
Loan need the column-by-column symplectic reduction, which is planned but not yet formalized.

Nothing here is in Mathlib beyond `Matrix.J` and `Matrix.symplecticGroup`.
-/

open Polynomial

namespace Matrix

section Charpoly

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The characteristic polynomial of `-N` is `(-1)^n χ_N(-X)`. -/
theorem charpoly_neg (N : Matrix n n R) :
    (-N).charpoly = (-1) ^ Fintype.card n * N.charpoly.comp (-X) := by
  have h1 : (charmatrix N).map (fun p => p.comp (-X)) = -charmatrix (-N) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [charmatrix_apply_eq, sub_comp]
      ring
    · simp [charmatrix_apply_ne _ _ _ hij]
  have h2 : N.charpoly.comp (-X) = ((charmatrix N).map (fun p => p.comp (-X))).det := by
    rw [charpoly]
    exact RingHom.map_det (compRingHom (-X)) (charmatrix N)
  rw [h2, h1, det_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]
  rfl

end Charpoly

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- `J` as a unit, with inverse `-J`. -/
private def unitJ (R : Type*) [CommRing R] : (Matrix (l ⊕ l) (l ⊕ l) R)ˣ where
  val := J l R
  inv := -J l R
  val_inv := by rw [Matrix.mul_neg, J_squared, neg_neg]
  inv_val := by rw [Matrix.neg_mul, J_squared, neg_neg]

/-- **The eigenvalues of a Hamiltonian matrix pair as `λ, -λ`, with multiplicities**
([golub2013matrix] §7.8.1 (3)): `χ_M(-X) = χ_M`. From `Mᵀ = J M J = -(J M J⁻¹)`
(`Matrix.IsHamiltonian.transpose_mul_J_eq`), `χ_M = χ_{Mᵀ} = (-1)^{2n} χ_M(-X)`. -/
theorem IsHamiltonian.charpoly_comp_neg {R : Type*} [CommRing R]
    {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M.IsHamiltonian) : M.charpoly.comp (-X) = M.charpoly := by
  have hT := hM.transpose_mul_J_eq
  have hconj : J l R * M * J l R = -((unitJ R).val * M * (unitJ R).val⁻¹) := by
    change J l R * M * J l R = -(J l R * M * (J l R)⁻¹)
    rw [J_inv, Matrix.mul_neg, neg_neg]
  have h := charpoly_transpose M
  rw [hT, hconj, charpoly_neg, charpoly_units_conj] at h
  have h2 : ((-1 : R[X]) ^ Fintype.card (l ⊕ l)) = 1 := by
    rw [Fintype.card_sum, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [h2, one_mul] at h
  exact h

/-- [golub2013matrix] §7.8.1 (3): the spectrum of a real Hamiltonian matrix is symmetric about the
imaginary axis, `λ ∈ σ(M) → -λ ∈ σ(M)` (spectra of the complexification). -/
theorem IsHamiltonian.neg_mem_spectrum {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : M.IsHamiltonian)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ M.complexify) : -μ ∈ spectrum ℂ M.complexify := by
  rw [mem_spectrum_complexify_iff] at hμ ⊢
  set p := M.charpoly.map (algebraMap ℝ ℂ) with hpdef
  have hp : p.comp (-X) = p := by
    rw [show (-X : ℂ[X]) = (-X : ℝ[X]).map (algebraMap ℝ ℂ) by simp, hpdef,
      ← Polynomial.map_comp, hM.charpoly_comp_neg]
  rw [IsRoot, ← hp, eval_comp]
  simpa using hμ

omit [Fintype l] in
/-- `J` complexified is `J` over `ℂ`. -/
private theorem complexify_J : (J l ℝ).complexify = J l ℂ := by
  exact map_J l Complex.ofRealHom

/-- [golub2013matrix] §7.8.1 (4): the eigenvalues of a real symplectic matrix are nonzero and pair
as `λ, λ⁻¹` (spectra of the complexification): `S⁻¹ = J⁻¹ Sᵀ J` is similar to `Sᵀ`, so
`σ(S⁻¹) = σ(S)`, and `S x = λ x` gives `S⁻¹ x = λ⁻¹ x`. -/
theorem inv_mem_spectrum_of_mem_symplecticGroup {S : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hS : S ∈ symplecticGroup l ℝ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ S.complexify) :
    μ ≠ 0 ∧ μ⁻¹ ∈ spectrum ℂ S.complexify := by
  set Sc := S.complexify with hSc
  have hinv : S⁻¹ = -J l ℝ * Sᵀ * J l ℝ := SymplecticGroup.inv_eq_symplectic_inv S hS
  have hSu : IsUnit S := (isUnit_iff_isUnit_det S).2 (SymplecticGroup.symplectic_det hS)
  have hScu : IsUnit Sc := by
    rw [isUnit_iff_isUnit_det] at hSu ⊢
    rw [hSc, complexify, show S.map Complex.ofReal = Complex.ofRealHom.mapMatrix S from rfl,
      ← RingHom.map_det]
    exact hSu.map _
  have hinvc : Sc⁻¹ = (unitJ ℂ).val⁻¹ * Scᵀ * (unitJ ℂ).val := by
    change Sc⁻¹ = (J l ℂ)⁻¹ * Scᵀ * J l ℂ
    rw [J_inv, hSc, ← complexify_inv, hinv, complexify_mul, complexify_mul, complexify_neg,
      complexify_transpose, complexify_J]
  have hspec : spectrum ℂ Sc⁻¹ = spectrum ℂ Sc := by
    ext ν
    rw [mem_spectrum_iff_isRoot_charpoly, mem_spectrum_iff_isRoot_charpoly, hinvc,
      charpoly_units_conj', charpoly_transpose]
  obtain ⟨x, hx0, hx⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul Sc μ).1 hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hx
    have := congrArg (Sc⁻¹ *ᵥ ·) hx
    simp only [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hScu),
      one_mulVec, mulVec_zero] at this
    exact hx0 this
  refine ⟨hμ0, ?_⟩
  rw [← hspec, mem_spectrum_iff_exists_mulVec_eq_smul]
  refine ⟨x, hx0, ?_⟩
  have := congrArg (fun v => μ⁻¹ • (Sc⁻¹ *ᵥ v)) hx
  simp only [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hScu), one_mulVec,
    mulVec_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul] at this
  rw [← this]

/-- [golub2013matrix] §7.8.1: `diag(P, P)` for an orthogonal `P` is orthogonal symplectic (in
particular for a Householder reflector). -/
theorem fromBlocks_diagonal_mem_symplecticGroup {P : Matrix l l ℝ}
    (hP : P ∈ orthogonalGroup l ℝ) :
    fromBlocks P 0 0 P ∈ orthogonalGroup (l ⊕ l) ℝ ∧ fromBlocks P 0 0 P ∈ symplecticGroup l ℝ := by
  have hP' := (mem_orthogonalGroup_iff' l ℝ).1 hP
  have hO : fromBlocks P 0 0 P ∈ orthogonalGroup (l ⊕ l) ℝ := by
    rw [mem_orthogonalGroup_iff', fromBlocks_transpose, fromBlocks_multiply]
    simp [hP', fromBlocks_one]
  refine ⟨hO, (mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup hO).2 ?_⟩
  exact (commute_J_iff).2 ⟨P, 0, by simp⟩

/-- [golub2013matrix] §7.8.1: a plane rotation in the coordinates `inl i`, `inr i` ("a Givens
rotation that involves planes `i` and `i + n`") is orthogonal symplectic: it has the block form
`fromBlocks Q₁ Q₂ (-Q₂) Q₁`, hence commutes with `J`. -/
theorem planeRotation_inl_inr_mem_symplecticGroup (i : l) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    planeRotation (Sum.inl i) (Sum.inr i) c s ∈ orthogonalGroup (l ⊕ l) ℝ ∧
      planeRotation (Sum.inl i) (Sum.inr i) c s ∈ symplecticGroup l ℝ := by
  have hne : (Sum.inl i : l ⊕ l) ≠ Sum.inr i := Sum.inl_ne_inr
  have hO := planeRotation_mem_orthogonalGroup hne hcs
  refine ⟨hO, (mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup hO).2 ?_⟩
  refine (commute_J_iff).2 ⟨1 + (c - 1) • single i i 1, (-s) • single i i 1, ?_⟩
  ext (a | a) (b | b) <;> by_cases ha : a = i <;> by_cases hb : b = i <;>
    simp [planeRotation_apply hne, one_apply, ha, hb, @eq_comm _ i]

/-- **The stable invariant subspace of a Hamiltonian matrix is Lagrangian** (the key lemma of the
real Hamiltonian–Schur form, [golub2013matrix] §7.8.1; Paige–Van Loan 1981): if `M` is
Hamiltonian, `M X₀ = X₀ T₁` and every eigenvalue of `T₁` has negative real part, then
`X₀ᵀ J X₀ = 0`. `W = X₀ᵀ J X₀` satisfies `T₁ᵀ W + W T₁ = 0` (`J M = -Mᵀ J`), and the Sylvester
operator of `T₁ᵀ` and `-T₁` is injective because their spectra lie in opposite open
half-planes. (No independence of the columns of `X₀` is needed.) -/
theorem IsHamiltonian.isLagrangian_stable_invariant {k : Type*} [Fintype k] [DecidableEq k]
    {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : M.IsHamiltonian) {X₀ : Matrix (l ⊕ l) k ℝ}
    {T₁ : Matrix k k ℝ} (hMX : M * X₀ = X₀ * T₁)
    (hT : ∀ μ ∈ spectrum ℂ T₁.complexify, μ.re < 0) : X₀ᵀ * J l ℝ * X₀ = 0 := by
  have hJ := isHamiltonian_iff_J_mul_eq.1 hM
  set W := X₀ᵀ * J l ℝ * X₀ with hWdef
  have h1 : T₁ᵀ * W = X₀ᵀ * Mᵀ * J l ℝ * X₀ := by
    rw [hWdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, ← hMX, transpose_mul]
  have h2 : W * T₁ = -(X₀ᵀ * Mᵀ * J l ℝ * X₀) := by
    rw [hWdef, Matrix.mul_assoc, ← hMX, Matrix.mul_assoc, ← Matrix.mul_assoc (J l ℝ), hJ]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hsyl : sylvesterMap T₁ᵀ (-T₁) W = 0 := by
    rw [sylvesterMap_apply, Matrix.mul_neg, sub_neg_eq_add, h1, h2, add_neg_cancel]
  have hcop : IsCoprime T₁ᵀ.charpoly (-T₁).charpoly := by
    rw [isCoprime_charpoly_iff_disjoint_spectrum_complexify, complexify_transpose,
      complexify_neg, spectrum_transpose, ← spectrum.neg_eq, Set.disjoint_left]
    intro μ hμ hμ'
    have h3 := hT μ hμ
    have h4 := hT (-μ) (Set.mem_neg.1 hμ')
    rw [Complex.neg_re] at h4
    linarith
  exact sylvesterMap_injective_of_isCoprime hcop (hsyl.trans (map_zero _).symm)

/-- **The algebraic Riccati equation from the Hamiltonian–Schur form** ([golub2013matrix]
(7.8.2)): let `M = fromBlocks A F G (-Aᵀ)` and `Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁` orthogonal with
`Qᵀ M Q = fromBlocks T R 0 (-Tᵀ)`. If `Q₁` is nonsingular then `X = Q₂ Q₁⁻¹` is symmetric, solves
`G + X A + Aᵀ X - X F X = 0`, and `A - F X = Q₁ T Q₁⁻¹`. The first block column of
`M Q = Q (Qᵀ M Q)`
reads `M [Q₁; -Q₂] = [Q₁; -Q₂] T`, that is `M [1; -X] = [1; -X] (Q₁ T Q₁⁻¹)`; the symmetry of `X`
is that of `Q₁ᵀ Q₂ = Q₁ᵀ X Q₁` (which [golub2013matrix] attributes to `Q₁ᵀ Q₁ + Q₂ᵀ Q₂ = I`; it is
the other orthogonality condition, `Matrix.fromBlocks_mem_orthogonalGroup_iff`). -/
theorem riccati_of_hamiltonianSchur {A F G T R Q₁ Q₂ : Matrix l l ℝ}
    (hQ : fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ orthogonalGroup (l ⊕ l) ℝ)
    (hS : (fromBlocks Q₁ Q₂ (-Q₂) Q₁)ᵀ * fromBlocks A F G (-Aᵀ) * fromBlocks Q₁ Q₂ (-Q₂) Q₁ =
      fromBlocks T R 0 (-Tᵀ)) (hQ₁ : IsUnit Q₁) :
    (Q₂ * Q₁⁻¹).IsSymm ∧
      G + Q₂ * Q₁⁻¹ * A + Aᵀ * (Q₂ * Q₁⁻¹) - Q₂ * Q₁⁻¹ * F * (Q₂ * Q₁⁻¹) = 0 ∧
      A - F * (Q₂ * Q₁⁻¹) = Q₁ * T * Q₁⁻¹ := by
  have hd : IsUnit Q₁.det := (isUnit_iff_isUnit_det Q₁).1 hQ₁
  have hinv : Q₁ * Q₁⁻¹ = 1 := mul_nonsing_inv Q₁ hd
  set Q := fromBlocks Q₁ Q₂ (-Q₂) Q₁ with hQdef
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (l ⊕ l) ℝ).1 hQ
  have hMQ : fromBlocks A F G (-Aᵀ) * Q = Q * fromBlocks T R 0 (-Tᵀ) := by
    rw [← hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  rw [hQdef, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hMQ
  obtain ⟨h11, -, h21, -⟩ := hMQ
  have hsym := ((fromBlocks_mem_orthogonalGroup_iff).1 hQ).1
  set X := Q₂ * Q₁⁻¹ with hX
  have hXQ : X * Q₁ = Q₂ := by
    rw [hX, Matrix.mul_assoc, nonsing_inv_mul Q₁ hd, Matrix.mul_one]
  -- the first block row
  have h11' : A * Q₁ - F * Q₂ = Q₁ * T := by
    simpa [Matrix.mul_neg, sub_eq_add_neg] using h11
  have h21' : G * Q₁ + Aᵀ * Q₂ = -(Q₂ * T) := by
    simpa [Matrix.mul_neg, Matrix.neg_mul] using h21
  have hA : A - F * X = Q₁ * T * Q₁⁻¹ := by
    rw [hX, ← h11', Matrix.sub_mul, Matrix.mul_assoc A, hinv, Matrix.mul_one,
      Matrix.mul_assoc F]
  refine ⟨?_, ?_, hA⟩
  · -- symmetry through `Q₁ᵀ X Q₁ = Q₁ᵀ Q₂`
    have hQt : IsUnit Q₁ᵀ.det := by rwa [det_transpose]
    have h1 : Q₁ᵀ * X * Q₁ = Q₁ᵀ * Q₂ := by rw [Matrix.mul_assoc, hXQ]
    have h2 : Q₁ᵀ * Xᵀ * Q₁ = Q₁ᵀ * Q₂ := by
      have := congrArg transpose h1
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      rw [this, hsym.eq]
    have h3 : Q₁ᵀ * Xᵀ * Q₁ = Q₁ᵀ * X * Q₁ := h2.trans h1.symm
    have h4 := congrArg (fun Y => (Q₁ᵀ)⁻¹ * Y * Q₁⁻¹) h3
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hQt, Matrix.one_mul] at h4
    simp only [Matrix.mul_assoc, hinv, Matrix.mul_one] at h4
    exact h4
  · -- the second block row: `G + Aᵀ X = -X (A - F X)`
    have e1 : (G * Q₁ + Aᵀ * Q₂) * Q₁⁻¹ = G + Aᵀ * X := by
      rw [hX, Matrix.add_mul, Matrix.mul_assoc G, hinv, Matrix.mul_one,
        Matrix.mul_assoc Aᵀ Q₂]
    have e2 : -(Q₂ * T) * Q₁⁻¹ = -(X * (Q₁ * T * Q₁⁻¹)) := by
      rw [← hXQ]; simp only [Matrix.neg_mul, Matrix.mul_assoc]
    have h' : G + Aᵀ * X = -(X * (Q₁ * T * Q₁⁻¹)) := by rw [← e1, h21', e2]
    rw [← hA, Matrix.mul_sub] at h'
    have : G + X * A + Aᵀ * X - X * F * X = (G + Aᵀ * X) + (X * A - X * F * X) := by abel
    rw [this, h']
    simp only [Matrix.mul_assoc]
    abel

/-- A Householder reflector (or the identity) carries a real vector to a multiple of a coordinate
vector. -/
private theorem exists_orthogonal_mulVec_eq_smul_single (v : l → ℝ) (i : l) :
    ∃ P ∈ orthogonalGroup l ℝ, ∃ β : ℝ, P *ᵥ v = β • Pi.single i 1 := by
  by_cases hv : v = 0
  · exact ⟨1, one_mem _, 0, by simp [hv]⟩
  exact ⟨_, householder_householderVec_mem_unitaryGroup hv i, _,
    householder_mulVec_eq_smul_single hv i⟩

/-- Orthogonal symplectic matrices are closed under products. -/
private theorem mul_mem_orthoSymp {P Q : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hP : P ∈ orthogonalGroup (l ⊕ l) ℝ ∧ P ∈ symplecticGroup l ℝ)
    (hQ : Q ∈ orthogonalGroup (l ⊕ l) ℝ ∧ Q ∈ symplecticGroup l ℝ) :
    P * Q ∈ orthogonalGroup (l ⊕ l) ℝ ∧ P * Q ∈ symplecticGroup l ℝ :=
  ⟨mul_mem hP.1 hQ.1, mul_mem hP.2 hQ.2⟩

/-- The transpose of an orthogonal symplectic matrix is orthogonal symplectic. -/
private theorem transpose_mem_orthoSymp {P : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hP : P ∈ orthogonalGroup (l ⊕ l) ℝ ∧ P ∈ symplecticGroup l ℝ) :
    Pᵀ ∈ orthogonalGroup (l ⊕ l) ℝ ∧ Pᵀ ∈ symplecticGroup l ℝ := by
  refine ⟨?_, SymplecticGroup.transpose_mem hP.2⟩
  have := Unitary.star_mem hP.1
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this

/-- **Any vector is carried to a multiple of a coordinate vector by an orthogonal symplectic
matrix** ([golub2013matrix] §7.8.1, the Householder–Givens–Householder reduction): for
`x : l ⊕ l → ℝ` and any `i₀ : l` there is an orthogonal symplectic `Q` with
`Qᵀ x = ‖x‖₂ e_{inl i₀}`. `diag(P₁, P₁)` reduces the bottom half to a multiple of `e_{i₀}`, a plane
rotation in the coordinates `inl i₀`, `inr i₀` (`Matrix.planeRotation_inl_inr_mem_symplecticGroup`)
moves it to the top, `diag(P₂, P₂)` reduces the top half, and `diag(±1, ±1)` fixes the sign; the
norm is preserved. -/
theorem exists_orthogonalSymplectic_mulVec_eq (x : l ⊕ l → ℝ) (i₀ : l) :
    ∃ Q : Matrix (l ⊕ l) (l ⊕ l) ℝ, Q ∈ orthogonalGroup (l ⊕ l) ℝ ∧ Q ∈ symplecticGroup l ℝ ∧
      Qᵀ *ᵥ x = ‖WithLp.toLp 2 x‖ • Pi.single (Sum.inl i₀) 1 := by
  -- step 1: the bottom half
  obtain ⟨P₁, hP₁, β, hβ⟩ := exists_orthogonal_mulVec_eq_smul_single (x ∘ Sum.inr) i₀
  set D₁ := fromBlocks P₁ 0 0 P₁
  have hD₁ := fromBlocks_diagonal_mem_symplecticGroup hP₁
  set y := D₁ *ᵥ x with hy
  have hy1 : y ∘ Sum.inr = β • Pi.single i₀ 1 := by
    rw [hy, fromBlocks_mulVec]; simp [hβ]
  -- step 2: the rotation
  have hne : (Sum.inl i₀ : l ⊕ l) ≠ Sum.inr i₀ := Sum.inl_ne_inr
  obtain ⟨hGk, -, hGq⟩ := transpose_planeRotation_givensPair_mulVec hne y
  have hG := planeRotation_inl_inr_mem_symplecticGroup i₀
    (givensPair_sq_add_sq (y (Sum.inl i₀)) (y (Sum.inr i₀)))
  set G := planeRotation (Sum.inl i₀) (Sum.inr i₀) (givensPair (y (Sum.inl i₀)) (y (Sum.inr i₀))).1
    (givensPair (y (Sum.inl i₀)) (y (Sum.inr i₀))).2
  set z := Gᵀ *ᵥ y with hz
  have hz2 : z ∘ Sum.inr = 0 := by
    ext j
    by_cases hj : j = i₀
    · subst hj; exact hGk
    · simp only [Function.comp_apply, Pi.zero_apply]
      rw [hGq (Sum.inr j) (by simp) (by simpa using hj)]
      have := congrFun hy1 j
      simp only [Function.comp_apply, Pi.smul_apply, Pi.single_apply, hj, ite_false,
        smul_zero] at this
      exact this
  -- step 3: the top half
  obtain ⟨P₂, hP₂, γ, hγ⟩ := exists_orthogonal_mulVec_eq_smul_single (z ∘ Sum.inl) i₀
  set D₂ := fromBlocks P₂ 0 0 P₂
  have hD₂ := fromBlocks_diagonal_mem_symplecticGroup hP₂
  have hw : D₂ *ᵥ z = γ • Pi.single (Sum.inl i₀) 1 := by
    rw [fromBlocks_mulVec, hz2, hγ]
    ext (j | j) <;> simp [Pi.single_apply]
  -- the composite and its norm
  set Q₀ := D₂ * Gᵀ * D₁
  have hQ₀ := mul_mem_orthoSymp (mul_mem_orthoSymp hD₂ (transpose_mem_orthoSymp hG)) hD₁
  have hQx : Q₀ *ᵥ x = γ • Pi.single (Sum.inl i₀) 1 := by
    rw [← hw, hz, hy, mulVec_mulVec, mulVec_mulVec]
  have hnorm : ‖WithLp.toLp 2 x‖ = |γ| := by
    have h1 := norm_toEuclideanLin_apply_of_mem_unitaryGroup hQ₀.1 (WithLp.toLp 2 x)
    rw [toEuclideanLin_apply, WithLp.ofLp_toLp, hQx] at h1
    rw [← h1, EuclideanSpace.norm_eq]
    simp [Pi.single_apply, Real.sqrt_sq_eq_abs]
  -- the sign
  set σ : ℝ := if 0 ≤ γ then 1 else -1
  have hσ : σ ^ 2 = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσγ : σ * γ = |γ| := by
    simp only [σ]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hP₃ : σ • (1 : Matrix l l ℝ) ∈ orthogonalGroup l ℝ := by
    rw [mem_orthogonalGroup_iff', transpose_smul, transpose_one, smul_mul_smul_comm,
      Matrix.one_mul, ← sq, hσ, one_smul]
  have hD₃ := fromBlocks_diagonal_mem_symplecticGroup hP₃
  refine ⟨(fromBlocks (σ • 1) 0 0 (σ • 1) * Q₀)ᵀ, (transpose_mem_orthoSymp
    (mul_mem_orthoSymp hD₃ hQ₀)).1, (transpose_mem_orthoSymp (mul_mem_orthoSymp hD₃ hQ₀)).2, ?_⟩
  have hD3e : fromBlocks (σ • (1 : Matrix l l ℝ)) 0 0 (σ • 1) *ᵥ
      (Pi.single (Sum.inl i₀) (1 : ℝ) : l ⊕ l → ℝ) =
      σ • (Pi.single (Sum.inl i₀) 1 : l ⊕ l → ℝ) := by
    rw [fromBlocks_mulVec]
    ext (j | j) <;> simp [Pi.single_apply, smul_mulVec]
  rw [transpose_transpose, ← mulVec_mulVec, hQx, mulVec_smul, hD3e, smul_smul, hnorm, ← hσγ,
    mul_comm γ σ]

/-! ### The real Hamiltonian–Schur form -/

section StableSubspace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complexification of a real vector. -/
private def cplx (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

/-- The sum of the generalized eigenspaces of a real matrix (acting on `ℂ^ι`) for the eigenvalues
satisfying `P`. -/
private noncomputable def specSub (M : Matrix ι ι ℝ) (P : ℂ → Prop) : Submodule ℂ (ι → ℂ) :=
  ⨆ μ, ⨆ _ : P μ, Module.End.maxGenEigenspace (toLin' M.complexify) μ

private theorem isCompl_specSub (M : Matrix ι ι ℝ) (P : ℂ → Prop) :
    IsCompl (specSub M P) (specSub M fun μ => ¬ P μ) :=
  Krylov.isCompl_iSup_maxGenEigenspace _ P

/-- Complex conjugation of the generalized eigenspaces of a real matrix. -/
private theorem star_mem_maxGenEigenspace {M : Matrix ι ι ℝ} {μ : ℂ} {v : ι → ℂ}
    (hv : v ∈ Module.End.maxGenEigenspace (toLin' M.complexify) μ) :
    star v ∈ Module.End.maxGenEigenspace (toLin' M.complexify) (star μ) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  have hstep : ∀ w : ι → ℂ, (toLin' M.complexify - star μ • (1 : Module.End ℂ (ι → ℂ))) (star w)
      = star ((toLin' M.complexify - μ • (1 : Module.End ℂ (ι → ℂ))) w) := by
    intro w
    ext i
    simp [complexify, mulVec, dotProduct, mul_comm]
  have hpow : ∀ j (w : ι → ℂ), ((toLin' M.complexify - star μ • (1 : Module.End ℂ (ι → ℂ))) ^ j)
      (star w) = star (((toLin' M.complexify - μ • (1 : Module.End ℂ (ι → ℂ))) ^ j) w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, hstep, pow_succ', Module.End.mul_apply]
  rw [hpow, hk, star_zero]

/-- A conjugation-closed predicate gives a conjugation-closed subspace. -/
private theorem star_mem_specSub {M : Matrix ι ι ℝ} {P : ℂ → Prop}
    (hP : ∀ μ, P μ → P (star μ)) {v : ι → ℂ} (hv : v ∈ specSub M P) : star v ∈ specSub M P := by
  set S : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | star w ∈ specSub M P}
      add_mem' := fun ha hb => by simpa [star_add] using add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c w hw => by
        simpa [star_smul] using Submodule.smul_mem _ (star c) hw }
  have hle : specSub M P ≤ S := by
    refine iSup₂_le fun μ hμ w hw => ?_
    exact Submodule.mem_iSup_of_mem (star μ) (Submodule.mem_iSup_of_mem (hP μ hμ)
      (star_mem_maxGenEigenspace hw))
  exact hle hv

/-- The spectral subspaces are invariant. -/
private theorem mulVec_mem_specSub {M : Matrix ι ι ℝ} {P : ℂ → Prop} {v : ι → ℂ}
    (hv : v ∈ specSub M P) : M.complexify *ᵥ v ∈ specSub M P := by
  set f := toLin' M.complexify
  have hle : specSub M P ≤ (specSub M P).comap f := by
    refine iSup₂_le fun μ hμ w hw => ?_
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hw))
  simpa [f] using hle hv

/-- A real vector splits into real parts of the two complementary spectral subspaces, when both
predicates are conjugation-closed. -/
private theorem exists_real_split (M : Matrix ι ι ℝ) {P : ℂ → Prop}
    (hP : ∀ μ, P μ ↔ P (star μ)) (x : ι → ℝ) :
    ∃ u w : ι → ℝ, x = u + w ∧ cplx u ∈ specSub M P ∧ cplx w ∈ specSub M fun μ => ¬ P μ := by
  have hc := isCompl_specSub M P
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1
    (hc.codisjoint.eq_top ▸ Submodule.mem_top : cplx x ∈ specSub M P ⊔ _)
  have hsa := star_mem_specSub (fun μ h => (hP μ).1 h) ha
  have hsb := star_mem_specSub (fun μ h => (hP μ).not.1 h) hb
  have hsx : star (cplx x) = cplx x := by ext i; simp [cplx]
  have hab' : star a + star b = cplx x := by rw [← star_add, hab, hsx]
  -- uniqueness of the decomposition
  have hdiff : a - star a ∈ specSub M P ⊓ specSub M fun μ => ¬ P μ := by
    refine ⟨sub_mem ha hsa, ?_⟩
    have : a - star a = star b - b := by
      have := hab.trans hab'.symm
      linear_combination this
    rw [this]; exact sub_mem hsb hb
  rw [hc.disjoint.eq_bot, Submodule.mem_bot, sub_eq_zero] at hdiff
  have hreal : ∀ i, a i = ((a i).re : ℂ) := fun i => by
    have := congrFun hdiff i
    exact (Complex.conj_eq_iff_re.1 (by simpa using this.symm)).symm
  have hb' : b = cplx x - a := by rw [← hab]; abel
  refine ⟨fun i => (a i).re, fun i => x i - (a i).re, by ext i; simp, ?_, ?_⟩
  · have : cplx (fun i => (a i).re) = a := by ext i; exact (hreal i).symm
    rw [this]; exact ha
  · have : cplx (fun i => x i - (a i).re) = b := by
      ext i; rw [hb']; simp [cplx, ← hreal i]
    rw [this]; exact hb

/-- Complexification commutes with products of rectangular matrices. -/
private theorem map_ofReal_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- `cplx` as a real linear map. -/
private def cplxLin : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) where
  toFun := cplx
  map_add' x y := by ext i; simp [cplx]
  map_smul' c x := by ext i; simp [cplx, Complex.real_smul]

omit [DecidableEq ι] in
private theorem cplx_mulVec (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    cplx (M *ᵥ x) = M.complexify *ᵥ cplx x := by
  ext i; simp [cplx, complexify, mulVec, dotProduct]

omit [DecidableEq ι] in
/-- An invariant real subspace has a matrix of orthonormal columns spanning it, on which the
matrix acts through its compression `X₀ᵀ M X₀`. -/
private theorem exists_orthonormal_cols (M : Matrix ι ι ℝ) (X : Submodule ℝ (ι → ℝ))
    (hinv : ∀ x ∈ X, M *ᵥ x ∈ X) {d : ℕ} (hd : Module.finrank ℝ X = d) :
    ∃ X₀ : Matrix ι (Fin d) ℝ, X₀ᵀ * X₀ = 1 ∧ M * X₀ = X₀ * (X₀ᵀ * M * X₀) ∧
      ∀ j, (fun r => X₀ r j) ∈ X := by
  set e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  set XE := X.map (e : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι)
  have hdE : Module.finrank ℝ XE = d := (LinearEquiv.finrank_map_eq e X).trans hd
  set b := (stdOrthonormalBasis ℝ XE).reindex (finCongr hdE)
  set X₀ : Matrix ι (Fin d) ℝ := of fun r j => WithLp.ofLp ((b j : XE) : EuclideanSpace ℝ ι) r
    with hX₀
  have hmemE : ∀ y : ι → ℝ, y ∈ X ↔ e y ∈ XE := fun y =>
    ⟨fun h => Submodule.mem_map_of_mem h, fun h => by
      obtain ⟨z, hz, hze⟩ := Submodule.mem_map.1 h
      rw [← e.injective hze]; exact hz⟩
  have hcol : ∀ j, (fun r => X₀ r j) ∈ X := fun j => by
    rw [hmemE]
    exact (b j).2
  have horth : X₀ᵀ * X₀ = 1 := by
    ext i j
    have h := orthonormal_iff_ite.1 b.orthonormal i j
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    simp only [transpose_apply, mul_apply, hX₀, of_apply, one_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [mul_comm]
  refine ⟨X₀, horth, ?_, hcol⟩
  · -- every vector of `X` is a combination of the columns
    have hspan : ∀ y ∈ X, ∃ c : Fin d → ℝ, y = X₀ *ᵥ c := by
      intro y hy
      refine ⟨fun i => inner ℝ (b i : EuclideanSpace ℝ ι) (e y), ?_⟩
      have h := b.sum_repr' ⟨e y, (hmemE y).1 hy⟩
      have h2 := congrArg (fun v : XE => WithLp.ofLp (v : EuclideanSpace ℝ ι)) h
      simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Submodule.coe_inner] at h2
      ext r
      have h3 := congrFun h2 r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
      rw [mulVec, dotProduct]
      simp only [hX₀, of_apply]
      rw [← show WithLp.ofLp (e y) r = y r from rfl, ← h3]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    choose c hc using fun j => hspan _ (hinv _ (hcol j))
    set C : Matrix (Fin d) (Fin d) ℝ := of fun i j => c j i
    have hMX : M * X₀ = X₀ * C := by
      ext r j
      have := congrFun (hc j) r
      simp only [mulVec, dotProduct] at this
      simp only [mul_apply, C, of_apply]
      exact this
    rw [Matrix.mul_assoc, hMX, ← Matrix.mul_assoc X₀ᵀ, horth, Matrix.one_mul]

/-- The compression of a real matrix to orthonormal columns whose complexifications lie in the
stable spectral subspace has only stable eigenvalues. -/
private theorem re_neg_of_cols {M : Matrix ι ι ℝ} {d : ℕ} {X₀ : Matrix ι (Fin d) ℝ}
    {T : Matrix (Fin d) (Fin d) ℝ} (h1 : X₀ᵀ * X₀ = 1) (hMX : M * X₀ = X₀ * T)
    (hcol : ∀ j, cplx (fun r => X₀ r j) ∈ specSub M fun μ => μ.re < 0) :
    ∀ μ ∈ spectrum ℂ T.complexify, μ.re < 0 := by
  intro μ hμ
  obtain ⟨w, hw0, hw⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul _ μ).1 hμ
  set Xc : Matrix ι (Fin d) ℂ := X₀.map Complex.ofReal
  have hXc1 : Xcᵀ * Xc = 1 := by
    rw [← transpose_map, ← map_ofReal_mul, h1, Matrix.map_one _ Complex.ofReal_zero
      Complex.ofReal_one]
  have hMXc : M.complexify * Xc = Xc * T.complexify := by
    rw [complexify, complexify, ← map_ofReal_mul, ← map_ofReal_mul, hMX]
  set y := Xc *ᵥ w
  have hy0 : y ≠ 0 := by
    intro h
    have := congrArg (Xcᵀ *ᵥ ·) h
    simp only [y, mulVec_mulVec, hXc1, one_mulVec, mulVec_zero] at this
    exact hw0 this
  have hy : M.complexify *ᵥ y = μ • y := by
    rw [mulVec_mulVec, hMXc, ← mulVec_mulVec, hw, mulVec_smul]
  have hymem : y ∈ specSub M fun μ => μ.re < 0 := by
    have : y = ∑ j, w j • cplx (fun r => X₀ r j) := by
      ext r
      simp [y, Xc, mulVec, dotProduct, cplx, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)
  by_contra hre
  have hyu : y ∈ specSub M fun μ => ¬ μ.re < 0 := by
    refine Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hre ?_)
    refine Module.End.eigenspace_le_maxGenEigenspace ?_
    rw [Module.End.mem_eigenspace_iff, toLin'_apply]
    exact hy
  have := (isCompl_specSub M fun μ => μ.re < 0).disjoint.le_bot ⟨hymem, hyu⟩
  exact hy0 ((Submodule.mem_bot ℂ).1 this)

end StableSubspace

section Isotropic

/-- An isotropic family of orthonormal vectors in the symplectic space `ℝ^{l ⊕ l}` has at most
`card l` members: the columns of `X₀` and of `J X₀` are orthonormal and mutually orthogonal. -/
private theorem card_le_of_isotropic {k : Type*} [Fintype k] [DecidableEq k]
    {X₀ : Matrix (l ⊕ l) k ℝ} (h1 : X₀ᵀ * X₀ = 1) (h2 : X₀ᵀ * J l ℝ * X₀ = 0) :
    Fintype.card k ≤ Fintype.card l := by
  set Y := J l ℝ * X₀
  have hY : Yᵀ * Y = 1 := by
    rw [transpose_mul, J_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (-J l ℝ),
      Matrix.neg_mul, J_squared, neg_neg, Matrix.one_mul, h1]
  have hrX : Fintype.card k ≤ X₀ᵀ.rank := by
    have := rank_mul_le_left X₀ᵀ X₀
    rwa [h1, rank_one] at this
  have hrY : Fintype.card k ≤ Y.rank := by
    have := rank_mul_le_left Yᵀ Y
    rwa [hY, rank_one, rank_transpose] at this
  have h0 : X₀ᵀ * Y = 0 := by rw [← Matrix.mul_assoc, h2]
  have hle : LinearMap.range Y.mulVecLin ≤ LinearMap.ker X₀ᵀ.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, h0, zero_mulVec]
  have hker := LinearMap.finrank_range_add_finrank_ker X₀ᵀ.mulVecLin
  have hrY' : Y.rank ≤ Module.finrank ℝ (LinearMap.ker X₀ᵀ.mulVecLin) :=
    Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at hker
  change X₀ᵀ.rank + _ = _ at hker
  omega

end Isotropic

section HamiltonianSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Without eigenvalues on the imaginary axis, the unstable spectral subspace of `M` lies in the
stable one of `-M`. -/
private theorem specSub_unstable_le (M : Matrix ι ι ℝ)
    (hre : ∀ μ ∈ spectrum ℂ M.complexify, μ.re ≠ 0) :
    specSub M (fun μ => ¬ μ.re < 0) ≤ specSub (-M) fun μ => μ.re < 0 := by
  refine iSup₂_le fun μ hμ v hv => ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · exact zero_mem _
  have hpos : 0 < μ.re := by
    refine lt_of_le_of_ne (not_lt.1 hμ) (Ne.symm fun h0 => hre μ ?_ h0)
    have hne : Module.End.maxGenEigenspace (toLin' M.complexify) μ ≠ ⊥ := fun h => by
      rw [h, Submodule.mem_bot] at hv; exact hv0 hv
    have h1 : Module.End.HasUnifEigenvalue (toLin' M.complexify) μ ⊤ := hne
    rw [Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)] at h1
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector h1
    refine (mem_spectrum_iff_exists_mulVec_eq_smul _ μ).2 ⟨x, hx.2, ?_⟩
    have := hx.apply_eq_smul
    rwa [toLin'_apply] at this
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  have hneg : (-μ).re < 0 := by rw [Complex.neg_re]; linarith
  refine Submodule.mem_iSup_of_mem (-μ) (Submodule.mem_iSup_of_mem hneg ?_)
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  have hneg : toLin' (-M).complexify - (-μ) • (1 : Module.End ℂ (ι → ℂ)) =
      -(toLin' M.complexify - μ • 1) := by
    rw [complexify_neg, map_neg, neg_smul]
    abel
  rw [hneg, neg_pow, Module.End.mul_apply, hk, map_zero]

/-- The real points of a spectral subspace. -/
private noncomputable def realSub (M : Matrix ι ι ℝ) (P : ℂ → Prop) : Submodule ℝ (ι → ℝ) :=
  ((specSub M P).restrictScalars ℝ).comap cplxLin

private theorem mem_realSub {M : Matrix ι ι ℝ} {P : ℂ → Prop} {x : ι → ℝ} :
    x ∈ realSub M P ↔ cplx x ∈ specSub M P := Iff.rfl

private theorem mulVec_mem_realSub {M : Matrix ι ι ℝ} {P : ℂ → Prop} {x : ι → ℝ}
    (hx : x ∈ realSub M P) : M *ᵥ x ∈ realSub M P := by
  rw [mem_realSub, cplx_mulVec]; exact mulVec_mem_specSub hx

end HamiltonianSchur

variable {n : ℕ}

/-- The stable invariant subspace of a Hamiltonian matrix without eigenvalues on the imaginary axis
has dimension `n` and an orthonormal, isotropic basis `X₀` with `M X₀ = X₀ T₁`, `T₁` stable. -/
private theorem exists_stable_lagrangian {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M.IsHamiltonian) (hre : ∀ μ ∈ spectrum ℂ M.complexify, μ.re ≠ 0) :
    ∃ X₀ : Matrix (Fin n ⊕ Fin n) (Fin n) ℝ, X₀ᵀ * X₀ = 1 ∧ X₀ᵀ * J (Fin n) ℝ * X₀ = 0 ∧
      M * X₀ = X₀ * (X₀ᵀ * M * X₀) ∧
      ∀ μ ∈ spectrum ℂ (X₀ᵀ * M * X₀).complexify, μ.re < 0 := by
  set Xs := realSub M fun μ => μ.re < 0
  set Xu := realSub M fun μ => ¬ μ.re < 0
  -- the dimension of a stable real subspace is at most `n`
  have hbound : ∀ (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ), N.IsHamiltonian →
      ∀ X : Submodule ℝ (Fin n ⊕ Fin n → ℝ), (∀ x ∈ X, N *ᵥ x ∈ X) →
        (∀ x ∈ X, cplx x ∈ specSub N fun μ => μ.re < 0) → Module.finrank ℝ X ≤ n := by
    intro N hN X hinv hsub
    obtain ⟨X₀, h1, hMX, hcol⟩ := exists_orthonormal_cols N X hinv rfl
    have hst := re_neg_of_cols h1 hMX fun j => hsub _ (hcol j)
    have hlag := hN.isLagrangian_stable_invariant hMX hst
    have := card_le_of_isotropic h1 hlag
    simpa using this
  have hs : Module.finrank ℝ Xs ≤ n :=
    hbound M hM Xs (fun x hx => mulVec_mem_realSub hx) fun x hx => hx
  have hu : Module.finrank ℝ Xu ≤ n := by
    refine hbound (-M) hM.neg Xu (fun x hx => ?_) fun x hx => specSub_unstable_le M hre hx
    rw [neg_mulVec]; exact neg_mem (mulVec_mem_realSub hx)
  have htop : Xs ⊔ Xu = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨u, w, rfl, hu', hw'⟩ := exists_real_split M (P := fun μ => μ.re < 0)
      (fun μ => by simp) x
    exact Submodule.add_mem_sup hu' hw'
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Xs Xu
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin] at hsum
  have hinf := Submodule.finrank_le (Xs ⊓ Xu)
  have hd : Module.finrank ℝ Xs = n := by omega
  obtain ⟨X₀, h1, hMX, hcol⟩ := exists_orthonormal_cols M Xs
    (fun x hx => mulVec_mem_realSub hx) hd
  have hst := re_neg_of_cols h1 hMX fun j => hcol j
  exact ⟨X₀, h1, hM.isLagrangian_stable_invariant hMX hst, hMX, hst⟩

/-- **The real Hamiltonian–Schur decomposition** ([golub2013matrix] (7.8.1); Paige and Van Loan
1981): a real Hamiltonian `M` with no eigenvalue on the imaginary axis has an orthogonal symplectic
`Q` with `Qᵀ M Q = fromBlocks T R 0 (-Tᵀ)`, `T` upper quasi-triangular, and the eigenvalues of `T`
are stable (negative real part). Route: the real stable invariant subspace has dimension `n`
(its complexification and that of the unstable one are complementary, and both are isotropic —
`Matrix.IsHamiltonian.isLagrangian_stable_invariant` — so neither exceeds `n`); an orthonormal
basis `[Q₁; -Q₂]` of it completes to the orthogonal symplectic `fromBlocks Q₁ Q₂ (-Q₂) Q₁`, which
makes `M` block upper triangular with Hamiltonian structure; the real Schur form `U` of the leading
block (`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`), applied as `diag(U, U)`,
finishes. -/
theorem exists_orthogonalSymplectic_hamiltonianSchur
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M.IsHamiltonian)
    (hre : ∀ μ ∈ spectrum ℂ M.complexify, μ.re ≠ 0) :
    ∃ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, Q ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
      Q ∈ symplecticGroup (Fin n) ℝ ∧ ∃ T R : Matrix (Fin n) (Fin n) ℝ,
        Qᵀ * M * Q = fromBlocks T R 0 (-Tᵀ) ∧ T.IsQuasiUpperTriangular ∧
          ∀ μ ∈ spectrum ℂ T.complexify, μ.re < 0 := by
  obtain ⟨X₀, h1, hlag, hMX, hst⟩ := exists_stable_lagrangian hM hre
  set T₁ := X₀ᵀ * M * X₀
  set Q₁ : Matrix (Fin n) (Fin n) ℝ := Matrix.toRows₁ X₀
  set Q₂ : Matrix (Fin n) (Fin n) ℝ := -Matrix.toRows₂ X₀
  have hX : X₀ = fromRows Q₁ (-Q₂) := by simp [Q₁, Q₂, fromRows_toRows]
  -- the orthogonal symplectic completion
  have hsum : Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1 := by
    rw [← h1, hX, transpose_fromRows, fromCols_mul_fromRows, transpose_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg]
    simp [Q₂]
  have hsymm : (Q₁ᵀ * Q₂).IsSymm := by
    have hJ : J (Fin n) ℝ * fromRows Q₁ (-Q₂) = fromRows Q₂ Q₁ := by
      simp [J, fromBlocks_mul_fromRows]
    have h := hlag
    rw [hX, Matrix.mul_assoc, hJ, transpose_fromRows, fromCols_mul_fromRows, transpose_neg,
      Matrix.neg_mul, ← sub_eq_add_neg, sub_eq_zero] at h
    rw [IsSymm, transpose_mul, transpose_transpose]
    exact h.symm
  set Q := fromBlocks Q₁ Q₂ (-Q₂) Q₁
  obtain ⟨hQo, hQs⟩ := mem_orthogonalGroup_symplecticGroup_iff.2 ⟨Q₁, Q₂, rfl, hsymm, hsum⟩
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQo
  have hQe : Q * fromRows (1 : Matrix (Fin n) (Fin n) ℝ) 0 = X₀ := by
    rw [hX, fromBlocks_mul_fromRows]; simp
  -- the block structure of `Qᵀ M Q`
  set S := Qᵀ * M * Q
  have hS1 : S * fromRows (1 : Matrix (Fin n) (Fin n) ℝ) 0 = fromRows T₁ 0 := by
    rw [Matrix.mul_assoc, hQe, Matrix.mul_assoc, hMX, ← hQe, ← Matrix.mul_assoc Qᵀ,
      ← Matrix.mul_assoc Qᵀ, hQQ, Matrix.one_mul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  have hSb : S = fromBlocks S.toBlocks₁₁ S.toBlocks₁₂ S.toBlocks₂₁ S.toBlocks₂₂ :=
    (fromBlocks_toBlocks S).symm
  have h11 : S.toBlocks₁₁ = T₁ ∧ S.toBlocks₂₁ = 0 := by
    have h := hS1
    rw [hSb, fromBlocks_mul_fromRows] at h
    simpa using fromRows_inj h
  have hQinv : Q⁻¹ = Qᵀ := inv_eq_left_inv hQQ
  have hSH : S.IsHamiltonian := by
    have := hM.conj_symplectic hQs
    rwa [hQinv] at this
  obtain ⟨R, hR⟩ : ∃ R, R = S.toBlocks₁₂ := ⟨_, rfl⟩
  have hS : S = fromBlocks T₁ R 0 (-T₁ᵀ) := by
    rw [hR]
    have hH : (fromBlocks T₁ S.toBlocks₁₂ 0 S.toBlocks₂₂).IsHamiltonian := by
      rw [← h11.1, ← h11.2, fromBlocks_toBlocks]; exact hSH
    rw [← (isHamiltonian_fromBlocks_iff.1 hH).1, ← h11.1, ← h11.2, fromBlocks_toBlocks]
  -- the real Schur form of the stable block
  obtain ⟨U, hU, hUT⟩ := exists_orthogonal_conj_isQuasiUpperTriangular T₁
  have hUU : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hUU' : U * Uᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hD := fromBlocks_diagonal_mem_symplecticGroup hU
  set D := fromBlocks U 0 0 U
  refine ⟨Q * D, mul_mem hQo hD.1, mul_mem hQs hD.2, Uᵀ * T₁ * U,
    Uᵀ * R * U, ?_, hUT, ?_⟩
  · have key : (Q * D)ᵀ * M * (Q * D) = Dᵀ * S * D := by
      rw [transpose_mul]; simp only [S, Matrix.mul_assoc]
    rw [key, hS, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, neg_zero,
      Matrix.mul_assoc]
  · intro μ hμ
    refine hst μ ?_
    rw [mem_spectrum_complexify_iff] at hμ ⊢
    set u : (Matrix (Fin n) (Fin n) ℝ)ˣ := ⟨U, Uᵀ, hUU', hUU⟩
    have hinv : U⁻¹ = Uᵀ := inv_eq_left_inv hUU
    have hc : (Uᵀ * T₁ * U).charpoly = T₁.charpoly := by
      have := charpoly_units_conj' u T₁
      rwa [show ((u : Matrix (Fin n) (Fin n) ℝ)) = U from rfl, hinv] at this
    rwa [hc] at hμ

end Matrix
