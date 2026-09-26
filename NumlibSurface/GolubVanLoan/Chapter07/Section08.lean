import Numlib.Eigen.HamiltonianSchur
import Numlib.Eigen.PeriodicSchur
import NumlibSurface.GolubVanLoan.Chapter07.Section04

/-!
# Golub–Van Loan §7.8: Hamiltonian and product eigenvalue problems

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.8: the skew-Hamiltonian and orthogonal symplectic rows of Figure 7.8.1, the
four facts (1)–(4) of §7.8.1, symplectic Householder and Givens transformations, the real
Hamiltonian–Schur form (7.8.1) and the algebraic Riccati equation (7.8.2), and the product
decompositions (7.8.5)–(7.8.6) with their block-cyclic restatement and its perfect-shuffle
Hessenberg form.

## Conventions

Real matrices on `Fin n ⊕ Fin n` (the book's `2n × 2n` with `n × n` blocks, `Matrix.fromBlocks`).
The book's `J = [0 I; -I 0]` is `-Matrix.J (Fin n) ℝ` (Mathlib's `J = [0 -I; I 0]`); every structure
here is invariant under `J ↦ -J`, and — as chapter 1 decided for §1.3.10 — the surface uses
Mathlib's `J` throughout. Hamiltonian is the backbone's `Matrix.IsHamiltonian`, skew-Hamiltonian
`Matrix.IsSkewHamiltonian`, symplectic Mathlib's `Matrix.symplecticGroup (Fin n) ℝ`. The complex
eigenvalues of a real matrix are those of `Matrix.complexify`. The product problem uses
`A₁, A₂, A₃` as the book does, `A = A₃ A₂ A₁`; the backbone indexes them by `Fin 3`.

## Not formalized

(7.8.7) (the iterates stay in Hessenberg–triangular–triangular form: no convergence statement);
"a structure-preserving QR iteration … has yet to be devised" and the quality of eigenvalues
computed from `M²` (no precise claims); rectangular and inverted factors (mentioned only).
-/

open Matrix

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.8.1 Hamiltonian matrix eigenproblems -/

/-- **Figure 7.8.1, skew-Hamiltonian row**: `J N` is skew-symmetric, `J N = -(J N)ᵀ`, exactly when
`N = [A G; F Aᵀ]` with `G` and `F` skew-symmetric. -/
theorem figure_7_8_1_skewHamiltonian (A G F H : Matrix (Fin n) (Fin n) ℝ) :
    (J (Fin n) ℝ * fromBlocks A G F H)ᵀ = -(J (Fin n) ℝ * fromBlocks A G F H) ↔
      H = Aᵀ ∧ Fᵀ = -F ∧ Gᵀ = -G := by
  rw [← isSkewHamiltonian_iff_transpose_J_mul, isSkewHamiltonian_iff_fromBlocks]

/-- **Figure 7.8.1, orthogonal symplectic row**: an orthogonal `Q` is symplectic iff `J Q = Q J` iff
`Q = [Q₁ Q₂; -Q₂ Q₁]`, and then `Q₁ᵀ Q₂` is symmetric and `I = Q₁ᵀ Q₁ + Q₂ᵀ Q₂`. -/
theorem figure_7_8_1_orthogonalSymplectic {Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ) :
    (Q ∈ symplecticGroup (Fin n) ℝ ↔ Commute (J (Fin n) ℝ) Q) ∧
      (Q ∈ symplecticGroup (Fin n) ℝ ↔ ∃ Q₁ Q₂ : Matrix (Fin n) (Fin n) ℝ,
        Q = fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∧ (Q₁ᵀ * Q₂).IsSymm ∧ Q₁ᵀ * Q₁ + Q₂ᵀ * Q₂ = 1) :=
  ⟨mem_symplecticGroup_iff_commute_J_of_mem_orthogonalGroup hQ, by
    rw [← mem_orthogonalGroup_symplecticGroup_iff]
    exact ⟨fun h => ⟨hQ, h⟩, fun h => h.2⟩⟩

/-- **§7.8.1 (1)**: "Symplectic similarity transformations preserve Hamiltonian structure", and
likewise skew-Hamiltonian structure (the remark before (7.8.4)). -/
theorem hamiltonian_symplectic_conj {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    (∀ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, M.IsHamiltonian →
      (S⁻¹ * M * S).IsHamiltonian) ∧
    ∀ N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, N.IsSkewHamiltonian →
      (S⁻¹ * N * S).IsSkewHamiltonian :=
  ⟨fun _ hM => hM.conj_symplectic hS, fun _ hN => hN.conj_symplectic hS⟩

/-- **§7.8.1 (2)**: the square of a Hamiltonian matrix is skew-Hamiltonian. -/
theorem hamiltonian_sq_skewHamiltonian {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M.IsHamiltonian) : (M * M).IsSkewHamiltonian :=
  hM.isSkewHamiltonian_mul_self

/-- The complexification of Mathlib's `J`. -/
private theorem complexify_J : (J (Fin n) ℝ).complexify = J (Fin n) ℂ := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [J, complexify, one_apply, h]

/-- `J [u; v] = [-v; u]` for Mathlib's `J`, so `[v; -u] = -J [u; v]`. -/
private theorem J_mulVec_eq (x : Fin n ⊕ Fin n → ℂ) :
    J (Fin n) ℂ *ᵥ x = -Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  rw [J, fromBlocks_mulVec]
  ext (i | i) <;> simp [neg_mulVec]

/-- **§7.8.1 (3)**: if `M` is Hamiltonian and `λ ∈ λ(M)`, then `-λ ∈ λ(M)`; the book's witness:
`M [u; v] = λ [u; v]` implies `Mᵀ [v; -u] = -λ [v; -u]`. -/
theorem hamiltonian_neg_mem_spectrum {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M.IsHamiltonian) :
    (∀ μ ∈ spectrum ℂ M.complexify, -μ ∈ spectrum ℂ M.complexify) ∧
      ∀ (x : Fin n ⊕ Fin n → ℂ) (μ : ℂ), M.complexify *ᵥ x = μ • x →
        (M.complexify)ᵀ *ᵥ Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) =
          (-μ) • Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  refine ⟨fun μ hμ => hM.neg_mem_spectrum hμ, fun x μ hx => ?_⟩
  have hJ : J (Fin n) ℂ * M.complexify = -(M.complexify)ᵀ * J (Fin n) ℂ := by
    have h := congrArg complexify (isHamiltonian_iff_J_mul_eq.1 hM)
    rwa [complexify_mul, complexify_mul, complexify_neg, complexify_transpose, complexify_J] at h
  have key : (M.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x) = (-μ) • (J (Fin n) ℂ *ᵥ x) := by
    have h := congrArg (· *ᵥ x) hJ
    simp only [← mulVec_mulVec, hx, mulVec_smul, Matrix.neg_mul, neg_mulVec] at h
    rw [neg_smul, h, neg_neg]
  rw [J_mulVec_eq, mulVec_neg, smul_neg, neg_inj] at key
  exact key

/-- **§7.8.1 (4)**: if `S` is symplectic and `λ ∈ λ(S)`, then `λ ≠ 0` and `1/λ ∈ λ(S)`; the book's
witness: `S [u; v] = λ [u; v]` implies `Sᵀ [v; -u] = (1/λ) [v; -u]`. -/
theorem symplectic_inv_mem_spectrum {S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hS : S ∈ symplecticGroup (Fin n) ℝ) :
    (∀ μ ∈ spectrum ℂ S.complexify, μ ≠ 0 ∧ μ⁻¹ ∈ spectrum ℂ S.complexify) ∧
      ∀ (x : Fin n ⊕ Fin n → ℂ) (μ : ℂ), μ ≠ 0 → S.complexify *ᵥ x = μ • x →
        (S.complexify)ᵀ *ᵥ Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) =
          μ⁻¹ • Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  refine ⟨fun μ hμ => inv_mem_spectrum_of_mem_symplecticGroup hS hμ, fun x μ hμ hx => ?_⟩
  have hSJ : (S.complexify)ᵀ * J (Fin n) ℂ * S.complexify = J (Fin n) ℂ := by
    have h := congrArg complexify (SymplecticGroup.mem_iff'.1 hS)
    rwa [complexify_mul, complexify_mul, complexify_transpose, complexify_J] at h
  have key : (S.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x) = μ⁻¹ • (J (Fin n) ℂ *ᵥ x) := by
    have h := congrArg (· *ᵥ x) hSJ
    simp only [← mulVec_mulVec, hx, mulVec_smul] at h
    calc (S.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x)
        = μ⁻¹ • (μ • ((S.complexify)ᵀ *ᵥ (J (Fin n) ℂ *ᵥ x))) := by
          rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (J (Fin n) ℂ *ᵥ x) := by rw [h]
  rw [J_mulVec_eq, mulVec_neg, smul_neg, neg_inj] at key
  exact key

/-- **§7.8.1, symplectic Householder and Givens transformations.** If `P` is orthogonal (a
Householder matrix `I - 2vvᵀ`, for instance), `diag(P, P)` is orthogonal symplectic; a Givens
rotation in the planes `i` and `n + i` is orthogonal symplectic; and (the
Householder–Givens–Householder sequence) every `x ∈ ℝ^{2n}` is mapped to a multiple of `e₁` by an
orthogonal symplectic `Qᵀ`. -/
theorem symplectic_householder_givens :
    (∀ P : Matrix (Fin n) (Fin n) ℝ, P ∈ orthogonalGroup (Fin n) ℝ →
      fromBlocks P 0 0 P ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
        fromBlocks P 0 0 P ∈ symplecticGroup (Fin n) ℝ) ∧
    (∀ (i : Fin n) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
      planeRotation (Sum.inl i) (Sum.inr i) c s ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
        planeRotation (Sum.inl i) (Sum.inr i) c s ∈ symplecticGroup (Fin n) ℝ) ∧
    ∀ (x : Fin n ⊕ Fin n → ℝ) (i₀ : Fin n),
      ∃ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, Q ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
        Q ∈ symplecticGroup (Fin n) ℝ ∧
        Qᵀ *ᵥ x = ‖WithLp.toLp 2 x‖ • Pi.single (Sum.inl i₀) 1 :=
  ⟨fun _ hP => fromBlocks_diagonal_mem_symplecticGroup hP,
    fun i _ _ hcs => planeRotation_inl_inr_mem_symplecticGroup i hcs,
    exists_orthogonalSymplectic_mulVec_eq⟩

/-- **(7.8.1), the real Hamiltonian–Schur decomposition.** If `M` is Hamiltonian with no purely
imaginary eigenvalue, there is an orthogonal symplectic `Q = [Q₁ Q₂; -Q₂ Q₁]` with
`Qᵀ M Q = [T R; 0 -Tᵀ]`, `T` upper quasi-triangular with `λ(T)` in the open left half-plane. -/
theorem equation_7_8_1 {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M.IsHamiltonian)
    (hre : ∀ μ ∈ spectrum ℂ M.complexify, μ.re ≠ 0) :
    ∃ Q₁ Q₂ T R : Matrix (Fin n) (Fin n) ℝ,
      fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ ∧
      fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ symplecticGroup (Fin n) ℝ ∧
      (fromBlocks Q₁ Q₂ (-Q₂) Q₁)ᵀ * M * fromBlocks Q₁ Q₂ (-Q₂) Q₁ = fromBlocks T R 0 (-Tᵀ) ∧
      T.IsQuasiUpperTriangular ∧ ∀ μ ∈ spectrum ℂ T.complexify, μ.re < 0 := by
  obtain ⟨Q, hQo, hQs, T, R, hQM, hT, hst⟩ := exists_orthogonalSymplectic_hamiltonianSchur hM hre
  obtain ⟨Q₁, Q₂, rfl, -, -⟩ := (figure_7_8_1_orthogonalSymplectic hQo).2.1 hQs
  exact ⟨Q₁, Q₂, T, R, hQo, hQs, hQM, hT, hst⟩

/-- **(7.8.2), the algebraic Riccati equation.** In the Hamiltonian–Schur form (7.8.1) of
`M = [A F; G -Aᵀ]` with `Q₁` nonsingular, `X = Q₂ Q₁⁻¹` is symmetric and satisfies
`G + X A + Aᵀ X - X F X = 0`, and `A - F X = Q₁ T Q₁⁻¹`, so `λ(A - F X) = λ(T)` (in the open left
half-plane when `T` is chosen so). (The book derives the symmetry of `X` "from
`I_n = Q₁ᵀ Q₁ + Q₂ᵀ Q₂`"; it follows from the symmetry of `Q₁ᵀ Q₂`.) -/
theorem equation_7_8_2 {A F G T R Q₁ Q₂ : Matrix (Fin n) (Fin n) ℝ}
    (hQ : fromBlocks Q₁ Q₂ (-Q₂) Q₁ ∈ orthogonalGroup (Fin n ⊕ Fin n) ℝ)
    (hS : (fromBlocks Q₁ Q₂ (-Q₂) Q₁)ᵀ * fromBlocks A F G (-Aᵀ) * fromBlocks Q₁ Q₂ (-Q₂) Q₁ =
      fromBlocks T R 0 (-Tᵀ)) (hQ₁ : IsUnit Q₁) :
    (Q₂ * Q₁⁻¹).IsSymm ∧
      G + Q₂ * Q₁⁻¹ * A + Aᵀ * (Q₂ * Q₁⁻¹) - Q₂ * Q₁⁻¹ * F * (Q₂ * Q₁⁻¹) = 0 ∧
      A - F * (Q₂ * Q₁⁻¹) = Q₁ * T * Q₁⁻¹ ∧
      spectrum ℂ (A - F * (Q₂ * Q₁⁻¹)).complexify = spectrum ℂ T.complexify := by
  obtain ⟨h1, h2, h3⟩ := riccati_of_hamiltonianSchur hQ hS hQ₁
  refine ⟨h1, h2, h3, ?_⟩
  have hsim : IsSimilar (A - F * (Q₂ * Q₁⁻¹)).complexify T.complexify := by
    refine ⟨Q₁.complexify, (isUnit_complexify_iff Q₁).2 hQ₁, ?_⟩
    rw [h3, ← complexify_inv, ← complexify_mul, ← complexify_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ₁), Matrix.mul_one, ← Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hQ₁), Matrix.one_mul]
  ext μ
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, hsim.charpoly_eq]

/-! ### §7.8.2 Product eigenvalue problems -/

/-- **(7.8.5) and the display after it**: for `A₁, A₂, A₃ ∈ ℝ^{n×n}` there are orthogonal `U₁`,
`U₂`, `U₃` with `U₁ᵀ A₃ U₃ = H₃` upper Hessenberg and `U₃ᵀ A₂ U₂ = T₂`, `U₂ᵀ A₁ U₁ = T₁` upper
triangular; then `U₁ᵀ (A₃ A₂ A₁) U₁ = H₃ T₂ T₁` is upper Hessenberg. (The book's "procedure" — QR
factorizations, then Givens rotations with bulge chasing — is described, not given as an algorithm.)
-/
theorem equation_7_8_5 (A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U₁ ∈ orthogonalGroup (Fin n) ℝ, ∃ U₂ ∈ orthogonalGroup (Fin n) ℝ,
      ∃ U₃ ∈ orthogonalGroup (Fin n) ℝ,
        (U₁ᵀ * A₃ * U₃).IsUpperHessenberg ∧ (U₃ᵀ * A₂ * U₂).IsUpperTriangular ∧
          (U₂ᵀ * A₁ * U₁).IsUpperTriangular ∧ (U₁ᵀ * (A₃ * A₂ * A₁) * U₁).IsUpperHessenberg := by
  obtain ⟨U, hU, hT, hH⟩ := exists_orthogonal_periodicHessenberg ![A₁, A₂, A₃]
  have hT₁ : ((U 1)ᵀ * A₁ * U 0).IsUpperTriangular := by simpa using hT 0
  have hT₂ : ((U 2)ᵀ * A₂ * U 1).IsUpperTriangular := by simpa using hT 1
  have hH₃ : ((U 0)ᵀ * A₃ * U 2).IsUpperHessenberg := by simpa using hH
  have h2 : U 2 * (U 2)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 2)
  have h1 : U 1 * (U 1)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 1)
  have hprod : (U 0)ᵀ * (A₃ * A₂ * A₁) * U 0 =
      ((U 0)ᵀ * A₃ * U 2) * ((U 2)ᵀ * A₂ * U 1) * ((U 1)ᵀ * A₁ * U 0) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U 2) (U 2)ᵀ, h2, Matrix.one_mul, ← Matrix.mul_assoc (U 1) (U 1)ᵀ, h1,
      Matrix.one_mul]
  refine ⟨U 0, hU 0, U 1, hU 1, U 2, hU 2, hH₃, hT₂, hT₁, ?_⟩
  rw [hprod]
  exact (hH₃.mul_isUpperTriangular hT₂).mul_isUpperTriangular hT₁

/-- **(7.8.6), the periodic real Schur form** of `A = A₃ A₂ A₁`: orthogonal `Q₁`, `Q₂`, `Q₃` with
`Q₁ᵀ A₃ Q₃ = T₃` upper quasi-triangular and `Q₃ᵀ A₂ Q₂ = T₂`, `Q₂ᵀ A₁ Q₁ = T₁` upper triangular, so
that `Q₁ᵀ A Q₁ = T₃ T₂ T₁` is a real Schur form of the product. -/
theorem equation_7_8_6 (A₁ A₂ A₃ : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q₁ ∈ orthogonalGroup (Fin n) ℝ, ∃ Q₂ ∈ orthogonalGroup (Fin n) ℝ,
      ∃ Q₃ ∈ orthogonalGroup (Fin n) ℝ,
        (Q₁ᵀ * A₃ * Q₃).IsQuasiUpperTriangular ∧ (Q₃ᵀ * A₂ * Q₂).IsUpperTriangular ∧
          (Q₂ᵀ * A₁ * Q₁).IsUpperTriangular ∧
          (Q₁ᵀ * (A₃ * A₂ * A₁) * Q₁).IsQuasiUpperTriangular := by
  obtain ⟨U, hU, hT, hH⟩ := exists_orthogonal_periodicRealSchur ![A₁, A₂, A₃]
  have hT₁ : ((U 1)ᵀ * A₁ * U 0).IsUpperTriangular := by simpa using hT 0
  have hT₂ : ((U 2)ᵀ * A₂ * U 1).IsUpperTriangular := by simpa using hT 1
  have hH₃ : ((U 0)ᵀ * A₃ * U 2).IsQuasiUpperTriangular := by simpa using hH
  have h2 : U 2 * (U 2)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 2)
  have h1 : U 1 * (U 1)ᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 (hU 1)
  have hprod : (U 0)ᵀ * (A₃ * A₂ * A₁) * U 0 =
      ((U 0)ᵀ * A₃ * U 2) * ((U 2)ᵀ * A₂ * U 1) * ((U 1)ᵀ * A₁ * U 0) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U 2) (U 2)ᵀ, h2, Matrix.one_mul, ← Matrix.mul_assoc (U 1) (U 1)ᵀ, h1,
      Matrix.one_mul]
  refine ⟨U 0, hU 0, U 1, hU 1, U 2, hU 2, hH₃, hT₂, hT₁, ?_⟩
  rw [hprod]
  exact ((hH₃.mul_isUpperTriangular hT₂).1.mul_isUpperTriangular hT₁).1

/-- **§7.8.2, the block-cyclic restatement**: with `U = diag(U₁, U₂, U₃)`,
`Uᵀ [0 0 A₃; A₁ 0 0; 0 A₂ 0] U = [0 0 U₁ᵀA₃U₃; U₂ᵀA₁U₁ 0 0; 0 U₃ᵀA₂U₂ 0]` (the factors indexed by
`Fin 3`, `A 0 = A₁`, `U 0 = U₁`), which for the `U_i` of (7.8.5) is `[0 0 H₃; T₁ 0 0; 0 T₂ 0] = H̃`.
-/
theorem blockCyclic_restatement (A U : Fin 3 → Matrix (Fin n) (Fin n) ℝ) :
    (blockDiagonal U)ᵀ * blockCyclic A * blockDiagonal U =
      blockCyclic fun i => (U (i + 1))ᵀ * A i * U i :=
  blockDiagonal_conj_blockCyclic A U

/-- **§7.8.2, the perfect shuffle**: "`𝒫 H̃ 𝒫ᵀ` is a highly structured upper Hessenberg matrix", for
every `n` (the book shows `n = 4`): if `T₁ = A 0`, `T₂ = A 1` are upper triangular and `H₃ = A 2` is
upper Hessenberg, the perfect-shuffle reindexing of the block-cyclic `H̃` is upper Hessenberg. -/
theorem blockCyclic_shuffle_isUpperHessenberg {A : Fin 3 → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i : Fin 2, (A i.castSucc).IsUpperTriangular) (hH : (A 2).IsUpperHessenberg) :
    ((blockCyclic A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).IsUpperHessenberg :=
  isUpperHessenberg_reindex_blockCyclic hA hH

end GolubVanLoan.Chapter07
