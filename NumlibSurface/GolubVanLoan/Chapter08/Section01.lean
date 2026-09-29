import Numlib.Analysis.Matrix.SingularValues
import Numlib.Analysis.Matrix.SpectralNorm
import Mathlib.Algebra.Order.Star.Real
import Numlib.Eigen.DivideConquer
import Numlib.Eigen.Inertia
import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.MinMax
import Numlib.Eigen.Perturbation
import Numlib.Eigen.RayleighRitz
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Polar
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Sylvester
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter07.Section02

/-!
# Golub–Van Loan §8.1: properties and decompositions of symmetric matrices

Surface file for [golub2013matrix] §8.1: the symmetric Schur decomposition, the min–max
characterization, eigenvalue perturbation (Gershgorin, Wielandt–Hoffman, Weyl, interlacing,
rank-one updates), invariant subspaces and their perturbation, approximate invariant subspaces and
Ritz pairs, and Sylvester's law of inertia.

## Conventions

The book's `λ_k(A)`, the `k`-th largest eigenvalue of a symmetric `A` (`λ_n ≤ ⋯ ≤ λ_1`), is
`symmEigenvalue hA ⟨k - 1, _⟩`: a reindexing to `Fin n` of Mathlib's sorted
`Matrix.IsHermitian.eigenvalues₀` (the backbone's `Matrix.IsHermitian.sortedEigenvalues`), for
`hA : A.IsSymm` (over `ℝ` the same as `A.IsHermitian`, `Matrix.isHermitian_iff_isSymm`). Orthogonal
matrices are elements of `Matrix.orthogonalGroup (Fin n) ℝ`, `‖·‖₂` is `Matrix.lpOpNorm 2`, `‖·‖_F`
the scoped `Matrix.Norms.Frobenius` norm.

## Readings

Theorem 8.1.13 is planned in the paired form its proof gives (`μ_k = λ_{σ(k)}(A)` for an injection
`σ`); the unpaired constant-`1` form is `theorem_8_1_13_weak`. Theorem 8.1.16 is paired likewise.
Corollary 8.1.11 and Theorem 8.1.12 bound `dist` in the coordinates of `Q`
(`Matrix.gap_range_fromRows_le`) rather than through the book's `‖Q₂ᵀ Q̂₁‖₂`. In the proof of
Theorem 8.1.16 the book's "`1 − σ_r² = τ`" is not true in general; (8.1.7)'s conclusion is. P8.1.5
is not used.

## Sources

Backbone `Numlib/Eigen/{MinMax, Perturbation, RayleighRitz, Inertia, InvariantSubspace}`,
`Numlib/LinearAlgebra/Matrix/{Polar, Schur, Sylvester, SVD}`,
`Numlib/Analysis/Matrix/{SingularValues, SpectralNorm}`; chapter 7's Theorem 7.2.1 (Gershgorin) for
Theorem 8.1.3; chapter 2's `subspaceDist` for Corollary 8.1.11 and Theorem 8.1.12.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.1.1 Eigenvalue and eigenvector properties -/

/-- **§8.1.1, `λ_k(A)`**: the eigenvalues of a symmetric `A`, sorted decreasingly and indexed by
`Fin n`; the book's `λ_k(A)` is `symmEigenvalue hA ⟨k - 1, _⟩`. -/
noncomputable def symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) : ℝ :=
  (isHermitian_iff_isSymm.2 hA).sortedEigenvalues k

/-- `symmEigenvalue` is the backbone's `sortedEigenvalues`, for any proof of Hermitianness. -/
theorem symmEigenvalue_eq_sortedEigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hH : A.IsHermitian) : symmEigenvalue hA = hH.sortedEigenvalues :=
  rfl

/-- `λ_1(A) ≥ λ_2(A) ≥ ⋯ ≥ λ_n(A)`. -/
theorem antitone_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    Antitone (symmEigenvalue hA) :=
  (isHermitian_iff_isSymm.2 hA).sortedEigenvalues_antitone

/-- The roots of the characteristic polynomial, with multiplicity, are the `λ_k(A)`. -/
theorem roots_charpoly_eq_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.charpoly.roots = Multiset.map (symmEigenvalue hA) Finset.univ.val := by
  rw [(isHermitian_iff_isSymm.2 hA).roots_charpoly_eq_sortedEigenvalues]
  congr 1

/-- The eigenvalues `λ_k(A)` are exactly the (real) spectrum of `A`. -/
theorem spectrum_eq_range_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    spectrum ℝ A = Set.range (symmEigenvalue hA) := by
  rw [(isHermitian_iff_isSymm.2 hA).spectrum_real_eq_range_eigenvalues]
  ext x
  simp only [Set.mem_range, IsHermitian.eigenvalues, symmEigenvalue,
    IsHermitian.sortedEigenvalues_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast (Fintype.card_fin n) ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i),
      by simp⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.cast (Fintype.card_fin n).symm k),
      by simp⟩

/-- Each `λ_k(A)` is an eigenvalue of `A`. -/
theorem symmEigenvalue_mem_spectrum {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) :
    symmEigenvalue hA k ∈ spectrum ℝ A := by
  rw [spectrum_eq_range_symmEigenvalue hA]
  exact ⟨k, rfl⟩

/-- The sorted eigenvalues of a symmetric operator do not depend on the name of the dimension. -/
private theorem eigenvalues_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {a b : ℕ}
    (ha : Module.finrank ℝ E = a) (hb : Module.finrank ℝ E = b) (h : a = b) (i : Fin a) :
    hT.eigenvalues ha i = hT.eigenvalues hb (Fin.cast h i) := by
  subst h
  rfl

/-- `λ_k(A)` is the `k`-th sorted eigenvalue of any operator equal to `toEuclideanLin A`. -/
private theorem symmEigenvalue_eq_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)} (hT : T.IsSymmetric)
    (h : toEuclideanLin A = T) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)
    (k : Fin n) : symmEigenvalue hA k = hT.eigenvalues hm k := by
  subst h
  change hT.eigenvalues finrank_euclideanSpace (Fin.cast (Fintype.card_fin n).symm k) = _
  rw [eigenvalues_cast hT finrank_euclideanSpace hm (Fintype.card_fin n)]
  rfl

/-- The symmetric operator of a symmetric matrix. -/
private theorem isSymmetric_toEuclideanLin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.2 hA)

/-- **§8.1.1, the Rayleigh quotient** `r(x) = xᵀAx / xᵀx` (also (8.2.6)). -/
noncomputable def rayleighQuotient (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)

/-- The book's Rayleigh quotient is Mathlib's `re ⟪T x, x⟫ / ‖x‖²` for `T = toEuclideanLin A`. -/
theorem rayleighQuotient_eq (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    rayleighQuotient A x = (toEuclideanLin A).rayleighQuotient (WithLp.toLp 2 x) := by
  rw [rayleighQuotient, LinearMap.rayleighQuotient, ← real_inner_self_eq_norm_sq,
    toEuclideanLin_toLp]
  simp only [EuclideanSpace.inner_toLp_toLp, RCLike.re_to_real, star_trivial]

/-- **Theorem 8.1.1 (symmetric Schur decomposition).** A symmetric `A` has an orthogonal `Q` with
`Qᵀ A Q = Λ = diag(λ_1, …, λ_n)`, and `A Q(:, k) = λ_k Q(:, k)`. -/
theorem theorem_8_1_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, Qᵀ * A * Q = diagonal (symmEigenvalue hA) ∧
      ∀ k, A *ᵥ Q.col k = symmEigenvalue hA k • Q.col k := by
  obtain ⟨U, hU, h1, h2⟩ :=
    (isHermitian_iff_isSymm.2 hA).exists_unitary_conj_eq_diagonal_eigenvalues₀
  refine ⟨U, hU, ?_, fun k => ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h1
    convert h1 using 2
    funext k
    simp [symmEigenvalue]
  · convert h2 k using 2
    simp [symmEigenvalue]

/-- **§8.1.1, after Theorem 8.1.1**: the singular values of a symmetric `A` are the `|λ_k(A)|`, and
`‖A‖₂ = max(|λ_1(A)|, |λ_n(A)|)`. -/
theorem l2_opNorm_eq_max_abs_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hn : 0 < n) :
    (∃ e : Fin n ≃ Fin n, ∀ k, A.colSingularValues (e k) = |symmEigenvalue hA k|) ∧
      lpOpNorm 2 A = max |symmEigenvalue hA ⟨0, hn⟩| |symmEigenvalue hA ⟨n - 1, by omega⟩| := by
  have hH := isHermitian_iff_isSymm.2 hA
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hH.exists_equiv_colSingularValues_eq_abs_eigenvalues
    refine ⟨((finCongr (Fintype.card_fin n).symm).trans
      (Fintype.equivOfCardEq (Fintype.card_fin _))).trans e, fun k => ?_⟩
    rw [Equiv.trans_apply, he]
    simp [IsHermitian.eigenvalues, symmEigenvalue, IsHermitian.sortedEigenvalues_apply]
  · set M := max |symmEigenvalue hA ⟨0, hn⟩| |symmEigenvalue hA ⟨n - 1, by omega⟩|
    have hbound : ∀ k, |symmEigenvalue hA k| ≤ M := fun k => by
      have h0 := antitone_symmEigenvalue hA
        (show (⟨0, hn⟩ : Fin n) ≤ k from Fin.le_def.2 (Nat.zero_le _))
      have h1 := antitone_symmEigenvalue hA
        (show k ≤ (⟨n - 1, by omega⟩ : Fin n) from Fin.le_def.2 (by simp; omega))
      exact (abs_le_max_abs_abs h1 h0).trans_eq (max_comm _ _)
    have hspec : ∀ μ : ℝ, Module.End.HasEigenvalue (toEuclideanLin A) μ ↔
        μ ∈ spectrum ℝ A := fun μ => by
      rw [Module.End.hasEigenvalue_iff_mem_spectrum]
      exact Iff.of_eq (congrArg (μ ∈ ·) (spectrum_toLpLin (A := A) 2))
    rw [lpOpNorm_two]
    refine hH.l2_opNorm_eq (fun μ hμ => ?_) ?_
    · obtain ⟨k, hk⟩ := (spectrum_eq_range_symmEigenvalue hA ▸ (hspec μ).1 hμ :
        μ ∈ Set.range (symmEigenvalue hA))
      simpa [← hk] using hbound k
    · rcases le_total |symmEigenvalue hA ⟨n - 1, by omega⟩| |symmEigenvalue hA ⟨0, hn⟩| with h | h
      · exact ⟨_, (hspec _).2 (symmEigenvalue_mem_spectrum hA ⟨0, hn⟩), by simp [M, h]⟩
      · exact ⟨_, (hspec _).2 (symmEigenvalue_mem_spectrum hA ⟨n - 1, by omega⟩), by simp [M, h]⟩

/-- The linear equivalence between `ℝⁿ` as `EuclideanSpace` and as functions. -/
private abbrev euclideanEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ)

/-- **Theorem 8.1.2 (Courant–Fischer minimax).** For symmetric `A` and `k = 1:n`,
`λ_k(A) = max_{dim(S) = k} min_{0 ≠ y ∈ S} yᵀAy / yᵀy` (0-based: `dim S = k + 1`), both extrema
attained. -/
theorem theorem_8_1_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) :
    IsGreatest {c | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = k + 1 ∧
      IsLeast (rayleighQuotient A '' {y | y ∈ S ∧ y ≠ 0}) c} (symmEigenvalue hA k) := by
  have hT := isSymmetric_toEuclideanLin hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hlam : symmEigenvalue hA k = hT.eigenvalues hn k :=
    symmEigenvalue_eq_eigenvalues hA hT rfl hn k
  set e := euclideanEquiv n
  refine ⟨⟨(hT.eigenvectorSpan hn (Finset.Iic k)).map e.toLinearMap, ?_, ?_, ?_⟩, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  · refine ⟨e (hT.eigenvectorBasis hn k), ⟨Submodule.mem_map_of_mem
      (hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Iic.mpr le_rfl)), ?_⟩, ?_⟩
    · simpa using hT.eigenvectorBasis_ne_zero hn k
    · rw [hlam, rayleighQuotient_eq, ← hT.rayleighQuotient_eigenvectorBasis hn k]
      rfl
  · rintro _ ⟨y, ⟨hyS, hy0⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyS
    rw [hlam, rayleighQuotient_eq]
    have hx0 : x ≠ 0 := fun h0 => hy0 (by rw [h0, map_zero])
    exact hT.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn k hx hx0
  · rintro c ⟨S, hS, hc⟩
    rw [hlam]
    refine (hT.isGreatest_eigenvalues hn k).2 ⟨S.map e.symm.toLinearMap, ?_, fun x hx hx0 => ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hS]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have := hc.2 ⟨y, ⟨hy, fun h0 => hx0 (by rw [h0, map_zero])⟩, rfl⟩
      rwa [rayleighQuotient_eq] at this

/-- **Theorem 8.1.2, the min–max form**: `λ_k(A) = min_{dim(S) = n-k+1} max_{0 ≠ y ∈ S} r(y)`
(0-based: `dim S = n - k`). -/
theorem theorem_8_1_2_minmax {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : Fin n) :
    IsLeast {c | ∃ S : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ S = n - k ∧
      IsGreatest (rayleighQuotient A '' {y | y ∈ S ∧ y ≠ 0}) c} (symmEigenvalue hA k) := by
  have hT := isSymmetric_toEuclideanLin hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hlam : symmEigenvalue hA k = hT.eigenvalues hn k :=
    symmEigenvalue_eq_eigenvalues hA hT rfl hn k
  set e := euclideanEquiv n
  refine ⟨⟨(hT.eigenvectorSpan hn (Finset.Ici k)).map e.toLinearMap, ?_, ?_, ?_⟩, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  · refine ⟨e (hT.eigenvectorBasis hn k), ⟨Submodule.mem_map_of_mem
      (hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Ici.mpr le_rfl)), ?_⟩, ?_⟩
    · simpa using hT.eigenvectorBasis_ne_zero hn k
    · rw [hlam, rayleighQuotient_eq, ← hT.rayleighQuotient_eigenvectorBasis hn k]
      rfl
  · rintro _ ⟨y, ⟨hyS, hy0⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyS
    rw [hlam, rayleighQuotient_eq]
    have hx0 : x ≠ 0 := fun h0 => hy0 (by rw [h0, map_zero])
    exact hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn k hx hx0
  · rintro c ⟨S, hS, hc⟩
    rw [hlam]
    refine (hT.isLeast_eigenvalues hn k).2 ⟨S.map e.symm.toLinearMap, ?_, fun x hx hx0 => ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hS]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have := hc.2 ⟨y, ⟨hy, fun h0 => hx0 (by rw [h0, map_zero])⟩, rfl⟩
      rwa [rayleighQuotient_eq] at this

/-- **§8.1.1, last sentence**: a symmetric positive definite `A` has `λ_n(A) > 0`, hence all
`λ_k(A) > 0`. -/
theorem symmEigenvalue_pos_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hP : A.PosDef) (k : Fin n) : 0 < symmEigenvalue hA k := by
  obtain ⟨i, hi⟩ : symmEigenvalue hA k ∈ Set.range hP.isHermitian.eigenvalues := by
    rw [← hP.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact symmEigenvalue_mem_spectrum hA k
  rw [← hi]
  exact hP.eigenvalues_pos i

/-- **Theorem 8.1.3 (Gershgorin).** For orthogonal `Q` with `Qᵀ A Q = D + F`, `D = diag(d)` and `F`
with zero diagonal, `λ(A) ⊆ ⋃ᵢ [dᵢ - rᵢ, dᵢ + rᵢ]` with `rᵢ = ∑ⱼ |f_ij|`. Chapter 7's Theorem 7.2.1
for the complexifications, whose discs meet the real line in these intervals. (The book assumes `A`
symmetric, which makes `λ(A)` real; the inclusion of the real eigenvalues holds for every `A`.) -/
theorem theorem_8_1_3 {A Q F : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (h : Qᵀ * A * Q = diagonal d + F) (hF : ∀ i, F i i = 0) :
    spectrum ℝ A ⊆ ⋃ i, Set.Icc (d i - ∑ j, |F i j|) (d i + ∑ j, |F i j|) := by
  intro μ hμ
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hQ
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det Q).2 (isUnit_det_of_left_inverse hQQ)
  have hinv : Q⁻¹ = Qᵀ := inv_eq_left_inv hQQ
  have hc : (complexify Q)⁻¹ * complexify A * complexify Q =
      diagonal (fun i => (d i : ℂ)) + complexify F := by
    rw [← complexify_inv, ← complexify_mul, ← complexify_mul, hinv, h, complexify_add]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hsub := GolubVanLoan.Chapter07.theorem_7_2_1 ((isUnit_complexify_iff Q).2 hQu) hc
    (fun i => by simp [hF i])
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub ((ofReal_mem_spectrum_complexify_iff A μ).2 hμ))
  rw [Metric.mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hi
  simp only [complexify_apply, Complex.norm_real, Real.norm_eq_abs] at hi
  obtain ⟨h1, h2⟩ := abs_le.1 hi
  exact Set.mem_iUnion.2 ⟨i, ⟨by linarith, by linarith⟩⟩

/-! ### §8.1.2 Eigenvalue sensitivity -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Theorem 8.1.4 (Wielandt–Hoffman).** For symmetric `A` and `E`,
`∑_k (λ_k(A + E) - λ_k(A))² ≤ ‖E‖_F²`. -/
theorem theorem_8_1_4 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hAE : (A + E).IsSymm) :
    ∑ k, (symmEigenvalue hAE k - symmEigenvalue hA k) ^ 2 ≤ ‖E‖ ^ 2 := by
  have h := IsHermitian.hoffman_wielandt (isHermitian_iff_isSymm.2 hAE)
    (isHermitian_iff_isSymm.2 hA)
  rw [add_sub_cancel_left] at h
  refine le_of_eq_of_le ?_ h
  exact (Equiv.sum_comp (finCongr (Fintype.card_fin n).symm)
    (fun j => ((isHermitian_iff_isSymm.2 hAE).eigenvalues₀ j -
      (isHermitian_iff_isSymm.2 hA).eigenvalues₀ j) ^ 2))

end Frobenius

/-- The trace is the sum of the `λ_k(A)`. -/
theorem trace_eq_sum_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.trace = ∑ k, symmEigenvalue hA k := by
  rw [(isHermitian_iff_isSymm.2 hA).trace_eq_sum_eigenvalues₀]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact (Equiv.sum_comp (finCongr (Fintype.card_fin n).symm) _).symm

/-- **Theorem 8.1.5.** For symmetric `A`, `E` (`n > 0`) and every `k`,
`λ_k(A) + λ_n(E) ≤ λ_k(A + E) ≤ λ_k(A) + λ_1(E)`. -/
theorem theorem_8_1_5 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hE : E.IsSymm)
    (hAE : (A + E).IsSymm) (hn : 0 < n) (k : Fin n) :
    symmEigenvalue hA k + symmEigenvalue hE ⟨n - 1, by omega⟩ ≤ symmEigenvalue hAE k ∧
      symmEigenvalue hAE k ≤ symmEigenvalue hA k + symmEigenvalue hE ⟨0, hn⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hTA := isSymmetric_toEuclideanLin hA
  have hTE := isSymmetric_toEuclideanLin hE
  have hTAE : (toEuclideanLin A + toEuclideanLin E).IsSymmetric := hTA.add hTE
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 :=
    finrank_euclideanSpace_fin
  have h := hTA.eigenvalues_add_mem_Icc hTE hTAE hm k
  have hlast : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  have hzero : (⟨0, hn⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp)
  simp only [hlast, hzero, symmEigenvalue_eq_eigenvalues hA hTA rfl hm,
    symmEigenvalue_eq_eigenvalues hE hTE rfl hm,
    symmEigenvalue_eq_eigenvalues hAE hTAE (map_add _ _ _) hm]
  exact h

/-- **Corollary 8.1.6 (Weyl).** For symmetric `A` and `E`, `|λ_k(A + E) - λ_k(A)| ≤ ‖E‖₂`. -/
theorem corollary_8_1_6 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hE : E.IsSymm)
    (hAE : (A + E).IsSymm) (k : Fin n) :
    |symmEigenvalue hAE k - symmEigenvalue hA k| ≤ lpOpNorm 2 E := by
  have hn : 0 < n := Fin.pos k
  have h := theorem_8_1_5 hA hE hAE hn k
  have hnorm := (l2_opNorm_eq_max_abs_symmEigenvalue hE hn).2
  have h1 : |symmEigenvalue hE ⟨0, hn⟩| ≤ lpOpNorm 2 E := hnorm ▸ le_max_left _ _
  have h2 : |symmEigenvalue hE ⟨n - 1, by omega⟩| ≤ lpOpNorm 2 E := hnorm ▸ le_max_right _ _
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Theorem 8.1.7 (interlacing).** For symmetric `A` and `r + 1 ≤ n`, with `A_r = A(1:r, 1:r)`,
`λ_{k+1}(A_{r+1}) ≤ λ_k(A_r) ≤ λ_k(A_{r+1})` for every `k < r` (0-based). -/
theorem theorem_8_1_7 {A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ} (hr : r + 1 ≤ n)
    (hAr : (A.submatrix (Fin.castLE (by omega : r ≤ n)) (Fin.castLE (by omega))).IsSymm)
    (hAr1 : (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).IsSymm) (k : Fin r) :
    symmEigenvalue hAr1 k.succ ≤ symmEigenvalue hAr k ∧
      symmEigenvalue hAr k ≤ symmEigenvalue hAr1 k.castSucc := by
  have hsub : (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (Fin.castLE (by omega : r ≤ n)) (Fin.castLE (by omega)) := by
    ext i j; rfl
  have h := (isHermitian_iff_isSymm.2 hAr1).sortedEigenvalues_submatrix_castSucc_interlace
    (hsub ▸ isHermitian_iff_isSymm.2 hAr) k
  rw [IsHermitian.sortedEigenvalues_congr hsub _ (isHermitian_iff_isSymm.2 hAr)] at h
  exact h

/-- The case `τ ≥ 0` of Theorem 8.1.8, in the form of the backbone's rank-one interlacing. -/
private theorem rankOne_interlace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) (hB : (A + τ • vecMulVec c c).IsSymm) (i : Fin n) :
    symmEigenvalue hA i ≤ symmEigenvalue hB i ∧
      ∀ hi : (i : ℕ) + 1 < n, symmEigenvalue hB ⟨i + 1, hi⟩ ≤ symmEigenvalue hA i := by
  have hTA := isSymmetric_toEuclideanLin hA
  have hTB := isSymmetric_toEuclideanLin hB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hsub : toEuclideanLin (A + τ • vecMulVec c c) - toEuclideanLin A =
      toEuclideanLin (τ • vecMulVec c c) := by
    rw [map_add, add_sub_cancel_left]
  have hpos : (toEuclideanLin (A + τ • vecMulVec c c) - toEuclideanLin A).IsPositive := by
    rw [hsub, isPositive_toEuclideanLin_iff]
    simpa using (posSemidef_vecMulVec_self_star c).smul hτ
  have hrank : Module.finrank ℝ (LinearMap.range
      (toEuclideanLin (A + τ • vecMulVec c c) - toEuclideanLin A)) ≤ 1 := by
    have hc : star c = c := funext fun i => by simp
    have := Matrix.finrank_range_toEuclideanLin_smul_vecMulVec_le τ c
    rw [hc] at this
    rw [hsub]
    exact this
  simp only [symmEigenvalue_eq_eigenvalues hA hTA rfl hn,
    symmEigenvalue_eq_eigenvalues hB hTB rfl hn]
  refine ⟨hTA.eigenvalues_le_of_re_inner_le hTB hn (fun x => ?_) i, fun hi =>
    (hTA.eigenvalues_le_of_isPositive_sub_of_finrank_range_le hTB hn hpos hrank i hi).1⟩
  have := hpos.2 x
  rw [LinearMap.sub_apply, inner_sub_left, map_sub] at this
  linarith

/-- **Theorem 8.1.8.** For symmetric `A`, `c ∈ ℝⁿ`, `τ ∈ ℝ` and `B = A + τ ccᵀ`: if `τ ≥ 0` then
`λ_i(B) ∈ [λ_i(A), λ_{i-1}(A)]` for `i = 2:n` (and `λ_1(A) ≤ λ_1(B)`); if `τ ≤ 0` then
`λ_i(B) ∈ [λ_{i+1}(A), λ_i(A)]` for `i = 1:n-1` (and `λ_n(B) ≤ λ_n(A)`). 0-based indices; the
book's normalization `‖c‖₂ = 1` is not needed. -/
theorem theorem_8_1_8 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (c : Fin n → ℝ) (τ : ℝ)
    (hB : (A + τ • vecMulVec c c).IsSymm) :
    (0 ≤ τ → ∀ i : Fin n, symmEigenvalue hA i ≤ symmEigenvalue hB i ∧
        ∀ hi : 1 ≤ (i : ℕ), symmEigenvalue hB i ≤ symmEigenvalue hA ⟨i - 1, by omega⟩) ∧
      (τ ≤ 0 → ∀ i : Fin n, symmEigenvalue hB i ≤ symmEigenvalue hA i ∧
        ∀ hi : (i : ℕ) + 1 < n, symmEigenvalue hA ⟨i + 1, hi⟩ ≤ symmEigenvalue hB i) := by
  refine ⟨fun hτ i => ⟨(rankOne_interlace hA c hτ hB i).1, fun hi => ?_⟩, fun hτ i => ?_⟩
  · have := (rankOne_interlace hA c hτ hB ⟨i - 1, by omega⟩).2
      (by have := i.isLt; simp only; omega)
    convert this using 2
    ext
    simp only
    omega
  · have hBA : (A + τ • vecMulVec c c) + (-τ) • vecMulVec c c = A := by
      rw [neg_smul, add_neg_cancel_right]
    have hA' : ((A + τ • vecMulVec c c) + (-τ) • vecMulVec c c).IsSymm := by rw [hBA]; exact hA
    have h := rankOne_interlace hB c (neg_nonneg.2 hτ) hA' i
    rw [symmEigenvalue_eq_sortedEigenvalues hA' (by rw [hBA]; exact isHermitian_iff_isSymm.2 hA),
      IsHermitian.sortedEigenvalues_congr hBA _ (isHermitian_iff_isSymm.2 hA)] at h
    exact ⟨h.1, fun hi => h.2 hi⟩

/-- **Theorem 8.1.8, last clause.** With `cᵀc = 1` (and `n ≥ 1`), there are `m_i ≥ 0` with
`∑ m_i = 1` and `λ_i(B) = λ_i(A) + m_i τ` for all `i`. -/
theorem theorem_8_1_8_b {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {c : Fin n → ℝ}
    (hc : c ⬝ᵥ c = 1) (τ : ℝ) (hB : (A + τ • vecMulVec c c).IsSymm) (hn : 0 < n) :
    ∃ m : Fin n → ℝ, (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 1 ∧
      ∀ i, symmEigenvalue hB i = symmEigenvalue hA i + m i * τ := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · have hBA : A + (0 : ℝ) • vecMulVec c c = A := by rw [zero_smul, add_zero]
    have heq : symmEigenvalue hB = symmEigenvalue hA :=
      IsHermitian.sortedEigenvalues_congr hBA _ _
    refine ⟨Pi.single ⟨0, hn⟩ 1, fun i => ?_, by simp, fun i => by rw [heq]; simp⟩
    by_cases h : i = ⟨0, hn⟩ <;> simp [h]
  · have h8 := theorem_8_1_8 hA c τ hB
    refine ⟨fun i => (symmEigenvalue hB i - symmEigenvalue hA i) / τ, fun i => ?_, ?_,
      fun i => ?_⟩
    · rcases hτ.lt_or_gt with h | h
      · exact div_nonneg_of_nonpos (by linarith [(h8.2 h.le i).1]) h.le
      · exact div_nonneg (by linarith [(h8.1 h.le i).1]) h.le
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← trace_eq_sum_symmEigenvalue,
        ← trace_eq_sum_symmEigenvalue, trace_add, trace_smul, trace_vecMulVec, hc, smul_eq_mul,
        mul_one, add_sub_cancel_left, div_self hτ]
    · rw [div_mul_cancel₀ _ hτ]
      ring

/-! ### §8.1.3 Invariant subspaces -/

/-- If the range of `Q₁` (orthonormal columns) is `A`-invariant, then `A Q₁ = Q₁ (Q₁ᵀ A Q₁)`. -/
private theorem mul_eq_mul_of_invariant {A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} (hQ : Q₁ᵀ * Q₁ = 1)
    (hinv : ∀ x ∈ LinearMap.range (toLin' Q₁), A *ᵥ x ∈ LinearMap.range (toLin' Q₁)) :
    A * Q₁ = Q₁ * (Q₁ᵀ * A * Q₁) := by
  refine toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨y, hy⟩ := hinv _ ⟨v, rfl⟩
  simp only [toLin'_apply] at hy
  simp only [toLin'_apply, ← mulVec_mulVec, Matrix.mul_assoc]
  rw [← hy]
  congr 1
  rw [mulVec_mulVec, hQ, one_mulVec]

/-- **Theorem 8.1.9 with (8.1.1).** If `A` is symmetric, `Q = [Q₁ Q₂]` is orthogonal and
`ran(Q₁)` is `A`-invariant, then `Qᵀ A Q = diag(D₁, D₂)` with `D₁ = Q₁ᵀ A Q₁`, `D₂ = Q₂ᵀ A Q₂`, and
`λ(A) = λ(D₁) ∪ λ(D₂)` with multiplicity: `det(A - λI) = det(D₁ - λI) det(D₂ - λI)`. -/
theorem theorem_8_1_9 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r s : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1) (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᵀ = 1)
    (hinv : ∀ x ∈ LinearMap.range (toLin' Q₁), A *ᵥ x ∈ LinearMap.range (toLin' Q₁)) :
    (fromCols Q₁ Q₂)ᵀ * A * fromCols Q₁ Q₂ = fromBlocks (Q₁ᵀ * A * Q₁) 0 0 (Q₂ᵀ * A * Q₂) ∧
      A.charpoly = (Q₁ᵀ * A * Q₁).charpoly * (Q₂ᵀ * A * Q₂).charpoly := by
  have hH := isHermitian_iff_isSymm.2 hA
  have hQ₁ : Q₁ᵀ * Q₁ = 1 := by
    have h := hQ
    rw [transpose_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at h
    exact h.1
  have hAQ := mul_eq_mul_of_invariant hQ₁ hinv
  simp only [← conjTranspose_eq_transpose_of_trivial] at hQ hQ' ⊢
  exact ⟨hH.conjTranspose_mul_mul_fromCols_eq_fromBlocks hQ hAQ,
    hH.charpoly_eq_mul_of_mul_eq_mul hQ hQ' hAQ⟩

/-- **(8.1.2), the separation** of the spectra of two symmetric matrices,
`sep(B, C) = min_{λ ∈ λ(B), μ ∈ λ(C)} |λ - μ|`. -/
noncomputable def sepSymm {p q : ℕ} (B : Matrix (Fin p) (Fin p) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  sInf {d | ∃ l ∈ spectrum ℝ B, ∃ m ∈ spectrum ℝ C, d = |l - m|}

/-- **P8.1.9**: for symmetric `B`, `C`, the Sylvester separation
`min_{X ≠ 0} ‖BX - XC‖_F / ‖X‖_F` of chapter 7 is the eigenvalue gap (8.1.2). -/
theorem sepSymm_eq_sep {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}
    (hB : B.IsSymm) (hC : C.IsSymm) (hp : 0 < p) (hq : 0 < q) : sep B C = sepSymm B C := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hB' := isHermitian_iff_isSymm.2 hB
  have hC' := isHermitian_iff_isSymm.2 hC
  rw [hB'.sep_eq_iInf_abs_eigenvalues_sub hC', sepSymm, hB'.spectrum_real_eq_range_eigenvalues,
    hC'.spectrum_real_eq_range_eigenvalues]
  have hbdd : ∀ i, BddBelow (Set.range fun j => |hB'.eigenvalues i - hC'.eigenvalues j|) :=
    fun i => ⟨0, by rintro _ ⟨j, rfl⟩; exact abs_nonneg _⟩
  have hbdd' : BddBelow (Set.range fun i => ⨅ j, |hB'.eigenvalues i - hC'.eigenvalues j|) :=
    ⟨0, by rintro _ ⟨i, rfl⟩; exact le_ciInf fun j => abs_nonneg _⟩
  apply le_antisymm
  · refine le_csInf ⟨_, _, ⟨⟨0, hp⟩, rfl⟩, _, ⟨⟨0, hq⟩, rfl⟩, rfl⟩ ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact (ciInf_le hbdd' i).trans (ciInf_le (hbdd i) j)
  · refine le_ciInf fun i => le_ciInf fun j => csInf_le ⟨0, ?_⟩ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    rintro _ ⟨_, _, _, _, rfl⟩
    exact abs_nonneg _

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm is invariant under `X ↦ Qᵀ X Q` for a `Q` with `Q Qᵀ = I`. -/
private theorem frobenius_norm_transpose_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix (Fin n) (Fin n) ℝ) {Q : Matrix (Fin n) ι ℝ} (hQ : Q * Qᵀ = 1) :
    ‖Qᵀ * E * Q‖ = ‖E‖ := by
  have h1 := frobenius_norm_sq_eq_trace (Qᵀ * E * Q)
  have h2 := frobenius_norm_sq_eq_trace E
  simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id] at h1 h2
  have htr : trace ((Qᵀ * E * Q)ᵀ * (Qᵀ * E * Q)) = trace (Eᵀ * E) := by
    have e : (Qᵀ * E * Q)ᵀ * (Qᵀ * E * Q) = Qᵀ * (Eᵀ * E * Q) := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qᵀ, hQ, Matrix.one_mul]
    rw [e, trace_mul_comm, Matrix.mul_assoc (Eᵀ * E) Q Qᵀ, hQ, Matrix.mul_one]
  rw [htr, ← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- A symmetric positive semidefinite matrix has a symmetric square root. -/
private theorem exists_isSymm_mul_self_eq {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    (hpos : M.PosSemidef) : ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsSymm ∧ S * S = M := by
  obtain ⟨V, hV, hVM, -⟩ := theorem_8_1_1 hM
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hV
  have hVV' : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hV
  have hnn : ∀ k, 0 ≤ symmEigenvalue hM k := fun k => by
    obtain ⟨i, hi⟩ : symmEigenvalue hM k ∈ Set.range hpos.isHermitian.eigenvalues := by
      rw [← hpos.isHermitian.spectrum_real_eq_range_eigenvalues]
      exact symmEigenvalue_mem_spectrum hM k
    rw [← hi]
    exact hpos.eigenvalues_nonneg i
  have hMe : M = V * diagonal (symmEigenvalue hM) * Vᵀ := by
    rw [← hVM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVV, Matrix.one_mul, Matrix.mul_assoc,
      hVV, Matrix.mul_one]
  refine ⟨V * diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * Vᵀ, ?_, ?_⟩
  · rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc]
  · refine (?_ : _ = V * diagonal (symmEigenvalue hM) * Vᵀ).trans hMe.symm
    have : diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) *
        diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) = diagonal (symmEigenvalue hM) := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext k
      exact Real.mul_self_sqrt (hnn k)
    calc V * diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * Vᵀ *
          (V * diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * Vᵀ)
        = V * (diagonal (fun k => Real.sqrt (symmEigenvalue hM k)) * (Vᵀ * V) *
            diagonal (fun k => Real.sqrt (symmEigenvalue hM k))) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = V * diagonal (symmEigenvalue hM) * Vᵀ := by rw [hVV', Matrix.mul_one, this]

/-- **Theorem 8.1.10.** Let `A` be symmetric (`E` need not be), `Q = [Q₁ Q₂]` orthogonal with
`Qᵀ A Q = diag(D₁, D₂)` (so `ran(Q₁)` is `A`-invariant), `Qᵀ E Q = [E₁₁ E₂₁ᵀ; E₂₁ E₂₂]`. If
`sep(D₁, D₂) > 0` and `‖E‖_F ≤ sep(D₁, D₂)/5`, there is `P` with
`‖P‖_F ≤ (4/sep(D₁, D₂)) ‖E₂₁‖_F` such that the columns of `Q̂₁ = (Q₁ + Q₂P)(I + PᵀP)^{-1/2}` are
orthonormal and span an `(A + E)`-invariant subspace. The square root is any symmetric
`S` with `S² = I + PᵀP` (one exists). -/
theorem theorem_8_1_10 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r s : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1) (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᵀ = 1)
    {D₁ : Matrix (Fin r) (Fin r) ℝ} {D₂ : Matrix (Fin s) (Fin s) ℝ}
    (hAQ : (fromCols Q₁ Q₂)ᵀ * A * fromCols Q₁ Q₂ = fromBlocks D₁ 0 0 D₂)
    (hsep : 0 < sepSymm D₁ D₂) (hEsmall : ‖E‖ ≤ sepSymm D₁ D₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℝ,
      ‖P‖ ≤ 4 / sepSymm D₁ D₂ * ‖((fromCols Q₁ Q₂)ᵀ * E * fromCols Q₁ Q₂).toBlocks₂₁‖ ∧
      (∃ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm ∧ S * S = 1 + Pᵀ * P) ∧
      ∀ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm → S * S = 1 + Pᵀ * P →
        ((Q₁ + Q₂ * P) * S⁻¹)ᵀ * ((Q₁ + Q₂ * P) * S⁻¹) = 1 ∧
          ∃ M : Matrix (Fin r) (Fin r) ℝ, (A + E) * ((Q₁ + Q₂ * P) * S⁻¹) =
            ((Q₁ + Q₂ * P) * S⁻¹) * M := by
  set Q := fromCols Q₁ Q₂
  set E' := Qᵀ * E * Q
  -- the diagonal blocks are symmetric, hence both nonempty since `sep > 0`
  have hQAQs : (Qᵀ * A * Q).IsSymm := by
    simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_iff_isSymm.1
      (isHermitian_conjTranspose_mul_mul Q (isHermitian_iff_isSymm.2 hA))
  have hD₁ : D₁.IsSymm := by
    have := hQAQs.eq
    rw [hAQ, fromBlocks_transpose, fromBlocks_inj] at this
    exact this.1
  have hD₂ : D₂.IsSymm := by
    have := hQAQs.eq
    rw [hAQ, fromBlocks_transpose, fromBlocks_inj] at this
    exact this.2.2.2
  have hr : 0 < r := by
    by_contra h0
    have : spectrum ℝ D₁ = ∅ := by
      rw [spectrum_eq_range_symmEigenvalue hD₁, Set.range_eq_empty_iff]
      exact ⟨fun k => absurd k.isLt (by omega)⟩
    simp [sepSymm, this] at hsep
  have hs : 0 < s := by
    by_contra h0
    have : spectrum ℝ D₂ = ∅ := by
      rw [spectrum_eq_range_symmEigenvalue hD₂, Set.range_eq_empty_iff]
      exact ⟨fun k => absurd k.isLt (by omega)⟩
    simp [sepSymm, this] at hsep
  have hsepeq : sep D₁ D₂ = sepSymm D₁ D₂ := sepSymm_eq_sep hD₁ hD₂ hr hs
  have hE' : ‖E'‖ = ‖E‖ := frobenius_norm_transpose_mul_mul E hQ'
  obtain ⟨P, hPn, hPeq⟩ := exists_invariant_graph_of_sep (𝕜 := ℝ) (T₁₁ := D₁)
    (T₁₂ := (0 : Matrix (Fin r) (Fin s) ℝ)) (T₂₂ := D₂) (E := E') (by rw [hsepeq]; exact hsep)
    (by rw [norm_zero, mul_zero, zero_div, add_zero, mul_one, hE', hsepeq]; exact hEsmall)
  have hQQ := hQ
  rw [transpose_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at hQQ
  obtain ⟨h11, h12, h21, h22⟩ := hQQ
  -- `Q [I; P] = Q₁ + Q₂ P`
  have hW : Q * fromRows 1 P = Q₁ + Q₂ * P := by
    simp only [Q, fromCols_mul_fromRows, Matrix.mul_one]
  set M := D₁ + E'.toBlocks₁₁ + (0 + E'.toBlocks₁₂) * P
  have hQAEQ : Qᵀ * (A + E) * Q = fromBlocks D₁ 0 0 D₂ + E' := by
    rw [← hAQ]
    simp only [E', Matrix.mul_add, Matrix.add_mul]
  have hinv : (A + E) * (Q₁ + Q₂ * P) = (Q₁ + Q₂ * P) * M := by
    calc (A + E) * (Q₁ + Q₂ * P) = Q * (Qᵀ * (A + E) * Q) * fromRows 1 P := by
          rw [← hW]
          simp only [← Matrix.mul_assoc]
          rw [hQ', Matrix.one_mul]
      _ = (Q₁ + Q₂ * P) * M := by
          rw [hQAEQ, Matrix.mul_assoc, hPeq, ← Matrix.mul_assoc, hW]
  have hWW : (Q₁ + Q₂ * P)ᵀ * (Q₁ + Q₂ * P) = 1 + Pᵀ * P := by
    simp only [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    rw [h11, ← Matrix.mul_assoc Q₁ᵀ Q₂ P, h12, h21, ← Matrix.mul_assoc Q₂ᵀ Q₂ P, h22]
    simp
  have hMsymm : (1 + Pᵀ * P).IsSymm := by
    rw [IsSymm, transpose_add, transpose_one, transpose_mul, transpose_transpose]
  have hMpos : (1 + Pᵀ * P).PosSemidef := by
    have := PosSemidef.one.add (posSemidef_conjTranspose_mul_self P)
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hMdef : (1 + Pᵀ * P).PosDef := by
    have := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P)
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨P, by rw [hsepeq] at hPn; rw [div_mul_eq_mul_div]; exact hPn,
    exists_isSymm_mul_self_eq hMsymm hMpos, fun S hS hSS => ?_⟩
  have hSdet : IsUnit S.det := by
    have h := hMdef.det_pos
    rw [← hSS, det_mul] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
  have hSi : S⁻¹ * S = 1 := nonsing_inv_mul S hSdet
  have hSi' : S * S⁻¹ = 1 := mul_nonsing_inv S hSdet
  have hSt : (S⁻¹)ᵀ = S⁻¹ := by rw [transpose_nonsing_inv, hS.eq]
  refine ⟨?_, S * M * S⁻¹, ?_⟩
  · rw [transpose_mul, hSt, Matrix.mul_assoc, ← Matrix.mul_assoc (Q₁ + Q₂ * P)ᵀ, hWW, ← hSS,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSi, Matrix.one_mul, hSi']
  · rw [← Matrix.mul_assoc, hinv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S, hSi, Matrix.one_mul]

open scoped MatrixOrder in
/-- **(8.1.3)**: for `P ∈ ℝ^{s×r}`, `‖P (I + PᵀP)^{-1/2}‖₂ ≤ ‖P‖₂ ≤ ‖P‖_F` (the bound used for
Corollary 8.1.11), the square root being `CFC.sqrt`. -/
theorem equation_8_1_3 {r s : ℕ} (P : Matrix (Fin s) (Fin r) ℝ) :
    lpOpNorm 2 (P * (CFC.sqrt (1 + Pᵀ * P))⁻¹) ≤ lpOpNorm 2 P ∧ lpOpNorm 2 P ≤ ‖P‖ := by
  have h := l2_opNorm_mul_inv_sqrt_one_add_gram_le P
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- For a square orthogonal `Q` (rows `Fin n`, columns any `ι`), the distance between the column
spaces of `Q M` and `Q N` is the gap between those of `M` and `N`: `Q` is an isometry of the
coordinate spaces. -/
private theorem subspaceDist_range_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Q : Matrix (Fin n) ι ℝ} (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1)
    (M N : Matrix ι κ ℝ) :
    Chapter02.subspaceDist (LinearMap.range (toEuclideanLin (Q * M)))
        (LinearMap.range (toEuclideanLin (Q * N))) =
      (LinearMap.range (toEuclideanLin M)).gap (LinearMap.range (toEuclideanLin N)) := by
  have hQh : Qᴴ * Q = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hQh' : Q * Qᴴ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  simp only [Chapter02.subspaceDist, range_mul_eq_map_of_mul_conjTranspose_eq_one hQh hQh']
  rw [Submodule.gap_map_linearIsometryEquiv]

/-- **Corollary 8.1.11.** "If the conditions of the theorem hold, then
`dist(ran(Q₁), ran(Q̂₁)) ≤ (4/sep(D₁, D₂)) ‖E₂₁‖_F`", for the `P` and `Q̂₁ = (Q₁ + Q₂P) S⁻¹` of
Theorem 8.1.10 (`theorem_8_1_10`, whose conclusions are repeated), `dist` being chapter 2's
`subspaceDist` of the column spaces. `ran Q̂₁ = ran(Q₁ + Q₂P) = ran(Q [I; P])` and
`ran Q₁ = ran(Q [I; 0])`; in the coordinates of `Q` their distance is at most `‖P‖₂ ≤ ‖P‖_F`
(`Matrix.gap_range_fromRows_le` and (8.1.3)), so the book's route through
`dist = ‖Q₂ᵀ Q̂₁‖₂ = ‖P (I + PᵀP)^{-1/2}‖₂` is not needed. -/
theorem corollary_8_1_11 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r s : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols Q₁ Q₂)ᵀ * fromCols Q₁ Q₂ = 1) (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᵀ = 1)
    {D₁ : Matrix (Fin r) (Fin r) ℝ} {D₂ : Matrix (Fin s) (Fin s) ℝ}
    (hAQ : (fromCols Q₁ Q₂)ᵀ * A * fromCols Q₁ Q₂ = fromBlocks D₁ 0 0 D₂)
    (hsep : 0 < sepSymm D₁ D₂) (hEsmall : ‖E‖ ≤ sepSymm D₁ D₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℝ,
      ‖P‖ ≤ 4 / sepSymm D₁ D₂ * ‖((fromCols Q₁ Q₂)ᵀ * E * fromCols Q₁ Q₂).toBlocks₂₁‖ ∧
      (∃ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm ∧ S * S = 1 + Pᵀ * P) ∧
      ∀ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm → S * S = 1 + Pᵀ * P →
        ((Q₁ + Q₂ * P) * S⁻¹)ᵀ * ((Q₁ + Q₂ * P) * S⁻¹) = 1 ∧
        (∃ M : Matrix (Fin r) (Fin r) ℝ, (A + E) * ((Q₁ + Q₂ * P) * S⁻¹) =
          ((Q₁ + Q₂ * P) * S⁻¹) * M) ∧
        Chapter02.subspaceDist (LinearMap.range (toEuclideanLin Q₁))
            (LinearMap.range (toEuclideanLin ((Q₁ + Q₂ * P) * S⁻¹))) ≤
          4 / sepSymm D₁ D₂ * ‖((fromCols Q₁ Q₂)ᵀ * E * fromCols Q₁ Q₂).toBlocks₂₁‖ := by
  obtain ⟨P, hP, hS, h⟩ := theorem_8_1_10 hA hQ hQ' hAQ hsep hEsmall
  refine ⟨P, hP, hS, fun S hSs hSS => ⟨(h S hSs hSS).1, (h S hSs hSS).2, ?_⟩⟩
  -- `S` is invertible, so `ran Q̂₁ = ran(Q₁ + Q₂ P)`
  have hSu : IsUnit S.det := by
    have hM : (1 + Pᵀ * P).PosDef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using
        PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P)
    have h2 := (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [← hSS, det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hrange : LinearMap.range (toEuclideanLin ((Q₁ + Q₂ * P) * S⁻¹)) =
      LinearMap.range (toEuclideanLin (Q₁ + Q₂ * P)) := by
    rw [toEuclideanLin_mul]
    refine LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 fun y => ?_)
    refine ⟨toEuclideanLin S y, ?_⟩
    rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ hSu, toEuclideanLin_one_apply]
  have h₁ : Q₁ = fromCols Q₁ Q₂ * fromRows (1 : Matrix (Fin r) (Fin r) ℝ) 0 := by
    rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have h₂ : Q₁ + Q₂ * P = fromCols Q₁ Q₂ * fromRows 1 P := by
    rw [fromCols_mul_fromRows, Matrix.mul_one]
  have hd := subspaceDist_range_mul hQ hQ' (fromRows (1 : Matrix (Fin r) (Fin r) ℝ) 0)
    (fromRows 1 P)
  rw [← h₁, ← h₂] at hd
  rw [hrange, hd]
  exact (gap_range_fromRows_le P).trans ((equation_8_1_3 P).2.trans hP)

/-- A column `x` with `xᵀ x = 1` is a unit vector. -/
private theorem norm_toLp_eq_one_of_transpose_mul_self {x : Fin n → ℝ}
    (h : (replicateCol (Fin 1) x)ᵀ * replicateCol (Fin 1) x = 1) : ‖WithLp.toLp 2 x‖ = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  simp only [mul_apply, transpose_apply, replicateCol_apply, one_apply_eq] at h00
  have h2 : ‖WithLp.toLp 2 x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [sq] using h00
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h2, one_pow])

/-- For unit vectors `q`, `u`, `sin θ(q, span{u}) = √(1 − ⟪u, q⟫²)` (Pythagoras). -/
private theorem sinAngle_span_singleton_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {q u : E} (hq : ‖q‖ = 1) (hu : ‖u‖ = 1) :
    (ℝ ∙ u).sinAngle q = √(1 - inner ℝ u q ^ 2) := by
  have hP : (ℝ ∙ u).starProjection q = inner ℝ u q • u := by
    rw [Submodule.starProjection_singleton, hu, one_pow, RCLike.ofReal_one, div_one]
  have h := Submodule.norm_starProjection_sq_add_norm_sub_sq (ℝ ∙ u) q
  rw [hP, norm_smul, hu, mul_one, hq, Real.norm_eq_abs, sq_abs] at h
  rw [Submodule.sinAngle, hq, div_one, hP,
    show 1 - inner ℝ u q ^ 2 = ‖q - inner ℝ u q • u‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg _)]

/-- **The distance between two lines**: for unit `u`, `v`,
`dist(span{u}, span{v}) = √(1 − (uᵀv)²)`. -/
private theorem subspaceDist_span_singleton {u v : Fin n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1)
    (hv : ‖WithLp.toLp 2 v‖ = 1) :
    Chapter02.subspaceDist (ℝ ∙ WithLp.toLp 2 u) (ℝ ∙ WithLp.toLp 2 v) = √(1 - (u ⬝ᵥ v) ^ 2) := by
  have hi : inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 u) = u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
  rw [Chapter02.subspaceDist, Submodule.gap_span_singleton_eq_sinAngle hu hv,
    sinAngle_span_singleton_eq hu hv, hi]

/-- **Theorem 8.1.12** (eigenvector perturbation). "Suppose `A` and `A + E` are `n`-by-`n`
symmetric matrices and that `Q = [q₁ | Q₂]` is an orthogonal matrix such that `q₁` is an
eigenvector for `A`. Partition `QᵀAQ = [λ 0; 0 D₂]`, `QᵀEQ = [ε eᵀ; e E₂₂]`. If
`d = min_{μ ∈ λ(D₂)} |λ − μ| > 0` and `‖E‖_F ≤ d/5`, then there exists `p ∈ ℝ^{n−1}` satisfying
`‖p‖₂ ≤ (4/d)‖e‖₂` such that `q̂₁ = (q₁ + Q₂p)/√(1 + pᵀp)` is a unit 2-norm eigenvector for
`A + E`. Moreover, `dist(span{q₁}, span{q̂₁}) = √(1 − (q₁ᵀq̂₁)²) ≤ (4/d)‖e‖₂`." Here `Q₂` has `s`
columns, `e` is the first column of the `(2,1)` block of `QᵀEQ` (symmetry of `E` is not needed),
and `dist` is chapter 2's `subspaceDist`. The case `r = 1` of Theorem 8.1.10 and Corollary 8.1.11,
where `d = sep((λ), D₂)` and the square root of `1 + pᵀp` is a scalar. -/
theorem theorem_8_1_12 {A E : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {s : ℕ}
    {q₁ : Fin n → ℝ} {Q₂ : Matrix (Fin n) (Fin s) ℝ}
    (hQ : (fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ * fromCols (replicateCol (Fin 1) q₁) Q₂ = 1)
    (hQ' : fromCols (replicateCol (Fin 1) q₁) Q₂ * (fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ = 1)
    {l : ℝ} {D₂ : Matrix (Fin s) (Fin s) ℝ}
    (hAQ : (fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ * A * fromCols (replicateCol (Fin 1) q₁) Q₂ =
      fromBlocks !![l] 0 0 D₂)
    {e : Fin s → ℝ} (he : replicateCol (Fin 1) e =
      ((fromCols (replicateCol (Fin 1) q₁) Q₂)ᵀ * E *
        fromCols (replicateCol (Fin 1) q₁) Q₂).toBlocks₂₁)
    {d : ℝ} (hd : d = sInf {x | ∃ μ ∈ spectrum ℝ D₂, x = |l - μ|}) (hd0 : 0 < d)
    (hE : ‖E‖ ≤ d / 5) :
    ∃ p : Fin s → ℝ, ‖WithLp.toLp 2 p‖ ≤ 4 / d * ‖WithLp.toLp 2 e‖ ∧
      ∀ qh₁ : Fin n → ℝ, qh₁ = (√(1 + p ⬝ᵥ p))⁻¹ • (q₁ + Q₂ *ᵥ p) →
        ‖WithLp.toLp 2 qh₁‖ = 1 ∧ (∃ μ : ℝ, (A + E) *ᵥ qh₁ = μ • qh₁) ∧
        Chapter02.subspaceDist (ℝ ∙ WithLp.toLp 2 q₁) (ℝ ∙ WithLp.toLp 2 qh₁) =
          √(1 - (q₁ ⬝ᵥ qh₁) ^ 2) ∧
        √(1 - (q₁ ⬝ᵥ qh₁) ^ 2) ≤ 4 / d * ‖WithLp.toLp 2 e‖ := by
  -- `d = sep((λ), D₂)`
  have hl : (!![l] : Matrix (Fin 1) (Fin 1) ℝ).IsSymm := by
    ext i j
    fin_cases i; fin_cases j; rfl
  have hspec : spectrum ℝ (!![l] : Matrix (Fin 1) (Fin 1) ℝ) = {l} := by
    have h : l = symmEigenvalue hl 0 := by
      simpa [trace_fin_one] using trace_eq_sum_symmEigenvalue hl
    rw [spectrum_eq_range_symmEigenvalue hl, Set.range_unique]
    exact congrArg (fun x : ℝ => ({x} : Set ℝ)) h.symm
  have hsep : sepSymm !![l] D₂ = d := by
    rw [hd, sepSymm, hspec]
    congr 1
    ext x
    simp
  obtain ⟨P, hP, -, h⟩ := corollary_8_1_11 hA hQ hQ' hAQ (by rwa [hsep]) (by rwa [hsep])
  have hEe : ‖replicateCol (Fin 1) e‖ = ‖WithLp.toLp 2 e‖ := frobenius_norm_replicateCol e
  rw [hsep, ← he, hEe] at hP
  set p : Fin s → ℝ := fun i => P i 0 with hp
  have hPp : P = replicateCol (Fin 1) p := by
    ext i j
    rw [Fin.fin_one_eq_zero j]
    rfl
  have hPn : ‖P‖ = ‖WithLp.toLp 2 p‖ := by
    rw [hPp]
    exact frobenius_norm_replicateCol p
  refine ⟨p, hPn ▸ hP,
    fun qh₁ hqh => ?_⟩
  -- the square root of `1 + PᵀP` is the scalar `c = √(1 + pᵀp)`
  have hpp : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
  set c := √(1 + p ⬝ᵥ p) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  have hcc : c * c = 1 + p ⬝ᵥ p := Real.mul_self_sqrt (by linarith)
  have hPP : 1 + Pᵀ * P = (1 + p ⬝ᵥ p) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp [hPp, mul_apply, dotProduct]
  set S : Matrix (Fin 1) (Fin 1) ℝ := c • 1 with hS
  have hSs : S.IsSymm := by rw [hS, IsSymm, transpose_smul, transpose_one]
  have hSS : S * S = 1 + Pᵀ * P := by
    rw [hPP, hS, Matrix.smul_mul, Matrix.one_mul, smul_smul, hcc]
  have hSinv : S⁻¹ = c⁻¹ • 1 := inv_eq_left_inv (by
    rw [hS, Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul])
  have hQh : (replicateCol (Fin 1) q₁ + Q₂ * P) * S⁻¹ = replicateCol (Fin 1) qh₁ := by
    rw [hSinv, Matrix.mul_smul, Matrix.mul_one, hqh]
    ext i j
    simp [hPp, mul_apply, mulVec, dotProduct, mul_add]
  obtain ⟨horth, ⟨M, hM⟩, hdist⟩ := h S hSs hSS
  rw [hQh] at horth hM hdist
  rw [hsep, ← he, hEe, range_toEuclideanLin_replicateCol,
    range_toEuclideanLin_replicateCol] at hdist
  -- `q₁` and `qh₁` are unit vectors
  have hQQ := hQ
  rw [transpose_fromCols, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at hQQ
  have hq₁ := norm_toLp_eq_one_of_transpose_mul_self hQQ.1
  have hqh₁ := norm_toLp_eq_one_of_transpose_mul_self horth
  have hgap := subspaceDist_span_singleton hq₁ hqh₁
  refine ⟨hqh₁, ⟨M 0 0, ?_⟩, hgap, hgap ▸ hdist⟩
  ext i
  have := congrFun (congrFun hM i) 0
  simpa [mul_apply, mulVec, dotProduct, mul_comm] using this

end Frobenius

/-! ### §8.1.4 Approximate invariant subspaces -/

/-- **Theorem 8.1.13** (paired form). "Suppose `A ∈ ℝ^{n×n}` and `S ∈ ℝ^{r×r}` are symmetric and
that `AQ₁ − Q₁S = E₁` where `Q₁ ∈ ℝ^{n×r}` satisfies `Q₁ᵀQ₁ = I_r`. Then there exist
`μ₁, …, μ_r ∈ λ(A)` such that `|μ_k − λ_k(S)| ≤ √2 ‖E₁‖₂` for `k = 1:r`." The `μ_k` are
`λ_{σ(k)}(A)` for an injection `σ`, as the book's proof produces them (Weyl's inequality pairs the
sorted eigenvalues of `A` with those of `B = diag(S, Q₂ᵀAQ₂)`, among which the eigenvalues of `S`
sit at distinct positions): the backbone's
`Matrix.IsHermitian.exists_embedding_abs_sub_le_of_mul_sub_mul`. -/
theorem theorem_8_1_13 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r : ℕ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hS : S.IsSymm) {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    (hQ : Q₁ᵀ * Q₁ = 1) :
    ∃ σ : Fin r ↪ Fin n, ∀ k, |symmEigenvalue hA (σ k) - symmEigenvalue hS k| ≤
      √2 * lpOpNorm 2 (A * Q₁ - Q₁ * S) := by
  obtain ⟨σ, hσ⟩ := (isHermitian_iff_isSymm.2 hA).exists_embedding_abs_sub_le_of_mul_sub_mul
    (isHermitian_iff_isSymm.2 hS) (by rwa [conjTranspose_eq_transpose_of_trivial]) le_rfl
  refine ⟨(finCongr (Fintype.card_fin r).symm).toEmbedding.trans
    (σ.toEmbedding.trans (finCongr (Fintype.card_fin n)).toEmbedding), fun k => ?_⟩
  have h := hσ (Fin.cast (Fintype.card_fin r).symm k)
  simp only [symmEigenvalue, IsHermitian.sortedEigenvalues_apply, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  exact h

/-- **Theorem 8.1.13, unpaired form.** For symmetric `A` and `S`, `Q₁` with `Q₁ᵀ Q₁ = I_r`, every
eigenvalue `θ` of `S` has an eigenvalue `μ` of `A` with `|μ - θ| ≤ ‖A Q₁ - Q₁ S‖₂` (constant `1`,
without the pairing of `theorem_8_1_13`). -/
theorem theorem_8_1_13_weak {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r : ℕ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hS : S.IsSymm) {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    (hQ : Q₁ᵀ * Q₁ = 1) {θ : ℝ} (hθ : θ ∈ spectrum ℝ S) :
    ∃ μ ∈ spectrum ℝ A, |μ - θ| ≤ lpOpNorm 2 (A * Q₁ - Q₁ * S) :=
  (isHermitian_iff_isSymm.2 hA).exists_mem_spectrum_abs_sub_le_of_mul_sub_mul
    (isHermitian_iff_isSymm.2 hS) (by rwa [conjTranspose_eq_transpose_of_trivial]) le_rfl hθ

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Theorem 8.1.14.** For `Q₁` with orthonormal columns, `S = Q₁ᵀ A Q₁` minimizes
`‖A Q₁ - Q₁ S‖_F`, and the minimum is `‖(I - Q₁ Q₁ᵀ) A Q₁‖_F`. -/
theorem theorem_8_1_14 (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    (hQ : Q₁ᵀ * Q₁ = 1) :
    IsLeast (Set.range fun S : Matrix (Fin r) (Fin r) ℝ => ‖A * Q₁ - Q₁ * S‖)
      ‖(1 - Q₁ * Q₁ᵀ) * A * Q₁‖ := by
  have h := isLeast_frobenius_norm_mul_sub_mul A (Q := Q₁)
    (by rwa [conjTranspose_eq_transpose_of_trivial])
  rwa [conjTranspose_eq_transpose_of_trivial] at h

end Frobenius

/-- A standard basis vector of `EuclideanSpace ℝ (Fin r)` has norm one. -/
private theorem norm_toLp_single_one {r : ℕ} (k : Fin r) :
    ‖(WithLp.toLp 2 (Pi.single k (1 : ℝ)) : EuclideanSpace ℝ (Fin r))‖ = 1 := by
  have := PiLp.norm_single (p := 2) (β := fun _ : Fin r => ℝ) k (1 : ℝ)
  rw [norm_one] at this
  exact this

/-- The residual identity behind Theorem 8.1.15: with `Zᵀ (Q₁ᵀ A Q₁) Z = diag(θ)` for an
orthogonal `Z`, `A y_k - θ_k y_k = (I - Q₁ Q₁ᵀ) A Q₁ Z e_k` for `y_k = Q₁ Z e_k`. -/
private theorem ritz_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} {Z : Matrix (Fin r) (Fin r) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin r) ℝ) {θ : Fin r → ℝ}
    (hZθ : Zᵀ * (Q₁ᵀ * A * Q₁) * Z = diagonal θ) (k : Fin r) :
    A *ᵥ (Q₁ * Z).col k - θ k • (Q₁ * Z).col k = ((1 - Q₁ * Q₁ᵀ) * A * Q₁) *ᵥ Z.col k := by
  have hZZ : Z * Zᵀ = 1 := (mem_orthogonalGroup_iff (Fin r) ℝ).1 hZ
  have hMZ : (Q₁ᵀ * A * Q₁) * Z = Z * diagonal θ := by
    rw [← hZθ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hZZ, Matrix.one_mul]
  have hcol : θ k • Z.col k = (Q₁ᵀ * A * Q₁) *ᵥ Z.col k := by
    rw [← col_mul_eq_mulVec_col, hMZ]
    ext i
    simp [col_apply, mul_diagonal, mul_comm]
  rw [col_mul_eq_mulVec_col, ← mulVec_smul, hcol, mulVec_mulVec, mulVec_mulVec, ← sub_mulVec]
  congr 1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

/-- **Theorem 8.1.15.** For `Q₁` with orthonormal columns, an orthogonal `Z` with
`Zᵀ (Q₁ᵀ A Q₁) Z = diag(θ_1, …, θ_r)` and `[y_1, …, y_r] = Q₁ Z`:
`‖A y_k - θ_k y_k‖₂ = ‖(I - Q₁Q₁ᵀ) A Q₁ Z e_k‖₂ ≤ ‖(I - Q₁Q₁ᵀ) A Q₁‖₂`. -/
theorem theorem_8_1_15 (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} {Q₁ : Matrix (Fin n) (Fin r) ℝ}
    {Z : Matrix (Fin r) (Fin r) ℝ} (hZ : Z ∈ orthogonalGroup (Fin r) ℝ) {θ : Fin r → ℝ}
    (hZθ : Zᵀ * (Q₁ᵀ * A * Q₁) * Z = diagonal θ) (k : Fin r) :
    A *ᵥ (Q₁ * Z).col k - θ k • (Q₁ * Z).col k = ((1 - Q₁ * Q₁ᵀ) * A * Q₁) *ᵥ Z.col k ∧
      ‖WithLp.toLp 2 (A *ᵥ (Q₁ * Z).col k - θ k • (Q₁ * Z).col k)‖ ≤
        lpOpNorm 2 ((1 - Q₁ * Q₁ᵀ) * A * Q₁) := by
  refine ⟨ritz_residual_eq A hZ hZθ k, ?_⟩
  rw [ritz_residual_eq A hZ hZθ k, ← toEuclideanLin_toLp, lpOpNorm_two]
  have hZ' : Zᴴ * Z = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact (mem_orthogonalGroup_iff' (Fin r) ℝ).1 hZ
  have hcol : ‖WithLp.toLp 2 (Z.col k)‖ = 1 := by
    rw [← mulVec_single_one, ← toEuclideanLin_toLp,
      norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hZ']
    exact norm_toLp_single_one k
  exact (norm_toEuclideanLin_apply_le _ _).trans_eq (by rw [hcol, mul_one])

/-- **§8.1.4, Ritz pairs.** In the setting of Theorem 8.1.15, each `(θ_k, y_k)` is a Ritz pair
of `A` on `ran(Q₁)` (`y_k ∈ ran(Q₁)`, `y_k ≠ 0`, residual orthogonal to `ran(Q₁)`); and conversely
every Ritz pair `(μ, u)` of `A` on `ran(Q₁)` is `u = Q₁ w` with `(Q₁ᵀ A Q₁) w = μ w`, `w ≠ 0`. -/
theorem ritzPair_isRitzPair (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ}
    {Q₁ : Matrix (Fin n) (Fin r) ℝ} (hQ : Q₁ᵀ * Q₁ = 1) {Z : Matrix (Fin r) (Fin r) ℝ}
    (hZ : Z ∈ orthogonalGroup (Fin r) ℝ) {θ : Fin r → ℝ}
    (hZθ : Zᵀ * (Q₁ᵀ * A * Q₁) * Z = diagonal θ) :
    (∀ k, Krylov.IsRitzPair (toEuclideanLin A) (LinearMap.range (toEuclideanLin Q₁)) (θ k)
      (WithLp.toLp 2 ((Q₁ * Z).col k))) ∧
    ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)),
      Krylov.IsRitzPair (toEuclideanLin A) (LinearMap.range (toEuclideanLin Q₁)) μ u →
        ∃ w : Fin r → ℝ, w ≠ 0 ∧ u = WithLp.toLp 2 (Q₁ *ᵥ w) ∧ (Q₁ᵀ * A * Q₁) *ᵥ w = μ • w := by
  have hQ' : Q₁ᴴ * Q₁ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hZ' : Zᴴ * Z = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact (mem_orthogonalGroup_iff' (Fin r) ℝ).1 hZ
  -- `⟪Q₁ x, v⟫ = x ⬝ Q₁ᵀ v`
  have hinner : ∀ (x : Fin r → ℝ) (v : Fin n → ℝ),
      inner ℝ (WithLp.toLp 2 (Q₁ *ᵥ x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v) =
        (Q₁ᵀ *ᵥ v) ⬝ᵥ x := fun x v => by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_mulVec, mulVec_transpose]
  refine ⟨fun k => ⟨⟨WithLp.toLp 2 (Z.col k), by rw [toEuclideanLin_toLp, col_mul_eq_mulVec_col]⟩,
    fun h0 => ?_, ?_⟩, fun μ u hu => ?_⟩
  · have hn1 : ‖WithLp.toLp 2 ((Q₁ * Z).col k)‖ = 1 := by
      rw [col_mul_eq_mulVec_col, ← toEuclideanLin_toLp,
        norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQ', ← mulVec_single_one,
        ← toEuclideanLin_toLp, norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hZ']
      exact norm_toLp_single_one k
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  · rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    rw [toEuclideanLin_apply, toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
      ritz_residual_eq A hZ hZθ k, hinner, mulVec_mulVec]
    have h0 : Q₁ᵀ * ((1 - Q₁ * Q₁ᵀ) * A * Q₁) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
        ← Matrix.mul_assoc, hQ, Matrix.one_mul, sub_self, Matrix.zero_mul, Matrix.zero_mul]
    rw [h0, zero_mulVec, zero_dotProduct]
  · obtain ⟨x, hx⟩ := hu.mem
    set w := WithLp.ofLp x
    have hu' : u = WithLp.toLp 2 (Q₁ *ᵥ w) := by rw [← hx, toEuclideanLin_apply]
    refine ⟨w, fun h0 => hu.ne_zero (by rw [hu', h0, mulVec_zero]; rfl), hu', ?_⟩
    have hres := hu.residual_mem_orthogonal
    rw [hu', toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
      Submodule.mem_orthogonal] at hres
    have hr : Q₁ᵀ *ᵥ (A *ᵥ (Q₁ *ᵥ w) - μ • (Q₁ *ᵥ w)) = 0 := by
      ext j
      have := hres _ ⟨WithLp.toLp 2 (Pi.single j 1), rfl⟩
      rw [toEuclideanLin_toLp, hinner, dotProduct_single, mul_one] at this
      exact this
    rw [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hQ, one_mulVec,
      sub_eq_zero] at hr
    exact hr

section L2

open scoped Matrix.Norms.L2Operator

/-- **(8.1.5).** For `S = X₁ᵀ A X₁`, `F₁ = A X₁ - X₁ S` and any `Q`, `E₁ = A Q - Q S` satisfies
`‖E₁‖₂ ≤ ‖F₁‖₂ + ‖Q - X₁‖₂ ‖A‖₂ (1 + ‖X₁‖₂²)`. (The book takes `Q` with orthonormal columns; the
bound does not need it.) -/
theorem equation_8_1_5 (A : Matrix (Fin n) (Fin n) ℝ) {r : ℕ} (X₁ Q : Matrix (Fin n) (Fin r) ℝ) :
    lpOpNorm 2 (A * Q - Q * (X₁ᵀ * A * X₁)) ≤ lpOpNorm 2 (A * X₁ - X₁ * (X₁ᵀ * A * X₁)) +
      lpOpNorm 2 (Q - X₁) * lpOpNorm 2 A * (1 + lpOpNorm 2 X₁ ^ 2) := by
  simp only [lpOpNorm_two]
  set S := X₁ᵀ * A * X₁
  have hS : ‖S‖ ≤ ‖X₁‖ ^ 2 * ‖A‖ := by
    calc ‖S‖ ≤ ‖X₁ᵀ * A‖ * ‖X₁‖ := l2_opNorm_mul _ _
      _ ≤ ‖X₁ᵀ‖ * ‖A‖ * ‖X₁‖ := by gcongr; exact l2_opNorm_mul _ _
      _ = ‖X₁‖ ^ 2 * ‖A‖ := by
        rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]; ring
  have heq : A * Q - Q * S = (A * X₁ - X₁ * S) + (A * (Q - X₁) - (Q - X₁) * S) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [heq]
  have h1 : ‖A * (Q - X₁)‖ ≤ ‖A‖ * ‖Q - X₁‖ := l2_opNorm_mul _ _
  have h2 : ‖(Q - X₁) * S‖ ≤ ‖Q - X₁‖ * (‖X₁‖ ^ 2 * ‖A‖) :=
    (l2_opNorm_mul _ _).trans (by gcongr)
  calc ‖(A * X₁ - X₁ * S) + (A * (Q - X₁) - (Q - X₁) * S)‖
      ≤ ‖A * X₁ - X₁ * S‖ + (‖A * (Q - X₁)‖ + ‖(Q - X₁) * S‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ ‖A * X₁ - X₁ * S‖ + (‖A‖ * ‖Q - X₁‖ + ‖Q - X₁‖ * (‖X₁‖ ^ 2 * ‖A‖)) := by gcongr
    _ = _ := by ring

/-- **(8.1.6).** If `‖X₁ᵀ X₁ - I_r‖₂ = τ`, then `‖X₁‖₂² ≤ 1 + τ`. -/
theorem equation_8_1_6 {r : ℕ} (X₁ : Matrix (Fin n) (Fin r) ℝ) {τ : ℝ}
    (hτ : lpOpNorm 2 (X₁ᵀ * X₁ - 1) = τ) : lpOpNorm 2 X₁ ^ 2 ≤ 1 + τ := by
  have h1 : lpOpNorm 2 (1 : Matrix (Fin r) (Fin r) ℝ) ≤ 1 := by
    rw [lpOpNorm, lpCLM_one]; exact ContinuousLinearMap.norm_id_le
  rw [lpOpNorm_two] at h1 hτ ⊢
  rw [sq, ← l2_opNorm_conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial]
  calc ‖X₁ᵀ * X₁‖ = ‖(X₁ᵀ * X₁ - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖X₁ᵀ * X₁ - 1‖ + ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ := norm_add_le _ _
    _ ≤ 1 + τ := by linarith

/-- If `‖X₁ᵀ X₁ - I_r‖₂ < 1` then `r ≤ n`: otherwise some `v ≠ 0` has `X₁ v = 0`, and
`(X₁ᵀ X₁ - I) v = -v`. -/
private theorem le_of_l2_opNorm_transpose_mul_self_sub_one_lt {r : ℕ}
    {X₁ : Matrix (Fin n) (Fin r) ℝ} (h : lpOpNorm 2 (X₁ᵀ * X₁ - 1) < 1) : r ≤ n := by
  by_contra hrn
  have hker : LinearMap.ker (toLin' X₁) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
  rw [LinearMap.mem_ker, toLin'_apply] at hv
  have hmv : (X₁ᵀ * X₁ - 1) *ᵥ v = -v := by
    rw [sub_mulVec, ← mulVec_mulVec, hv, mulVec_zero, one_mulVec, zero_sub]
  have hle := lpSeminorm_mulVec_le (r := 2) (X₁ᵀ * X₁ - 1) v
  rw [hmv, lpSeminorm_apply, lpSeminorm_apply, WithLp.toLp_neg, norm_neg] at hle
  have hpos : 0 < ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin r))‖ :=
    norm_pos_iff.2 (fun h0 => hv0 (by simpa using congrArg WithLp.ofLp h0))
  nlinarith

/-- **(8.1.7)** (in the proof of Theorem 8.1.16): if `‖X₁ᵀ X₁ - I_r‖₂ = τ < 1` there is `Q` with
orthonormal columns and `‖Q - X₁‖₂ ≤ τ` — the book's `Q = U Vᵀ` from the thin SVD
`Uᵀ X₁ V = Σ`, i.e. the polar factor of `X₁` (`Matrix.exists_orthonormal_cols_norm_sub_le`). The
book's intermediate `1 - σ_r² = τ` is not needed (and holds only when `σ_r` is the singular value
farthest from `1`). -/
theorem equation_8_1_7 {r : ℕ} (X₁ : Matrix (Fin n) (Fin r) ℝ) {τ : ℝ}
    (hτ : lpOpNorm 2 (X₁ᵀ * X₁ - 1) = τ) (hτ1 : τ < 1) :
    ∃ Q : Matrix (Fin n) (Fin r) ℝ, Qᵀ * Q = 1 ∧ lpOpNorm 2 (Q - X₁) ≤ τ := by
  have hr := le_of_l2_opNorm_transpose_mul_self_sub_one_lt (hτ ▸ hτ1)
  obtain ⟨Q, hQ, -, hle⟩ := exists_orthonormal_cols_norm_sub_le X₁ (by simpa using hr)
    (by rw [conjTranspose_eq_transpose_of_trivial, hτ]) hτ1
  exact ⟨Q, by rwa [conjTranspose_eq_transpose_of_trivial] at hQ, hle⟩

end L2

/-- The `S = X₁ᵀ A X₁` of Theorem 8.1.16 is symmetric. -/
theorem isSymm_transpose_mul_mul {r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (X₁ : Matrix (Fin n) (Fin r) ℝ) : (X₁ᵀ * A * X₁).IsSymm := by
  rw [IsSymm, transpose_mul, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]

/-- **Theorem 8.1.16** (paired form). "Suppose `A ∈ ℝ^{n×n}` is symmetric and that
`AX₁ − X₁S = F₁` where `X₁ ∈ ℝ^{n×r}` and `S = X₁ᵀAX₁`. If `‖X₁ᵀX₁ − I_r‖₂ = τ < 1` (8.1.4), then
there exist `μ₁, …, μ_r ∈ λ(A)` such that `|μ_k − λ_k(S)| ≤ √2 (‖F₁‖₂ + τ(2 + τ)‖A‖₂)` for
`k = 1:r`." As in Theorem 8.1.13 the `μ_k` are `λ_{σ(k)}(A)` for an injection `σ`. The book's
proof: `Q` with orthonormal columns and `‖Q − X₁‖₂ ≤ τ` from (8.1.7), (8.1.5) with (8.1.6) bounds
`‖AQ − QS‖₂ ≤ ‖F₁‖₂ + τ(2 + τ)‖A‖₂`, and Theorem 8.1.13 applies to `Q`. -/
theorem theorem_8_1_16 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {r : ℕ}
    (X₁ : Matrix (Fin n) (Fin r) ℝ) {τ : ℝ} (hτ : lpOpNorm 2 (X₁ᵀ * X₁ - 1) = τ) (hτ1 : τ < 1) :
    ∃ σ : Fin r ↪ Fin n, ∀ k,
      |symmEigenvalue hA (σ k) - symmEigenvalue (isSymm_transpose_mul_mul hA X₁) k| ≤
        √2 * (lpOpNorm 2 (A * X₁ - X₁ * (X₁ᵀ * A * X₁)) + τ * (2 + τ) * lpOpNorm 2 A) := by
  obtain ⟨Q, hQ, hQX⟩ := equation_8_1_7 X₁ hτ hτ1
  obtain ⟨σ, hσ⟩ := theorem_8_1_13 hA (isSymm_transpose_mul_mul hA X₁) hQ
  refine ⟨σ, fun k => (hσ k).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2))⟩
  have h5 := equation_8_1_5 A X₁ Q
  have h6 := equation_8_1_6 X₁ hτ
  have hτ0 : 0 ≤ τ := hτ ▸ lpOpNorm_nonneg _ _
  have hA0 : 0 ≤ lpOpNorm 2 A := lpOpNorm_nonneg _ _
  have h7 : lpOpNorm 2 (Q - X₁) * lpOpNorm 2 A * (1 + lpOpNorm 2 X₁ ^ 2) ≤
      τ * (2 + τ) * lpOpNorm 2 A := by
    have h8 : 1 + lpOpNorm 2 X₁ ^ 2 ≤ 2 + τ := by linarith
    calc lpOpNorm 2 (Q - X₁) * lpOpNorm 2 A * (1 + lpOpNorm 2 X₁ ^ 2)
        ≤ τ * lpOpNorm 2 A * (2 + τ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hQX hA0) h8 (by positivity)
            (mul_nonneg hτ0 hA0)
      _ = τ * (2 + τ) * lpOpNorm 2 A := by ring
  linarith

/-! ### §8.1.5 The law of inertia -/

/-- **§8.1.5, the inertia** `(m, z, p)` of a symmetric `A`: the numbers of negative, zero and
positive eigenvalues. -/
noncomputable def inertia {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) : ℕ × ℕ × ℕ :=
  (isHermitian_iff_isSymm.2 hA).inertia

/-- Counting the values of `p ∘ e` for an equivalence `e` is counting the values of `p`. -/
private theorem card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a => p (e a)).card = (Finset.univ.filter p).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv fun _ => Iff.rfl)

/-- The inertia counts the `λ_k(A)` that are negative, zero and positive. -/
theorem inertia_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    inertia hA = ((Finset.univ.filter fun k => symmEigenvalue hA k < 0).card,
      (Finset.univ.filter fun k => symmEigenvalue hA k = 0).card,
      (Finset.univ.filter fun k => 0 < symmEigenvalue hA k).card) := by
  have hH := isHermitian_iff_isSymm.2 hA
  rw [inertia, hH.inertia_eq_eigenvalues₀]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
      (fun j => hH.eigenvalues₀ j < 0)).symm
  · exact (card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
      (fun j => hH.eigenvalues₀ j = 0)).symm
  · exact (card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
      (fun j => 0 < hH.eigenvalues₀ j)).symm

/-- Counting the `λ_k(A)` with a property is counting Mathlib's `IsHermitian.eigenvalues` with it:
both are `eigenvalues₀` composed with an equivalence. -/
theorem card_filter_symmEigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (p : ℝ → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun k => p (symmEigenvalue hA k)).card =
      (Finset.univ.filter fun i => p ((isHermitian_iff_isSymm.2 hA).eigenvalues i)).card :=
  (card_filter_comp_equiv (finCongr (Fintype.card_fin n).symm)
    (fun j => p ((isHermitian_iff_isSymm.2 hA).eigenvalues₀ j))).trans
    (card_filter_comp_equiv (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => p ((isHermitian_iff_isSymm.2 hA).eigenvalues₀ j))).symm

/-- The inertia depends on the matrix only. -/
private theorem inertia_congr {A B : Matrix (Fin n) (Fin n) ℝ} (h : A = B) (hA : A.IsSymm)
    (hB : B.IsSymm) : inertia hA = inertia hB := by
  subst h
  rfl

/-- **Theorem 8.1.17 (Sylvester law of inertia).** For symmetric `A` and nonsingular `X`, `A` and
`Xᵀ A X` have the same inertia. -/
theorem theorem_8_1_17 {A X : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hX : IsUnit X.det)
    (hXAX : (Xᵀ * A * X).IsSymm) : inertia hXAX = inertia hA := by
  have hc : Xᴴ * A * X = Xᵀ * A * X := by rw [conjTranspose_eq_transpose_of_trivial]
  have h := (isHermitian_iff_isSymm.2 hA).inertia_conj ((isUnit_iff_isUnit_det X).2 hX)
  rw [← inertia_congr hc (isHermitian_iff_isSymm.1
    (isHermitian_conjTranspose_mul_mul X (isHermitian_iff_isSymm.2 hA))) hXAX]
  exact h

end GolubVanLoan.Chapter08
