import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Eigen.Normal
import Numlib.Eigen.NumericalRange
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# Golub–Van Loan §7.1: properties and decompositions

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.1: the spectrum and the attributes attached to it — spectral radius (7.1.1)
and abscissa (7.1.2), numerical radius (7.1.3) and range (7.1.4) — invariant subspaces (§7.1.1),
decoupling (Lemma 7.1.1), the unitary reductions (Lemma 7.1.2, the Schur decomposition 7.1.3 with
any order of the diagonal, the Schur vectors (7.1.8), normal matrices 7.1.4, the departure from
normality), the nonunitary reductions (the Sylvester map of Lemma 7.1.5, block diagonalization
7.1.6, Corollaries 7.1.7–7.1.8, the Jordan decomposition 7.1.9 and its uniqueness), the density of
diagonalizable matrices (§7.1.5), and singular values against eigenvalues (§7.1.6).

## Conventions

Complex throughout, as in the book: `A : Matrix (Fin n) (Fin n) ℂ`, 0-based. The spectrum
`λ(A)` is Mathlib's `spectrum ℂ A` in the algebra of matrices (the root set of `A.charpoly`,
`Matrix.mem_spectrum_iff_isRoot_charpoly`), and "the eigenvalues `λ₁, …, λₙ`" counted with
multiplicity are the multiset `A.charpoly.roots`. A unitary `Q` is a member of
`Matrix.unitaryGroup (Fin n) ℂ`, and `Qᴴ = star Q`. A block partition `[T₁₁ T₁₂; 0 T₂₂]` is
`Matrix.fromBlocks` on `Fin p ⊕ Fin q`, reindexed by `finSumFinEquiv` where the book's matrix is a
single `n × n` array. A matrix is *strictly upper triangular* when its entries on and below the
diagonal vanish. The 2-norm is the scoped `Matrix.Norms.L2Operator` norm and the Frobenius norm
the scoped `Matrix.Norms.Frobenius` norm, each opened in its own section; `σ_min(A)` and
`σ_max(A)` are `⨅ i, A.colSingularValues i` and `⨆ i, A.colSingularValues i` over the backbone's
column-indexed `Matrix.colSingularValues`.

## Sources

The decompositions are the backbone's `Numlib/LinearAlgebra/Matrix/{Schur,Jordan,Similar,
Sylvester}` and `Numlib/Eigen/Normal`; the numerical range is `Numlib/Eigen/NumericalRange`
(Toeplitz–Hausdorff); the singular-value facts are `Numlib/LinearAlgebra/Matrix/SVD`.

## Not formalized

The roundoff claims (7.1.14)–(7.1.15) (`fl(X⁻¹AX) = X⁻¹AX + E`, `‖E‖₂ ≈ u κ₂(X) ‖A‖₂`) name no
algorithm for forming `X⁻¹ A X` and carry a `≈`; the remark "`max |λ_i|/|λ_j| ≪ κ₂(A)` may occur" is
an illustration (its rigorous half, `|λ_i|/|λ_j| ≤ κ₂(A)`, is in `sigmaMin_le_norm_eigenvalue`).
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.1.1 Eigenvalues and invariant subspaces -/

/-- The spectrum of a complex matrix is finite: it is the root set of the characteristic
polynomial. -/
private theorem spectrum_finite (A : Matrix (Fin n) (Fin n) ℂ) : (spectrum ℂ A).Finite := by
  have h : spectrum ℂ A = {z | A.charpoly.IsRoot z} := by
    ext z; exact Matrix.mem_spectrum_iff_isRoot_charpoly
  rw [h]
  exact Polynomial.finite_setOfPred_isRoot A.charpoly_monic.ne_zero

/-- The spectrum of a complex matrix of positive size is nonempty. -/
private theorem spectrum_nonempty [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (spectrum ℂ A).Nonempty := by
  have hdeg : A.charpoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree A.charpoly_monic.ne_zero, A.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
    exact_mod_cast NeZero.ne n
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root A.charpoly hdeg
  exact ⟨z, Matrix.mem_spectrum_iff_isRoot_charpoly.2 hz⟩

/-- **§7.1.1, determinant and trace.** If `λ(A) = {λ₁, …, λₙ}` (with multiplicity) then
`det(A) = λ₁ λ₂ ⋯ λₙ` and `tr(A) = λ₁ + ⋯ + λₙ`: the eigenvalues counted with multiplicity are the
roots of the characteristic polynomial. -/
theorem det_eq_prod_eigenvalues (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det = A.charpoly.roots.prod ∧ A.trace = A.charpoly.roots.sum :=
  ⟨A.det_eq_prod_roots_charpoly, A.trace_eq_sum_roots_charpoly⟩

/-- **(7.1.1), the spectral radius** `ρ(A) = max_{λ ∈ λ(A)} |λ|`, as the supremum of the moduli of
the eigenvalues (`0` for `n = 0`; the spectrum is finite, so for `n ≥ 1` it is a maximum). Its
agreement with Mathlib's `ℝ≥0∞`-valued `spectralRadius` of the matrix algebra is
`spectralRadius_eq`. -/
noncomputable def spectralRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup ((‖·‖) '' spectrum ℂ A)

/-- The spectral radius (7.1.1) is Mathlib's spectral radius of `A` in the algebra of matrices. -/
theorem spectralRadius_eq (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius A = (_root_.spectralRadius ℂ A).toReal := by
  have h : _root_.spectralRadius ℂ A = ⨆ k ∈ spectrum ℂ A, (‖k‖₊ : ENNReal) := by
    rw [_root_.spectralRadius, quasispectrum_eq_spectrum_union_zero, iSup_union]
    simp
  rw [h, iSup_subtype', ENNReal.toReal_iSup fun _ => ENNReal.coe_ne_top, spectralRadius,
    sSup_image']
  simp only [ENNReal.coe_toReal, coe_nnnorm]

/-- **(7.1.2), the spectral abscissa** `α(A) = max_{λ ∈ λ(A)} Re(λ)`, as a supremum; it is attained
for `n ≥ 1` (`spectralAbscissa_mem`). -/
noncomputable def spectralAbscissa (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ A)

/-- The spectral abscissa (7.1.2) is a maximum: some eigenvalue has real part `α(A)`. -/
theorem spectralAbscissa_mem [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ μ ∈ spectrum ℂ A, μ.re = spectralAbscissa A :=
  ((spectrum_nonempty A).image _).csSup_mem ((spectrum_finite A).image _)

/-- **(7.1.4), the numerical range** (field of values) `W(A) = {xᴴ A x : ‖x‖₂ = 1}`. Its agreement
with the backbone's operator numerical range, defined by Rayleigh quotients of nonzero vectors, is
`numericalRange_eq`. -/
def numericalRange (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : Fin n → ℂ, ‖WithLp.toLp 2 x‖ = 1 ∧ star x ⬝ᵥ (A *ᵥ x) = z}

/-- The quadratic form `xᴴ A x` is the inner product `⟪x, A x⟫` in `EuclideanSpace ℂ (Fin n)`. -/
private theorem star_dotProduct_mulVec_eq_inner (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) =
      inner ℂ (WithLp.toLp 2 x) (toEuclideanLin A (WithLp.toLp 2 x)) := by
  simp only [toLpLin_toLp, EuclideanSpace.inner_toLp_toLp, toLin'_apply, dotProduct_comm]

/-- The numerical range (7.1.4) is the backbone's numerical range of `A` as an operator on
`EuclideanSpace ℂ (Fin n)`, `{⟪x, A x⟫ / ⟪x, x⟫ : x ≠ 0}`: normalize `x`. -/
theorem numericalRange_eq (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A = LinearMap.numericalRange (toEuclideanLin A) := by
  ext z
  rw [LinearMap.mem_numericalRange]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, fun h => by simp [h] at hx, ?_⟩
    rw [inner_self_eq_norm_sq_to_K, hx, star_dotProduct_mulVec_eq_inner]
    simp
  · rintro ⟨y, hy, rfl⟩
    have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    refine ⟨WithLp.ofLp ((‖y‖⁻¹ : ℂ) • y), ?_, ?_⟩
    · rw [WithLp.toLp_ofLp, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ hy0]
    · rw [star_dotProduct_mulVec_eq_inner, WithLp.toLp_ofLp, map_smul, inner_smul_left,
        inner_smul_right, inner_self_eq_norm_sq_to_K]
      have : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hy0
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
      exact (mul_div_cancel_left₀ _ (pow_ne_zero 2 this)).symm

/-- **(7.1.3), the numerical radius** `r(A) = max {|xᴴ A x| : ‖x‖₂ = 1}`, the supremum of the moduli
of the numerical range. The book prints the maximum as `max_{λ ∈ λ(A)}`, a misprint for the
maximum over unit `x`. -/
noncomputable def numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup ((‖·‖) '' numericalRange A)

/-- **§7.1.1, "the numerical range … obviously includes `λ(A)`"**: a unit eigenvector `x` for `λ`
gives `xᴴ A x = λ`. -/
theorem spectrum_subset_numericalRange (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro μ hμ
  rw [numericalRange_eq, LinearMap.mem_numericalRange]
  obtain ⟨x, hx0, hx⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).1 hμ
  refine ⟨WithLp.toLp 2 x, by simpa using hx0, ?_⟩
  have hne : (inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 x) : ℂ) ≠ 0 :=
    inner_self_ne_zero.2 (by simpa using hx0)
  rw [toLpLin_toLp, toLin'_apply, hx, WithLp.toLp_smul, inner_smul_right, mul_div_assoc,
    div_self hne, mul_one]

/-- **§7.1.1, "It can be shown that `W(A)` is convex"** (the Toeplitz–Hausdorff theorem). -/
theorem convex_numericalRange (A : Matrix (Fin n) (Fin n) ℂ) : Convex ℝ (numericalRange A) := by
  rw [numericalRange_eq]
  exact LinearMap.convex_numericalRange _

/-- If `X` has full column rank, `X y = 0` forces `y = 0`. -/
private theorem eq_zero_of_mulVec_eq_zero {m k : ℕ} {X : Matrix (Fin m) (Fin k) ℂ}
    (hX : X.rank = k) {y : Fin k → ℂ} (hy : X *ᵥ y = 0) : y = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  rw [← Matrix.rank, hX, Module.finrank_fin_fun, add_eq_left,
    Submodule.finrank_eq_zero] at h
  have hmem : y ∈ LinearMap.ker X.mulVecLin := by simpa using hy
  rw [h] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

/-- **§7.1.1, invariant subspaces from `A X = X B`**, for `X ∈ ℂ^{n×k}`, `B ∈ ℂ^{k×k}`: `ran(X)` is
invariant for `A`; `B y = λ y ⇒ A (X y) = λ (X y)`; if `X` has full column rank then
`λ(B) ⊆ λ(A)`; and a similarity `B = X⁻¹ A X` with `X` square and nonsingular preserves the
spectrum. -/
theorem spectrum_subset_of_mul_eq_mul {k : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin n) (Fin k) ℂ} {B : Matrix (Fin k) (Fin k) ℂ} (h : A * X = X * B) :
    LinearMap.range (toLin' X) ∈ Module.End.invtSubmodule (toLin' A) ∧
      (∀ (y : Fin k → ℂ) (μ : ℂ), B *ᵥ y = μ • y → A *ᵥ (X *ᵥ y) = μ • (X *ᵥ y)) ∧
      (X.rank = k → spectrum ℂ B ⊆ spectrum ℂ A) ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y → spectrum ℂ (Y⁻¹ * A * Y) = spectrum ℂ A := by
  have hb : ∀ (y : Fin k → ℂ) (μ : ℂ), B *ᵥ y = μ • y → A *ᵥ (X *ᵥ y) = μ • (X *ᵥ y) :=
    fun y μ hy => by rw [mulVec_mulVec, h, ← mulVec_mulVec, hy, mulVec_smul]
  refine ⟨?_, hb, fun hX μ hμ => ?_, fun Y hY => ?_⟩
  · rw [Module.End.mem_invtSubmodule]
    rintro _ ⟨y, rfl⟩
    refine ⟨B *ᵥ y, ?_⟩
    simp only [toLin'_apply]
    rw [mulVec_mulVec, ← h, ← mulVec_mulVec]
  · obtain ⟨y, hy0, hy⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul B μ).1 hμ
    exact (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).2
      ⟨X *ᵥ y, fun h0 => hy0 (eq_zero_of_mulVec_eq_zero hX h0), hb y μ hy⟩
  · have hsim : IsSimilar A (Y⁻¹ * A * Y) := ⟨Y, hY, rfl⟩
    ext μ
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, hsim.charpoly_eq]

/-! ### §7.1.2 Decoupling -/

/-- **Lemma 7.1.1.** If `T = [T₁₁ T₁₂; 0 T₂₂]` then `λ(T) = λ(T₁₁) ∪ λ(T₂₂)`; with multiplicity,
the characteristic polynomial of `T` is the product of those of the diagonal blocks (the book's
"same cardinality" argument is this multiset statement). -/
theorem lemma_7_1_1 {p q : ℕ} (T₁₁ : Matrix (Fin p) (Fin p) ℂ) (T₁₂ : Matrix (Fin p) (Fin q) ℂ)
    (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    spectrum ℂ (fromBlocks T₁₁ T₁₂ 0 T₂₂) = spectrum ℂ T₁₁ ∪ spectrum ℂ T₂₂ ∧
      (fromBlocks T₁₁ T₁₂ 0 T₂₂).charpoly = T₁₁.charpoly * T₂₂.charpoly := by
  have hc := Matrix.charpoly_fromBlocks_zero₂₁ T₁₁ T₁₂ T₂₂
  refine ⟨?_, hc⟩
  ext μ
  simp only [Set.mem_union, Matrix.mem_spectrum_iff_isRoot_charpoly, hc, Polynomial.IsRoot.def,
    Polynomial.eval_mul, mul_eq_zero]

/-! ### §7.1.3 Basic unitary decompositions -/

/-- Similar matrices have the same spectrum. -/
private theorem IsSimilar.spectrum_eq {m : ℕ} {B C : Matrix (Fin m) (Fin m) ℂ}
    (h : IsSimilar B C) : spectrum ℂ B = spectrum ℂ C := by
  ext μ
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, h.charpoly_eq]

/-- **Lemma 7.1.2.** If `A X = X B` with `rank(X) = p` (7.1.5), then a unitary `Q` puts `A` in block
upper triangular form `Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]` (7.1.6) with `λ(T₁₁) = λ(A) ∩ λ(B)`. -/
theorem lemma_7_1_2 {p q : ℕ} {A : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    {B : Matrix (Fin p) (Fin p) ℂ} {X : Matrix (Fin (p + q)) (Fin p) ℂ} (hAX : A * X = X * B)
    (hX : X.rank = p) :
    ∃ Q ∈ unitaryGroup (Fin (p + q)) ℂ, ∃ (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
      (T₁₂ : Matrix (Fin p) (Fin q) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ),
      (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
        fromBlocks T₁₁ T₁₂ 0 T₂₂ ∧ spectrum ℂ T₁₁ = spectrum ℂ A ∩ spectrum ℂ B := by
  obtain ⟨Q, hQ, T₁₁, T₁₂, T₂₂, hT, hsim⟩ := exists_unitary_conj_fromBlocks_of_mul_eq_mul hAX hX
  refine ⟨Q, hQ, T₁₁, T₁₂, T₂₂, hT, ?_⟩
  rw [← IsSimilar.spectrum_eq hsim,
    Set.inter_eq_right.2 ((spectrum_subset_of_mul_eq_mul hAX).2.2.1 hX)]

/-- **Theorem 7.1.3 (Schur decomposition)** (7.1.7). There is a unitary `Q` with `Qᴴ A Q = D + N`,
`D = diag(λ₁, …, λₙ)` listing the eigenvalues and `N` strictly upper triangular; and `Q` can be
chosen so that the eigenvalues appear in any prescribed order `μ` along the diagonal. -/
theorem theorem_7_1_3 (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ Q ∈ unitaryGroup (Fin n) ℂ, ∃ (d : Fin n → ℂ) (N : Matrix (Fin n) (Fin n) ℂ),
      (∀ i j, j ≤ i → N i j = 0) ∧ star Q * A * Q = diagonal d + N ∧
        A.charpoly = ∏ i, (X - C (d i))) ∧
    ∀ μ : Fin n → ℂ, A.charpoly = ∏ i, (X - C (μ i)) →
      ∃ Q ∈ unitaryGroup (Fin n) ℂ, (star Q * A * Q).IsUpperTriangular ∧
        ∀ i, (star Q * A * Q) i i = μ i := by
  refine ⟨?_, fun μ hμ => exists_unitary_conj_upperTriangular_diag_eq A μ hμ⟩
  obtain ⟨Q, hQ, hT, hchar⟩ := exists_unitary_conj_upperTriangular A
  set T := star Q * A * Q
  refine ⟨Q, hQ, fun i => T i i, T - diagonal fun i => T i i, fun i j hji => ?_, by abel,
    hchar⟩
  rcases hji.lt_or_eq with hlt | rfl
  · simp [Matrix.sub_apply, hT hlt, diagonal_apply_ne _ hlt.ne']
  · simp

/-- The spectrum of an upper triangular matrix is the set of its diagonal entries. -/
private theorem spectrum_eq_range_diag {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ}
    (hT : T.IsUpperTriangular) : spectrum ℂ T = Set.range fun i => T i i := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_of_isUpperTriangular T hT,
    Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

/-- `A Q = Q T` for a unitary `Q` and `T = Qᴴ A Q`. -/
private theorem mul_eq_mul_conj {Q A : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) : A * Q = Q * (star Q * A * Q) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ, Matrix.one_mul]

/-- **(7.1.8) and the paragraph after it: the Schur vectors.** Let `Qᴴ A Q = T` be upper triangular
with `Q` unitary and `q_k` the columns of `Q`. Then (a) `A q_k = t_kk q_k + ∑_{i<k} t_ik q_i`;
(b) each `S_k = span{q₀, …, q_k}` is invariant for `A`; (c) with `Q_k = [q₀ | ⋯ | q_{k-1}]`,
`λ(Q_kᴴ A Q_k) = {t₀₀, …, t_{k-1,k-1}}`; (d) `q_k` is an eigenvector of `A` exactly when column
`k` of the strictly upper triangular part of `T` vanishes. -/
theorem equation_7_1_8 {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Q).IsUpperTriangular) :
    (∀ k, A *ᵥ Q.col k = (star Q * A * Q) k k • Q.col k +
      ∑ i ∈ Finset.Iio k, (star Q * A * Q) i k • Q.col i) ∧
    (∀ k, Submodule.span ℂ (Q.col '' Set.Iic k) ∈ Module.End.invtSubmodule (toLin' A)) ∧
    (∀ (k : ℕ) (hk : k ≤ n),
      spectrum ℂ ((Q.submatrix id (Fin.castLE hk))ᴴ * A * Q.submatrix id (Fin.castLE hk)) =
        Set.range fun i : Fin k => (star Q * A * Q) (Fin.castLE hk i) (Fin.castLE hk i)) ∧
    ∀ k, (∃ μ : ℂ, A *ᵥ Q.col k = μ • Q.col k) ↔ ∀ i < k, (star Q * A * Q) i k = 0 := by
  set T := star Q * A * Q with hTdef
  have hAQ : A * Q = Q * T := mul_eq_mul_conj hQ
  have hcol : ∀ k, Q.col k = Q *ᵥ Pi.single k 1 := fun k => by
    rw [mulVec_single_one]
  -- `A q_k = Q (T e_k)`
  have hAq : ∀ k, A *ᵥ Q.col k = Q *ᵥ T.col k := fun k => by
    rw [hcol, mulVec_mulVec, hAQ, ← mulVec_mulVec, mulVec_single_one]
  -- (a)
  have ha : ∀ k, A *ᵥ Q.col k = T k k • Q.col k + ∑ i ∈ Finset.Iio k, T i k • Q.col i := by
    intro k
    rw [hAq]
    ext r
    simp only [mulVec, dotProduct, col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic k)) fun i _ hi => by
      simp only [Finset.mem_Iic, not_le] at hi; rw [hT hi, mul_zero],
      ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    simp only [mul_comm]
  refine ⟨ha, fun k => ?_, fun k hk => ?_, fun k => ?_⟩
  · -- (b)
    rw [Module.End.mem_invtSubmodule, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [Submodule.mem_comap, toLin'_apply, SetLike.mem_coe]
    rw [ha j]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩))
      (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨i, ?_, rfl⟩))
    exact le_trans (Finset.mem_Iio.1 hi).le hj
  · -- (c)
    have hsub : (Q.submatrix id (Fin.castLE hk))ᴴ * A * Q.submatrix id (Fin.castLE hk) =
        T.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      rw [conjTranspose_submatrix, hTdef, star_eq_conjTranspose,
        submatrix_mul _ _ _ id _ Function.bijective_id,
        submatrix_mul _ _ _ id _ Function.bijective_id]
      rfl
    rw [hsub, spectrum_eq_range_diag]
    · rfl
    · intro i j hij
      have hij' : (j : ℕ) < i := hij
      exact hT (show Fin.castLE hk j < Fin.castLE hk i from Fin.lt_def.2 (by simpa using hij'))
  · -- (d)
    have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
    constructor
    · rintro ⟨μ, hμ⟩ i hi
      have h1 : T.col k = μ • Pi.single k 1 := by
        have h := congrArg (star Q *ᵥ ·) hμ
        rw [hAq, mulVec_mulVec, hQQ, one_mulVec, hcol, mulVec_smul, mulVec_mulVec, hQQ,
          one_mulVec] at h
        exact h
      have h2 := congrFun h1 i
      simpa [col_apply, Pi.single_apply, hi.ne] using h2
    · intro h
      refine ⟨T k k, ?_⟩
      rw [hAq, hcol, ← mulVec_smul]
      congr 1
      ext i
      rcases lt_trichotomy i k with hi | rfl | hi
      · simp [col_apply, h i hi, hi.ne]
      · simp [col_apply]
      · simp [col_apply, hT hi, hi.ne']

/-- **Corollary 7.1.4.** `A` is normal (`Aᴴ A = A Aᴴ`) if and only if there is a unitary `Q` with
`Qᴴ A Q = diag(λ₁, …, λₙ)`. -/
theorem corollary_7_1_4 (A : Matrix (Fin n) (Fin n) ℂ) :
    IsStarNormal A ↔ ∃ Q ∈ unitaryGroup (Fin n) ℂ, ∃ d : Fin n → ℂ,
      star Q * A * Q = diagonal d := by
  rw [IsStarNormal.spectral_theorem]
  simp only [star_eq_conjTranspose]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§7.1.3, Definition: the departure from normality**
`Δ(A) = (‖A‖_F² - ∑ |λ_i|²)^{1/2}`, the eigenvalues counted with multiplicity. -/
noncomputable def departureFromNormality (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  √(‖A‖ ^ 2 - (A.charpoly.roots.map fun z => ‖z‖ ^ 2).sum)

/-- **§7.1.3: `‖N‖_F` does not depend on the Schur decomposition.** If `Qᴴ A Q = diag(d) + N` with
`Q` unitary and `N` strictly upper triangular, then `‖N‖_F² = ‖A‖_F² - ∑ |d_i|² = Δ²(A)`. -/
theorem departureFromNormality_eq {A Q N : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hN : ∀ i j, j ≤ i → N i j = 0)
    (h : star Q * A * Q = diagonal d + N) :
    ‖N‖ ^ 2 = ‖A‖ ^ 2 - ∑ i, ‖d i‖ ^ 2 ∧
      ‖A‖ ^ 2 - ∑ i, ‖d i‖ ^ 2 = departureFromNormality A ^ 2 := by
  have hnorm : ‖star Q * A * Q‖ = ‖A‖ :=
    frobenius_norm_unitary_mul_mul_unitary (Unitary.star_mem hQ) A hQ
  have hsplit : ‖diagonal d + N‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 + ‖N‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => ‖N i j‖ ^ 2) (Finset.mem_univ i), hN i i le_rfl]
    have hoff : ∀ j ∈ Finset.univ.erase i, ‖(diagonal d + N) i j‖ ^ 2 = ‖N i j‖ ^ 2 :=
      fun j hj => by
        have hij : i ≠ j := fun e => by simp [e] at hj
        simp [diagonal_apply_ne _ hij]
    rw [Finset.sum_congr rfl hoff]
    simp [hN i i le_rfl]
  have h1 : ‖N‖ ^ 2 = ‖A‖ ^ 2 - ∑ i, ‖d i‖ ^ 2 := by
    rw [← hnorm, h, hsplit]; ring
  refine ⟨h1, ?_⟩
  -- the diagonal lists the eigenvalues
  have hsim : IsSimilar A (star Q * A * Q) := by
    refine ⟨Q, (Matrix.isUnit_iff_isUnit_det Q).2
      (Matrix.isUnit_det_of_right_inverse (mem_unitaryGroup_iff.1 hQ)), ?_⟩
    rw [Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)]
  have hup : (diagonal d + N).IsUpperTriangular := fun i j hij => by
    have hij' : j < i := hij
    rw [Matrix.add_apply, diagonal_apply_ne d (ne_of_gt hij'), hN i j hij'.le, add_zero]
  have hdiag : ∀ i, (diagonal d + N) i i = d i := fun i => by simp [hN i i le_rfl]
  have hroots : A.charpoly.roots = Finset.univ.val.map d := by
    rw [hsim.charpoly_eq, h, charpoly_of_isUpperTriangular _ hup]
    simp only [hdiag]
    rw [show (∏ i, (X - C (d i))) = ((Finset.univ.val.map d).map fun a => X - C a).prod by
      rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hsum : ((Finset.univ.val.map d).map fun z => ‖z‖ ^ 2).sum = ∑ i, ‖d i‖ ^ 2 := by
    rw [Multiset.map_map]; rfl
  rw [departureFromNormality, hroots, hsum, Real.sq_sqrt (by rw [← h1]; positivity)]

end Frobenius

/-! ### §7.1.4 Nonunitary reductions -/

/-- **Lemma 7.1.5, first half.** The Sylvester map `φ(X) = T₁₁ X - X T₂₂` on `ℂ^{p×q}` is
nonsingular if and only if `λ(T₁₁) ∩ λ(T₂₂) = ∅`. (The book's SVD argument for "`φ` singular ⇒
a common eigenvalue" is replaced by the characteristic-polynomial argument of the backbone.) -/
theorem lemma_7_1_5 {p q : ℕ} (T₁₁ : Matrix (Fin p) (Fin p) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    Function.Bijective (sylvesterMap T₁₁ T₂₂) ↔ spectrum ℂ T₁₁ ∩ spectrum ℂ T₂₂ = ∅ := by
  rw [sylvesterMap_bijective_iff_disjoint_spectrum, Set.disjoint_iff_inter_eq_empty]

/-- The inverse of the block unit upper triangular `[I Z; 0 I]` is `[I -Z; 0 I]`. -/
private theorem inv_fromBlocks_one {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    (fromBlocks 1 Z 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)⁻¹ = fromBlocks 1 (-Z) 0 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [fromBlocks_multiply]
  simp [fromBlocks_one]

/-- **Lemma 7.1.5, second half.** If `φ(Z) = -T₁₂` and `Y = [I Z; 0 I]`, then
`Y⁻¹ T Y = diag(T₁₁, T₂₂)` for `T = [T₁₁ T₁₂; 0 T₂₂]`. (The book assumes `φ` nonsingular, which
only guarantees that such a `Z` exists.) -/
theorem lemma_7_1_5_blockDiagonal {p q : ℕ} (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₁₂ : Matrix (Fin p) (Fin q) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) {Z : Matrix (Fin p) (Fin q) ℂ}
    (hZ : sylvesterMap T₁₁ T₂₂ Z = -T₁₂) :
    (fromBlocks 1 Z 0 1)⁻¹ * fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromBlocks 1 Z 0 1 =
      fromBlocks T₁₁ 0 0 T₂₂ := by
  rw [inv_fromBlocks_one, fromBlocks_one_neg_mul_fromBlocks_mul_fromBlocks_one]
  rw [sylvesterMap_apply] at hZ
  rw [hZ, neg_add_cancel]

/-- **Theorem 7.1.6 (block diagonal decomposition)** (7.1.9)–(7.1.10). Let `Qᴴ A Q = T` with `Q`
unitary and `T` block upper triangular for the block index `b` (square diagonal blocks
`T_ii = T.toSquareBlock b i`). If `λ(T_ii) ∩ λ(T_jj) = ∅` whenever `i ≠ j`, there is a nonsingular
`Y` with `(Q Y)⁻¹ A (Q Y) = diag(T₁₁, …, T_qq)`, the block diagonal part of `T`. The book prints the
hypothesis as `λ(T_ij) ∩ λ(T_jj) = ∅`, a misprint for `λ(T_ii)`. -/
theorem theorem_7_1_6 {q : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    {b : Fin n → Fin q} (hT : (star Q * A * Q).BlockTriangular b)
    (hdisj : ∀ i j, i ≠ j → spectrum ℂ ((star Q * A * Q).toSquareBlock b i) ∩
      spectrum ℂ ((star Q * A * Q).toSquareBlock b j) = ∅) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y ∧
      (Q * Y)⁻¹ * A * (Q * Y) = of fun i j => if b i = b j then (star Q * A * Q) i j else 0 := by
  obtain ⟨Y, hY, hYT⟩ := exists_isUnit_conj_eq_blockDiagonalPart hT fun i j hij =>
    Set.disjoint_iff_inter_eq_empty.2 (hdisj i j hij)
  refine ⟨Y, hY, ?_⟩
  rw [← hYT, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)]
  simp only [Matrix.mul_assoc]

/-- Reindexing the blocks of a block diagonal matrix along equivalences of the block index
types. -/
private theorem blockDiagonal'_submatrix_sigmaCongrRight {q : ℕ} {κ κ' : Fin q → Type*}
    (M : ∀ i, Matrix (κ' i) (κ' i) ℂ) (f : ∀ i, κ i ≃ κ' i) :
    (blockDiagonal' M).submatrix (Equiv.sigmaCongrRight f) (Equiv.sigmaCongrRight f) =
      blockDiagonal' fun i => (M i).submatrix (f i) (f i) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  rcases eq_or_ne a b with rfl | hab
  · simp only [submatrix_apply, Equiv.sigmaCongrRight_apply, blockDiagonal'_apply_eq]
  · simp only [submatrix_apply, Equiv.sigmaCongrRight_apply, blockDiagonal'_apply_ne _ _ _ hab]

/-- **Corollary 7.1.7** (7.1.11). There is a nonsingular `X` with
`X⁻¹ A X = diag(λ₁ I + N₁, …, λ_q I + N_q)`, the `λ_i` distinct, `N_i ∈ ℂ^{n_i×n_i}` strictly upper
triangular and `n₁ + ⋯ + n_q = n` (the blocks laid out along `Fin n` by `σ`). Read off the Jordan
form grouped by eigenvalue (`Matrix.exists_conj_blockDiagonal'_jordanForm`), whose outer block for
`λ_i` is `λ_i I` plus a direct sum of nilpotent Jordan blocks — a shorter route than the book's
Theorem 7.1.6 applied to an ordered Schur form. -/
theorem corollary_7_1_7 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (q : ℕ) (μ : Fin q → ℂ) (sz : Fin q → ℕ) (N : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℂ)
      (σ : ((i : Fin q) × Fin (sz i)) ≃ Fin n) (X : Matrix (Fin n) (Fin n) ℂ),
      Function.Injective μ ∧ ∑ i, sz i = n ∧ (∀ i a b, b ≤ a → N i a b = 0) ∧ IsUnit X ∧
        X⁻¹ * A * X = reindex σ σ (blockDiagonal' fun i => μ i • (1 : Matrix _ _ ℂ) + N i) := by
  obtain ⟨q, ν, d, e, σ, P, hinj, -, -, hP, hPA⟩ := exists_conj_blockDiagonal'_jordanForm A
  let f : ∀ i : Fin q, ((j : Fin (d i)) × Fin (e i j)) ≃ Fin (∑ j, e i j) :=
    fun _ => finSigmaFinEquiv
  let N : ∀ i : Fin q, Matrix (Fin (∑ j, e i j)) (Fin (∑ j, e i j)) ℂ :=
    fun i => reindex (f i) (f i) (jordanForm (e i) fun _ => (0 : ℂ))
  let τ := Equiv.sigmaCongrRight f
  refine ⟨q, ν, fun i => ∑ j, e i j, N, τ.symm.trans σ, P, hinj, ?_, ?_, hP, ?_⟩
  · have h := Fintype.card_congr (τ.symm.trans σ)
    simpa [Fintype.card_sigma] using h
  · intro i a b hba
    obtain ⟨⟨j, x⟩, rfl⟩ := (f i).surjective a
    obtain ⟨⟨j', y⟩, rfl⟩ := (f i).surjective b
    simp only [N, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, jordanForm_def]
    rcases eq_or_ne j j' with rfl | hjj
    · rw [blockDiagonal'_apply_eq, jordanBlock_zero_apply]
      split_ifs with hxy
      · exfalso
        rw [Fin.le_def] at hba
        simp only [f, finSigmaFinEquiv_apply] at hba
        omega
      · rfl
    · exact blockDiagonal'_apply_ne _ _ _ hjj
  · have hblk : (blockDiagonal' fun i => ν i • (1 : Matrix _ _ ℂ) + N i).submatrix τ τ =
        blockDiagonal' fun i => jordanForm (e i) fun _ => ν i := by
      rw [blockDiagonal'_submatrix_sigmaCongrRight]
      congr 1
      funext i
      rw [jordanForm_const_eq_add_smul_one, add_comm]
      ext a b
      simp [N, reindex_apply, Matrix.add_apply, one_apply]
    rw [hPA, ← hblk]
    ext a b
    simp [reindex_apply, τ]

/-- **§7.1.4, Definition: algebraic multiplicity.** The algebraic multiplicity of `λ` as an
eigenvalue of `A` is its multiplicity as a root of the characteristic polynomial. With it come the
geometric multiplicity (`geometricMultiplicity`), simple eigenvalues (`IsSimpleEigenvalue`) and
defective eigenvalues and matrices (`IsDefectiveEigenvalue`, `IsDefective`). -/
noncomputable def algebraicMultiplicity (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : ℕ :=
  A.charpoly.rootMultiplicity μ

/-- **§7.1.4, Definition: geometric multiplicity**, the number of independent eigenvectors,
`dim null(A - λI)`. -/
noncomputable def geometricMultiplicity (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : ℕ :=
  Module.finrank ℂ (Module.End.eigenspace A.mulVecLin μ)

/-- **§7.1.4, Definition**: `λ` is a *simple* eigenvalue if its algebraic multiplicity is `1`. -/
def IsSimpleEigenvalue (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : Prop :=
  algebraicMultiplicity A μ = 1

/-- **§7.1.4, Definition**: `λ` is a *defective* eigenvalue if its algebraic multiplicity exceeds
its geometric multiplicity. -/
def IsDefectiveEigenvalue (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : Prop :=
  geometricMultiplicity A μ < algebraicMultiplicity A μ

/-- **§7.1.4, Definition**: a *defective* matrix is one with a defective eigenvalue; nondefective
matrices are called diagonalizable (Corollary 7.1.8). -/
def IsDefective (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ μ, IsDefectiveEigenvalue A μ

/-- **Corollary 7.1.8 (diagonal form)** (7.1.12). `A` is nondefective if and only if
`X⁻¹ A X = diag(λ₁, …, λₙ)` for a nonsingular `X`; and then the columns of `X` are right
eigenvectors and the rows of `X⁻¹` left eigenvectors of `A`. -/
theorem corollary_7_1_8 (A : Matrix (Fin n) (Fin n) ℂ) :
    (¬ IsDefective A ↔ ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d : Fin n → ℂ,
      X⁻¹ * A * X = diagonal d) ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ), IsUnit X → X⁻¹ * A * X = diagonal d →
      ∀ i, A *ᵥ X.col i = d i • X.col i ∧ X⁻¹.row i ᵥ* A = d i • X⁻¹.row i := by
  refine ⟨?_, fun X d hX hXA i => ?_⟩
  · have hle : ∀ μ, geometricMultiplicity A μ ≤ algebraicMultiplicity A μ := fun μ =>
      finrank_eigenspace_le_rootMultiplicity_charpoly A μ
    have hiff : ¬ IsDefective A ↔ ∀ μ, geometricMultiplicity A μ = algebraicMultiplicity A μ := by
      simp only [IsDefective, IsDefectiveEigenvalue, not_exists, not_lt]
      exact forall_congr' fun μ => ⟨fun h => le_antisymm (hle μ) h, fun h => h.ge⟩
    rw [hiff]
    unfold geometricMultiplicity algebraicMultiplicity
    rw [← isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity]
    constructor
    · rintro ⟨d, X, hX, hXA⟩
      exact ⟨X, hX, d, hXA.symm⟩
    · rintro ⟨X, hX, d, hXA⟩
      exact ⟨d, X, hX, hXA.symm⟩
  · have hXX : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X ((isUnit_iff_isUnit_det X).1 hX)
    have hXX' : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X ((isUnit_iff_isUnit_det X).1 hX)
    have hAX : A * X = X * diagonal d := by
      rw [← hXA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.one_mul]
    have hXA' : X⁻¹ * A = diagonal d * X⁻¹ := by
      rw [← hXA, Matrix.mul_assoc _ X, hXX, Matrix.mul_one]
    constructor
    · have h : A *ᵥ (X *ᵥ Pi.single i 1) = X *ᵥ (diagonal d *ᵥ Pi.single i 1) := by
        rw [mulVec_mulVec, mulVec_mulVec, hAX]
      rw [diagonal_mulVec_single, mul_one, mulVec_single_one, mulVec_single,
        op_smul_eq_smul] at h
      exact h
    · have h : Pi.single i 1 ᵥ* (X⁻¹ * A) = Pi.single i 1 ᵥ* (diagonal d * X⁻¹) := by
        rw [hXA']
      rw [← vecMul_vecMul, ← vecMul_vecMul, single_one_vecMul, single_vecMul_diagonal, one_mul,
        single_vecMul] at h
      exact h

/-- **§7.1.4, the terms attached to (7.1.11).** In a decomposition as in Corollary 7.1.7, `n_i` is
the algebraic multiplicity of `λ_i` and `dim null(N_i)` is its geometric multiplicity: the blocks
for the other eigenvalues `λ_j - λ_i ≠ 0` are nonsingular. -/
theorem corollary_7_1_7_multiplicity {A X : Matrix (Fin n) (Fin n) ℂ} {q : ℕ} {μ : Fin q → ℂ}
    {sz : Fin q → ℕ} {N : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℂ}
    {σ : ((i : Fin q) × Fin (sz i)) ≃ Fin n} (hμ : Function.Injective μ)
    (hN : ∀ i a b, b ≤ a → N i a b = 0) (hX : IsUnit X)
    (h : X⁻¹ * A * X = reindex σ σ (blockDiagonal' fun i => μ i • (1 : Matrix _ _ ℂ) + N i))
    (i : Fin q) :
    algebraicMultiplicity A (μ i) = sz i ∧
      geometricMultiplicity A (μ i) = Module.finrank ℂ (LinearMap.ker (N i).mulVecLin) := by
  have hsim : IsSimilar A (X⁻¹ * A * X) := ⟨X, hX, rfl⟩
  have hup : ∀ j (c : ℂ),
      (c • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j).IsUpperTriangular :=
    fun j c a b hab => by
    have hab' : b < a := hab
    rw [Matrix.add_apply, Matrix.smul_apply, one_apply_ne (ne_of_gt hab'), smul_zero,
      hN j a b hab'.le, add_zero]
  have hdiag : ∀ j (c : ℂ) a, (c • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j) a a = c :=
    fun j c a => by simp [hN j a a le_rfl]
  constructor
  · have hchar : A.charpoly = ∏ j, (Polynomial.X - C (μ j)) ^ sz j := by
      rw [hsim.charpoly_eq, h, charpoly_reindex, charpoly_blockDiagonal']
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [charpoly_of_isUpperTriangular _ (hup j (μ j))]
      simp [hdiag]
    have hne : ∀ j : Fin q, ((Polynomial.X - C (μ j)) ^ sz j : ℂ[X]) ≠ 0 := fun j =>
      pow_ne_zero _ (X_sub_C_ne_zero _)
    unfold algebraicMultiplicity
    rw [hchar, ← count_roots, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun j _ => hne j),
      show (Finset.univ.val.bind fun j => ((Polynomial.X - C (μ j)) ^ sz j : ℂ[X]).roots)
        = ∑ j, ((Polynomial.X - C (μ j)) ^ sz j : ℂ[X]).roots from rfl,
      Multiset.count_sum', Finset.sum_eq_single i]
    · rw [roots_pow, roots_X_sub_C, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
    · intro j _ hji
      rw [roots_pow, roots_X_sub_C, Multiset.count_nsmul, Multiset.count_singleton]
      have hne' : μ i ≠ μ j := fun h' => hji (hμ h').symm
      simp [hne']
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · unfold geometricMultiplicity
    rw [eigenspace_mulVecLin_eq_ker, (hsim.sub_smul_one (μ i)).finrank_ker_mulVecLin_eq, h]
    have hsub : reindex σ σ (blockDiagonal' fun j => μ j • (1 : Matrix _ _ ℂ) + N j) - μ i • 1 =
        reindex σ σ (blockDiagonal' fun j => μ j • (1 : Matrix _ _ ℂ) + N j - μ i • 1) := by
      rw [← blockDiagonal'_sub_smul_one]
      ext a b
      simp [reindex_apply, Matrix.sub_apply, one_apply]
    rw [hsub, finrank_ker_mulVecLin_reindex, finrank_ker_mulVecLin_blockDiagonal',
      Finset.sum_eq_single i]
    · rw [add_sub_cancel_left]
    · intro j _ hji
      have heq : μ j • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j - μ i • 1 =
          (μ j - μ i) • 1 + N j := by
        rw [sub_smul]; abel
      rw [heq]
      have hdet : ((μ j - μ i) • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j).det ≠ 0 := by
        rw [det_of_isUpperTriangular (hup j _)]
        simp only [hdiag]
        exact Finset.prod_ne_zero_iff.2 fun _ _ => sub_ne_zero.2 (hμ.ne hji)
      have hu : IsUnit ((μ j - μ i) • (1 : Matrix (Fin (sz j)) (Fin (sz j)) ℂ) + N j) :=
        (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      rw [LinearMap.ker_eq_bot.2 (mulVec_injective_iff_isUnit.2 hu), finrank_bot]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-- **Theorem 7.1.9 (Jordan decomposition).** There is a nonsingular `X` with
`X⁻¹ A X = diag(J₁, …, J_q)`, `J_i` the Jordan block of size `n_i ≥ 1` for `λ_i`, `∑ n_i = n` (the
blocks laid out consecutively along the diagonal). -/
theorem theorem_7_1_9 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (q : ℕ) (e : Fin q → ℕ) (μ : Fin q → ℂ) (he : ∑ i, e i = n)
      (X : Matrix (Fin n) (Fin n) ℂ), (∀ i, 0 < e i) ∧ IsUnit X ∧
        X⁻¹ * A * X = reindex (finSigmaFinEquiv.trans (finCongr he))
          (finSigmaFinEquiv.trans (finCongr he)) (jordanForm e μ) :=
  exists_conj_jordanForm A

/-- **The uniqueness remark after Theorem 7.1.9**: "The number and dimensions of the Jordan blocks
associated with each distinct eigenvalue are unique". For two Jordan decompositions of `A`
(blocks of positive size, laid out along `Fin n` by any `σ`, `σ'`), each eigenvalue `c` has the
same number of blocks of each size `k`. -/
theorem theorem_7_1_9_unique {A : Matrix (Fin n) (Fin n) ℂ} {q q' : ℕ} {e : Fin q → ℕ}
    {μ : Fin q → ℂ} {e' : Fin q' → ℕ} {μ' : Fin q' → ℂ} (he : ∀ i, 0 < e i)
    (he' : ∀ i, 0 < e' i) (σ : ((i : Fin q) × Fin (e i)) ≃ Fin n)
    (σ' : ((i : Fin q') × Fin (e' i)) ≃ Fin n) {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (hX' : IsUnit X') (h : X⁻¹ * A * X = reindex σ σ (jordanForm e μ))
    (h' : X'⁻¹ * A * X' = reindex σ' σ' (jordanForm e' μ')) (c : ℂ) (k : ℕ) :
    (Finset.univ.filter fun i => μ i = c ∧ e i = k).card =
      (Finset.univ.filter fun i => μ' i = c ∧ e' i = k).card :=
  card_jordanBlocks_eq_of_isSimilar he he' σ σ' ⟨X, hX, h.symm⟩ ⟨X', hX', h'.symm⟩ c k

/-! ### §7.1.5 Some comments on nonunitary similarity -/

/-- A matrix whose characteristic polynomial has distinct roots is diagonalizable: every eigenvalue
is simple, and an eigenvector makes its geometric multiplicity `1`. -/
private theorem exists_diagonal_of_charpoly_eq_prod {A : Matrix (Fin n) (Fin n) ℂ}
    {d : Fin n → ℂ} (hd : Function.Injective d)
    (h : A.charpoly = ∏ i, (Polynomial.X - C (d i))) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d' : Fin n → ℂ, X⁻¹ * A * X = diagonal d' := by
  refine (corollary_7_1_8 A).1.1 ?_
  rintro ⟨μ, hμ⟩
  unfold IsDefectiveEigenvalue at hμ
  have hroots : A.charpoly.roots = Finset.univ.val.map d := by
    rw [h, show (∏ i, (Polynomial.X - C (d i))) =
      ((Finset.univ.val.map d).map fun a => Polynomial.X - C a).prod by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hle : algebraicMultiplicity A μ ≤ 1 := by
    unfold algebraicMultiplicity
    rw [← count_roots, hroots]
    exact Multiset.nodup_iff_count_le_one.1 (Finset.univ.nodup.map hd) μ
  have hpos : 0 < algebraicMultiplicity A μ := lt_of_le_of_lt (Nat.zero_le _) hμ
  have hroot : A.charpoly.IsRoot μ := (rootMultiplicity_pos A.charpoly_monic.ne_zero).1 hpos
  obtain ⟨v, hv0, hv⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).1
    (Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot)
  have hgeo : geometricMultiplicity A μ = 0 := by omega
  unfold geometricMultiplicity at hgeo
  have hmem : v ∈ Module.End.eigenspace A.mulVecLin μ := by
    rw [Module.End.mem_eigenspace_iff]; exact hv
  rw [Submodule.finrank_eq_zero.1 hgeo, Submodule.mem_bot] at hmem
  exact hv0 hmem

/-- **§7.1.5: "The set of `n`-by-`n` diagonalizable matrices is dense in `ℂ^{n×n}`"** (the book's
P7.1.5). From a Schur form `Qᴴ A Q = T`, the matrices `Q (T + t diag(0, 1, …, n-1)) Qᴴ` tend to `A`
as `t → 0`, and for all but finitely many `t` their (triangular) diagonal entries are distinct. -/
theorem dense_diagonalizable :
    Dense {A : Matrix (Fin n) (Fin n) ℂ |
      ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d : Fin n → ℂ, X⁻¹ * A * X = diagonal d} := by
  intro A
  obtain ⟨Q, hQ, hT, -⟩ := exists_unitary_conj_upperTriangular A
  set T := star Q * A * Q
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => ((i : ℕ) : ℂ)
  set F : ℂ → Matrix (Fin n) (Fin n) ℂ := fun t => Q * (T + t • D) * star Q
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hF0 : F 0 = A := by
    simp only [F, T, zero_smul, add_zero, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hcont : Continuous F :=
    (continuous_const.matrix_mul
      (continuous_const.add (continuous_id.smul continuous_const))).matrix_mul continuous_const
  -- the finitely many shifts for which two diagonal entries coincide
  set bad : Set ℂ :=
    Set.range fun p : Fin n × Fin n => (T p.2 p.2 - T p.1 p.1) / ((p.1 : ℕ) - (p.2 : ℕ) : ℂ)
  have hgood : ∀ t, t ∉ bad → F t ∈ {A : Matrix (Fin n) (Fin n) ℂ |
      ∃ X : Matrix (Fin n) (Fin n) ℂ, IsUnit X ∧ ∃ d : Fin n → ℂ, X⁻¹ * A * X = diagonal d} := by
    intro t ht
    have hup : (T + t • D).IsUpperTriangular := fun i j hij => by
      have hij' : j < i := hij
      simp [D, hT hij, diagonal_apply_ne _ (ne_of_gt hij')]
    have hinj : Function.Injective fun i => (T + t • D) i i := by
      intro i j hij
      by_contra hne
      apply ht
      refine ⟨(i, j), ?_⟩
      simp only [D, Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul] at hij
      have hsub : ((i : ℕ) : ℂ) - (j : ℕ) ≠ 0 := by
        rw [sub_ne_zero, Ne, Nat.cast_inj]
        exact fun h' => hne (Fin.ext h')
      rw [div_eq_iff hsub]
      linear_combination -hij
    have hsim : IsSimilar (F t) (T + t • D) := by
      refine ⟨Q, (Matrix.isUnit_iff_isUnit_det _).2
        (Matrix.isUnit_det_of_right_inverse hQQ), ?_⟩
      rw [Matrix.inv_eq_left_inv hQQ']
      simp only [F, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
    exact exists_diagonal_of_charpoly_eq_prod hinj
      (by rw [hsim.charpoly_eq, charpoly_of_isUpperTriangular _ hup])
  have hbad : bad.Finite := Set.finite_range _
  have hev : ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, t ∉ bad := by
    have h1 : (bad \ {0})ᶜ ∈ nhds (0 : ℂ) :=
      (hbad.subset Set.sdiff_subset).isClosed.compl_mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht ht0
    exact fun hb => ht ⟨hb, ht0⟩
  have hlim : Filter.Tendsto F (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds A) :=
    hF0 ▸ (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlim (hev.mono hgood)

/-! ### §7.1.6 Singular values and eigenvalues -/

section L2

open scoped Matrix.Norms.L2Operator

/-- **§7.1.6.** `σ_min(A) ≤ |λ| ≤ σ_max(A) = ‖A‖₂` for every eigenvalue `λ` of `A`; and (the
rigorous half of the remark that follows) `|λ_i| / |λ_j| ≤ κ₂(A)` for a nonsingular `A`. -/
theorem sigmaMin_le_norm_eigenvalue [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ μ ∈ spectrum ℂ A, (⨅ i, A.colSingularValues i) ≤ ‖μ‖ ∧ ‖μ‖ ≤ ⨆ i, A.colSingularValues i) ∧
    ‖A‖ = ⨆ i, A.colSingularValues i ∧
    (IsUnit A → ∀ μ ∈ spectrum ℂ A, ∀ ν ∈ spectrum ℂ A,
      ‖μ‖ / ‖ν‖ ≤ NormedRing.condNumber A) := by
  have hbound : ∀ μ ∈ spectrum ℂ A,
      (⨅ i, A.colSingularValues i) ≤ ‖μ‖ ∧ ‖μ‖ ≤ ⨆ i, A.colSingularValues i := by
    intro μ hμ
    obtain ⟨x, hx0, hx⟩ := (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A μ).1 hμ
    set y : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
    have hy0 : ‖y‖ ≠ 0 := by simpa [y] using hx0
    have hAy : ‖toEuclideanLin A y‖ = ‖μ‖ * ‖y‖ := by
      rw [toLpLin_toLp, toLin'_apply, hx, WithLp.toLp_smul, norm_smul]
    have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    constructor
    · have h := A.iInf_colSingularValues_mul_norm_le y
      rw [hAy] at h
      exact le_of_mul_le_mul_right h hpos
    · have h := A.norm_toEuclideanLin_le_iSup_colSingularValues y
      rw [hAy] at h
      exact le_of_mul_le_mul_right h hpos
  refine ⟨hbound, l2_opNorm_eq_iSup_colSingularValues A, fun hA μ hμ ν hν => ?_⟩
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  -- `σ_min > 0`: otherwise `‖A⁻¹‖ = 0`
  have hmin : 0 < ⨅ i, A.colSingularValues i := by
    refine lt_of_le_of_ne (le_ciInf fun i => A.colSingularValues_nonneg i) fun h0 => ?_
    have hinv := l2_opNorm_inv_eq_inv_iInf_colSingularValues A hdet
    rw [← h0, _root_.inv_zero, norm_eq_zero] at hinv
    have h1 := Matrix.mul_nonsing_inv A hdet
    rw [hinv, Matrix.mul_zero] at h1
    exact zero_ne_one h1
  rw [condNumber_l2_eq_div_colSingularValues A hdet]
  exact div_le_div₀ ((norm_nonneg μ).trans (hbound μ hμ).2) (hbound μ hμ).2 hmin
    (hbound ν hν).1

/-- An entry is bounded by the 2-norm. -/
private theorem norm_entry_le_lpOpNorm_two {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) (i : Fin m)
    (j : Fin k) : ‖M i j‖ ≤ lpOpNorm 2 M := by
  rw [lpOpNorm_two]
  exact norm_entry_le_l2_opNorm M i j

end L2

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- The 2-norm is at most the Frobenius norm, written out entrywise. -/
private theorem lpOpNorm_two_le_sqrt {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    lpOpNorm 2 M ≤ √(∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  rw [← frobenius_norm_sq_eq_sum_sq, Real.sqrt_sq (norm_nonneg _)]
  exact l2_opNorm_le_frobenius_norm M

end Frobenius

/-- **(7.1.13)**: for `0 < ε`, every `X` diagonalizing `A = [1 + ε, 1; 0, 1 - ε]` has
`κ₂(X) ≥ 1/(2ε)`, and some diagonalizing `X` has `κ₂(X) ≤ 1/ε + 2ε` — the rigorous reading of
"a 2-norm condition of order `1/ε`". If `X⁻¹ A X` is diagonal, the column `x` of `X` and the row
`yᴴ` of `X⁻¹` belonging to `λ = 1 + ε` are right and left eigenvectors with `yᴴ x = 1`; the
eigenvector equations force `x = (x₁, 0)` and `y₁ = 2ε y₂`, so `2ε x₁ y₂ = 1`. -/
theorem equation_7_1_13 {ε : ℝ} (hε : 0 < ε) :
    (∀ (X : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ), IsUnit X →
      X⁻¹ * !![1 + (ε : ℂ), 1; 0, 1 - ε] * X = diagonal d → 1 / (2 * ε) ≤ condNumberLp 2 X) ∧
    ∃ X : Matrix (Fin 2) (Fin 2) ℂ, IsUnit X ∧
      (∃ d : Fin 2 → ℂ, X⁻¹ * !![1 + (ε : ℂ), 1; 0, 1 - ε] * X = diagonal d) ∧
      condNumberLp 2 X ≤ 1 / ε + 2 * ε := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![1 + (ε : ℂ), 1; 0, 1 - ε] with hA
  constructor
  · intro X d hX h
    have hdet : IsUnit X.det := (isUnit_iff_isUnit_det X).1 hX
    -- `1 + ε` is an eigenvalue, hence a diagonal entry of `X⁻¹ A X`
    have hmem : (1 + ε : ℂ) ∈ spectrum ℂ A := by
      refine (Matrix.mem_spectrum_iff_exists_mulVec_eq_smul A _).2 ⟨![1, 0], ?_, ?_⟩
      · intro h0
        have := congrFun h0 0
        simp at this
      · ext i
        fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two]
    rw [IsSimilar.spectrum_eq ⟨X, hX, rfl⟩, h, spectrum_diagonal] at hmem
    obtain ⟨k, hk⟩ := hmem
    obtain ⟨hcol, hrow⟩ := (corollary_7_1_8 A).2 X d hX h k
    rw [hk] at hcol hrow
    have h1 : (1 - (ε : ℂ)) * X 1 k = (1 + ε) * X 1 k := by
      have := congrFun hcol 1
      simpa [A, mulVec, dotProduct, Fin.sum_univ_two] using this
    have h2 : X⁻¹ k 0 + X⁻¹ k 1 * (1 - ε) = (1 + ε) * X⁻¹ k 1 := by
      have := congrFun hrow 1
      simpa [A, vecMul, dotProduct, Fin.sum_univ_two, mul_comm] using this
    have h3 : X⁻¹ k 0 * X 0 k + X⁻¹ k 1 * X 1 k = 1 := by
      have := congrFun (congrFun (Matrix.nonsing_inv_mul X hdet) k) k
      simpa [mul_apply, Fin.sum_univ_two] using this
    have hx : X 1 k = 0 := by
      have h4 : (2 * ε : ℂ) * X 1 k = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd h5 (mul_ne_zero two_ne_zero hε')
      · exact h5
    have h5 : (2 * ε : ℂ) * (X⁻¹ k 1 * X 0 k) = 1 := by
      rw [hx, mul_zero, add_zero] at h3
      linear_combination h3 - X 0 k * h2
    have h6 : ‖X 0 k‖ * ‖X⁻¹ k 1‖ = 1 / (2 * ε) := by
      have h7 := congrArg norm h5
      rw [norm_mul, norm_mul, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le,
        Complex.norm_two] at h7
      field_simp
      linarith
    rw [← h6, condNumberLp]
    exact mul_le_mul (norm_entry_le_lpOpNorm_two X 0 k) (norm_entry_le_lpOpNorm_two X⁻¹ k 1)
      (norm_nonneg _) ((norm_nonneg _).trans (norm_entry_le_lpOpNorm_two X 0 k))
  · set X : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, -(2 * ε : ℂ)] with hXdef
    set Y : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1 / (2 * ε : ℂ); 0, -(1 / (2 * ε : ℂ))] with hYdef
    have hYX : Y * X = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [X, Y, mul_apply, Fin.sum_univ_two]
      · simpa [X, Y, mul_apply, Fin.sum_univ_two] using
          (show (1 : ℂ) * 1 + 1 / (2 * ε) * -(2 * ε) = 0 by field_simp; ring)
      · simp [X, Y, mul_apply, Fin.sum_univ_two]
      · simpa [X, Y, mul_apply, Fin.sum_univ_two] using
          (show (0 : ℂ) * 1 + -(1 / (2 * ε)) * -(2 * ε) = 1 by field_simp; ring)
    have hinv : X⁻¹ = Y := Matrix.inv_eq_left_inv hYX
    have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 (isUnit_det_of_left_inverse hYX)
    refine ⟨X, hXu, ⟨![1 + ε, 1 - ε], ?_⟩, ?_⟩
    · have hAX : A * X = X * diagonal ![1 + (ε : ℂ), 1 - ε] := by
        ext i j
        fin_cases i <;> fin_cases j
        · simp [X, A, mul_apply, Fin.sum_univ_two]
        · simpa [X, A, mul_apply, Fin.sum_univ_two] using
            (show (1 + ε : ℂ) * 1 + 1 * -(2 * ε) = 1 * (1 - ε) by ring)
        · simp [X, A, mul_apply, Fin.sum_univ_two]
        · simpa [X, A, mul_apply, Fin.sum_univ_two] using
            (show (0 : ℂ) * 1 + (1 - ε) * -(2 * ε) = -(2 * ε) * (1 - ε) by ring)
      rw [Matrix.mul_assoc, hAX, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul X ((isUnit_iff_isUnit_det X).1 hXu), Matrix.one_mul]
    · have hXn : lpOpNorm 2 X ≤ √(2 + 4 * ε ^ 2) :=
        (lpOpNorm_two_le_sqrt X).trans_eq (by
          congr 1
          simp [X, Fin.sum_univ_two, mul_pow]
          ring)
      have hYn : lpOpNorm 2 Y ≤ √(1 + 1 / (2 * ε ^ 2)) :=
        (lpOpNorm_two_le_sqrt Y).trans_eq (by
          congr 1
          simp [Y, Fin.sum_univ_two, mul_pow]
          field_simp
          ring)
      rw [condNumberLp, hinv]
      calc lpOpNorm 2 X * lpOpNorm 2 Y ≤ √(2 + 4 * ε ^ 2) * √(1 + 1 / (2 * ε ^ 2)) :=
            mul_le_mul hXn hYn (lpOpNorm_nonneg 2 Y) (Real.sqrt_nonneg _)
        _ = 1 / ε + 2 * ε := by
          rw [← Real.sqrt_mul (by positivity),
            show (2 + 4 * ε ^ 2) * (1 + 1 / (2 * ε ^ 2)) = (1 / ε + 2 * ε) ^ 2 by
              field_simp
              ring,
            Real.sqrt_sq (by positivity)]

end GolubVanLoan.Chapter07
