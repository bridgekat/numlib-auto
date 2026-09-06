import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Schur

/-!
# Saad §1.8: canonical forms of matrices

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §1.8: similarity and the canonical forms — diagonal (§1.8.1), Jordan (§1.8.2) and Schur
(§1.8.3) — and the application to powers of matrices (§1.8.4).

**Theorem 1.8, the Jordan canonical form, is not stated.** Mathlib has no Jordan form, the book
states it without proof, and nothing in this library needs it: the two results the book derives
from it, Theorems 1.10 and 1.11, are proved in `Numlib/LinearAlgebra/Matrix/Complexify` from
Gelfand's formula instead. The multiplicity vocabulary the section introduces around it —
algebraic and geometric multiplicity, simple, semisimple, defective, derogatory — is Mathlib's
`Module.End.eigenspace`, `Module.End.maxGenEigenspace` and `Polynomial.rootMultiplicity` of the
characteristic polynomial, and gets no declaration here.

Similarity is a surface definition, `SaadSparse.Chapter01.IsSimilar`, because the book's `A = X B
X⁻¹` with `X` nonsingular is what every statement of the section uses; it is an equivalence
relation, it transports eigenvectors, and it preserves the characteristic polynomial (Problem
P-1.9).

Theorems 1.10, 1.11 and 1.12 are the backbone's, in stronger form, and are restated here in the
book's words. Theorem 1.12, Gelfand's formula, is stated for the Euclidean operator norm; the book
states it for an arbitrary matrix norm and defers the proof to Problem P-1.10.
-/

open Matrix Filter Topology
open scoped ENNReal

namespace SaadSparse.Chapter01

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### §1.8 Definition 1.5: similarity -/

/-- **Saad Definition 1.5**: two matrices are *similar* when `A = X B X⁻¹` for some nonsingular
`X`. The book's phrase "there is a nonsingular matrix `X` such that …" is the `IsUnit X` here. -/
def IsSimilar (A B : Matrix (Fin n) (Fin n) 𝕜) : Prop := ∃ X, IsUnit X ∧ A = X * B * X⁻¹

/-- Similarity is reflexive. -/
theorem IsSimilar.refl (A : Matrix (Fin n) (Fin n) 𝕜) : IsSimilar A A :=
  ⟨1, isUnit_one, by simp⟩

/-- Similarity is symmetric. -/
theorem IsSimilar.symm {A B : Matrix (Fin n) (Fin n) 𝕜} (h : IsSimilar A B) : IsSimilar B A := by
  obtain ⟨X, hX, rfl⟩ := h
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  refine ⟨X⁻¹, Matrix.isUnit_nonsing_inv_iff.2 hX, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv X hd]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul X hd, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul X hd, Matrix.one_mul]

/-- Similarity is transitive. -/
theorem IsSimilar.trans {A B C : Matrix (Fin n) (Fin n) 𝕜} (hAB : IsSimilar A B)
    (hBC : IsSimilar B C) : IsSimilar A C := by
  obtain ⟨X, hX, rfl⟩ := hAB
  obtain ⟨Y, hY, rfl⟩ := hBC
  refine ⟨X * Y, hX.mul hY, ?_⟩
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/-- Similar matrices have the same eigenvalues, with the eigenvectors transported by `X`: if
`B u = μ u` then `A (X u) = μ (X u)`. This is the content the book draws from Definition 1.5. -/
theorem mulVec_eq_smul_of_isSimilar {A B X : Matrix (Fin n) (Fin n) 𝕜} (hX : IsUnit X)
    (hAB : A = X * B * X⁻¹) {μ : 𝕜} {u : Fin n → 𝕜} (hu : B *ᵥ u = μ • u) :
    A *ᵥ (X *ᵥ u) = μ • (X *ᵥ u) := by
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  have h1 : A * X = X * B := by
    rw [hAB, Matrix.mul_assoc, Matrix.nonsing_inv_mul X hd, Matrix.mul_one]
  calc A *ᵥ (X *ᵥ u) = (A * X) *ᵥ u := by rw [Matrix.mulVec_mulVec]
    _ = (X * B) *ᵥ u := by rw [h1]
    _ = X *ᵥ (B *ᵥ u) := by rw [Matrix.mulVec_mulVec]
    _ = X *ᵥ (μ • u) := by rw [hu]
    _ = μ • (X *ᵥ u) := by rw [Matrix.mulVec_smul]

/-- **Saad Problem P-1.9**: similar matrices have the same characteristic polynomial, so the
eigenvalues of `A` and `B` agree with their algebraic multiplicities. -/
theorem charpoly_eq_of_isSimilar {A B : Matrix (Fin n) (Fin n) 𝕜} (h : IsSimilar A B) :
    A.charpoly = B.charpoly := by
  obtain ⟨X, hX, rfl⟩ := h
  have h1 := Matrix.charpoly_units_conj hX.unit B
  rwa [IsUnit.unit_spec] at h1

/-! ### §1.8.1 Theorem 1.6: diagonalizability -/

/-- **Saad Theorem 1.6**: a matrix is *diagonalizable* — similar to a diagonal matrix — exactly
when it has `n` linearly independent eigenvectors. Both directions read the relation `A X = X D`
column by column: the columns of the transforming matrix `X` are the eigenvectors, and `X` is
nonsingular exactly when they are independent. -/
theorem theorem_1_6 (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∃ d : Fin n → 𝕜, IsSimilar A (Matrix.diagonal d)) ↔
      ∃ (d : Fin n → 𝕜) (v : Fin n → Fin n → 𝕜),
        LinearIndependent 𝕜 v ∧ ∀ j, A *ᵥ v j = d j • v j := by
  constructor
  · rintro ⟨d, X, hX, hA⟩
    have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
    have hAX : A * X = X * Matrix.diagonal d := by
      rw [hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul X hd, Matrix.mul_one]
    refine ⟨d, X.col, Matrix.linearIndependent_cols_iff_isUnit.2 hX, fun j => ?_⟩
    funext i
    have h := congrFun (congrFun hAX i) j
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    change ∑ k, A i k * X k j = d j * X i j
    rw [h]
    exact mul_comm _ _
  · rintro ⟨d, v, hv, hvA⟩
    have hX : IsUnit ((Matrix.of v)ᵀ) := Matrix.linearIndependent_cols_iff_isUnit.1 hv
    have hd : IsUnit ((Matrix.of v)ᵀ).det := (Matrix.isUnit_iff_isUnit_det _).1 hX
    have hAX : A * (Matrix.of v)ᵀ = (Matrix.of v)ᵀ * Matrix.diagonal d := by
      ext i j
      have h := congrFun (hvA j) i
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [show ((Matrix.of v)ᵀ) i j = v j i from rfl, mul_comm]
      exact h
    exact ⟨d, (Matrix.of v)ᵀ, hX, by
      rw [← hAX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]⟩

/-- Saad's corollary to Proposition 1.7, which is Problem P-1.2: eigenvectors belonging to
distinct eigenvalues are linearly independent, so a matrix with `n` distinct eigenvalues is
diagonalizable. -/
theorem diagonalizable_of_injective_eigenvalues {A : Matrix (Fin n) (Fin n) 𝕜} {d : Fin n → 𝕜}
    (hd : Function.Injective d) {v : Fin n → Fin n → 𝕜} (hv : ∀ j, v j ≠ 0)
    (hAv : ∀ j, A *ᵥ v j = d j • v j) : ∃ e : Fin n → 𝕜, IsSimilar A (Matrix.diagonal e) :=
  (theorem_1_6 A).2 ⟨d, v, Module.End.eigenvectors_linearIndependent' A.mulVecLin d hd v
    fun j => ⟨Module.End.mem_eigenspace_iff.2 (hAv j), hv j⟩, hAv⟩

/-! ### §1.8.2 Proposition 1.7: semisimple eigenvalues -/

/-- If the eigenvectors of `f` span the whole space then no eigenvalue is defective: the maximal
generalized eigenspace of `μ` is already the eigenspace of `μ`. The reason is that `f - μ` maps
every *other* eigenspace into itself and annihilates the `μ`-eigenspace, so its range misses the
`μ`-eigenspace; a vector killed by `(f - μ)²` therefore has `(f - μ) v` in both, hence zero, and
the general power follows by induction. -/
private theorem maxGenEigenspace_le_eigenspace {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {f : Module.End K M} (hf : (⨆ μ : K, Module.End.eigenspace f μ) = ⊤) (μ : K) :
    Module.End.maxGenEigenspace f μ ≤ Module.End.eigenspace f μ := by
  set g := f - μ • (1 : Module.End K M) with hg
  have hgx : ∀ x : M, g x = f x - μ • x := by
    intro x
    rw [hg]
    simp
  have hker : Module.End.eigenspace f μ = LinearMap.ker g := by
    rw [hg, Module.End.eigenspace_def]
  have hmapν : ∀ ν : K,
      Submodule.map g (Module.End.eigenspace f ν) ≤ Module.End.eigenspace f ν := by
    rintro ν _ ⟨x, hx, rfl⟩
    have hx' : f x = ν • x := Module.End.mem_eigenspace_iff.1 hx
    have hgv : g x = (ν - μ) • x := by rw [hgx, hx', sub_smul]
    rw [Module.End.mem_eigenspace_iff, hgv, map_smul, hx', smul_comm]
  have hmapμ : Submodule.map g (Module.End.eigenspace f μ) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : f x = μ • x := Module.End.mem_eigenspace_iff.1 hx
    rw [hgx, hx', sub_self]
  have hrange : LinearMap.range g ≤ ⨆ (ν : K) (_ : ν ≠ μ), Module.End.eigenspace f ν := by
    have h1 : LinearMap.range g = Submodule.map g (⨆ ν : K, Module.End.eigenspace f ν) := by
      rw [hf, Submodule.map_top]
    rw [h1, Submodule.map_iSup]
    refine iSup_le fun ν => ?_
    rcases eq_or_ne ν μ with rfl | hν
    · rw [hmapμ]
      exact bot_le
    · exact (hmapν ν).trans (le_iSup_of_le ν (le_iSup_of_le hν le_rfl))
  have hdisj := iSupIndep_def.1 (Module.End.eigenspaces_iSupIndep f) μ
  have key : ∀ x : M, g (g x) = 0 → g x = 0 := by
    intro x hx
    refine Submodule.disjoint_def.1 hdisj (g x) ?_ (hrange (LinearMap.mem_range_self g x))
    rw [hker, LinearMap.mem_ker]
    exact hx
  have hpow : ∀ (k : ℕ) (x : M), (g ^ k) x = 0 → g x = 0 := by
    intro k
    induction k with
    | zero =>
        intro x hx
        rw [pow_zero, Module.End.one_apply] at hx
        rw [hx, map_zero]
    | succ k ih =>
        intro x hx
        rw [pow_succ, Module.End.mul_apply] at hx
        exact key x (ih (g x) hx)
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  rw [hker, LinearMap.mem_ker]
  exact hpow k v (by rw [hg]; exact hk)

/-- Diagonalizability is exactly the statement that the eigenspaces span: Theorem 1.6 transported
to the operator `A.mulVecLin`. -/
theorem isSimilar_diagonal_iff_iSup_eigenspace (A : Matrix (Fin n) (Fin n) 𝕜) :
    (∃ d : Fin n → 𝕜, IsSimilar A (Matrix.diagonal d)) ↔
      (⨆ μ : 𝕜, Module.End.eigenspace A.mulVecLin μ) = ⊤ := by
  rw [theorem_1_6]
  constructor
  · rintro ⟨d, v, hv, hvA⟩
    have hcard : Fintype.card (Fin n) = Module.finrank 𝕜 (Fin n → 𝕜) := by
      rw [Module.finrank_fin_fun, Fintype.card_fin]
    have hspan : Submodule.span 𝕜 (Set.range v) = ⊤ :=
      hv.span_eq_top_of_card_eq_finrank' hcard
    refine top_le_iff.1 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (d j) (Module.End.mem_eigenspace_iff.2 (hvA j))
  · intro hsup
    obtain ⟨b, hbsub, hbspan, hbind⟩ :=
      exists_linearIndependent 𝕜 (⋃ μ : 𝕜, (Module.End.eigenspace A.mulVecLin μ : Set (Fin n → 𝕜)))
    have hbtop : Submodule.span 𝕜 b = ⊤ := by
      rw [hbspan, ← Submodule.iSup_eq_span]
      exact hsup
    have hbas : Module.Basis b 𝕜 (Fin n → 𝕜) :=
      Module.Basis.mk hbind (by rw [Subtype.range_coe, hbtop])
    have hfin : Fintype b := FiniteDimensional.fintypeBasisIndex hbas
    have hcard : Fintype.card b = n := by
      rw [← Module.finrank_eq_card_basis hbas, Module.finrank_fin_fun]
    have hchoice : ∀ x : b, ∃ μ : 𝕜,
        (x : Fin n → 𝕜) ∈ Module.End.eigenspace A.mulVecLin μ := by
      intro x
      simpa using hbsub x.2
    choose dd hdd using hchoice
    obtain ⟨e⟩ : Nonempty (b ≃ Fin n) := ⟨Fintype.equivFinOfCardEq hcard⟩
    refine ⟨fun j => dd (e.symm j), fun j => (e.symm j : Fin n → 𝕜),
      hbind.comp _ e.symm.injective, fun j => ?_⟩
    exact Module.End.mem_eigenspace_iff.1 (hdd (e.symm j))

/-- **Saad Proposition 1.7**: over `ℂ`, a matrix is diagonalizable if and only if every eigenvalue
is *semisimple* — its eigenspace is already the whole maximal generalized eigenspace, so the
geometric and algebraic multiplicities agree. One direction is that the generalized eigenspaces
always span over an algebraically closed field; the other is that a spanning family of eigenspaces
leaves no room for a defective eigenvalue. Saad's corollary, that `n` distinct eigenvalues force
diagonalizability, is `SaadSparse.Chapter01.diagonalizable_of_injective_eigenvalues`. -/
theorem proposition_1_7 (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ d : Fin n → ℂ, IsSimilar A (Matrix.diagonal d)) ↔
      ∀ μ : ℂ, Module.End.eigenspace A.mulVecLin μ =
        Module.End.maxGenEigenspace A.mulVecLin μ := by
  rw [isSimilar_diagonal_iff_iSup_eigenspace]
  constructor
  · exact fun hsup μ => le_antisymm Module.End.eigenspace_le_maxGenEigenspace
      (maxGenEigenspace_le_eigenspace hsup μ)
  · intro hss
    calc (⨆ μ : ℂ, Module.End.eigenspace A.mulVecLin μ)
        = ⨆ μ : ℂ, Module.End.maxGenEigenspace A.mulVecLin μ := iSup_congr hss
      _ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top _

/-! ### §1.8.3 Theorem 1.9: the Schur canonical form -/

/-- **Saad Theorem 1.9**, the Schur canonical form: every complex square matrix is unitarily
similar to an upper triangular matrix, whose diagonal carries the eigenvalues of `A` with their
algebraic multiplicities. The alternative proof from the Jordan form and a QR factorization
(Problem P-1.7) is not available here, the Jordan form not being. -/
theorem theorem_1_9 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ,
      (star Q * A * Q).IsUpperTriangular ∧
        A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((star Q * A * Q) i i)) :=
  Matrix.exists_unitary_conj_upperTriangular A

/-- The consequence Saad draws from Theorem 1.9: the span of the first `k` Schur vectors — the
first `k` columns of `Q` — is invariant under `A`, which is the *partial* Schur decomposition
`A Q_k = Q_k R_k`. At `k = 1` it says that `q₁` is an eigenvector of `A`.

The quasi-Schur (real Schur) form with `2 × 2` diagonal blocks is not stated: the book gives it
without proof and nothing here needs it. -/
theorem theorem_1_9_partial {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hR : (star Q * A * Q).IsUpperTriangular) (k : ℕ)
    {v : Fin n → ℂ} (hv : v ∈ Submodule.span ℂ (Q.col '' {i : Fin n | (i : ℕ) < k})) :
    A *ᵥ v ∈ Submodule.span ℂ (Q.col '' {i : Fin n | (i : ℕ) < k}) := by
  have hQstar : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ
  have hAQ : A * Q = Q * (star Q * A * Q) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQstar, Matrix.one_mul]
  have hgen : ∀ j : Fin n, (j : ℕ) < k →
      A *ᵥ Q.col j ∈ Submodule.span ℂ (Q.col '' {i : Fin n | (i : ℕ) < k}) := by
    intro j hj
    have hcol : A *ᵥ Q.col j = ∑ l, (star Q * A * Q) l j • Q.col l := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h := congrFun (congrFun hAQ i) j
      simp only [Matrix.mul_apply] at h
      rw [h]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hcol]
    refine Submodule.sum_mem _ fun l _ => ?_
    rcases le_or_gt (l : ℕ) (j : ℕ) with hlj | hlj
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨l, by simpa using lt_of_le_of_lt hlj hj, rfl⟩)
    · rw [hR (by exact_mod_cast hlj), zero_smul]
      exact Submodule.zero_mem _
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact hgen j hj
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

/-! ### §1.8.4 Theorems 1.10–1.12: powers of a matrix -/

/-- **Saad Theorem 1.10**: `A^k → 0` exactly when the spectral radius of `A` is less than `1`.
The book proves the hard direction with the Jordan form; the backbone proves it with Gelfand's
formula, in `Numlib/LinearAlgebra/Matrix/Complexify`. Cited by Theorem 4.1. -/
theorem theorem_1_10 (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ A.complexSpectralRadius < 1 :=
  Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one A

open scoped Matrix.Norms.L2Operator in
/-- **Saad Theorem 1.11**: the Neumann series `∑ A^k` converges exactly when the spectral radius
is less than `1`. Stated over `ℂ` for the Euclidean operator norm, which is where the Banach
algebra machinery lives. -/
theorem theorem_1_11 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (Summable fun k => A ^ k) ↔ spectralRadius ℂ A < 1 :=
  summable_pow_iff_spectralRadius_lt_one A

/-- The second half of **Saad Theorem 1.11**: when the spectral radius is less than `1`, the
matrix `I - A` is nonsingular. For a real matrix it is the complex spectral radius that decides,
because `spectrum ℝ` can miss the eigenvalues altogether. Cited by Theorem 1.29 and by §4.1.2. -/
theorem theorem_1_11_isUnit {A : Matrix (Fin n) (Fin n) ℝ} (h : A.complexSpectralRadius < 1) :
    IsUnit (1 - A) :=
  Matrix.isUnit_one_sub_of_complexSpectralRadius_lt_one h

open scoped Matrix.Norms.L2Operator in
/-- **Saad Theorem 1.12**, Gelfand's formula: `‖A^k‖^{1/k} → ρ(A)`. Stated for the Euclidean
operator norm; the book states it for any matrix norm and defers the proof to Problem P-1.10.
Cited by Theorem 1.28 and by §4.2.1. -/
theorem theorem_1_12 (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) :=
  Matrix.tendsto_pow_rpow_complexSpectralRadius A

end SaadSparse.Chapter01
