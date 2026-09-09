import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Numlib.Analysis.Normed.Module.NormEquivalence
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.Schur

/-!
# Saad §1.8: canonical forms of matrices

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §1.8: similarity and the canonical forms — diagonal (§1.8.1), Jordan (§1.8.2) and Schur
(§1.8.3) — and the application to powers of matrices (§1.8.4).

§1.8.3 gets both Schur forms: `theorem_1_9` is the complex triangulation and `realSchur` the
quasi-Schur (real Schur) form, which the book states without proof.

§1.8.2 gets the Jordan canonical form, `theorem_1_8`, from the backbone's
`Numlib/LinearAlgebra/Matrix/Jordan`, which builds it from scratch: Mathlib has none. The two
results the book derives from it, Theorems 1.10 and 1.11, are nonetheless proved in
`Numlib/LinearAlgebra/Matrix/Complexify` from Gelfand's formula instead, which needs less.

Theorem 1.8 states a block structure and then identifies the three numbers in it. `theorem_1_8` is
the block structure; the identifications are `theorem_1_8_geometricMultiplicity`,
`theorem_1_8_algebraicMultiplicity` and `theorem_1_8_index`, three separate statements about a
decomposition of that shape rather than three more clauses of one existential, so that a consumer
can use the structure without unpacking the arithmetic and the other way round.

The multiplicity vocabulary the section introduces around them — algebraic and geometric
multiplicity, simple, semisimple, defective, derogatory — is Mathlib's `Module.End.eigenspace`,
`Module.End.maxGenEigenspace` and `Polynomial.rootMultiplicity` of the characteristic polynomial,
and gets no definition here; the index of an eigenvalue is spelled out where it is used, as the
least `k` at which `Null (A - λ I)^k` stops growing.

Similarity is a surface definition, `SaadSparse.Chapter01.IsSimilar`, because the book's `A = X B
X⁻¹` with `X` nonsingular is what every statement of the section uses; it is an equivalence
relation, it transports eigenvectors, and it preserves the characteristic polynomial (Problem
P-1.9).

Theorems 1.10, 1.11 and 1.12 are the backbone's, in stronger form, and are restated here in the
book's words. Theorem 1.12, Gelfand's formula, comes twice: `theorem_1_12` in the Euclidean
operator norm, which is the norm the backbone proves it for, and `theorem_1_12_norm` for an
arbitrary matrix norm, which is what the book states and defers to Problem P-1.10. The second
follows from the first because all norms on a finite-dimensional space are equivalent and the
equivalence constants disappear under a `k`-th root
(`Numlib/Analysis/Normed/Module/NormEquivalence.lean`); no consistency condition on the norm is
used.
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

/-! ### §1.8.1 Proposition 1.7: semisimple eigenvalues -/

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

/-! ### §1.8.2 Theorem 1.8: the Jordan canonical form -/

/-- Similarity survives subtracting a scalar from both matrices: `X (B - λ I) X⁻¹ = A - λ I`. -/
theorem IsSimilar.sub_smul_one {A B : Matrix (Fin n) (Fin n) 𝕜} (h : IsSimilar A B) (c : 𝕜) :
    IsSimilar (A - c • 1) (B - c • 1) := by
  obtain ⟨X, hX, rfl⟩ := h
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  refine ⟨X, hX, ?_⟩
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.mul_nonsing_inv X hd]

/-- Similar matrices have similar powers. -/
theorem IsSimilar.pow {A B : Matrix (Fin n) (Fin n) 𝕜} (h : IsSimilar A B) (k : ℕ) :
    IsSimilar (A ^ k) (B ^ k) := by
  obtain ⟨X, hX, rfl⟩ := h
  have hd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  refine ⟨X, hX, ?_⟩
  induction k with
  | zero => simp [Matrix.mul_nonsing_inv X hd]
  | succ k ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc X⁻¹ X, Matrix.nonsing_inv_mul X hd, Matrix.one_mul]

/-- Similar matrices have null spaces of the same dimension, because they have the same rank. With
`IsSimilar.sub_smul_one` and `IsSimilar.pow` this says that similar matrices give every eigenvalue
the same geometric multiplicity and the same index, as Problem P-1.9 says they give it the same
algebraic multiplicity. -/
theorem finrank_ker_mulVecLin_eq_of_isSimilar {A B : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsSimilar A B) :
    Module.finrank 𝕜 (LinearMap.ker A.mulVecLin)
      = Module.finrank 𝕜 (LinearMap.ker B.mulVecLin) := by
  obtain ⟨X, hX, rfl⟩ := h
  exact Matrix.finrank_ker_mulVecLin_conj hX

/-- The eigenspace of `A` at `c` is `Null (A - c I)`, the null space of the matrix `A - c I`. -/
private theorem eigenspace_mulVecLin_eq_ker (A : Matrix (Fin n) (Fin n) 𝕜) (c : 𝕜) :
    Module.End.eigenspace A.mulVecLin c = LinearMap.ker ((A - c • 1).mulVecLin) := by
  ext v
  simp [LinearMap.mem_ker, sub_eq_zero]

/-- **Saad Theorem 1.8**, the Jordan canonical form: every complex square matrix is similar to a
block diagonal matrix consisting of `p` diagonal blocks, one associated with each distinct
eigenvalue `lam i`, and each of those blocks has itself a block diagonal structure consisting of
`γ i` sub-blocks, the Jordan blocks `Matrix.jordanBlock (l i k) (lam i)` — upper bidiagonal, with
the constant `lam i` on the diagonal and the constant one on the superdiagonal, of positive size.
The equivalence `σ` names the indices of the block diagonal matrix by `Fin n`; composing with it is
a permutation similarity, so this is the book's `X⁻¹ A X = J`.

What is proved here is the block structure and that the `lam i` are exactly the distinct
eigenvalues of `A`. The book's three further identifications of the numbers involved are the three
statements that follow, each about a decomposition of this shape: `γ i` is the geometric
multiplicity of `lam i` (`SaadSparse.Chapter01.theorem_1_8_geometricMultiplicity`), the `i`-th
diagonal block has size the algebraic multiplicity `m i` of `lam i`
(`SaadSparse.Chapter01.theorem_1_8_algebraicMultiplicity`), and the sub-blocks have size at most
the index `l i` of `lam i`, which is itself at most `m i`
(`SaadSparse.Chapter01.theorem_1_8_index`). -/
theorem theorem_1_8 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (p : ℕ) (lam : Fin p → ℂ) (γ : Fin p → ℕ) (l : ∀ i : Fin p, Fin (γ i) → ℕ)
      (σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n),
      Function.Injective lam ∧ (∀ μ : ℂ, (∃ v ≠ 0, A *ᵥ v = μ • v) ↔ μ ∈ Set.range lam) ∧
        (∀ i k, 0 < l i k) ∧
        IsSimilar A (Matrix.reindex σ σ
          (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))) := by
  obtain ⟨p, lam, γ, l, σ, P, hinj, heig, hlpos, hP, hPA⟩ :=
    Matrix.exists_conj_blockDiagonal'_jordanForm A
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  refine ⟨p, lam, γ, l, σ, hinj, heig, hlpos, P, hP, ?_⟩
  rw [← hPA]
  calc A = P * P⁻¹ * A * (P * P⁻¹) := by
        rw [Matrix.mul_nonsing_inv P hd, Matrix.one_mul, Matrix.mul_one]
    _ = P * (P⁻¹ * A * P) * P⁻¹ := by simp only [Matrix.mul_assoc]

/-- For a matrix in the Jordan form of Theorem 1.8, `Null (A - lam i I)^k` has the dimension the
`i`-th diagonal block gives it: the other diagonal blocks carry other eigenvalues and contribute
nothing. -/
private theorem finrank_ker_pow_sub_smul_one_of_jordan {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {lam : Fin p → ℂ} {γ : Fin p → ℕ} {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) (k : ℕ) :
    Module.finrank ℂ (LinearMap.ker (((A - lam i • 1) ^ k).mulVecLin))
      = Module.finrank ℂ (LinearMap.ker
          (((Matrix.jordanForm (l i) (fun _ => lam i) - lam i • 1) ^ k).mulVecLin)) := by
  classical
  set J : Matrix ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k))
      ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ℂ :=
    Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i) with hJ
  have hre : (Matrix.reindex σ σ J - lam i • 1) ^ k
      = Matrix.reindex σ σ ((J - lam i • 1) ^ k) := by
    simp only [← Matrix.coe_reindexAlgEquiv ℂ ℂ σ]
    rw [← map_one (Matrix.reindexAlgEquiv ℂ ℂ σ), ← map_smul, ← map_sub, ← map_pow]
  rw [finrank_ker_mulVecLin_eq_of_isSimilar ((hA.sub_smul_one (lam i)).pow k), hre,
    Matrix.finrank_ker_mulVecLin_reindex, hJ, Matrix.blockDiagonal'_sub_smul_one,
    ← Matrix.blockDiagonal'_pow, Matrix.finrank_ker_mulVecLin_blockDiagonal']
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rw [show ((fun j => Matrix.jordanForm (l j) (fun _ => lam j) - lam i • 1) ^ k) j
      = (Matrix.jordanForm (l j) (fun _ => lam j) - lam i • 1) ^ k from rfl,
    Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow,
    Finset.filter_false_of_mem fun _ _ (h : lam j = lam i) => hj (hinj h), Finset.sum_empty]

/-- **Saad Theorem 1.8, the geometric multiplicity**: in the Jordan form of Theorem 1.8 the number
`γ i` of sub-blocks of the `i`-th diagonal block is the geometric multiplicity of `lam i`, the
dimension of its eigenspace. Each Jordan block "corresponds to a different eigenvector associated
with the eigenvalue", contributing exactly one dimension. -/
theorem theorem_1_8_geometricMultiplicity {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {lam : Fin p → ℂ} {γ : Fin p → ℕ} {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hlpos : ∀ i k, 0 < l i k)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) :
    Module.finrank ℂ (Module.End.eigenspace A.mulVecLin (lam i)) = γ i := by
  classical
  have h := finrank_ker_pow_sub_smul_one_of_jordan hinj hA i 1
  rw [pow_one, pow_one] at h
  rw [eigenspace_mulVecLin_eq_ker, h,
    Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one (hlpos i) (fun _ => lam i) (lam i),
    Finset.filter_true_of_mem fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

/-- **Saad Theorem 1.8, the algebraic multiplicity**: in the Jordan form of Theorem 1.8 the `i`-th
diagonal block has size `m i`, the algebraic multiplicity of `lam i` — the multiplicity of `lam i`
as a root of the characteristic polynomial of `A`. Its size is `∑ k, l i k`, the total size of its
sub-blocks, which is the number of columns of the Jordan submatrix `J i`. -/
theorem theorem_1_8_algebraicMultiplicity {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ}
    {lam : Fin p → ℂ} {γ : Fin p → ℕ} {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) :
    A.charpoly.rootMultiplicity (lam i) = ∑ k, l i k := by
  classical
  have hcp : A.charpoly = (Matrix.jordanForm (fun j => ∑ k, l j k) lam).charpoly := by
    rw [Matrix.charpoly_jordanForm, charpoly_eq_of_isSimilar hA, Matrix.charpoly_reindex,
      Matrix.charpoly_blockDiagonal']
    exact Finset.prod_congr rfl fun j _ => by
      rw [Matrix.charpoly_jordanForm, Finset.prod_pow_eq_pow_sum]
  have hfilter : (Finset.univ.filter fun j => lam j = lam i) = {i} := by
    ext j
    simp [hinj.eq_iff]
  rw [hcp, Matrix.rootMultiplicity_charpoly_jordanForm, hfilter, Finset.sum_singleton]

/-- **Saad Theorem 1.8, the index**: in the Jordan form of Theorem 1.8 the sub-blocks of the `i`-th
diagonal block have size at most `L`, the index of `lam i` — the smallest integer with
`Null (A - lam i I)^(L+1) = Null (A - lam i I)^L` — and `L` is at most the algebraic multiplicity
`m i = ∑ k, l i k`. This is the book's "of size not exceeding `l i ≤ m i`"; `L` is the size of the
largest sub-block, and so is attained. -/
theorem theorem_1_8_index {A : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} {lam : Fin p → ℂ} {γ : Fin p → ℕ}
    {l : ∀ i : Fin p, Fin (γ i) → ℕ}
    {σ : ((i : Fin p) × (k : Fin (γ i)) × Fin (l i k)) ≃ Fin n} (hinj : Function.Injective lam)
    (hA : IsSimilar A (Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => Matrix.jordanForm (l i) (fun _ => lam i))))
    (i : Fin p) :
    ∃ L : ℕ, IsLeast {k : ℕ | LinearMap.ker (((A - lam i • 1) ^ (k + 1)).mulVecLin)
          = LinearMap.ker (((A - lam i • 1) ^ k).mulVecLin)} L ∧
        (∀ k, l i k ≤ L) ∧ L ≤ ∑ k, l i k := by
  classical
  have hiff : ∀ k : ℕ,
      LinearMap.ker (((A - lam i • 1) ^ (k + 1)).mulVecLin)
          = LinearMap.ker (((A - lam i • 1) ^ k).mulVecLin) ↔ ∀ κ, l i κ ≤ k := by
    intro k
    have hbb := Matrix.finrank_ker_mulVecLin_jordanForm_sub_smul_one_pow_succ_eq_iff (l i)
      (fun _ => lam i) (lam i) k
    rw [← finrank_ker_pow_sub_smul_one_of_jordan hinj hA i,
      ← finrank_ker_pow_sub_smul_one_of_jordan hinj hA i] at hbb
    refine Iff.trans ?_ (hbb.trans ⟨fun h κ => h κ rfl, fun h κ _ => h κ⟩)
    exact ⟨fun h => by rw [h], fun h => (Submodule.eq_of_le_of_finrank_eq
      (Matrix.ker_mulVecLin_pow_le_succ (A - lam i • 1) k) h.symm).symm⟩
  refine ⟨Finset.univ.sup fun k => l i k, ⟨(hiff _).2 fun κ => Finset.le_sup (Finset.mem_univ κ),
    fun k hk => Finset.sup_le fun κ _ => (hiff k).1 hk κ⟩,
    fun k => Finset.le_sup (Finset.mem_univ k), Finset.sup_le fun κ _ => ?_⟩
  exact Finset.single_le_sum (f := fun κ => l i κ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)

/-! ### §1.8.3 Theorem 1.9: the Schur canonical form -/

/-- **Saad Theorem 1.9**, the Schur canonical form: every complex square matrix is unitarily
similar to an upper triangular matrix, whose diagonal carries the eigenvalues of `A` with their
algebraic multiplicities. The proof here is the book's induction on the dimension; the alternative
proof from the Jordan form and a QR factorization (Problem P-1.7) is not carried out. -/
theorem theorem_1_9 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ,
      (star Q * A * Q).IsUpperTriangular ∧
        A.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((star Q * A * Q) i i)) :=
  Matrix.exists_unitary_conj_upperTriangular A

/-- The consequence Saad draws from Theorem 1.9: the span of the first `k` Schur vectors — the
first `k` columns of `Q` — is invariant under `A`, which is the *partial* Schur decomposition
`A Q_k = Q_k R_k`. At `k = 1` it says that `q₁` is an eigenvector of `A`.

The quasi-Schur (real Schur) form with `2 × 2` diagonal blocks is
`SaadSparse.Chapter01.realSchur` below. -/
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
operator norm, which is the one the backbone proves it for; `theorem_1_12_norm` is the book's own
statement, for an arbitrary matrix norm. Cited by Theorem 1.28 and by §4.2.1. -/
theorem theorem_1_12 (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) :=
  Matrix.tendsto_pow_rpow_complexSpectralRadius A

open scoped Matrix.Norms.L2Operator in
/-- **Saad Theorem 1.12 for an arbitrary matrix norm**, which is how the book states it, deferring
the proof to Problem P-1.10: `p(A^k)^{1/k} → ρ(A)` for every norm `p` on the matrices.

A matrix norm in the sense of (1.7)–(1.9) is exactly a `Seminorm ℝ` — nonnegative, absolutely
homogeneous, subadditive — that is definite, and `p` here carries the definiteness as the
hypothesis `hp`. The consistency condition (1.11) of §1.4 is *not* needed: matrix norms all being
equivalent, the limit is the same for every one of them, which is
`Seminorm.tendsto_rpow_one_div`. -/
theorem theorem_1_12_norm (p : Seminorm ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hp : ∀ M : Matrix (Fin n) (Fin n) ℝ, p M = 0 → M = 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => p (A ^ k) ^ (1 / k : ℝ)) atTop (𝓝 A.complexSpectralRadius.toReal) :=
  p.tendsto_rpow_one_div hp (theorem_1_12 A)

/-- **Saad §1.8.3, the quasi-Schur form**, also called the real Schur form: every *real* square
matrix is orthogonally similar to a quasi upper triangular matrix — block upper triangular with
diagonal blocks of size `1 × 1` or `2 × 2`, the `2 × 2` blocks carrying the pairs of complex
conjugate eigenvalues. The book gives it without proof, as a "slight variation" on Theorem 1.9,
and illustrates it only by the decimal matrices of Example 1.2.

The block structure is the monotone index `p : Fin n → ℕ`: `Monotone p` makes each block an
interval of consecutive indices, the cardinality bound makes every block `1 × 1` or `2 × 2`, and
`Matrix.BlockTriangular` says that the entries below the blocks vanish. Theorem 1.9 does not
specialize to this, because over `ℝ` there need be no eigenvector: the induction has to peel off
an invariant subspace of dimension one *or two*
(`LinearMap.exists_invariant_finrank_le_two`), and the backbone is
`Matrix.exists_orthogonal_conj_quasiUpperTriangular`. -/
theorem realSchur (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∃ p : Fin n → ℕ, Monotone p ∧
      (∀ k, (Finset.univ.filter fun i => p i = k).card ≤ 2) ∧
      (Qᵀ * A * Q).BlockTriangular p :=
  Matrix.exists_orthogonal_conj_quasiUpperTriangular A

end SaadSparse.Chapter01
