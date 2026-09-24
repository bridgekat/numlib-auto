/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.SingularValues`, beside Mathlib's
`LinearMap.singularValues`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Eigen.MinMax

/-!
# Singular values of a linear map

Facts about Mathlib's `LinearMap.singularValues` of a linear map `T : E →ₗ[𝕜] F` between
finite-dimensional inner product spaces, stated coordinate-free. Mathlib's
`LinearMap.singularValues` is the `ℕ`-indexed sequence of the square roots of the eigenvalues of
`T† T`, sorted decreasingly and zero from `finrank E` on. Mathlib has no min–max characterization,
no Weyl or interlacing inequality, no singular value decomposition of a map and no dilation; this
module supplies them ([golub2013matrix] §2.4, §8.6.1–8.6.2).

## Main results

* `LinearMap.isGreatest_singularValues`, `LinearMap.isLeast_singularValues`: the max–min and
  min–max characterizations (Courant–Fischer for `T† T`), with the bilinear form
  `LinearMap.isLeast_singularValues_bilinear` of [golub2013matrix] Theorem 8.6.1. The two one-sided
  forms `LinearMap.le_singularValues_of_mul_norm_le` and
  `LinearMap.singularValues_le_of_norm_le_mul` accept subspaces of *at least* the right dimension,
  and are what the other proofs use.
* `LinearMap.singularValues_add_le`: **Weyl's inequality** `σ_{i+j}(S + T) ≤ σ_i(S) + σ_j(T)`, the
  one principle behind the perturbation bound `LinearMap.abs_singularValues_sub_le` and the lower
  half of the Eckart–Young theorem.
* `LinearMap.singularValues_comp_linearIsometry_le`,
  `LinearMap.singularValues_add_le_singularValues_comp_linearIsometry` and
  `LinearMap.singularValues_domRestrict_interlace`: interlacing under restriction of the domain.
* `LinearMap.singularValues_eq_of_forall_norm_eq`, `LinearMap.singularValues_adjoint`,
  `LinearMap.singularValues_comp_linearIsometryEquiv`: invariance under isometries and adjoints.
* `LinearMap.exists_orthonormal_singularVectors`: the singular value decomposition of a map as a
  pair of orthonormal families.
* `LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues`: the **stacked-isometry
  identity** `‖Q₂‖² = 1 - σ_min(Q₁)²` when `‖Q₁ x‖² + ‖Q₂ x‖² = ‖x‖²`.
* `LinearMap.hermitianDilation`: the **Hermitian dilation** (Jordan–Wielandt operator)
  `(x, y) ↦ (A† y, A x)` on `WithLp 2 (E × F)`, and its sorted spectrum
  `LinearMap.eigenvalues_hermitianDilation`: `σ_0, …, σ_{p-1}, 0, …, 0, -σ_{p-1}, …, -σ_0`.
* `LinearMap.IsSymmetric.eigenvalues_eq_of_antitone`: the sorted eigenvalues of a symmetric
  operator are determined by its characteristic polynomial.

## Implementation notes

The module is the coordinate-free rung of the library's singular-value theory: it imports nothing
from the matrix layer, only Courant–Fischer (`Numlib/Eigen/MinMax`), and the matrix singular value
decomposition (`Numlib/LinearAlgebra/Matrix/SVD`) and the matrix corollaries
(`Numlib/Analysis/Matrix/SingularValues`) import it.

Every inequality is proved from the two one-sided max–min lemmas: a subspace on which `T`
stretches by at least `c` bounds a singular value from below, a subspace on which it stretches by
at most `c` bounds one from above. The spectrum of the dilation, in particular, is read off by
exhibiting such subspaces (a graph of `A` over a max–min subspace, and a product with the whole
codomain), not by computing an eigenbasis. The dilation takes the adjoint as a second argument
`Astar` with the hypothesis `∀ u x, ⟪Astar u, x⟫ = ⟪u, A x⟫`, as in `Numlib/Krylov/NormalEquations`,
so that it needs neither completeness nor finite dimension; its block order (domain factor first)
is that of the matrix `Matrix.hermitianDilation A = fromBlocks 0 Aᴴ A 0`.

## References

* [golub2013matrix] G. H. Golub and C. F. Van Loan, *Matrix Computations*, 4th ed., §2.4,
  §8.6.1–8.6.2.
-/

open Module

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The sorted eigenvalues of a symmetric operator are determined by its characteristic
polynomial**: if the roots of `T.charpoly` are the values of an antitone `d : Fin n → ℝ`, then
`hT.eigenvalues hn = d`. This is `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues` read
backwards. -/
theorem IsSymmetric.eigenvalues_eq_of_antitone {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n) {d : Fin n → ℝ} (hd : Antitone d)
    (hroots : T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val) :
    hT.eigenvalues hn = d := by
  rw [← List.ofFn_inj, ← hT.sort_roots_charpoly_eq_eigenvalues hn, hroots]
  simp_rw [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def, RCLike.ofReal_re,
    Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hd.sortedGE_ofFn

/-- The dimension of the image of a subspace under an injective map. -/
private theorem finrank_map_of_injective {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (f : M →ₗ[𝕜] N) (hf : Function.Injective f)
    (S : Submodule 𝕜 M) : finrank 𝕜 (S.map f) = finrank 𝕜 S :=
  (Submodule.equivMapOfInjective f hf S).finrank_eq.symm

/-! ### The Hermitian dilation -/

section Dilation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **The Hermitian dilation** (Jordan–Wielandt operator) of `A : E →ₗ[𝕜] F` with a given adjoint
`Astar : F →ₗ[𝕜] E`: the operator `(x, y) ↦ (Astar y, A x)` on `WithLp 2 (E × F)`, domain factor
first. Its matrix is `Matrix.hermitianDilation A = fromBlocks 0 Aᴴ A 0`, the Jordan–Wielandt matrix
`S₃ = [0 Aᵀ; A 0]` of [golub2013matrix] §8.6.1 and `Ã` of (8.6.4); (10.4.16) writes it with the two
factors exchanged. For `Astar = adjoint A` it is symmetric
(`LinearMap.isSymmetric_hermitianDilation_adjoint`), with spectrum `±` the singular values of `A`
padded by zeros (`LinearMap.eigenvalues_hermitianDilation`). -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    (Astar ∘ₗ WithLp.sndₗ 2 𝕜 E F).prod (A ∘ₗ WithLp.fstₗ 2 𝕜 E F)

@[simp]
theorem hermitianDilation_apply (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (z : WithLp 2 (E × F)) :
    hermitianDilation A Astar z = WithLp.toLp 2 (Astar z.snd, A z.fst) :=
  rfl

/-- The dilation of `-A` (with adjoint `-Astar`) is minus the dilation of `A`. -/
theorem hermitianDilation_neg (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) :
    hermitianDilation (-A) (-Astar) = -hermitianDilation A Astar :=
  LinearMap.ext fun z => by
    simp only [hermitianDilation_apply, neg_apply, ← WithLp.toLp_neg, Prod.neg_mk]

variable {A : E →ₗ[𝕜] F} {Astar : F →ₗ[𝕜] E}

/-- The Hermitian dilation of a map with a given adjoint is symmetric. -/
theorem isSymmetric_hermitianDilation (hadj : ∀ u x, inner 𝕜 (Astar u) x = inner 𝕜 u (A x)) :
    (hermitianDilation A Astar).IsSymmetric := by
  intro z w
  have h : inner 𝕜 (A z.fst) w.snd = inner 𝕜 z.fst (Astar w.snd) := by
    rw [← inner_conj_symm, ← hadj, inner_conj_symm]
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd, hadj, h]
  ring

/-- The quadratic form of the Hermitian dilation: `re ⟪H (x, y), (x, y)⟫ = 2 re ⟪A x, y⟫`. -/
theorem re_inner_hermitianDilation_apply_self
    (hadj : ∀ u x, inner 𝕜 (Astar u) x = inner 𝕜 u (A x)) (z : WithLp 2 (E × F)) :
    RCLike.re (inner 𝕜 (hermitianDilation A Astar z) z) =
      2 * RCLike.re (inner 𝕜 (A z.fst) z.snd) := by
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd, hadj, map_add]
  rw [inner_re_symm z.snd]
  ring

end Dilation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- The images under `T` of the sorted orthonormal eigenbasis of `T† T` are pairwise orthogonal,
with squared norms the squared singular values. -/
theorem inner_apply_eigenvectorBasis_adjoint_comp_self {n : ℕ} (hn : finrank 𝕜 E = n)
    (i j : Fin n) :
    inner 𝕜 (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i))
        (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j))
      = if i = j then ((T.singularValues j ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← adjoint_inner_right, ← comp_apply, T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis,
    inner_smul_right,
    orthonormal_iff_ite.1 (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).orthonormal i j,
    ← T.sq_singularValues_fin hn j]
  split_ifs <;> simp

/-- The image under `T` of the `j`-th vector of the sorted eigenbasis of `T† T` has norm the `j`-th
singular value. -/
theorem norm_apply_eigenvectorBasis_adjoint_comp_self {n : ℕ} (hn : finrank 𝕜 E = n) (j : Fin n) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j)‖ = T.singularValues j := by
  have h := T.inner_apply_eigenvectorBasis_adjoint_comp_self hn j j
  rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j)‖ ^ 2
      = T.singularValues j ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (T.singularValues_nonneg j) two_ne_zero).1 h2

/-- The singular values vanish from the dimension of the *codomain* on, as they do from the
dimension of the domain on (`LinearMap.singularValues_of_finrank_le`): only `rank T` of them are
nonzero. -/
theorem singularValues_of_finrank_codomain_le {i : ℕ} (hi : finrank 𝕜 F ≤ i) :
    T.singularValues i = 0 :=
  T.singularValues_eq_zero_iff_le_finrank_range.2 ((Submodule.finrank_le _).trans hi)

/-- A positive singular value sits below the dimension of the domain. -/
theorem lt_finrank_of_singularValues_pos {k : ℕ} (hk : 0 < T.singularValues k) :
    k < finrank 𝕜 E := by
  by_contra h
  rw [T.singularValues_of_finrank_le (not_lt.1 h)] at hk
  exact lt_irrefl _ hk

/-! ### The max–min characterizations -/

/-- The Rayleigh quotient of the Gram operator `T† T` is the squared stretch of `T`. -/
theorem rayleighQuotient_adjoint_comp_self (x : E) :
    (adjoint T ∘ₗ T).rayleighQuotient x = ‖T x‖ ^ 2 / ‖x‖ ^ 2 := by
  rw [rayleighQuotient, comp_apply, adjoint_inner_left, inner_self_eq_norm_sq]

/-- A lower bound `c ≥ 0` on the Rayleigh quotient of `T† T` by `c ^ 2` is a lower bound on the
stretch by `c`. -/
theorem sq_le_rayleighQuotient_adjoint_comp_self_iff {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0) :
    c ^ 2 ≤ (adjoint T ∘ₗ T).rayleighQuotient x ↔ c * ‖x‖ ≤ ‖T x‖ := by
  rw [rayleighQuotient_adjoint_comp_self, le_div_iff₀ (pow_pos (norm_pos_iff.2 hx) 2), ← mul_pow]
  exact pow_le_pow_iff_left₀ (mul_nonneg hc (norm_nonneg x)) (norm_nonneg _) two_ne_zero

/-- An upper bound `c ≥ 0` on the Rayleigh quotient of `T† T` by `c ^ 2` is an upper bound on the
stretch by `c`. -/
theorem rayleighQuotient_adjoint_comp_self_le_sq_iff {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0) :
    (adjoint T ∘ₗ T).rayleighQuotient x ≤ c ^ 2 ↔ ‖T x‖ ≤ c * ‖x‖ := by
  rw [rayleighQuotient_adjoint_comp_self, div_le_iff₀ (pow_pos (norm_pos_iff.2 hx) 2), ← mul_pow]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x)) two_ne_zero

/-- **Max–min, the easy direction**: if `T` stretches every vector of a subspace of dimension at
least `k + 1` by at least `c`, then `c ≤ σ_k(T)`. -/
theorem le_singularValues_of_mul_norm_le {k : ℕ} {c : ℝ} {S : Submodule 𝕜 E}
    (hS : k + 1 ≤ finrank 𝕜 S) (h : ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖) : c ≤ T.singularValues k := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (T.singularValues_nonneg k)
  have hk : k < finrank 𝕜 E := by have := Submodule.finrank_le S; omega
  obtain ⟨x, hxS, hx0, hle⟩ :=
    T.isSymmetric_adjoint_comp_self.exists_mem_ne_zero_rayleighQuotient_le rfl ⟨k, hk⟩ hS
  rw [← T.sq_singularValues_of_lt rfl hk,
    T.rayleighQuotient_adjoint_comp_self_le_sq_iff (T.singularValues_nonneg k) hx0] at hle
  exact le_of_mul_le_mul_right ((h x hxS).trans hle) (norm_pos_iff.2 hx0)

/-- **Min–max, the easy direction**: if `T` stretches every vector of a subspace of dimension at
least `finrank E - k` by at most `c`, then `σ_k(T) ≤ c` (for `k < finrank E`). -/
theorem singularValues_le_of_norm_le_mul {k : ℕ} (hk : k < finrank 𝕜 E) {c : ℝ}
    {S : Submodule 𝕜 E} (hS : finrank 𝕜 E - k ≤ finrank 𝕜 S) (h : ∀ x ∈ S, ‖T x‖ ≤ c * ‖x‖) :
    T.singularValues k ≤ c := by
  obtain ⟨x, hxS, hx0, hle⟩ :=
    T.isSymmetric_adjoint_comp_self.exists_mem_ne_zero_le_rayleighQuotient rfl ⟨k, hk⟩ hS
  rw [← T.sq_singularValues_of_lt rfl hk,
    T.sq_le_rayleighQuotient_adjoint_comp_self_iff (T.singularValues_nonneg k) hx0] at hle
  exact le_of_mul_le_mul_right (hle.trans (h x hxS)) (norm_pos_iff.2 hx0)

/-- **Max–min characterization of singular values** ([golub2013matrix] Theorem 8.6.1, right-hand
form): `σ_k(T)` is the largest `c` such that `T` stretches every vector of some subspace of
dimension `k + 1` by at least `c`. At `k = finrank E - 1` the subspace is everything, and
`σ_{n-1}` is the least stretch. -/
theorem isGreatest_singularValues {k : ℕ} (hk : k < finrank 𝕜 E) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 E, finrank 𝕜 S = k + 1 ∧ ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖}
      (T.singularValues k) := by
  refine ⟨?_, fun c ⟨S, hS, h⟩ => T.le_singularValues_of_mul_norm_le hS.ge h⟩
  obtain ⟨⟨S, hS, h⟩, -⟩ := T.isSymmetric_adjoint_comp_self.isGreatest_eigenvalues rfl ⟨k, hk⟩
  refine ⟨S, hS, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have := h x hx hx0
  rwa [← T.sq_singularValues_of_lt rfl hk,
    T.sq_le_rayleighQuotient_adjoint_comp_self_iff (T.singularValues_nonneg k) hx0] at this

/-- **Min–max characterization of singular values**: `σ_k(T)` is the least `c` such that `T`
stretches every vector of some subspace of dimension `finrank E - k` by at most `c`. At `k = 0`
the subspace is everything, and `σ_0` is the operator norm. -/
theorem isLeast_singularValues {k : ℕ} (hk : k < finrank 𝕜 E) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, finrank 𝕜 S = finrank 𝕜 E - k ∧
      ∀ x ∈ S, ‖T x‖ ≤ c * ‖x‖} (T.singularValues k) := by
  refine ⟨?_, fun c ⟨S, hS, h⟩ => T.singularValues_le_of_norm_le_mul hk hS.ge h⟩
  obtain ⟨⟨S, hS, h⟩, -⟩ := T.isSymmetric_adjoint_comp_self.isLeast_eigenvalues rfl ⟨k, hk⟩
  refine ⟨S, hS, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have := h x hx hx0
  rwa [← T.sq_singularValues_of_lt rfl hk,
    T.rayleighQuotient_adjoint_comp_self_le_sq_iff (T.singularValues_nonneg k) hx0] at this

/-- **The bilinear min–max form** ([golub2013matrix] Theorem 8.6.1, left-hand form):
`σ_k(T) = min_{dim S = n - k} max_{x ∈ S, y} re ⟪y, T x⟫ / (‖x‖ ‖y‖)`, as an `IsLeast`. The
codomain must be nonzero: otherwise every `c` bounds the form `0`. -/
theorem isLeast_singularValues_bilinear [Nontrivial F] {k : ℕ} (hk : k < finrank 𝕜 E) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, finrank 𝕜 S = finrank 𝕜 E - k ∧
      ∀ x ∈ S, ∀ y : F, RCLike.re (inner 𝕜 y (T x)) ≤ c * (‖x‖ * ‖y‖)} (T.singularValues k) := by
  obtain ⟨⟨S, hS, h⟩, hlow⟩ := T.isLeast_singularValues hk
  refine ⟨⟨S, hS, fun x hx y => ?_⟩, fun c ⟨S', hS', h'⟩ => hlow ⟨S', hS', fun x hx => ?_⟩⟩
  · calc RCLike.re (inner 𝕜 y (T x)) ≤ ‖y‖ * ‖T x‖ := re_inner_le_norm _ _
      _ ≤ ‖y‖ * (T.singularValues k * ‖x‖) := by gcongr; exact h x hx
      _ = T.singularValues k * (‖x‖ * ‖y‖) := by ring
  · -- test against `y = T x`, or against a nonzero `y` when `T x = 0`
    rcases eq_or_ne (T x) 0 with h0 | h0
    · rw [h0, norm_zero]
      rcases eq_or_ne x 0 with rfl | hx0
      · simp
      obtain ⟨y, hy⟩ := exists_ne (0 : F)
      have h2 := h' x hx y
      rw [h0, inner_zero_right, map_zero] at h2
      have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.2 hx0) (norm_pos_iff.2 hy)
      have : 0 ≤ c := nonneg_of_mul_nonneg_left h2 hpos
      positivity
    · have h1 := h' x hx (T x)
      rw [inner_self_eq_norm_sq] at h1
      have hpos : 0 < ‖T x‖ := norm_pos_iff.2 h0
      nlinarith

/-! ### Weyl's inequality -/

/-- There is a subspace of dimension at least `finrank E - k` on which `T` stretches by at most
`σ_k(T)`, for every `k` (for `k ≥ finrank E`, the zero subspace). -/
theorem exists_submodule_norm_apply_le (k : ℕ) :
    ∃ S : Submodule 𝕜 E, finrank 𝕜 E - k ≤ finrank 𝕜 S ∧
      ∀ x ∈ S, ‖T x‖ ≤ T.singularValues k * ‖x‖ := by
  by_cases hk : k < finrank 𝕜 E
  · obtain ⟨S, hS, h⟩ := (T.isLeast_singularValues hk).1
    exact ⟨S, hS.ge, h⟩
  · refine ⟨⊥, by simp; omega, fun x hx => ?_⟩
    rw [(Submodule.mem_bot 𝕜).1 hx]
    simp

/-- **Weyl's inequality for singular values, general form** (Weyl 1949; the principle behind
[golub2013matrix] Corollary 2.4.4, Corollary 8.6.2 and the lower half of Theorem 2.4.8):
`σ_{i+j}(S + T) ≤ σ_i(S) + σ_j(T)`. The min–max subspaces of `S` at `i` and of `T` at `j` meet in
a subspace of dimension at least `finrank E - (i + j)`, on which `S + T` stretches by at most
`σ_i(S) + σ_j(T)`. -/
theorem singularValues_add_le (S T : E →ₗ[𝕜] F) (i j : ℕ) :
    (S + T).singularValues (i + j) ≤ S.singularValues i + T.singularValues j := by
  by_cases h : finrank 𝕜 E ≤ i + j
  · rw [singularValues_of_finrank_le _ h]
    exact add_nonneg (S.singularValues_nonneg i) (T.singularValues_nonneg j)
  push Not at h
  obtain ⟨VS, hVS, hS⟩ := S.exists_submodule_norm_apply_le i
  obtain ⟨VT, hVT, hT⟩ := T.exists_submodule_norm_apply_le j
  refine (S + T).singularValues_le_of_norm_le_mul h (S := VS ⊓ VT) ?_ fun x hx => ?_
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq VS VT
    have h2 := Submodule.finrank_le (VS ⊔ VT)
    omega
  · rw [add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hS x hx.1) (hT x hx.2))

/-- A bound on the stretch bounds every singular value. -/
theorem singularValues_le_of_forall_norm_apply_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖T x‖ ≤ C * ‖x‖) (k : ℕ) : T.singularValues k ≤ C := by
  by_cases hk : k < finrank 𝕜 E
  · exact T.singularValues_le_of_norm_le_mul hk (S := ⊤) (by simp) fun x _ => h x
  · rw [singularValues_of_finrank_le _ (not_lt.1 hk)]
    exact hC

/-- **Weyl's perturbation bound for singular values** ([golub2013matrix] Corollary 8.6.2 and
Corollary 2.4.4): if `‖(T - S) x‖ ≤ C ‖x‖` for all `x`, then `|σ_k(T) - σ_k(S)| ≤ C`. The `j = 0`
case of `LinearMap.singularValues_add_le`, twice. The hypothesis `0 ≤ C` is only needed when `E`
is zero. -/
theorem abs_singularValues_sub_le {S T : E →ₗ[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖(T - S) x‖ ≤ C * ‖x‖) (k : ℕ) :
    |T.singularValues k - S.singularValues k| ≤ C := by
  have h1 := singularValues_add_le S (T - S) k 0
  have h2 := singularValues_add_le T (S - T) k 0
  rw [add_sub_cancel, add_zero] at h1
  rw [add_sub_cancel, add_zero] at h2
  have h3 := (T - S).singularValues_le_of_forall_norm_apply_le hC h 0
  have h4 := (S - T).singularValues_le_of_forall_norm_apply_le hC
    (fun x => by rw [← neg_sub, neg_apply, norm_neg]; exact h x) 0
  rw [abs_le]
  constructor <;> linarith

/-! ### Interlacing and invariance -/

variable {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

/-- Singular values are monotone in the stretch: if `‖T x‖ ≤ ‖T' x‖` for all `x`, then
`σ_k(T) ≤ σ_k(T')`. -/
theorem singularValues_le_of_forall_norm_le {T' : E →ₗ[𝕜] F'} (h : ∀ x, ‖T x‖ ≤ ‖T' x‖)
    (k : ℕ) : T.singularValues k ≤ T'.singularValues k := by
  by_cases hk : k < finrank 𝕜 E
  · obtain ⟨S, hS, hS'⟩ := (T.isGreatest_singularValues hk).1
    exact T'.le_singularValues_of_mul_norm_le hS.ge fun x hx => (hS' x hx).trans (h x)
  · rw [singularValues_of_finrank_le _ (not_lt.1 hk)]
    exact T'.singularValues_nonneg k

/-- Two maps with the same stretch everywhere have the same singular values; in particular
composing on the left with a linear isometry does not change them
(`LinearMap.singularValues_linearIsometry_comp`). -/
theorem singularValues_eq_of_forall_norm_eq {T' : E →ₗ[𝕜] F'} (h : ∀ x, ‖T x‖ = ‖T' x‖) :
    T.singularValues = T'.singularValues := by
  ext k
  exact le_antisymm (T.singularValues_le_of_forall_norm_le (fun x => (h x).le) k)
    (T'.singularValues_le_of_forall_norm_le (fun x => (h x).ge) k)

/-- Composing on the left with a linear isometry does not change the singular values. -/
theorem singularValues_linearIsometry_comp (f : F →ₗᵢ[𝕜] F') :
    (f.toLinearMap ∘ₗ T).singularValues = T.singularValues :=
  singularValues_eq_of_forall_norm_eq _ fun x => by simp

/-- Negation does not change the singular values. -/
@[simp]
theorem singularValues_neg : (-T).singularValues = T.singularValues :=
  singularValues_eq_of_forall_norm_eq _ fun x => by simp

/-- Restricting the domain along a linear isometry can only decrease the singular values: the
upper half of the interlacing inequalities. -/
theorem singularValues_comp_linearIsometry_le (e : E' →ₗᵢ[𝕜] E) (k : ℕ) :
    (T ∘ₗ e.toLinearMap).singularValues k ≤ T.singularValues k := by
  by_cases hk : k < finrank 𝕜 E'
  · obtain ⟨S, hS, h⟩ := ((T ∘ₗ e.toLinearMap).isGreatest_singularValues hk).1
    refine T.le_singularValues_of_mul_norm_le (S := S.map e.toLinearMap) ?_ ?_
    · rw [finrank_map_of_injective _ e.injective, hS]
    · rintro _ ⟨y, hy, rfl⟩
      simpa using h y hy
  · rw [singularValues_of_finrank_le _ (not_lt.1 hk)]
    exact T.singularValues_nonneg k

/-- Restricting the domain along a linear isometry of codimension `r` decreases the singular values
by at most `r` places: the lower half of the interlacing inequalities. -/
theorem singularValues_add_le_singularValues_comp_linearIsometry (e : E' →ₗᵢ[𝕜] E) {r : ℕ}
    (hr : finrank 𝕜 E' + r = finrank 𝕜 E) (k : ℕ) :
    T.singularValues (k + r) ≤ (T ∘ₗ e.toLinearMap).singularValues k := by
  by_cases hk : k < finrank 𝕜 E'
  · obtain ⟨S, hS, h⟩ := ((T ∘ₗ e.toLinearMap).isLeast_singularValues hk).1
    refine T.singularValues_le_of_norm_le_mul (by omega) (S := S.map e.toLinearMap) ?_ ?_
    · rw [finrank_map_of_injective _ e.injective, hS]
      omega
    · rintro _ ⟨y, hy, rfl⟩
      simpa using h y hy
  · rw [singularValues_of_finrank_le _ (by omega : finrank 𝕜 E ≤ k + r)]
    exact singularValues_nonneg _ k

/-- **Singular-value interlacing under restriction to a subspace** ([golub2013matrix] Corollary
8.6.3 in operator form, for any codimension `r`; the Corollary is `r = 1`): for `K ≤ E` with
`finrank K + r = finrank E`, `σ_{k+r}(T) ≤ σ_k(T|_K) ≤ σ_k(T)`. -/
theorem singularValues_domRestrict_interlace (K : Submodule 𝕜 E) {r : ℕ}
    (hr : finrank 𝕜 K + r = finrank 𝕜 E) (k : ℕ) :
    T.singularValues (k + r) ≤ (T.domRestrict K).singularValues k ∧
      (T.domRestrict K).singularValues k ≤ T.singularValues k :=
  ⟨T.singularValues_add_le_singularValues_comp_linearIsometry K.subtypeₗᵢ hr k,
    T.singularValues_comp_linearIsometry_le K.subtypeₗᵢ k⟩

/-- **Singular values are unitarily invariant**: composing with a linear isometry equivalence on
the right and a linear isometry on the left does not change them. -/
theorem singularValues_comp_linearIsometryEquiv (e : E' ≃ₗᵢ[𝕜] E) (f : F →ₗᵢ[𝕜] F') :
    (f.toLinearMap ∘ₗ T ∘ₗ e.toLinearIsometry.toLinearMap).singularValues =
      T.singularValues := by
  rw [singularValues_linearIsometry_comp]
  ext k
  refine le_antisymm (T.singularValues_comp_linearIsometry_le e.toLinearIsometry k) ?_
  have h := (T ∘ₗ e.toLinearIsometry.toLinearMap).singularValues_comp_linearIsometry_le
    e.symm.toLinearIsometry k
  have hT : (T ∘ₗ e.toLinearIsometry.toLinearMap) ∘ₗ e.symm.toLinearIsometry.toLinearMap = T := by
    ext x
    simp
  rwa [hT] at h

/-- `σ_k(T) ≤ σ_k(T†)`: the image under `T` of a max–min subspace of `T` is one for `T†`, because
`‖T x‖² = re ⟪T† T x, x⟫ ≤ ‖T† T x‖ ‖x‖`. -/
theorem singularValues_le_singularValues_adjoint (k : ℕ) :
    T.singularValues k ≤ (adjoint T).singularValues k := by
  rcases (T.singularValues_nonneg k).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact singularValues_nonneg _ k
  have hk := T.lt_finrank_of_singularValues_pos hpos
  obtain ⟨S, hS, h⟩ := (T.isGreatest_singularValues hk).1
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [← ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h1 := h x x.2
    rw [mem_ker, comp_apply, Submodule.subtype_apply] at hx
    rw [hx, norm_zero] at h1
    have h2 : ‖(x : E)‖ ≤ 0 := by nlinarith [norm_nonneg (x : E)]
    exact Subtype.ext (norm_le_zero_iff.1 h2)
  refine (adjoint T).le_singularValues_of_mul_norm_le (S := S.map T) ?_ ?_
  · rw [← Submodule.range_subtype S, ← range_comp, finrank_range_of_inj hinj, hS]
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := h x hx
    have h2 : ‖T x‖ ^ 2 ≤ ‖adjoint T (T x)‖ * ‖x‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← adjoint_inner_left]
      exact re_inner_le_norm _ _
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hx := norm_pos_iff.2 hx0
    refine le_of_mul_le_mul_right ?_ hx
    nlinarith [norm_nonneg (T x), norm_nonneg (adjoint T (T x))]

/-- **A map and its adjoint have the same singular values** (with Mathlib's zero padding). -/
@[simp]
theorem singularValues_adjoint : (adjoint T).singularValues = T.singularValues := by
  ext k
  refine le_antisymm ?_ (T.singularValues_le_singularValues_adjoint k)
  simpa using (adjoint T).singularValues_le_singularValues_adjoint k

/-- `σ_0(T)` bounds the stretch of `T` everywhere: it is the operator norm. -/
theorem norm_apply_le_singularValues_zero_mul (x : E) :
    ‖T x‖ ≤ T.singularValues 0 * ‖x‖ := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 E) with h0 | hpos
  · rw [Module.finrank_zero_iff.1 h0 |>.elim x 0, map_zero, norm_zero, norm_zero, mul_zero]
  · obtain ⟨S, hS, h⟩ := (T.isLeast_singularValues hpos).1
    have hS' : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hS]; omega)
    exact h x (hS' ▸ Submodule.mem_top)

/-- **Deflation of a top singular pair**: if `T v = σ_0 u` and `T† u = σ_0 v` for unit vectors `u`,
`v`, and `e : E' →ₗᵢ E` is an isometry of codimension one whose range is orthogonal to `v`, then
the singular values of `T` restricted along `e` are those of `T` shifted by one:
`σ_i(T ∘ e) = σ_{i+1}(T)`. `T` maps `v⊥` into `u⊥`, and a max–min subspace of `T ∘ e` together
with `v` is one for `T`, one dimension higher. This is what makes the recursive definition of the
principal angles well posed. -/
theorem singularValues_comp_linearIsometry_eq_succ (e : E' →ₗᵢ[𝕜] E)
    (hr : finrank 𝕜 E' + 1 = finrank 𝕜 E) {u : F} {v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hTv : T v = (T.singularValues 0 : 𝕜) • u)
    (hTu : adjoint T u = (T.singularValues 0 : 𝕜) • v) (he : ∀ x, inner 𝕜 v (e x) = 0)
    (i : ℕ) : (T ∘ₗ e.toLinearMap).singularValues i = T.singularValues (i + 1) := by
  refine le_antisymm ?_ (T.singularValues_add_le_singularValues_comp_linearIsometry e hr i)
  set c := (T ∘ₗ e.toLinearMap).singularValues i with hc
  set σ := T.singularValues 0 with hσ
  have hc0 : 0 ≤ c := singularValues_nonneg _ i
  have hcσ : c ≤ σ := (T.singularValues_comp_linearIsometry_le e i).trans
    (T.singularValues_antitone (Nat.zero_le i))
  by_cases hi : i < finrank 𝕜 E'
  swap
  · rw [hc, singularValues_of_finrank_le _ (not_lt.1 hi)]
    exact T.singularValues_nonneg _
  obtain ⟨S, hS, h⟩ := ((T ∘ₗ e.toLinearMap).isGreatest_singularValues hi).1
  have hdisj : S.map e.toLinearMap ⊓ (𝕜 ∙ v) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨⟨y, -, rfl⟩, hx⟩
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx
    have h1 := he y
    rw [LinearIsometry.coe_toLinearMap] at hb ⊢
    rw [← hb, inner_smul_right, inner_self_eq_norm_sq_to_K, hv] at h1
    rw [← hb, show b = 0 by simpa using h1, zero_smul]
  have hS' : i + 1 + 1 ≤ finrank 𝕜 ↥(S.map e.toLinearMap ⊔ (𝕜 ∙ v)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.map e.toLinearMap) (𝕜 ∙ v)
    rw [hdisj, finrank_bot, add_zero, finrank_map_of_injective _ e.injective, hS,
      finrank_span_singleton (norm_ne_zero_iff.1 (by rw [hv]; norm_num))] at h1
    omega
  refine T.le_singularValues_of_mul_norm_le hS' fun x hx => ?_
  obtain ⟨_, ⟨y, hy, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [LinearIsometry.coe_toLinearMap]
  have hTey : inner 𝕜 (T (e y)) u = 0 := by
    rw [← adjoint_inner_right, hTu, inner_smul_right, ← inner_conj_symm, he, map_zero, mul_zero]
  have hey : inner 𝕜 (e y) (b • v) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, he, map_zero, mul_zero]
  have h1 : ‖e y + b • v‖ ^ 2 = ‖y‖ ^ 2 + ‖b‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hey
    rw [pow_two, pow_two, pow_two, this, e.norm_map, norm_smul, hv, mul_one]
  have h2 : ‖T (e y + b • v)‖ ^ 2 = ‖T (e y)‖ ^ 2 + ‖b‖ ^ 2 * σ ^ 2 := by
    rw [map_add, map_smul, hTv, smul_smul]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (T (e y)) ((b * σ) • u)
      (by rw [inner_smul_right, hTey, mul_zero])
    rw [pow_two, pow_two, this, norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg
      (T.singularValues_nonneg 0), hu, mul_one]
    ring
  have h3 : c * ‖y‖ ≤ ‖T (e y)‖ := h y hy
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rw [mul_pow, h1, h2]
  have h4 : (c * ‖y‖) ^ 2 ≤ ‖T (e y)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  have h5 : c ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hc0 hcσ 2
  nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg ‖b‖)]

/-! ### The singular value decomposition of a map -/

/-- **The SVD of a linear map** (operator form of [golub2013matrix] Theorem 2.4.1 and Corollary
2.4.2): if `finrank E = q ≤ finrank F`, there are an orthonormal basis `v` of `E` and an
orthonormal family `u` in `F` with `T (v i) = σ_i • u i`. The basis `v` is the sorted eigenbasis of
`T† T`; `u i = σ_i⁻¹ T (v i)` where `σ_i ≠ 0`, completed orthonormally elsewhere. -/
theorem exists_orthonormal_singularVectors {q : ℕ} (hq : finrank 𝕜 E = q)
    (hqF : q ≤ finrank 𝕜 F) :
    ∃ (v : OrthonormalBasis (Fin q) 𝕜 E) (u : Fin q → F), Orthonormal 𝕜 u ∧
      ∀ i, T (v i) = (T.singularValues i : 𝕜) • u i := by
  set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv
  set w : Fin (finrank 𝕜 F) → F := fun j =>
    if h : (j : ℕ) < q then ((T.singularValues j : 𝕜)⁻¹) • T (v ⟨j, h⟩) else 0 with hw
  set s : Set (Fin (finrank 𝕜 F)) := {j | (j : ℕ) < q ∧ T.singularValues j ≠ 0} with hs
  have hws : ∀ j (hj : j ∈ s), w j = ((T.singularValues j : 𝕜)⁻¹) • T (v ⟨j, hj.1⟩) :=
    fun j hj => by simp [hw, hj.1]
  have horth : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rw [Set.domRestrict_apply, Set.domRestrict_apply, hws i hi, hws j hj, inner_smul_left,
      inner_smul_right, hv, inner_apply_eigenvectorBasis_adjoint_comp_self]
    simp only [Subtype.mk.injEq]
    by_cases hij : i = j
    · subst hij
      have h0 : (T.singularValues i : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hi.2
      simp only [ite_true, map_inv₀, RCLike.conj_ofReal, RCLike.ofReal_pow]
      field_simp
    · have : (⟨i, hi.1⟩ : Fin q) ≠ ⟨j, hj.1⟩ := fun h => hij (Fin.ext (Fin.mk.inj_iff.1 h))
      simp [this, hij]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨v, fun i => b (Fin.castLE hqF i), b.orthonormal.comp _ (Fin.castLE_injective hqF),
    fun i => ?_⟩
  dsimp only
  by_cases h0 : T.singularValues i = 0
  · rw [h0, RCLike.ofReal_zero, zero_smul, ← norm_eq_zero, hv,
      norm_apply_eigenvectorBasis_adjoint_comp_self, h0]
  · have hi : Fin.castLE hqF i ∈ s := ⟨i.2, h0⟩
    rw [hb _ hi, hws _ hi]
    simp only [Fin.val_castLE, Fin.eta, smul_smul]
    rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 h0), one_smul]

/-! ### Stacked isometries -/

/-- **The stacked-isometry identity**: if `‖Q₁ x‖² + ‖Q₂ x‖² = ‖x‖²` for all `x` (the map
`x ↦ (Q₁ x, Q₂ x)` is an isometry) on a nonzero finite-dimensional `E`, then
`‖Q₂‖² = 1 - σ_min(Q₁)²`, where `σ_min = σ_{finrank E - 1}` is the least stretch of `Q₁`. It is the
one fact behind the subspace-distance identity of [golub2013matrix] Theorem 2.5.1, the norms of the
blocks of a CS decomposition, (7.3.19), and the one-sided gap of `Submodule.gap`. -/
theorem norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (Q₁ : E →ₗ[𝕜] F₁) (Q₂ : E →ₗ[𝕜] F₂)
    (hE : 0 < finrank 𝕜 E) (hQ : ∀ x, ‖Q₁ x‖ ^ 2 + ‖Q₂ x‖ ^ 2 = ‖x‖ ^ 2) :
    ‖LinearMap.toContinuousLinearMap Q₂‖ ^ 2 = 1 - Q₁.singularValues (finrank 𝕜 E - 1) ^ 2 := by
  set σ := Q₁.singularValues (finrank 𝕜 E - 1) with hσ
  have hk : finrank 𝕜 E - 1 < finrank 𝕜 E := by omega
  have hσ0 : 0 ≤ σ := Q₁.singularValues_nonneg _
  have hQ₁ : ∀ x, ‖Q₁ x‖ ≤ 1 * ‖x‖ := fun x => by
    rw [one_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [hQ x, sq_nonneg ‖Q₂ x‖])
  have hσ1 : σ ≤ 1 := Q₁.singularValues_le_of_forall_norm_apply_le zero_le_one hQ₁ _
  -- the least stretch of `Q₁` is `σ`, on all of `E`
  have hlow : ∀ x, σ * ‖x‖ ≤ ‖Q₁ x‖ := by
    obtain ⟨S, hS, h⟩ := (Q₁.isGreatest_singularValues hk).1
    have hS' : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hS]; omega)
    exact fun x => h x (hS' ▸ Submodule.mem_top)
  apply le_antisymm
  · have hb : ‖LinearMap.toContinuousLinearMap Q₂‖ ≤ Real.sqrt (1 - σ ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
      rw [LinearMap.coe_toContinuousLinearMap', ← Real.sqrt_sq (norm_nonneg x),
        ← Real.sqrt_mul (by nlinarith), ← Real.sqrt_sq (norm_nonneg (Q₂ x))]
      refine Real.sqrt_le_sqrt ?_
      nlinarith [hQ x, hlow x, mul_nonneg hσ0 (norm_nonneg x)]
    calc ‖LinearMap.toContinuousLinearMap Q₂‖ ^ 2 ≤ Real.sqrt (1 - σ ^ 2) ^ 2 := by
          gcongr
      _ = 1 - σ ^ 2 := Real.sq_sqrt (by nlinarith)
  · obtain ⟨S, hS, h⟩ := (Q₁.isLeast_singularValues hk).1
    have hS1 : 0 < finrank 𝕜 S := by rw [hS]; omega
    have : Nontrivial S := Module.finrank_pos_iff.1 hS1
    obtain ⟨⟨x, hxS⟩, hx0⟩ := exists_ne (0 : S)
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hx := norm_pos_iff.2 hx0'
    have h1 := h x hxS
    have h2 := (LinearMap.toContinuousLinearMap Q₂).le_opNorm x
    rw [LinearMap.coe_toContinuousLinearMap'] at h2
    have h3 : (1 - σ ^ 2) * ‖x‖ ^ 2 ≤ ‖LinearMap.toContinuousLinearMap Q₂‖ ^ 2 * ‖x‖ ^ 2 := by
      nlinarith [hQ x, norm_nonneg (Q₂ x), norm_nonneg (Q₁ x),
        mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap Q₂)) (norm_nonneg x)]
    exact le_of_mul_le_mul_right h3 (by positivity)

/-! ### The spectrum of the Hermitian dilation -/

section DilationSpectrum

variable (A : E →ₗ[𝕜] F)

/-- The dilation of a map with its adjoint is symmetric. -/
theorem isSymmetric_hermitianDilation_adjoint : (hermitianDilation A (adjoint A)).IsSymmetric :=
  isSymmetric_hermitianDilation fun u x => adjoint_inner_left A x u

/-- The dimension of the `L²` product. -/
private theorem finrank_withLp_prod :
    finrank 𝕜 (WithLp 2 (E × F)) = finrank 𝕜 E + finrank 𝕜 F :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).finrank_eq.trans Module.finrank_prod

/-- The eigenvalues of the dilation lie below the singular values: the product of a min–max
subspace of `A` at `i` with the whole codomain has dimension at least `finrank - i`, and on it
the quadratic form `2 re ⟪A x, y⟫` is at most `σ_i (‖x‖² + ‖y‖²)`. -/
private theorem eigenvalues_hermitianDilation_le {N : ℕ}
    (hN : finrank 𝕜 (WithLp 2 (E × F)) = N) (i : Fin N) :
    A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN i ≤ A.singularValues i := by
  have hσ : 0 ≤ A.singularValues i := A.singularValues_nonneg i
  obtain ⟨V, hV, hVb⟩ := A.exists_submodule_norm_apply_le i
  let ψ : V × F →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ V.subtype.prodMap LinearMap.id
  have hψ : ∀ p : V × F, ψ p = WithLp.toLp 2 ((p.1 : E), p.2) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    rw [hψ, hψ] at h
    have h' := (WithLp.toLp_injective 2) h
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (Subtype.ext h'.1) h'.2
  have hS : N - (i : ℕ) ≤ finrank 𝕜 (range ψ) := by
    rw [finrank_range_of_inj hinj, Module.finrank_prod]
    have := finrank_withLp_prod (𝕜 := 𝕜) (E := E) (F := F)
    omega
  obtain ⟨z, ⟨⟨x, y⟩, rfl⟩, hz0, hle⟩ :=
    A.isSymmetric_hermitianDilation_adjoint.exists_mem_ne_zero_le_rayleighQuotient hN i hS
  refine hle.trans ?_
  rw [rayleighQuotient, div_le_iff₀ (pow_pos (norm_pos_iff.2 hz0) 2),
    re_inner_hermitianDilation_apply_self (fun u x => adjoint_inner_left A x u),
    WithLp.prod_norm_sq_eq_of_L2, hψ]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  have h1 := re_inner_le_norm (𝕜 := 𝕜) (A x) y
  have h2 := mul_le_mul_of_nonneg_right (hVb x x.2) (norm_nonneg y)
  nlinarith [mul_nonneg hσ (sq_nonneg (‖(x : E)‖ - ‖y‖))]

/-- The positive singular values lie below the eigenvalues of the dilation: the graph
`{(σ x, A x)}` of `A` over a max–min subspace of `A` at `i` has dimension `i + 1`, and on it the
quadratic form is at least `σ_i` times the squared norm. -/
private theorem singularValues_le_eigenvalues_hermitianDilation {N : ℕ}
    (hN : finrank 𝕜 (WithLp 2 (E × F)) = N) (i : Fin N) (hσ : 0 < A.singularValues i) :
    A.singularValues i ≤ A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN i := by
  set σ := A.singularValues i with hσdef
  have hi := A.lt_finrank_of_singularValues_pos hσ
  obtain ⟨V, hV, hVb⟩ := (A.isGreatest_singularValues hi).1
  let ψ : V →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      ((σ : 𝕜) • V.subtype).prod (A ∘ₗ V.subtype)
  have hψ : ∀ x : V, ψ x = WithLp.toLp 2 ((σ : 𝕜) • (x : E), A x) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro x x' h
    rw [hψ, hψ] at h
    have h' := congrArg Prod.fst ((WithLp.toLp_injective 2) h)
    exact Subtype.ext (smul_right_injective E (RCLike.ofReal_ne_zero.2 hσ.ne') h')
  have hS : (i : ℕ) + 1 ≤ finrank 𝕜 (range ψ) := by rw [finrank_range_of_inj hinj, hV]
  obtain ⟨z, ⟨x, rfl⟩, hz0, hle⟩ :=
    A.isSymmetric_hermitianDilation_adjoint.exists_mem_ne_zero_rayleighQuotient_le hN i hS
  refine le_trans ?_ hle
  rw [rayleighQuotient, le_div_iff₀ (pow_pos (norm_pos_iff.2 hz0) 2),
    re_inner_hermitianDilation_apply_self (fun u x => adjoint_inner_left A x u),
    WithLp.prod_norm_sq_eq_of_L2, hψ]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [map_smul, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
    norm_smul, RCLike.norm_ofReal, abs_of_pos hσ]
  have h3 : (σ * ‖(x : E)‖) ^ 2 ≤ ‖A x‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hσ.le (norm_nonneg _)) (hVb x x.2) 2
  nlinarith

/-- **The spectrum of the Hermitian dilation** ([golub2013matrix] (8.6.3), operator form): the
sorted eigenvalues of `(x, y) ↦ (A† y, A x)` on `WithLp 2 (E × F)` (of dimension `N = n + m`) are
`λ_i = σ_i - σ_{N-1-i}`, that is `σ_0, …, σ_{p-1}`, then `N - 2p` zeros, then
`-σ_{p-1}, …, -σ_0`, where `p = min n m` (at most one of the two terms is nonzero, since `σ_k = 0`
for `k ≥ p`). Proof: `λ_i ≤ σ_i` for all `i`, and `σ_i ≤ λ_i` when `σ_i > 0`, by exhibiting
subspaces for Courant–Fischer; the dilation of `-A` is `-H`, whose sorted eigenvalues are
`-λ_{N-1-i}`, which gives the other half. -/
theorem eigenvalues_hermitianDilation {N : ℕ} (hN : finrank 𝕜 (WithLp 2 (E × F)) = N)
    (i : Fin N) :
    A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN i =
      A.singularValues i - A.singularValues (N - 1 - i) := by
  have hNEF := finrank_withLp_prod (𝕜 := 𝕜) (E := E) (F := F)
  have hneg : ∀ j : Fin N, (-A).isSymmetric_hermitianDilation_adjoint.eigenvalues hN j =
      -A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN j.rev := by
    intro j
    rw [← A.isSymmetric_hermitianDilation_adjoint.eigenvalues_neg hN j]
    exact IsSymmetric.eigenvalues_congr _ _ (by rw [map_neg, hermitianDilation_neg]) hN j
  have hrev : ((i.rev : Fin N) : ℕ) = N - 1 - i := by rw [Fin.val_rev]; omega
  have h1 := A.eigenvalues_hermitianDilation_le hN i
  have h3 := (-A).eigenvalues_hermitianDilation_le hN i.rev
  rw [hneg, Fin.rev_rev, singularValues_neg, hrev] at h3
  have hs := A.singularValues_nonneg i
  have hs' := A.singularValues_nonneg (N - 1 - i)
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]
    rw [← h0] at h1
    rcases hs'.eq_or_lt with h0' | hpos'
    · rw [← h0'] at h3 ⊢
      linarith
    · have h4 := (-A).singularValues_le_eigenvalues_hermitianDilation hN i.rev
        (by rwa [singularValues_neg, hrev])
      rw [hneg, Fin.rev_rev, singularValues_neg, hrev] at h4
      linarith
  · -- `σ_i > 0` forces `σ_{N-1-i} = 0`
    have hiE := A.lt_finrank_of_singularValues_pos hpos
    have hiF : (i : ℕ) < finrank 𝕜 F := by
      by_contra h
      rw [A.singularValues_of_finrank_codomain_le (not_lt.1 h)] at hpos
      exact lt_irrefl _ hpos
    have hz : A.singularValues (N - 1 - i) = 0 :=
      A.singularValues_of_finrank_le (by omega)
    have h2 := A.singularValues_le_eigenvalues_hermitianDilation hN i hpos
    rw [hz]
    linarith

end DilationSpectrum

end LinearMap
