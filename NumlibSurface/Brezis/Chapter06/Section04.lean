import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.InnerProductSpace.Ascent
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis
import NumlibSurface.Brezis.Chapter06.Section03

/-!
# Brezis §6.4: spectral decomposition of self-adjoint compact operators

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §6.4, for `T : H →L[ℝ] H` on a real Hilbert space `H`
(`[NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]`). The book identifies `H*`
with `H` and reads `T*` as a bounded operator on `H`; self-adjointness is Mathlib's
`IsSelfAdjoint T`, i.e. `ContinuousLinearMap.adjoint T = T`. Proposition 6.9's bounds
`m = inf_{|u|=1} (Tu, u)`, `M = sup_{|u|=1} (Tu, u)` are written as infima and suprema over the
unit sphere `Metric.sphere (0 : H) 1`, as the book has them, and converted to the backbone's
Rayleigh-quotient form (`Numlib/Analysis/InnerProductSpace/CompactSpectral/Basis`, over
`RCLike 𝕜` with `{x // x ≠ 0}` as index) by
`ContinuousLinearMap.iInf_rayleigh_eq_iInf_rayleigh_sphere`. Theorem 6.11 is the backbone's
`exists_type_hilbertBasis_eigenvectors`, with an index type in the universe of `H`; the book's
separability hypothesis is carried for faithfulness although the theorem holds for every
Hilbert space. Steps (i) and (ii) of its proof are Mathlib's
`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` and
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`.

## Main results

* `isSelfAdjoint_iff` — the Definition: `T* = T`, i.e. `(Tu, v) = (u, Tv)`.
* `proposition_6_9_subset`, `proposition_6_9_inf_mem`, `proposition_6_9_sup_mem`,
  `proposition_6_9_norm` — `σ(T) ⊆ [m, M]`, `m, M ∈ σ(T)`, `‖T‖ = max (|m|, |M|)`.
* `corollary_6_10` — a self-adjoint operator with `σ(T) = {0}` is zero.
* `theorem_6_11`, `theorem_6_11_orthogonal`, `theorem_6_11_dense` — a compact self-adjoint
  operator on a separable Hilbert space has a Hilbert basis of eigenvectors; the eigenspaces
  are mutually orthogonal and span a dense subspace.
* `remark_6_8` — the finite-rank truncations of the eigen-expansion converge to `T` in norm.
* `multiplicity_eq_of_isSelfAdjoint` — the ascent of `T - λI` is `1` for self-adjoint `T`
  (Comments on Chapter 6, 3).
-/

open Filter Topology Module.End
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The Definition of §6.4.** A bounded operator `T ∈ L(H)` is self-adjoint if `T* = T`
(Mathlib's `ContinuousLinearMap.adjoint`, after the identification `H* = H`), i.e.
`(Tu, v) = (u, Tv)` for all `u, v ∈ H`. Both readings are Mathlib's `IsSelfAdjoint T`. -/
theorem isSelfAdjoint_iff (T : H →L[ℝ] H) :
    (IsSelfAdjoint T ↔ ContinuousLinearMap.adjoint T = T) ∧
      (IsSelfAdjoint T ↔ ∀ u v : H, ⟪T u, v⟫_ℝ = ⟪u, T v⟫_ℝ) :=
  ⟨ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric⟩

/-! ### Proposition 6.9 -/

omit [CompleteSpace H] in
/-- On the unit sphere the Rayleigh quotient is `(Tu, u)`. -/
private theorem rayleighQuotient_sphere (T : H →L[ℝ] H) (x : Metric.sphere (0 : H) 1) :
    T.rayleighQuotient x = ⟪T x, x⟫_ℝ := by
  have hx : ‖(x : H)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  simp [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, hx]

omit [CompleteSpace H] in
/-- The backbone's `m` is the book's `inf_{|u|=1} (Tu, u)`. -/
private theorem iInf_rayleigh_eq (T : H →L[ℝ] H) :
    ⨅ x : {x : H // x ≠ 0}, T.rayleighQuotient x = ⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ := by
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere one_pos]
  exact iInf_congr (rayleighQuotient_sphere T)

omit [CompleteSpace H] in
/-- The backbone's `M` is the book's `sup_{|u|=1} (Tu, u)`. -/
private theorem iSup_rayleigh_eq (T : H →L[ℝ] H) :
    ⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x = ⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ := by
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere one_pos]
  exact iSup_congr (rayleighQuotient_sphere T)

/-- **Proposition 6.9, `σ(T) ⊆ [m, M]`.** Let `T ∈ L(H)` be self-adjoint and
`m = inf_{|u|=1} (Tu, u)`, `M = sup_{|u|=1} (Tu, u)`. Then `σ(T) ⊆ [m, M]`. (The book's
Lax–Milgram proof uses no symmetry: this clause holds for every bounded operator.) -/
theorem proposition_6_9_subset {T : H →L[ℝ] H} (_hT : IsSelfAdjoint T) :
    spectrum ℝ T ⊆
      Set.Icc (⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ)
        (⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ) := by
  intro t ht
  have h := T.mem_Icc_of_ofReal_mem_spectrum (𝕜 := ℝ) (t := t)
    (by simpa only [RCLike.ofReal_real_eq_id, id] using ht)
  rwa [iInf_rayleigh_eq, iSup_rayleigh_eq] at h

/-- **Proposition 6.9, `m ∈ σ(T)`.** For `T` self-adjoint on a nontrivial Hilbert space,
`m = inf_{|u|=1} (Tu, u)` belongs to the spectrum. -/
theorem proposition_6_9_inf_mem [Nontrivial H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    (⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ) ∈ spectrum ℝ T := by
  have h := hT.ofReal_iInf_rayleighQuotient_mem_spectrum
  simpa only [RCLike.ofReal_real_eq_id, id, iInf_rayleigh_eq] using h

/-- **Proposition 6.9, `M ∈ σ(T)`.** For `T` self-adjoint on a nontrivial Hilbert space,
`M = sup_{|u|=1} (Tu, u)` belongs to the spectrum. -/
theorem proposition_6_9_sup_mem [Nontrivial H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    (⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ) ∈ spectrum ℝ T := by
  have h := hT.ofReal_iSup_rayleighQuotient_mem_spectrum
  simpa only [RCLike.ofReal_real_eq_id, id, iSup_rayleigh_eq] using h

/-- **Proposition 6.9, "moreover `‖T‖ = max {|m|, |M|}`".** -/
theorem proposition_6_9_norm [Nontrivial H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    ‖T‖ = max |⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ|
      |⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ| := by
  rw [hT.norm_eq_max_abs_iInf_abs_iSup, iInf_rayleigh_eq, iSup_rayleigh_eq]

/-- **Corollary 6.10.** Let `T ∈ L(H)` be self-adjoint with `σ(T) = {0}`. Then `T = 0`. -/
theorem corollary_6_10 {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (h : spectrum ℝ T = {0}) :
    T = 0 :=
  hT.eq_zero_of_spectrum_subset_zero h.le

/-! ### Theorem 6.11 -/

section Universe

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Theorem 6.11.** Let `H` be a separable Hilbert space and `T` a compact self-adjoint
operator. Then there is a Hilbert basis `(eᵢ)` of `H` composed of eigenvectors of `T`. The
index type lives in the universe of `H`; the separability hypothesis is carried as the book
states it and is not used (the theorem holds in every Hilbert space). -/
theorem theorem_6_11 [TopologicalSpace.SeparableSpace H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T)
    (hK : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ H), ∀ i, ∃ μ : ℝ, T (b i) = μ • b i := by
  obtain ⟨ι, b, hb⟩ := ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT) hK
  refine ⟨ι, b, fun i => ?_⟩
  obtain ⟨μ, hμ⟩ := hb i
  exact ⟨μ, by simpa only [RCLike.ofReal_real_eq_id, id] using hμ⟩

end Universe

/-- **Theorem 6.11, step (i) of the proof.** The eigenspaces `Eₙ = N(T - λₙ I)` of a
self-adjoint `T` (including `E₀ = N(T)`) are mutually orthogonal. Compactness is not needed. -/
theorem theorem_6_11_orthogonal {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    OrthogonalFamily ℝ (fun μ : ℝ => eigenspace (T : Module.End ℝ H) μ)
      fun μ => (eigenspace (T : Module.End ℝ H) μ).subtypeₗᵢ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT).orthogonalFamily_eigenspaces

/-- **Theorem 6.11, step (ii) of the proof.** The space `F` spanned by the eigenspaces of a
compact self-adjoint `T` is dense in `H`: `F^⊥ = {0}`. The book's argument — `T` restricted to
`F^⊥` is compact self-adjoint with spectrum `{0}`, hence zero by Corollary 6.10 — is the proof
Mathlib gives. -/
theorem theorem_6_11_dense {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) :
    (⨆ μ : ℝ, eigenspace (T : Module.End ℝ H) μ)ᗮ = ⊥ ∧
      Dense ((⨆ μ : ℝ, eigenspace (T : Module.End ℝ H) μ : Submodule ℝ H) : Set H) := by
  have h := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hK
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT)
  exact ⟨h, Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 h)⟩

/-! ### Remark 8 -/

/-- **Remark 8.** Let `T` be a compact self-adjoint operator, `(eᵢ)` a Hilbert basis of
eigenvectors with `T eᵢ = μᵢ eᵢ` (Theorem 6.11). Then `T u = ∑ μᵢ (u, eᵢ) eᵢ`, and the truncated
sums are finite-rank operators converging to `T` in norm: for every `ε > 0` only finitely
many `|μᵢ|` exceed `ε`, and for every finite set `s` of indices containing them the finite-rank
operator `Tₛ u = ∑_{i ∈ s} μᵢ (u, eᵢ) eᵢ` satisfies `‖Tₛ - T‖ ≤ ε` — the book's
`‖T_k - T‖ ≤ sup_{n ≥ k+1} |λₙ| → 0`, with the truncation at `|λ| > ε` since the index set is
not ordered. (Every compact operator into a Hilbert space is a norm limit of finite-rank
operators, self-adjoint or not: `remark_6_1`.) -/
theorem remark_6_8 {T : H →L[ℝ] H} (_hT : IsSelfAdjoint T) (hK : IsCompactOperator T)
    {ι : Type*} (b : HilbertBasis ι ℝ H) (μ : ι → ℝ) (hb : ∀ i, T (b i) = μ i • b i) {ε : ℝ}
    (hε : 0 < ε) :
    {i | ε < |μ i|}.Finite ∧
      ∀ s : Finset ι, (∀ i, ε < |μ i| → i ∈ s) →
        IsFiniteRank (∑ i ∈ s, μ i • InnerProductSpace.rankOne ℝ (b i) (b i)) ∧
          ‖(∑ i ∈ s, μ i • InnerProductSpace.rankOne ℝ (b i) (b i)) - T‖ ≤ ε := by
  classical
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩⟩
  · -- finitely many `|μᵢ| > ε`: finitely many eigenvalues of modulus `> ε`, and finitely many
    -- orthonormal `eᵢ` in each (finite-dimensional) eigenspace
    have hS : {t : ℝ | HasEigenvalue (T : Module.End ℝ H) t ∧ ε ≤ ‖t‖}.Finite :=
      hK.finite_setOf_hasEigenvalue_norm_le hε
    have hsub : {i | ε < |μ i|} ⊆
        ⋃ t ∈ {t : ℝ | HasEigenvalue (T : Module.End ℝ H) t ∧ ε ≤ ‖t‖}, {i | μ i = t} := by
      intro i hi
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      refine ⟨μ i, ⟨?_, ?_⟩, rfl⟩
      · refine hasEigenvalue_of_hasEigenvector (x := b i) ⟨?_, b.orthonormal.ne_zero i⟩
        rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe]
        exact hb i
      · rw [Real.norm_eq_abs]
        exact hi.le
    refine (hS.biUnion fun t ht => ?_).subset hsub
    have ht0 : t ≠ 0 := fun h => by
      have := ht.2
      rw [h, norm_zero] at this
      exact absurd this (not_le.2 hε)
    by_contra hinf
    have : Infinite {i // μ i = t} := Set.infinite_coe_iff.2 hinf
    have := hK.finiteDimensional_ker_pow ht0 1
    have hmem : ∀ i : {i // μ i = t}, b i ∈ ((t • (1 : H →L[ℝ] H) - T) ^ 1).ker := fun i => by
      rw [pow_one, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, smul_apply,
        one_apply_eq_self, hb, i.2, sub_self]
    have hli : LinearIndependent ℝ fun i : {i // μ i = t} =>
        (⟨b i, hmem i⟩ : ((t • (1 : H →L[ℝ] H) - T) ^ 1).ker) := by
      refine LinearIndependent.of_comp (((t • (1 : H →L[ℝ] H) - T) ^ 1).ker.subtype) ?_
      exact (b.orthonormal.comp _ Subtype.val_injective).linearIndependent
    exact Module.Finite.not_linearIndependent_of_infinite _ hli
  · -- `Tₛ` has finite rank: its range lies in the span of the `eᵢ`, `i ∈ s`
    set G : Submodule ℝ H := Submodule.span ℝ (Set.range fun i : s => b (i : ι)) with hG
    have hGfin : FiniteDimensional ℝ G := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le (S₂ := G) fun y hy => ?_
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy
    rw [ContinuousLinearMap.coe_coe, sum_apply]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [smul_apply, InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
  · -- the bound: `(T - Tₛ) u = ∑_{i ∉ s} μᵢ (eᵢ, u) eᵢ` has `ℓ²`-coefficients dominated by
    -- `ε (eᵢ, u)`, so its norm is at most `ε ‖u‖` by Parseval
    rw [norm_sub_rev]
    refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun u => ?_
    set c : ι → ℝ := fun i => if i ∈ s then 0 else μ i * ⟪b i, u⟫_ℝ with hc
    have hdom : ∀ i, ‖c i‖ ≤ ‖(ε • b.repr u) i‖ := fun i => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, b.repr_apply_apply, Real.norm_eq_abs,
        Real.norm_eq_abs]
      change |if i ∈ s then 0 else μ i * ⟪b i, u⟫_ℝ| ≤ |ε * ⟪b i, u⟫_ℝ|
      split_ifs with hi
      · rw [abs_zero]
        positivity
      · rw [abs_mul, abs_mul, abs_of_pos hε]
        exact mul_le_mul_of_nonneg_right (not_lt.1 fun h => hi (hs i h)) (abs_nonneg _)
    have hmem : Memℓp c 2 := (lp.memℓp (ε • b.repr u)).mono' hdom
    have h1 : HasSum (fun i => (μ i * ⟪b i, u⟫_ℝ) • b i) (T u) := by
      have h := (b.hasSum_repr u).mapL T
      have heq : (fun i => T (b.repr u i • b i)) = fun i => (μ i * ⟪b i, u⟫_ℝ) • b i :=
        funext fun i => by rw [map_smul, hb, smul_smul, b.repr_apply_apply, mul_comm]
      rwa [heq] at h
    have h2 : HasSum (fun i => if i ∈ s then (μ i * ⟪b i, u⟫_ℝ) • b i else 0)
        ((∑ i ∈ s, μ i • InnerProductSpace.rankOne ℝ (b i) (b i)) u) := by
      have hSu : (∑ i ∈ s, μ i • InnerProductSpace.rankOne ℝ (b i) (b i)) u =
          ∑ i ∈ s, (if i ∈ s then (μ i * ⟪b i, u⟫_ℝ) • b i else 0) := by
        rw [sum_apply]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [hi, ite_true, smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
      rw [hSu]
      exact hasSum_sum_of_ne_finset_zero fun i hi => by simp [hi]
    have hsum : HasSum (fun i => c i • b i)
        ((T - ∑ i ∈ s, μ i • InnerProductSpace.rankOne ℝ (b i) (b i)) u) := by
      rw [sub_apply]
      refine (h1.sub h2).congr_fun fun i => ?_
      by_cases hi : i ∈ s <;> simp [hc, hi]
    have heq : (T - ∑ i ∈ s, μ i • InnerProductSpace.rankOne ℝ (b i) (b i)) u =
        b.repr.symm ⟨c, hmem⟩ :=
      hsum.unique (b.hasSum_repr_symm ⟨c, hmem⟩)
    rw [heq, LinearIsometryEquiv.norm_map]
    calc ‖(⟨c, hmem⟩ : lp (fun _ : ι => ℝ) 2)‖ ≤ ‖ε • b.repr u‖ := lp.norm_mono two_ne_zero hdom
      _ = ε * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, LinearIsometryEquiv.norm_map]

/-! ### The ascent of a self-adjoint operator -/

/-- **Comments on Chapter 6, 3, last sentence.** For a self-adjoint `T ∈ L(H)` (compact or not)
and `λ ∈ ℝ`, the geometric and algebraic multiplicities of `λ` coincide because the ascent of
`T - λI` is `1`: `N((T - λI)²) = N(T - λI)`, hence `N((T - λI)ᵏ) = N(T - λI)` for all `k ≥ 1`
(Problem 36). Indeed `(T - λI)² v = 0` gives `|(T - λI) v|² = ((T - λI)² v, v) = 0` — the
backbone's `IsSelfAdjoint.ker_sq_sub_smul_eq_ker` and `IsSelfAdjoint.ker_pow_sub_smul_eq_ker`,
over the real scalars for which every `λ` is real. -/
theorem multiplicity_eq_of_isSelfAdjoint {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (l : ℝ) :
    ((T - l • (1 : H →L[ℝ] H)) ^ 2).ker = (T - l • (1 : H →L[ℝ] H)).ker ∧
      ∀ k, 1 ≤ k → ((T - l • (1 : H →L[ℝ] H)) ^ k).ker = (T - l • (1 : H →L[ℝ] H)).ker :=
  ⟨hT.ker_sq_sub_smul_eq_ker (conj_trivial l),
    fun _ hk ↦ hT.ker_pow_sub_smul_eq_ker (conj_trivial l) hk⟩

end Brezis.Chapter06

end
