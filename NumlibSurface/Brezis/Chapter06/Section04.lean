/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.InnerProductSpace.Ascent
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis
import NumlibSurface.Brezis.Chapter06.Section03

/-!
# Brezis, Section 6.4: Spectral decomposition of self-adjoint compact operators

This module formalizes Section 6.4 of [brezis2011functional] for a bounded operator
$T \in \mathcal{L}(H)$ on a real Hilbert space $H$ with scalar product $(u, v)$. The source
identifies $H^\star$ with $H$, so the adjoint $T^\star$ is again an operator on $H$, and $T$ is
self-adjoint if $T^\star = T$, that is, $(Tu, v) = (u, Tv)$ for all $u, v$. For a self-adjoint $T$
put
$$m = \inf_{|u| = 1} (Tu, u), \qquad M = \sup_{|u| = 1} (Tu, u).$$
Then $\sigma(T) \subseteq [m, M]$, both $m$ and $M$ lie in $\sigma(T)$, and
$\|T\| = \max\{|m|, |M|\}$ (Proposition 6.9); so a self-adjoint operator with $\sigma(T) = \{0\}$ is
zero (Corollary 6.10). A compact self-adjoint operator on a separable Hilbert space has a Hilbert
basis of eigenvectors (Theorem 6.11), and the finite truncations of its eigenvector expansion
converge to $T$ in norm (Remark 8).

Proposition 6.9 specializes the Rayleigh-quotient results of the backbone module
`Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis`. Theorem 6.11 is the backbone's
`ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors`, and the steps of its proof
are Mathlib's `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` and
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. The last result specializes
`Numlib.Analysis.InnerProductSpace.Ascent`.

## Main definitions

* Section 6.4, definition of a self-adjoint operator, `Brezis.Chapter06.isSelfAdjoint_iff`:
  Mathlib's `IsSelfAdjoint T` means $T^\star = T$, and also $(Tu, v) = (u, Tv)$ for all $u, v$.

## Main results

* Proposition 6.9, `Brezis.Chapter06.proposition_6_9_subset`: $\sigma(T) \subseteq [m, M]$.
* Proposition 6.9, `Brezis.Chapter06.proposition_6_9_inf_mem` and
  `Brezis.Chapter06.proposition_6_9_sup_mem`: $m \in \sigma(T)$ and $M \in \sigma(T)$.
* Proposition 6.9, `Brezis.Chapter06.proposition_6_9_norm`: $\|T\| = \max\{|m|, |M|\}$.
* Corollary 6.10, `Brezis.Chapter06.corollary_6_10`: a self-adjoint operator with
  $\sigma(T) = \{0\}$ is zero.
* Theorem 6.11, `Brezis.Chapter06.theorem_6_11`: a compact self-adjoint operator on a separable
  Hilbert space has a Hilbert basis of eigenvectors.
* Theorem 6.11, `Brezis.Chapter06.theorem_6_11_orthogonal` and
  `Brezis.Chapter06.theorem_6_11_dense`: the eigenspaces are mutually orthogonal, and for compact
  $T$ they span a dense subspace.
* Remark 8, `Brezis.Chapter06.remark_6_8`: the finite truncations of
  $Tu = \sum_i \mu_i (u, e_i) e_i$ have finite rank and converge to $T$ in norm.
* Comments on Chapter 6, item 3, `Brezis.Chapter06.multiplicity_eq_of_isSelfAdjoint`: for
  self-adjoint $T$, $N((T - \lambda I)^k) = N(T - \lambda I)$ for all $k \ge 1$.

## Conventions

* Self-adjointness is Mathlib's `IsSelfAdjoint T`, which means `ContinuousLinearMap.adjoint T = T`.
* The numbers $m$ and $M$ are the infimum and the supremum of $(Tu, u)$ over the unit sphere
  `Metric.sphere (0 : H) 1`, as the source writes them.

## Implementation notes

* The backbone states Proposition 6.9 for the Rayleigh quotient $(Tx, x)/|x|^2$ over $x \neq 0$,
  over `RCLike 𝕜`. Mathlib's `ContinuousLinearMap.iInf_rayleigh_eq_iInf_rayleigh_sphere` converts it
  to the unit sphere.
* In Theorem 6.11 the index type of the Hilbert basis is in the universe of $H$.

## Deviations from the source

* **Proposition 6.9** (reading). The statements $m, M \in \sigma(T)$ and $\|T\| = \max\{|m|, |M|\}$
  assume $H \neq \{0\}$, which the source leaves implicit. See
  `Brezis.Chapter06.proposition_6_9_inf_mem`.
* **Theorem 6.11** (reading). The source's Hilbert basis is a sequence $(e_n)$. Here the basis is
  indexed by an arbitrary type, which also covers finite dimension. See
  `Brezis.Chapter06.theorem_6_11`.
* **Proof of Theorem 6.11** (generalization). Orthogonality and density of the eigenspaces
  apply without separability. Orthogonality also holds without compactness. See
  `Brezis.Chapter06.theorem_6_11_orthogonal` and `Brezis.Chapter06.theorem_6_11_dense`.
* **Remark 8** (reading). The source truncates the expansion after the first $k$ eigenvalues. Here
  the index set is not ordered, and the truncation keeps a finite set of indices that contains all
  $i$ with $|\mu_i| > \varepsilon$. See `Brezis.Chapter06.remark_6_8`.
* **Multiplicity of eigenvalues** (generalization). The kernel stabilization identity holds
  for any real shift of a bounded self-adjoint operator. See
  `Brezis.Chapter06.multiplicity_eq_of_isSelfAdjoint`.
-/

open Filter Topology Module.End
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Section 6.4** of [brezis2011functional], definition of a self-adjoint operator. Let $H$ be a
Hilbert space and $T \in \mathcal{L}(H)$. Then $T$ is self-adjoint in the sense of Mathlib's
`IsSelfAdjoint T` if and only if $T^\star = T$, and also if and only if
$$(Tu, v) = (u, Tv) \quad \text{for all } u, v \in H.$$

The adjoint $T^\star$ is Mathlib's `ContinuousLinearMap.adjoint T`, which identifies $H^\star$
with $H$ as the source does. -/
theorem isSelfAdjoint_iff (T : H →L[ℝ] H) :
    (IsSelfAdjoint T ↔ ContinuousLinearMap.adjoint T = T) ∧
      (IsSelfAdjoint T ↔ ∀ u v : H, ⟪T u, v⟫_ℝ = ⟪u, T v⟫_ℝ) :=
  ⟨ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric⟩

/-! ### Proposition 6.9 -/

omit [CompleteSpace H] in
/-- On the unit sphere, the Rayleigh quotient of $T$ at $u$ is $(Tu, u)$. -/
private theorem rayleighQuotient_sphere (T : H →L[ℝ] H) (x : Metric.sphere (0 : H) 1) :
    T.rayleighQuotient x = ⟪T x, x⟫_ℝ := by
  have hx : ‖(x : H)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  simp [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, hx]

omit [CompleteSpace H] in
/-- The infimum of the Rayleigh quotient of $T$ over $x \neq 0$ is $\inf_{|u| = 1} (Tu, u)$. -/
private theorem iInf_rayleigh_eq (T : H →L[ℝ] H) :
    ⨅ x : {x : H // x ≠ 0}, T.rayleighQuotient x = ⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ := by
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere one_pos]
  exact iInf_congr (rayleighQuotient_sphere T)

omit [CompleteSpace H] in
/-- The supremum of the Rayleigh quotient of $T$ over $x \neq 0$ is $\sup_{|u| = 1} (Tu, u)$. -/
private theorem iSup_rayleigh_eq (T : H →L[ℝ] H) :
    ⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x = ⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ := by
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere one_pos]
  exact iSup_congr (rayleighQuotient_sphere T)

/-- **Proposition 6.9** of [brezis2011functional], the inclusion. Let $H$ be a Hilbert space and let
$T \in \mathcal{L}(H)$ be self-adjoint. Put $m = \inf_{|u| = 1} (Tu, u)$ and
$M = \sup_{|u| = 1} (Tu, u)$. Then
$$\sigma(T) \subseteq [m, M].$$

The proof of the source uses the Lax–Milgram theorem and no symmetry, so this inclusion holds
for every bounded operator; the self-adjointness hypothesis is not used. If $H = \{0\}$, then
the sphere is empty, $m = M = 0$ by the convention for the infimum and the supremum of an empty
set in `ℝ`, and $\sigma(T) = \emptyset$. -/
theorem proposition_6_9_subset {T : H →L[ℝ] H} (_hT : IsSelfAdjoint T) :
    spectrum ℝ T ⊆
      Set.Icc (⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ)
        (⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ) := by
  intro t ht
  have h := T.mem_Icc_of_ofReal_mem_spectrum (𝕜 := ℝ) (t := t)
    (by simpa only [RCLike.ofReal_real_eq_id, id] using ht)
  rwa [iInf_rayleigh_eq, iSup_rayleigh_eq] at h

/-- **Proposition 6.9** of [brezis2011functional], the lower end. Let $H \neq \{0\}$ be a Hilbert
space and let $T \in \mathcal{L}(H)$ be self-adjoint. Then $m = \inf_{|u| = 1} (Tu, u)$ belongs
to $\sigma(T)$.

**Reading.** The hypothesis $H \neq \{0\}$ is implicit in the source. For $H = \{0\}$ the
spectrum is empty. -/
theorem proposition_6_9_inf_mem [Nontrivial H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    (⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ) ∈ spectrum ℝ T := by
  have h := hT.ofReal_iInf_rayleighQuotient_mem_spectrum
  simpa only [RCLike.ofReal_real_eq_id, id, iInf_rayleigh_eq] using h

/-- **Proposition 6.9** of [brezis2011functional], the upper end. Let $H \neq \{0\}$ be a Hilbert
space and let $T \in \mathcal{L}(H)$ be self-adjoint. Then $M = \sup_{|u| = 1} (Tu, u)$ belongs
to $\sigma(T)$.

**Reading.** The hypothesis $H \neq \{0\}$ is implicit in the source. For $H = \{0\}$ the
spectrum is empty. -/
theorem proposition_6_9_sup_mem [Nontrivial H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    (⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ) ∈ spectrum ℝ T := by
  have h := hT.ofReal_iSup_rayleighQuotient_mem_spectrum
  simpa only [RCLike.ofReal_real_eq_id, id, iSup_rayleigh_eq] using h

/-- **Proposition 6.9** of [brezis2011functional], the norm. Let $H \neq \{0\}$ be a Hilbert space
and let $T \in \mathcal{L}(H)$ be self-adjoint, with $m = \inf_{|u| = 1} (Tu, u)$ and
$M = \sup_{|u| = 1} (Tu, u)$. Then
$$\|T\| = \max\{|m|, |M|\}.$$

The source states this with the word "moreover".

**Reading.** Makes nonzero Hilbert space explicit so the extrema are taken over a nonempty unit
sphere.
-/
theorem proposition_6_9_norm [Nontrivial H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    ‖T‖ = max |⨅ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ|
      |⨆ u : Metric.sphere (0 : H) 1, ⟪T u, u⟫_ℝ| := by
  rw [hT.norm_eq_max_abs_iInf_abs_iSup, iInf_rayleigh_eq, iSup_rayleigh_eq]

/-- **Corollary 6.10** of [brezis2011functional]. Let $H$ be a Hilbert space and let
$T \in \mathcal{L}(H)$ be self-adjoint with $\sigma(T) = \{0\}$. Then $T = 0$. -/
theorem corollary_6_10 {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (h : spectrum ℝ T = {0}) :
    T = 0 :=
  hT.eq_zero_of_spectrum_subset_zero h.le

/-! ### Theorem 6.11 -/

section Universe

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Theorem 6.11** of [brezis2011functional]. Let $H$ be a separable Hilbert space and let
$T \in \mathcal{L}(H)$ be compact and self-adjoint. Then there is a Hilbert basis
$(e_i)_{i \in I}$ of $H$ composed of eigenvectors of $T$: for every $i$ there is
$\mu_i \in \mathbb{R}$ with $T e_i = \mu_i e_i$.

**Reading.** The source's Hilbert basis is a sequence $(e_n)$. Here the basis is indexed by a
type $I$, which may be finite. The countability of $I$, which follows from separability, is not
stated.

The index type is in the universe of $H$. The separability hypothesis is kept as the source
states it but is not used: the backbone theorem
`ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors` holds in every Hilbert
space. -/
theorem theorem_6_11 [TopologicalSpace.SeparableSpace H] {T : H →L[ℝ] H} (hT : IsSelfAdjoint T)
    (hK : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ H), ∀ i, ∃ μ : ℝ, T (b i) = μ • b i := by
  obtain ⟨ι, b, hb⟩ := ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT) hK
  refine ⟨ι, b, fun i => ?_⟩
  obtain ⟨μ, hμ⟩ := hb i
  exact ⟨μ, by simpa only [RCLike.ofReal_real_eq_id, id] using hμ⟩

end Universe

/-- **Theorem 6.11** of [brezis2011functional], step (i) of the proof. Let $H$ be a Hilbert space
and let $T \in \mathcal{L}(H)$ be self-adjoint. Then the eigenspaces
$E(\lambda) = N(T - \lambda I)$, $\lambda \in \mathbb{R}$, are mutually orthogonal: they form an
orthogonal family in the sense of Mathlib's `OrthogonalFamily`.

The family includes $E(0) = N(T)$.

**Generalization.** The eigenspaces are mutually orthogonal without compactness or separability. -/
theorem theorem_6_11_orthogonal {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    OrthogonalFamily ℝ (fun μ : ℝ => eigenspace (T : Module.End ℝ H) μ)
      fun μ => (eigenspace (T : Module.End ℝ H) μ).subtypeₗᵢ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT).orthogonalFamily_eigenspaces

/-- **Theorem 6.11** of [brezis2011functional], step (ii) of the proof. Let $H$ be a Hilbert space
and let $T \in \mathcal{L}(H)$ be compact and self-adjoint, and let $F$ be the linear space
spanned by the eigenspaces $N(T - \lambda I)$, $\lambda \in \mathbb{R}$. Then $F^\perp = \{0\}$,
and $F$ is dense in $H$.

The argument of the source is the proof of Mathlib's
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`: the restriction of $T$ to
$F^\perp$ is compact and self-adjoint and has no nonzero spectral values, so it is zero.

**Generalization.** The eigenspaces span a dense space without separability of $H$. -/
theorem theorem_6_11_dense {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) :
    (⨆ μ : ℝ, eigenspace (T : Module.End ℝ H) μ)ᗮ = ⊥ ∧
      Dense ((⨆ μ : ℝ, eigenspace (T : Module.End ℝ H) μ : Submodule ℝ H) : Set H) := by
  have h := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hK
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT)
  exact ⟨h, Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 h)⟩

/-! ### Remark 8 -/

/-- **Remark 8** in Chapter 6 of [brezis2011functional]. Let $H$ be a Hilbert space and let
$T \in \mathcal{L}(H)$ be compact and self-adjoint. Let $(e_i)_{i \in I}$ be a Hilbert basis of
$H$ and $(\mu_i)$ real numbers with $T e_i = \mu_i e_i$ for all $i$, and let $\varepsilon > 0$.
Then the set of $i$ with $|\mu_i| > \varepsilon$ is finite, and for every finite set
$s \subseteq I$ that contains all these $i$, the operator
$$T_s u = \sum_{i \in s} \mu_i (u, e_i) e_i$$
has finite rank and satisfies $\|T_s - T\| \le \varepsilon$.

**Reading.** The source orders the eigenvalues as a sequence $(\lambda_n)$ and proves $\|T_k -
T\| \le \sup_{n \ge k+1} |\lambda_n| \to 0$ for the truncation $T_k$ after $k$ terms. Here the
index set is not ordered, so the truncation is made at $|\mu_i| > \varepsilon$.

The operator $u \mapsto (u, e_i) e_i$ is `InnerProductSpace.rankOne ℝ (b i) (b i)`. Every
compact operator into a Hilbert space is a norm limit of operators of finite rank, self-adjoint
or not: see `Brezis.Chapter06.remark_6_1`. -/
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

/-- **Comments on Chapter 6, item 3,** of [brezis2011functional], last sentence. Let $H$ be a
Hilbert space, let $T \in \mathcal{L}(H)$ be self-adjoint, compact or not, and let
$\lambda \in \mathbb{R}$. Then
$$N((T - \lambda I)^2) = N(T - \lambda I), \qquad N((T - \lambda I)^k) = N(T - \lambda I) \quad
  \text{for all } k \ge 1.$$
So the ascent of $T - \lambda I$ is at most $1$, and the geometric and algebraic multiplicities
of $\lambda$ are equal.

This is also Problem 36 of the source. If $(T - \lambda I)^2 v = 0$, then $|(T - \lambda I)
v|^2 = ((T - \lambda I)^2 v, v) = 0$. The proof specializes
`IsSelfAdjoint.ker_sq_sub_smul_eq_ker` and `IsSelfAdjoint.ker_pow_sub_smul_eq_ker`.

**Generalization.** The kernel identities hold for every real $\lambda$ and every bounded
self-adjoint operator. The source discusses nonzero eigenvalues of compact operators. -/
theorem multiplicity_eq_of_isSelfAdjoint {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) (l : ℝ) :
    ((T - l • (1 : H →L[ℝ] H)) ^ 2).ker = (T - l • (1 : H →L[ℝ] H)).ker ∧
      ∀ k, 1 ≤ k → ((T - l • (1 : H →L[ℝ] H)) ^ k).ker = (T - l • (1 : H →L[ℝ] H)).ker :=
  ⟨hT.ker_sq_sub_smul_eq_ker (conj_trivial l),
    fun _ hk ↦ hT.ker_pow_sub_smul_eq_ker (conj_trivial l) hk⟩

end Brezis.Chapter06

end
