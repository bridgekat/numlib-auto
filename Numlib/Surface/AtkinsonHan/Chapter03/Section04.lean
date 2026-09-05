import Numlib.Approximation.BestApprox
import Numlib.Surface.AtkinsonHan.Chapter03.Section03
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Atkinson–Han §3.4: best approximation in inner product spaces

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §3.4. The book works over a **real** inner product space
throughout §3.4, and that is kept here; Theorem 3.4.6, Theorem 3.4.7 and (3.4.6) are stated over
`RCLike 𝕜`, which contains the book's real case.

The book's inner product `(u, v)` is linear in its first argument and Mathlib's `⟪u, v⟫` in its
second, so the book's `(u − û, v − û)` is `inner ℝ (u - uhat) (v - uhat)` (symmetric in the real
case) and its `(u − û, v)` is `inner 𝕜 v (u - uhat)`.

## Main results

* `lemma_3_4_1`, `corollary_3_4_2` — the variational characterization (3.4.1) and uniqueness.
* `theorem_3_4_3`, `projConvex` — the projection onto a nonempty closed convex set.
* `proposition_3_4_4`, `proposition_3_4_4'` — `P_K` is monotone and non-expansive.
* `theorem_3_4_5` — the finite-dimensional case.
* `theorem_3_4_6`, `exercise_3_4_8` — subspaces: the orthogonality characterization (3.4.2).
* `theorem_3_4_7` — the orthogonal projection operator, (3.4.3)–(3.4.5).
* `equation_3_4_6`, `hilbertBasis_expansion` — least squares from an orthonormal family and the
  expansion of `u`.

## Not formalized here

Example 3.4.8 (Legendre least squares) and Example 3.4.9 (Fourier series in `L²(0, 2π)`) need
`L²` function spaces, which are out of scope. §3.5 (orthogonal polynomials) is cited only as a
black box; (3.5.2) is the instance of `equation_3_4_6` for an orthonormal polynomial family.
-/

open Filter Topology

namespace AtkinsonHan.Ch03

/-! ### The real theory of §3.4 -/

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Lemma 3.4.1**, the variational characterization (3.4.1): `û ∈ K` is a best approximation of
`u` from a convex set `K` if and only if `(u − û, v − û) ≤ 0` for all `v ∈ K`. -/
theorem lemma_3_4_1 {K : Set H} (hK : Convex ℝ K) {u uhat : H} (hu : uhat ∈ K) :
    IsBestApprox K u uhat ↔ ∀ v ∈ K, inner ℝ (u - uhat) (v - uhat) ≤ 0 :=
  isBestApprox_iff_inner_le_zero hK hu

/-- **Corollary 3.4.2.** Best approximations from a convex subset of an inner product space are
unique. -/
theorem corollary_3_4_2 {K : Set H} (hK : Convex ℝ K) {u v₁ v₂ : H} (h₁ : IsBestApprox K u v₁)
    (h₂ : IsBestApprox K u v₂) : v₁ = v₂ :=
  h₁.unique hK h₂

/-- **Theorem 3.4.3** (projection onto a closed convex set). In a real Hilbert space, every point
has a unique best approximation from a nonempty closed convex set. It is characterized by (3.4.1),
that is by `lemma_3_4_1`. -/
theorem theorem_3_4_3 [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : H) : ∃! uhat, IsBestApprox K u uhat := by
  obtain ⟨v, hv, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hK u
  have hbest : IsBestApprox K u v := (isBestApprox_iff_norm_eq_iInf K u v).2 ⟨hv, hnorm⟩
  exact ⟨v, hbest, fun w hw => corollary_3_4_2 hK hw hbest⟩

/-- The **projection operator onto a nonempty closed convex set** `K`, written `P_K` in the book
(after Theorem 3.4.3). It is not linear unless `K` is a subspace. -/
noncomputable def projConvex [CompleteSpace H] (K : Set H) (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : H) : H :=
  (theorem_3_4_3 hne hcl hK u).exists.choose

/-- Defining property of `projConvex`: it is the best approximation from `K`. -/
theorem isBestApprox_projConvex [CompleteSpace H] (K : Set H) (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (u : H) :
    IsBestApprox K u (projConvex K hne hcl hK u) :=
  (theorem_3_4_3 hne hcl hK u).exists.choose_spec

/-- On a complete subspace, `P_K` is Mathlib's orthogonal projection. -/
theorem projConvex_eq_starProjection [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    (hne : (K : Set H).Nonempty) (hcl : IsClosed (K : Set H)) (hK : Convex ℝ (K : Set H)) (u : H) :
    projConvex (K : Set H) hne hcl hK u = K.starProjection u :=
  (isBestApprox_projConvex (K : Set H) hne hcl hK u).eq_starProjection K

/-- **Proposition 3.4.4** (pairs form). The metric projection onto a convex set is monotone and
non-expansive. No completeness is needed in this form. -/
theorem proposition_3_4_4 {K : Set H} (hK : Convex ℝ K) {u v uhat vhat : H}
    (hu : IsBestApprox K u uhat) (hv : IsBestApprox K v vhat) :
    0 ≤ inner ℝ (uhat - vhat) (u - v) ∧ ‖uhat - vhat‖ ≤ ‖u - v‖ :=
  hu.dist_le_dist hK hv

/-- **Proposition 3.4.4** in the book's form, for the projection operator `P_K`. -/
theorem proposition_3_4_4' [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u v : H) :
    0 ≤ inner ℝ (projConvex K hne hcl hK u - projConvex K hne hcl hK v) (u - v) ∧
      ‖projConvex K hne hcl hK u - projConvex K hne hcl hK v‖ ≤ ‖u - v‖ :=
  proposition_3_4_4 hK (isBestApprox_projConvex K hne hcl hK u)
    (isBestApprox_projConvex K hne hcl hK v)

/-- **Theorem 3.4.5.** A nonempty closed convex subset of a finite-dimensional subspace of an
inner product space admits a unique best approximation to every point; no completeness of the
ambient space is required. -/
theorem theorem_3_4_5 {K : Set H} (S : Submodule ℝ H) [FiniteDimensional ℝ S] (hKS : K ⊆ S)
    (hcl : IsClosed K) (hK : Convex ℝ K) (hne : K.Nonempty) (u : H) :
    ∃! uhat, IsBestApprox K u uhat := by
  obtain ⟨v, hv⟩ := exists_isBestApprox_of_isClosed_of_finiteDimensional hcl hne S hKS u
  exact ⟨v, hv, fun w hw => corollary_3_4_2 hK hw hv⟩

/-- **Exercise 3.4.8.** For a subspace the variational inequality (3.4.1) and the orthogonality
condition (3.4.2) are equivalent, both being equivalent to being a best approximation. -/
theorem exercise_3_4_8 (K : Submodule ℝ H) {u uhat : H} (hu : uhat ∈ K) :
    (∀ v ∈ K, inner ℝ (u - uhat) (v - uhat) ≤ 0) ↔ ∀ v ∈ K, inner ℝ v (u - uhat) = 0 := by
  constructor
  · intro h
    exact (Submodule.mem_orthogonal K _).1
      ((isBestApprox_iff_mem_orthogonal K hu).1 ((lemma_3_4_1 K.convex hu).2 h))
  · intro h
    exact (lemma_3_4_1 K.convex hu).1
      ((isBestApprox_iff_mem_orthogonal K hu).2 ((Submodule.mem_orthogonal K _).2 h))

end Real

/-! ### Subspaces and the orthogonal projection operator -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Theorem 3.4.6.** A complete subspace `K` admits a unique best approximation to every point,
characterized by the orthogonality relation (3.4.2) `(u − û, v) = 0` for all `v ∈ K`. -/
theorem theorem_3_4_6 (K : Submodule 𝕜 H) [CompleteSpace K] (u : H) :
    (∃! uhat, IsBestApprox (K : Set H) u uhat) ∧
      ∀ uhat ∈ K, (IsBestApprox (K : Set H) u uhat ↔ ∀ v ∈ K, inner 𝕜 v (u - uhat) = 0) := by
  refine ⟨⟨K.starProjection u, isBestApprox_starProjection K u, fun w hw => ?_⟩,
    fun uhat huhat => ?_⟩
  · exact hw.eq_starProjection K
  · rw [isBestApprox_iff_mem_orthogonal K huhat, Submodule.mem_orthogonal]

/-- **Theorem 3.4.7**, the properties (3.4.3)–(3.4.5) of the orthogonal projection operator
`P_K` onto a complete subspace: it is self-adjoint, `‖v‖² = ‖P_K v‖² + ‖v − P_K v‖²`, and
`‖P_K‖ ≤ 1` with equality unless `K = {0}`. Linearity and boundedness of `P_K` are built into the
type `H →L[𝕜] H` of `Submodule.starProjection`.

**Book imprecision.** The book states (3.4.5) as `‖P_K‖ = 1`; this fails for `K = {0}`, where
`P_K = 0`. The correct statement is `‖P_K‖ ≤ 1`, with equality when `K ≠ {0}`. -/
theorem theorem_3_4_7 (K : Submodule 𝕜 H) [CompleteSpace K] :
    (∀ u v : H, inner 𝕜 (K.starProjection u) v = inner 𝕜 u (K.starProjection v)) ∧
      (∀ v : H, ‖v‖ ^ 2 = ‖K.starProjection v‖ ^ 2 + ‖v - K.starProjection v‖ ^ 2) ∧
      ‖K.starProjection‖ ≤ 1 ∧ (K ≠ ⊥ → ‖K.starProjection‖ = 1) := by
  refine ⟨fun u v => K.starProjection_isSymmetric u v, fun v => ?_, K.starProjection_norm_le,
    fun hK => K.norm_starProjection hK⟩
  have hzero : inner 𝕜 (K.starProjection v) (v - K.starProjection v) = 0 :=
    (K.mem_orthogonal _).1 (K.sub_starProjection_mem_orthogonal v) _ (K.starProjection_apply_mem v)
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (K.starProjection v) (v - K.starProjection v) hzero
  have hsum : K.starProjection v + (v - K.starProjection v) = v := by abel
  rw [hsum] at hpy
  simp only [← pow_two] at hpy
  exact hpy

/-- **(3.4.6).** Least-squares approximation from the span of a finite orthonormal family: the
best approximation of `u` is `∑ᵢ (u, φᵢ) φᵢ`. -/
theorem equation_3_4_6 [DecidableEq H] {ι : Type*} {φ : ι → H} (hφ : Orthonormal 𝕜 φ) (s : Finset ι)
    (u : H) :
    (Submodule.span 𝕜 (s.image φ : Set H)).starProjection u = ∑ i ∈ s, inner 𝕜 (φ i) u • φ i := by
  rw [(OrthonormalBasis.span hφ s).starProjection_eq_sum_rankOne]
  simp only [FunLike.coe_sum, Finset.sum_apply, InnerProductSpace.rankOne_apply,
    OrthonormalBasis.span_apply]
  exact Finset.sum_coe_sort s fun i => inner 𝕜 (φ i) u • φ i

/-- The expansion of a vector in a Hilbert basis, `u = ∑ᵢ (u, φᵢ) φᵢ` (the infinite-dimensional
form of (3.4.6)). -/
theorem hilbertBasis_expansion {ι : Type*} (b : HilbertBasis ι 𝕜 H) (u : H) :
    HasSum (fun i => inner 𝕜 (b i) u • b i) u := by
  simpa [b.repr_apply_apply] using b.hasSum_repr u

end Hilbert

end AtkinsonHan.Ch03
