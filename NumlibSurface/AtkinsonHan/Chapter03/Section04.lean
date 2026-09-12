import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.OrthogonalPolynomial
import NumlibSurface.AtkinsonHan.Chapter03.Section03

/-!
# Atkinson–Han §3.4: best approximation in inner product spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.4: the book works over a **real** inner product
space throughout §3.4, and that is kept here; Theorem 3.4.6, Theorem 3.4.7 and (3.4.6) are stated
over `RCLike 𝕜`, which contains the book's real case.

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
* `example_3_4_8` — the normalized Legendre polynomials `Lₙ = √((2n+1)/2) Pₙ` are a Hilbert basis of
  `L²(-1, 1)`, so the truncated Legendre expansion is the best approximation from `𝒫N`,
  converges to `u`, and satisfies Parseval's equality. Completeness comes from the backbone's
  `OrthogonalPolynomial.hilbertBasisOfDegreeEq`, which is Weierstrass plus the density of the
  continuous functions in `L²`.
* `example_3_4_9` — the same for the real trigonometric system on `L²(0, 2π)`: the best `L²`
  approximation from `𝕋ₙ` is the `n`-th partial sum of the Fourier series, and the series
  converges in `L²`.

The book's `L²_w(-1, 1)` of §3.5 is `Lp ℝ 2 (weightMeasure w)` there, and (3.5.2) is the instance of
`equation_3_4_6` for an orthonormal polynomial family.
-/

open Filter Topology

namespace AtkinsonHan.Chapter03

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

/-! ### Example 3.4.8: least squares by Legendre polynomials in `L²(-1, 1)` -/

section Legendre

open MeasureTheory OrthogonalPolynomial Polynomial Real

/-- The **normalized Legendre polynomials** `Lₙ = √((2n + 1)/2) Pₙ` of Example 3.4.8: the Legendre
polynomials of (3.5.4) scaled to unit `L²(-1, 1)` norm, by the orthogonality relation (3.5.5)
`(Pₘ, Pₙ) = 2 δₘₙ/(2n + 1)`. -/
noncomputable def legendreNormalized (n : ℕ) : ℝ[X] :=
  C (√((2 * (n : ℝ) + 1) / 2)) * legendre n

private theorem sqrt_coeff_pos (n : ℕ) : 0 < √((2 * (n : ℝ) + 1) / 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- The `n`-th normalized Legendre polynomial has degree `n`. -/
theorem degree_legendreNormalized (n : ℕ) : (legendreNormalized n).degree = n := by
  rw [legendreNormalized, degree_C_mul (sqrt_coeff_pos n).ne', degree_legendre]

/-- The Legendre weight is carried by `[-1, 1]`, so Weierstrass applies to it. -/
theorem legendreMeasure_compl_Icc : legendreMeasure (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hempty : (Set.Icc (-1 : ℝ) 1)ᶜ ∩ Set.Ioo (-1 : ℝ) 1 = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx => hx.1 (Set.Ioo_subset_Icc_self hx.2)
  rw [legendreMeasure, Measure.restrict_apply' measurableSet_Ioo, hempty, measure_empty]

/-- The normalized Legendre polynomials as elements of `L²(-1, 1)`. -/
noncomputable def legendreLp (n : ℕ) : Lp ℝ 2 legendreMeasure :=
  isWeight_legendreMeasure.toLpₗ (legendreNormalized n)

/-- The normalized Legendre polynomials are orthonormal in `L²(-1, 1)`: this is (3.5.5) with the
normalizing factor `√((2n + 1)/2)` put in. -/
theorem orthonormal_legendreLp : Orthonormal ℝ legendreLp := by
  have hbase : ∀ m n : ℕ, inner ℝ (legendreLp m) (legendreLp n)
      = (√((2 * (m : ℝ) + 1) / 2) * √((2 * (n : ℝ) + 1) / 2)) *
        (if m = n then 2 / (2 * (n : ℝ) + 1) else 0) := by
    intro m n
    have hval : ∀ x : ℝ, (legendreNormalized m).eval x * (legendreNormalized n).eval x
        = (√((2 * (m : ℝ) + 1) / 2) * √((2 * (n : ℝ) + 1) / 2)) *
          ((legendre m).eval x * (legendre n).eval x) := by
      intro x
      simp only [legendreNormalized, eval_mul, eval_C]
      ring
    rw [legendreLp, legendreLp, IsWeight.inner_toLpₗ]
    simp only [hval]
    rw [integral_const_mul, integral_legendreMeasure, integral_legendre_mul_legendre]
  have hinner : ∀ m n : ℕ, inner ℝ (legendreLp m) (legendreLp n)
      = if m = n then (1 : ℝ) else 0 := by
    intro m n
    rw [hbase m n]
    split_ifs with h
    · subst h
      rw [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) / 2)]
      have h2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    · rw [mul_zero]
  constructor
  · intro n
    have h : ‖legendreLp n‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hinner n n]
      simp
    nlinarith [norm_nonneg (legendreLp n)]
  · intro m n hmn
    rw [hinner m n]
    simp [hmn]

/-- **Example 3.4.8**, the completeness half: the normalized Legendre polynomials form a Hilbert
basis of `L²(-1, 1)`. Orthonormality is (3.5.5); completeness is the density of the polynomials,
which is Weierstrass together with the density of the continuous functions in `L²`. -/
noncomputable def legendreHilbertBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 legendreMeasure) :=
  hilbertBasisOfDegreeEq isWeight_legendreMeasure legendreMeasure_compl_Icc
    degree_legendreNormalized orthonormal_legendreLp

/-- The Legendre Hilbert basis is the family of normalized Legendre polynomials. -/
@[simp]
theorem coe_legendreHilbertBasis : ⇑legendreHilbertBasis = legendreLp :=
  coe_hilbertBasisOfDegreeEq _ _ _ _

/-- **Example 3.4.8.** For the Legendre weight on `(-1, 1)`:

* the normalized Legendre polynomials `Lₙ` are orthonormal;
* `P_N u = ∑_{i ≤ N} (u, Lᵢ) Lᵢ` is the best `L²(-1, 1)` approximation of `u` by polynomials of
  degree at most `N`, by (3.4.6);
* `‖u - P_N u‖ → 0`, so `u = ∑_i (u, Lᵢ) Lᵢ` in `L²(-1, 1)`; and
* Parseval's equality `‖u‖² = ∑_i (u, Lᵢ)²` holds.

The last two are the content of the example: they say that the `Lₙ` are not merely orthonormal but
complete, which is where Weierstrass enters. -/
theorem example_3_4_8 (N : ℕ) (u : Lp ℝ 2 legendreMeasure) :
    Orthonormal ℝ legendreLp ∧
      IsBestApprox
        ((Polynomial.degreeLE ℝ N).map isWeight_legendreMeasure.toLpₗ :
          Set (Lp ℝ 2 legendreMeasure))
        u (∑ k ∈ Finset.range (N + 1), inner ℝ (legendreLp k) u • legendreLp k) ∧
      HasSum (fun n => inner ℝ (legendreLp n) u • legendreLp n) u ∧
      Tendsto
        (fun N => ‖u - ∑ k ∈ Finset.range (N + 1), inner ℝ (legendreLp k) u • legendreLp k‖)
        atTop (𝓝 0) ∧
      HasSum (fun n => inner ℝ (legendreLp n) u ^ 2) (‖u‖ ^ 2) := by
  have hsum : HasSum (fun n => inner ℝ (legendreLp n) u • legendreLp n) u := by
    simpa only [coe_legendreHilbertBasis, HilbertBasis.repr_apply_apply] using
      legendreHilbertBasis.hasSum_repr u
  have htend : Tendsto
      (fun N => ∑ k ∈ Finset.range (N + 1), inner ℝ (legendreLp k) u • legendreLp k) atTop (𝓝 u) :=
    hsum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  refine ⟨orthonormal_legendreLp, ?_, hsum, ?_, ?_⟩
  · have h := isBestApprox_truncation_of_degree_eq isWeight_legendreMeasure
      degree_legendreNormalized orthonormal_legendreLp N u
    rw [Fin.sum_univ_eq_sum_range fun k =>
      inner ℝ (isWeight_legendreMeasure.toLpₗ (legendreNormalized k)) u •
        isWeight_legendreMeasure.toLpₗ (legendreNormalized k)] at h
    exact h
  · simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.1 htend
  · have h := legendreHilbertBasis.hasSum_inner_mul_inner u u
    rw [real_inner_self_eq_norm_sq] at h
    refine h.congr_fun fun n => ?_
    rw [coe_legendreHilbertBasis, real_inner_comm, sq]

end Legendre

/-! ### Example 3.4.9: least squares by trigonometric polynomials in `L²(0, 2π)` -/

section Fourier

open MeasureTheory Real

/-- The book's `𝕋ₙ` inside `L²(0, 2π)`: the image of the trigonometric polynomials of degree at
most `n` under the inclusion `C(ℝ/2πℤ, ℝ) → L²`. -/
noncomputable def trigPolyLpLE (n : ℕ) :
    Submodule ℝ (Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :=
  (trigPolyLE (2 * π) n).map
    (ContinuousMap.toLp (E := ℝ) 2 AddCircle.haarAddCircle ℝ).toLinearMap

/-- `𝕋ₙ` inside `L²` is spanned by the members of the trigonometric system of index at most
`n`. -/
theorem trigPolyLpLE_eq_span (n : ℕ) :
    trigPolyLpLE n = Submodule.span ℝ (trigLp (2 * π) '' Set.Icc (-(n : ℤ)) n) := by
  rw [trigPolyLpLE, trigPolyLE, Submodule.map_span, ← Set.image_comp]
  rfl

/-- **Example 3.4.9.** For `f ∈ L²(0, 2π)`:

* the best `L²` approximation of `f` from `𝕋ₙ` is the `n`-th partial sum of its Fourier series,
  `S_n f = ∑_{|m| ≤ n} (f, φₘ) φₘ` in the real trigonometric system `φ = trigFun (2π)`; and
* letting `n → ∞` gives the Fourier expansion (3.4.10) of `f` in `L²`.

**Normalization.** The measure here is `AddCircle.haarAddCircle`, the *probability* Haar measure of
the circle, so the inner product is `(2π)⁻¹ ∫_{-π}^{π}` and `trigFun (2π)` is `√(2π)` times the
book's orthonormal system `1/√(2π), cos (j x)/√π, sin (j x)/√π` of Theorem 1.3.13. The two
rescalings cancel in `(f, φₘ) φₘ`, so the three assertions are the book's verbatim; only the
numerical value of `‖·‖` differs, by the constant `√(2π)`. (`equation_3_7_5` of §3.7 uses the
unnormalized measure of the same circle instead, because there the constant `√(2π)` is the
statement.)

The book writes the partial sum in the classical coefficients as
`a₀/2 + ∑_{j ≤ n} (aⱼ cos (j x) + bⱼ sin (j x))`, with `aⱼ, bⱼ` the integrals (3.4.9) = (4.1.2)
that Chapter 4 works with; the dictionary between those and the coefficients `(f, φₘ)` against the
orthonormal system is `AtkinsonHan.Chapter04.equation_4_1_3_const`, `_cos` and `_sin`, which supply
the factors `2` and `√2`. -/
theorem example_3_4_9 (n : ℕ)
    (f : Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))) :
    IsBestApprox (trigPolyLpLE n : Set (Lp ℝ 2 AddCircle.haarAddCircle)) f
        (trigPartialSum n f) ∧
      trigPartialSum n f
        = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, inner ℝ (trigLp (2 * π) m) f • trigLp (2 * π) m ∧
      HasSum
        (fun m : ℤ => realFourierCoeff (f : AddCircle (2 * π) → ℝ) m • trigLp (2 * π) m) f := by
  classical
  have hcoeff : trigPartialSum n f
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, inner ℝ (trigLp (2 * π) m) f • trigLp (2 * π) m :=
    Finset.sum_congr rfl fun m _ => by rw [inner_trigLp]
  refine ⟨?_, hcoeff, hasSum_trigSeries f⟩
  have hspan : (((Finset.Icc (-(n : ℤ)) n).image (trigLp (2 * π)) : Finset _) :
      Set (Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))))
      = trigLp (2 * π) '' Set.Icc (-(n : ℤ)) n := by
    rw [Finset.coe_image, Finset.coe_Icc]
  have hproj := isBestApprox_starProjection
    (Submodule.span ℝ (((Finset.Icc (-(n : ℤ)) n).image (trigLp (2 * π)) : Finset _) :
      Set (Lp ℝ 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))))) f
  rw [equation_3_4_6 orthonormal_trigFun _ f, hspan] at hproj
  rw [trigPolyLpLE_eq_span, hcoeff]
  exact hproj

end Fourier

end AtkinsonHan.Chapter03
