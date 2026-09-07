import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Numlib.Analysis.InnerProductSpace.CompactSpectral
import Numlib.Analysis.Normed.Operator.Compact
import Numlib.Analysis.Normed.Operator.Riesz
import Numlib.IntegralEquations.Basic
import Numlib.IntegralEquations.WeaklySingular
import NumlibSurface.AtkinsonHan.Chapter02.Section04

/-!
# Atkinson–Han §2.8: compact linear operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.8: compact operators and their closure
properties, the Fredholm alternative for an equation of the second kind `(λ - K) u = f`, the Riesz
theory of the spectrum of a compact operator, and the spectral theorem for a compact self-adjoint
operator.

Mathlib carries most of this. `IsCompactOperator` is the book's Definition 2.8.1 in the *preimage*
form, and `isCompactOperator_iff_isCompact_closure_image_closedBall` is the book's own phrasing;
`definition_2_8_1` below adds the sequential reading the book uses in practice.
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` is Theorem 2.8.10 exactly, and
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` is the spectral theorem. The
elementary closure properties, Schauder's theorem, the discreteness of the spectrum and the closed
range are `Numlib/Analysis/Normed/Operator/Compact`.

## Main results

* `definition_2_8_1` — compactness in the sequential form.
* `proposition_2_8_4`, `proposition_2_8_6`, `proposition_2_8_7` — finite rank, composition and
  operator-norm limits.
* `example_2_8_5`, `example_2_8_5_isCompactOperator`, `example_2_8_5_norm` — a degenerate kernel
  gives a finite-rank operator, its range in the span of the `β i`, with `‖K‖ ≤ ∑ ‖β i‖ ∫ |γ i|`.
* `example_2_8_8`, `example_2_8_8_interval` — an integral operator with a continuous kernel is
  compact on `C(D)` for a compact region `D ⊆ ℝ^d`, and on `C[a, b]`.
* `equation_2_8_2`, `equation_2_8_5`, `equation_2_8_6_le`, `equation_2_8_6`,
  `isCompactOperator_of_isAdmissibleKernel` — §2.8.1: a kernel integrable in `y` and satisfying
  (A₁)–(A₂) gives a bounded, compact operator on `C(D)`, with the oscillation estimate (2.8.5) in
  terms of the modulus of continuity in the mean (2.8.3) and the norm (2.8.6).
* `example_2_8_9`, `example_2_8_2` — the two weakly singular kernels of an interval,
  `|x − y| ^ (-γ)` with `0 < γ < 1` and `log |cos x − cos y|` on `[0, π]`, give compact operators.
* `theorem_2_8_10` — the Fredholm alternative, with `theorem_2_8_10_inverse` for the bounded
  inverse the book gets from its own Theorem 2.4.3.
* `theorem_2_8_12_1`, `theorem_2_8_12_2`, `theorem_2_8_12_4` — the eigenvalues accumulate only at
  `0`, the nonzero eigenspaces are finite-dimensional, and `range (λ - K)` is closed.
* `theorem_2_8_12_3`, `theorem_2_8_12_5`, `theorem_2_8_12_6` — the Riesz index `ν(λ)` of a nonzero
  eigenvalue, the decomposition (2.8.28) into `K`-invariant summands at that index, and the
  Fredholm alternative for an operator only some power of which is compact.
* `lemma_2_8_13` — Schauder's theorem.
* `theorem_2_8_14`, `theorem_2_8_14_isCompl` — solvability of `(λ - K) u = f` and the orthogonal
  decomposition (2.8.30) it gives; `theorem_2_8_14_hasEigenvalue_adjoint` and `theorem_2_8_14_dim`
  for clause (1), that `conj λ` is an eigenvalue of `K*` and that the two null spaces have equal
  dimension.
* `theorem_2_8_15`, `theorem_2_8_15_eigenvalue_real`, `theorem_2_8_15_index`,
  `theorem_2_8_15_closure_range`, `theorem_2_8_15_enumeration` — the spectral theorem for compact
  self-adjoint operators, the reality of the eigenvalues, the index-one clause
  `N((λ - K)²) = N(λ - K)`, the location `(ker K)ᗮ = closure (range K)` of the eigenvectors for the
  nonzero eigenvalues, and the decreasing enumeration (2.8.31)–(2.8.32) with its orthonormal basis.

## Conventions

The book writes `λ` for the scalar of the second-kind equation; `λ` is a keyword in Lean, so it is
written `l` below. The book states §2.8 over a general scalar field and specializes to real or
complex scalars; the statements here are over `RCLike 𝕜`, as elsewhere in this surface.

The continuous-kernel case, which is what Chapters 12 and 13 use, is `example_2_8_8`.
-/

open Filter Topology Metric Module.End

open scoped InnerProductSpace

namespace AtkinsonHan.Chapter02

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Definition 2.8.1 and its sequential form -/

/-- **Definition 2.8.1**, with the sequential reading that follows it: a bounded operator
is compact exactly when every bounded sequence `(uₙ)` has a subsequence along which the images
`K uₙ` converge. Mathlib's `IsCompactOperator` is the same notion in the form "the image of the
closed unit ball has compact closure", which is the book's own definition. -/
theorem definition_2_8_1 (K : V →L[𝕜] W) :
    IsCompactOperator K ↔
      ∀ u : ℕ → V, (∃ C, ∀ n, ‖u n‖ ≤ C) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w, Tendsto (fun n => K (u (φ n))) atTop (𝓝 w) := by
  constructor
  · rintro hK u ⟨C, hC⟩
    obtain ⟨S, hS, hSsub⟩ := hK.image_closedBall_subset_compact (max C 1)
    obtain ⟨w, -, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := fun n => K (u n)) fun n =>
      hSsub ⟨u n, mem_closedBall_zero_iff.2 ((hC n).trans (le_max_left _ _)), rfl⟩
    exact ⟨φ, hφ, w, hlim⟩
  · intro hseq
    refine (isCompactOperator_iff_isCompact_closure_image_closedBall
      (K : V →ₗ[𝕜] W) one_pos).2 (IsSeqCompact.isCompact fun x hx => ?_)
    have hchoice : ∀ n : ℕ, ∃ v : V, ‖v‖ ≤ 1 ∧ dist (x n) (K v) < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨y, ⟨v, hv, rfl⟩, hd⟩ :=
        Metric.mem_closure_iff.1 (hx n) (1 / ((n : ℝ) + 1)) (by positivity)
      exact ⟨v, mem_closedBall_zero_iff.1 hv, hd⟩
    choose v hv hd using hchoice
    obtain ⟨φ, hφ, w, hw⟩ := hseq v ⟨1, hv⟩
    have hmem : ∀ n, K (v (φ n)) ∈ closure ((K : V →ₗ[𝕜] W) '' closedBall 0 1) := fun n =>
      subset_closure ⟨v (φ n), mem_closedBall_zero_iff.2 (hv _), rfl⟩
    refine ⟨w, isClosed_closure.mem_of_tendsto hw (.of_forall hmem), φ, hφ, ?_⟩
    have hone : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact h0.comp hφ.tendsto_atTop
    have h1 : Tendsto (fun n => dist (x (φ n)) (K (v (φ n)))) atTop (𝓝 0) :=
      squeeze_zero (fun n => dist_nonneg) (fun n => (hd (φ n)).le) hone
    have h2 : Tendsto (fun n => dist (K (v (φ n))) w) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hw
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg)
      (fun n => dist_triangle (x (φ n)) (K (v (φ n))) w) ?_
    simpa using h1.add h2

/-! ### Propositions 2.8.4, 2.8.6 and 2.8.7: closure properties -/

/-- **Proposition 2.8.4.** A bounded linear operator of finite rank — Definition 2.8.3 —
is compact. -/
theorem proposition_2_8_4 (K : V →L[𝕜] W)
    [FiniteDimensional 𝕜 (LinearMap.range (K : V →ₗ[𝕜] W))] : IsCompactOperator K :=
  IsCompactOperator.of_finiteDimensional_range K

/-- **Proposition 2.8.6.** A composition of bounded operators in which at least one
factor is compact is compact. -/
theorem proposition_2_8_6 {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (A : U →L[𝕜] V) (B : W →L[𝕜] U) {K : V →L[𝕜] W} (hK : IsCompactOperator K) :
    IsCompactOperator (K.comp A) ∧ IsCompactOperator (B.comp K) :=
  ⟨hK.comp_clm A, hK.clm_comp B⟩

/-- **Proposition 2.8.7.** With a complete codomain, an operator-norm limit of compact
operators is compact. This is what makes an integral operator whose kernel is a uniform limit of
degenerate kernels compact (the book's Example 2.8.8). -/
theorem proposition_2_8_7 [CompleteSpace W] {A : ℕ → V →L[𝕜] W} {K : V →L[𝕜] W}
    (hA : ∀ n, IsCompactOperator (A n)) (h : Tendsto (fun n => ‖A n - K‖) atTop (𝓝 0)) :
    IsCompactOperator K :=
  IsCompactOperator.of_tendsto hA h

end Banach

/-! ### Examples 2.8.5 and 2.8.8: integral operators -/

section IntegralOperators

open MeasureTheory IntegralOperator

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] {n : ℕ}

/-- **Example 2.8.5.** A *degenerate* kernel `k (x, y) = ∑ i, β i x * γ i y` gives a finite-rank
operator on `C(X)`, its range lying in the span of `β 1, …, β n`. The book takes the `γ i` merely
absolutely integrable; `IntegralOperator.degenerateKernel` takes them continuous, which is what its
consumers in the book supply. -/
theorem example_2_8_5 (β γ : Fin n → C(X, ℝ)) :
    LinearMap.range (kernelCLM μ (degenerateKernel β γ) : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) ≤
      Submodule.span ℝ (Set.range β) :=
  range_kernelCLM_degenerateKernel_le μ β γ

/-- **Example 2.8.5**, the compactness it is used for: a degenerate kernel operator has
finite-dimensional range, so Proposition 2.8.4 makes it compact. -/
theorem example_2_8_5_isCompactOperator (β γ : Fin n → C(X, ℝ)) :
    IsCompactOperator (kernelCLM μ (degenerateKernel β γ)) :=
  have := finiteDimensional_range_kernelCLM_degenerateKernel μ β γ
  proposition_2_8_4 (𝕜 := ℝ) _

/-- **Example 2.8.5**, the bound `‖K‖ ≤ ∑ i, ‖β i‖_∞ ∫ |γ i|` on the norm of a degenerate kernel
operator. -/
theorem example_2_8_5_norm (β γ : Fin n → C(X, ℝ)) :
    ‖kernelCLM μ (degenerateKernel β γ)‖ ≤ ∑ i, ‖β i‖ * ∫ y, |γ i y| ∂μ :=
  norm_kernelCLM_degenerateKernel_le μ β γ

/-- **Example 2.8.8.** For a closed bounded `D ⊆ ℝ^d` and a continuous kernel `k` on `D × D`, the
integral operator `K v (x) = ∫_D k (x, y) v (y) dy` is compact on `C(D)`.

The book's "closed and bounded" is `IsCompact D` by Heine–Borel (Theorem 1.6.2), written here as
the instance `CompactSpace ↥D`, and `IntegralOperator.regionMeasure D` is Lebesgue measure on `D`.
The proof is Arzelà–Ascoli (Theorem 1.6.3) applied to the image of the unit ball, carried out in
the backbone at the generality of a compact space with a finite Borel measure; the book instead
approximates `k` uniformly by degenerate kernels and appeals to Examples 2.8.5, Propositions 2.8.4
and 2.8.7. -/
theorem example_2_8_8 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace D]
    (k : C(D × D, ℝ)) : IsCompactOperator (kernelCLM (regionMeasure D) k) :=
  isCompactOperator_kernelCLM _ k

/-- **Example 2.8.8 on an interval**: the Fredholm operator
`u ↦ (x ↦ ∫ y in a..b, k (x, y) u y)` of a continuous kernel is compact on `C[a, b]`. This is the
instance that discharges the `IsCompactOperator` hypothesis of the projection and Nyström methods
of Chapter 12 on a concrete operator. -/
theorem example_2_8_8_interval {a b : ℝ} (hab : a ≤ b)
    (k : C(Set.Icc a b × Set.Icc a b, ℝ)) : IsCompactOperator (fredholm hab k) :=
  isCompactOperator_fredholm hab k

end IntegralOperators

/-! ### §2.8.1: integral operators with a weakly singular kernel -/

section WeaklySingular

open MeasureTheory IntegralOperator

variable {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace D] {k : D × D → ℝ}
  (hk : IsAdmissibleKernel (regionMeasure D) k)

include hk

/-- **(2.8.2).** For a kernel integrable in its second variable and satisfying the conditions
(A₁)–(A₂) of §2.8.1, `K v (x) = ∫_D k (x, y) v (y) dy` is an operator on `C(D)`. The book's
`ω(h) → 0` is `IntegralOperator.IsAdmissibleKernel.tendsto_kernelModulus`, and (A₂), the bound
(2.8.4), is `IntegralOperator.IsAdmissibleKernel.bddAbove_integral_abs`. -/
theorem equation_2_8_2 (u : C(D, ℝ)) (x : D) :
    admissibleKernelCLM hk u x = ∫ y, k (x, y) * u y ∂(regionMeasure D) :=
  rfl

/-- **(2.8.5).** `|K v (x) − K v (z)| ≤ ω(‖x − z‖) ‖v‖_∞`, with `ω` the modulus of continuity in
the mean (2.8.3) of the kernel. This is what makes the image of the unit ball equicontinuous. -/
theorem equation_2_8_5 (u : C(D, ℝ)) (x z : D) :
    |admissibleKernelCLM hk u x - admissibleKernelCLM hk u z|
      ≤ kernelModulus (regionMeasure D) k (dist x z) * ‖u‖ :=
  hk.abs_admissibleKernelCLM_sub_le u x z

/-- **(2.8.6)**, the inequality half: `‖K‖ ≤ sup_x ∫_D |k (x, y)| dy`. `equation_2_8_6` is the
equality the book states. -/
theorem equation_2_8_6_le :
    ‖admissibleKernelCLM hk‖ ≤ ⨆ x, ∫ y, |k (x, y)| ∂(regionMeasure D) :=
  norm_admissibleKernelCLM_le hk

/-- **(2.8.6)**: `‖K‖ = sup_x ∫_D |k (x, y)| dy`. The reverse inequality tests `K` against a
continuous approximation to the sign of one row of the kernel, which exists because `C(D)` is dense
in `L¹(D)`. The book writes a maximum; for a merely integrable kernel there is no reason for the
supremum to be attained, so it is a `⨆`. -/
theorem equation_2_8_6 :
    ‖admissibleKernelCLM hk‖ = ⨆ x, ∫ y, |k (x, y)| ∂(regionMeasure D) :=
  norm_admissibleKernelCLM hk

/-- The conclusion of §2.8.1: **an integral operator whose kernel satisfies (A₁)–(A₂) is compact
on `C(D)`**, by Arzelà–Ascoli (Theorem 1.6.3) applied to the image of the unit ball, which is
uniformly bounded by (2.8.6) and equicontinuous by (2.8.5). `example_2_8_2` and `example_2_8_9`
below are the two instances the book gives. -/
theorem isCompactOperator_of_isAdmissibleKernel :
    IsCompactOperator (admissibleKernelCLM hk) :=
  isCompactOperator_admissibleKernelCLM hk

end WeaklySingular

/-! ### Examples 2.8.2 and 2.8.9: the two weakly singular kernels of an interval -/

section SingularExamples

open MeasureTheory IntegralOperator

open scoped Real

/-- **Example 2.8.9.** The kernel `k (x, y) = |x − y| ^ (-γ)` of (2.8.14), with `0 < γ < 1`, gives a
compact integral operator on `C[a, b]`.

The book truncates `k` at height `n ^ γ` as in (2.8.15), computes
`‖K − Kₙ‖ = 2γ / ((1 − γ) n^{1-γ})`
and appeals to Proposition 2.8.7. The backbone runs the same truncation inside the (A₁)–(A₂)
framework of §2.8.1, so that the operator produced is the one of (2.8.2); the exact value of
`‖K − Kₙ‖` is not needed, only that it tends to `0`. -/
theorem example_2_8_9 {a b γ : ℝ} (hab : a ≤ b) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    IsCompactOperator
      (admissibleKernelCLM (isAdmissibleKernel_abs_sub_rpow hab hγ0 hγ1)) :=
  isCompactOperator_admissibleKernelCLM _

/-- **Example 2.8.2.** The kernel `k (x, y) = log |cos x − cos y|` gives a compact integral operator
on `C[0, π]`.

The book writes `k = |x − y| ^ (-1/2) · (|x − y| ^ (1/2) log |cos x − cos y|)` as in (2.8.10), the
second factor being continuous, and appeals to the splitting rule (2.8.9); the backbone reads that
factorisation as the bound `|log |cos x − cos y|| ≤ C |x − y| ^ (-1/2)` instead, which is what
`IntegralOperator.isAdmissibleKernel_log_cos_sub_cos` proves. -/
theorem example_2_8_2 :
    IsCompactOperator (admissibleKernelCLM isAdmissibleKernel_log_cos_sub_cos) :=
  isCompactOperator_admissibleKernelCLM _

end SingularExamples

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Theorem 2.8.10: the Fredholm alternative -/

section Fredholm

variable [CompleteSpace V] {K : V →L[𝕜] V} {l : 𝕜}

/-- Injectivity of `l - K` makes it a unit, by the Fredholm alternative of Mathlib. -/
private theorem isUnit_smul_one_sub (hK : IsCompactOperator K) (hl : l ≠ 0)
    (hinj : ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0) :
    IsUnit (l • (1 : V →L[𝕜] V) - K) := by
  have hne : ¬ HasEigenvalue (K : Module.End 𝕜 V) l := by
    intro hev
    refine hev (Submodule.eq_bot_iff _ |>.2 fun u hu => hinj u ?_)
    rw [mem_eigenspace_iff] at hu
    have hu' : K u = l • u := hu
    simp [hu']
  have hres := (hK.hasEigenvalue_or_mem_resolventSet hl).resolve_left hne
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
  exact hres

/-- **Theorem 2.8.10**, the **Fredholm alternative** for an equation of the second kind:
for compact `K` on a Banach space and `l ≠ 0`, the equation `(l - K) u = f` has a unique solution
for every right-hand side exactly when the homogeneous equation `(l - K) u = 0` has only the
trivial solution. -/
theorem theorem_2_8_10 (hK : IsCompactOperator K) (hl : l ≠ 0) :
    (∀ f : V, ∃! u : V, (l • (1 : V →L[𝕜] V) - K) u = f) ↔
      ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0 := by
  constructor
  · intro h u hu
    obtain ⟨z, -, huniq⟩ := h 0
    rw [huniq u hu, ← huniq 0 (by simp)]
  · intro hinj
    have hbij := ContinuousLinearMap.isUnit_iff_bijective.1 (isUnit_smul_one_sub hK hl hinj)
    exact fun f => (hbij.existsUnique f)

/-- The second half of Theorem 2.8.10: when the homogeneous equation has only the trivial
solution, the solution operator `(l - K)⁻¹` is bounded. The book obtains this from its own
Theorem 2.4.3, the open mapping theorem, and so does this proof. -/
theorem theorem_2_8_10_inverse (hK : IsCompactOperator K) (hl : l ≠ 0)
    (hinj : ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0) :
    ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = l • (1 : V →L[𝕜] V) - K :=
  theorem_2_4_3 _ (ContinuousLinearMap.isUnit_iff_bijective.1 (isUnit_smul_one_sub hK hl hinj))

end Fredholm

/-! ### Theorem 2.8.12: the spectrum of a compact operator -/

/-- **Theorem 2.8.12 (1).** The eigenvalues of a compact operator can accumulate only at
`0` — for every `ε > 0` there are only finitely many eigenvalues of modulus at least `ε`. -/
theorem theorem_2_8_12_1 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | HasEigenvalue (K : Module.End 𝕜 V) μ ∧ ε ≤ ‖μ‖}.Finite :=
  hK.finite_setOf_hasEigenvalue_norm_le hε

/-- **Theorem 2.8.12 (2).** Every nonzero eigenvalue of a compact operator on a Banach
space has a finite-dimensional eigenspace. -/
theorem theorem_2_8_12_2 [CompleteSpace V] {K : V →L[𝕜] V} (hK : IsCompactOperator K) (μ : 𝕜)
    (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (eigenspace K.toLinearMap μ) := by
  have hinv : ∀ v ∈ eigenspace K.toLinearMap μ, K.toLinearMap v ∈ eigenspace K.toLinearMap μ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (Module.End.eigenspace_mem_invtSubmodule K.toLinearMap μ)
  have hclosed : IsClosed ((eigenspace K.toLinearMap μ : Submodule 𝕜 V) : Set V) := by
    have hset : ((eigenspace K.toLinearMap μ : Submodule 𝕜 V) : Set V)
        = {v : V | K v - μ • v = 0} := by
      ext v
      simp [SetLike.mem_coe, sub_eq_zero]
    rw [hset]
    exact isClosed_eq (by fun_prop) continuous_const
  have : CompleteSpace (eigenspace K.toLinearMap μ) :=
    completeSpace_coe_iff_isComplete.2 hclosed.isComplete
  replace hK := hK.restrict' hinv
  rw [Module.End.restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hK
  rwa [← isCompactOperator_id_iff_finiteDimensional]

/-- **Theorem 2.8.12 (4).** For a compact `K` and `l ≠ 0` the range of `l - K` is
closed. -/
theorem theorem_2_8_12_4 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    IsClosed ((LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V)) : Set V) :=
  hK.isClosed_range_smul_sub hl

/-- Injectivity of `l - K` says exactly that `l` is not an eigenvalue. -/
private theorem ker_smul_one_sub_ne_bot {K : V →L[𝕜] V} {l : 𝕜}
    (hev : HasEigenvalue (K : Module.End 𝕜 V) l) :
    ((l • (1 : V →L[𝕜] V) - K) ^ 1).ker ≠ ⊥ := by
  rw [pow_one]
  intro h
  refine hev (Submodule.eq_bot_iff _ |>.2 fun u hu => ?_)
  rw [mem_eigenspace_iff] at hu
  have hu' : K u = l • u := hu
  exact (Submodule.eq_bot_iff _).1 h u (by simp [hu'])

/-- **Theorem 2.8.12 (3).** Every nonzero eigenvalue `l` of a compact operator has a finite index
`ν(l) ≥ 1`: the null spaces `N((l - K)^j)` increase strictly up to `j = ν(l)` and are constant
from there on (2.8.27), and `N((l - K)^{ν(l)})` is finite dimensional. -/
theorem theorem_2_8_12_3 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0)
    (hev : HasEigenvalue (K : Module.End 𝕜 V) l) :
    ∃ ν : ℕ, 1 ≤ ν ∧
      (∀ j < ν, ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        < ((l • (1 : V →L[𝕜] V) - K) ^ (j + 1)).ker) ∧
      (∀ j, ν ≤ j → ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        = ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) ∧
      FiniteDimensional 𝕜 (((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) := by
  obtain ⟨ν, hstrict, hstab, -, -⟩ := hK.exists_riesz_index hl
  refine ⟨ν, ?_, hstrict, hstab, hK.finiteDimensional_ker_pow hl ν⟩
  by_contra hν
  refine ker_smul_one_sub_ne_bot hev ?_
  rw [hstab 1 (by omega), ← hstab 0 (by omega), pow_zero]
  exact Submodule.eq_bot_iff _ |>.2 fun u hu => by simpa using hu

/-- **Theorem 2.8.12 (5).** At the index `ν(l)` of Theorem 2.8.12 (3) the space splits as
`V = N((l - K)^{ν(l)}) ⊕ R((l - K)^{ν(l)})` (2.8.28), and both summands are invariant under `K`.
The `ν` produced here is the same one: it is characterised by the two chain clauses, which are
those of `theorem_2_8_12_3`. -/
theorem theorem_2_8_12_5 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    ∃ ν : ℕ,
      (∀ j < ν, ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        < ((l • (1 : V →L[𝕜] V) - K) ^ (j + 1)).ker) ∧
      (∀ j, ν ≤ j → ((l • (1 : V →L[𝕜] V) - K) ^ j).ker
        = ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) ∧
      IsCompl (((l • (1 : V →L[𝕜] V) - K) ^ ν).ker)
        (((l • (1 : V →L[𝕜] V) - K) ^ ν).range) ∧
      (∀ u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker,
        K u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).ker) ∧
      (∀ u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).range,
        K u ∈ ((l • (1 : V →L[𝕜] V) - K) ^ ν).range) := by
  obtain ⟨ν, hstrict, hstab, -, hcompl⟩ := hK.exists_riesz_index hl
  exact ⟨ν, hstrict, hstab, hcompl, fun u hu => IsCompactOperator.mapsTo_ker_pow K l ν hu,
    fun u hu => IsCompactOperator.mapsTo_range_pow K l ν hu⟩

/-- **Theorem 2.8.12 (6).** The Fredholm alternative survives when only a power `K^m` of the
operator is compact: `(l - K) u = f` is uniquely solvable for every `f` exactly when the
homogeneous equation has only the trivial solution. -/
theorem theorem_2_8_12_6 [CompleteSpace V] {K : V →L[𝕜] V} {m : ℕ}
    (hK : IsCompactOperator (K ^ m)) {l : 𝕜}
    (hl : l ≠ 0) :
    (∀ f : V, ∃! u : V, (l • (1 : V →L[𝕜] V) - K) u = f) ↔
      ∀ u : V, (l • (1 : V →L[𝕜] V) - K) u = 0 → u = 0 := by
  constructor
  · intro h u hu
    obtain ⟨z, -, huniq⟩ := h 0
    rw [huniq u hu, ← huniq 0 (by simp)]
  · intro hinj
    have hbij := ContinuousLinearMap.isUnit_iff_bijective.1
      (hK.isUnit_smul_one_sub_of_isCompactOperator_pow hl hinj)
    exact fun f => hbij.existsUnique f

end Banach

/-! ### Lemma 2.8.13, Theorem 2.8.14 and Theorem 2.8.15: the Hilbert space case -/

section Hilbert

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W]

/-- **Lemma 2.8.13**, **Schauder's theorem**: the adjoint of a compact operator between
Hilbert spaces is compact. -/
theorem lemma_2_8_13 {K : V →L[𝕜] W} (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) :=
  hK.adjoint

/-- **Theorem 2.8.14 (2)**, the solvability criterion (2.8.29)–(2.8.30): for a compact
`K` on a Hilbert space and `l ≠ 0`, the equation `(l - K) u = f` is solvable exactly when `f` is
orthogonal to every solution of the homogeneous adjoint equation `(conj l - K*) v = 0`. -/
theorem theorem_2_8_14 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V) =
      (LinearMap.ker (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) -
        ContinuousLinearMap.adjoint K : V →L[𝕜] V) : V →ₗ[𝕜] V))ᗮ :=
  hK.range_smul_sub_eq_orthogonal_ker_adjoint hl

/-- The decomposition (2.8.30) that goes with it: the Hilbert space is the orthogonal direct sum
of the null space of the adjoint equation and the range of `l - K`. -/
theorem theorem_2_8_14_isCompl {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    IsCompl (LinearMap.ker (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) -
        ContinuousLinearMap.adjoint K : V →L[𝕜] V) : V →ₗ[𝕜] V))
      (LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V)) := by
  rw [theorem_2_8_14 hK hl]
  have hclosed := hK.isClosed_range_smul_sub hl
  have : CompleteSpace (LinearMap.ker (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) -
      ContinuousLinearMap.adjoint K : V →L[𝕜] V) : V →ₗ[𝕜] V)) := by
    refine completeSpace_coe_iff_isComplete.2 (IsClosed.isComplete ?_)
    exact (ContinuousLinearMap.isClosed_ker _)
  exact Submodule.isCompl_orthogonal _

/-- **Theorem 2.8.14 (1)**, the half that needs no ascent–descent theory: if `λ ≠ 0` is an
eigenvalue of a compact `K` on a Hilbert space then `conj λ` is an eigenvalue of `K*`.

Were it not, the Fredholm alternative applied to the compact `K*` would make `conj λ - K*`
bijective, while `theorem_2_8_14` read for `K*` says its range is `(ker (λ - K))ᗮ`, a proper
subspace because `λ` *is* an eigenvalue of `K`. The other half of the clause, the equality of
dimensions, is `theorem_2_8_14_dim`. -/
theorem theorem_2_8_14_hasEigenvalue_adjoint {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜}
    (hl : l ≠ 0) (hev : HasEigenvalue (K : Module.End 𝕜 V) l) :
    HasEigenvalue ((ContinuousLinearMap.adjoint K : V →L[𝕜] V) : Module.End 𝕜 V)
      ((starRingEnd 𝕜) l) := by
  have hl' : (starRingEnd 𝕜) l ≠ 0 := by simpa using hl
  by_contra hno
  have hres := (hK.adjoint.hasEigenvalue_or_mem_resolventSet hl').resolve_left hno
  rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
  have hsurj : Function.Surjective
      ((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) - ContinuousLinearMap.adjoint K) :=
    (ContinuousLinearMap.isUnit_iff_bijective.1 hres).2
  have hrange : LinearMap.range
      (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) - ContinuousLinearMap.adjoint K : V →L[𝕜] V) :
        V →ₗ[𝕜] V) = ⊤ := LinearMap.range_eq_top.2 hsurj
  have h14 : LinearMap.range
      (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V) - ContinuousLinearMap.adjoint K : V →L[𝕜] V) :
        V →ₗ[𝕜] V) = (LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V))ᗮ := by
    simpa using theorem_2_8_14 hK.adjoint hl'
  rw [h14] at hrange
  have hbot : LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hmem : x ∈ (LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V))ᗮ := by
      rw [hrange]; trivial
    exact inner_self_eq_zero.1 (hmem x hx)
  refine hev (Submodule.eq_bot_iff _ |>.2 fun u hu => ?_)
  rw [mem_eigenspace_iff] at hu
  have hu' : K u = l • u := hu
  have hker : u ∈ LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V) := by
    simp [hu']
  rw [hbot, Submodule.mem_bot] at hker
  exact hker

/-- **Theorem 2.8.14 (1)**, the dimension clause: for compact `K` on a Hilbert space and `λ ≠ 0`,
`dim N(λ - K) = dim N(conj λ - K*)`. Equivalently `λ - K` has Fredholm index zero, so the
second-kind equation `(λ - K) u = f` has exactly as many independent homogeneous solutions as the
adjoint equation has, which is what makes the solvability criterion (2.8.29) of `theorem_2_8_14` a
set of conditions of that same size. -/
theorem theorem_2_8_14_dim {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    Module.finrank 𝕜 ((l • (1 : V →L[𝕜] V) - K).ker)
      = Module.finrank 𝕜 (((starRingEnd 𝕜) l • (1 : V →L[𝕜] V)
          - ContinuousLinearMap.adjoint K).ker) :=
  hK.finrank_ker_eq_finrank_ker_adjoint hl

/-- **Theorem 2.8.15**, the **spectral theorem** for a compact self-adjoint operator on a
Hilbert space: the eigenvectors span a dense subspace, so an orthonormal basis of eigenvectors
exists. -/
theorem theorem_2_8_15 {K : V →L[𝕜] V} (hKc : IsCompactOperator K) (hK : IsSelfAdjoint K) :
    (⨆ μ, eigenspace (K : Module.End 𝕜 V) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hKc
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK)

/-- The first clause of Theorem 2.8.15: the eigenvalues of a self-adjoint operator are real. -/
theorem theorem_2_8_15_eigenvalue_real {K : V →L[𝕜] V} (hK : IsSelfAdjoint K) {μ : 𝕜}
    (hμ : HasEigenvalue (K : Module.End 𝕜 V) μ) : (starRingEnd 𝕜) μ = μ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK).conj_eigenvalue_eq_self hμ

/-- **Theorem 2.8.15**, the index clause: every eigenvalue of a compact self-adjoint operator has
index one, `N((λ - K)²) = N(λ - K)`. The general ascent–descent theory of Theorem 2.8.12 (3) is not
needed for it: with `λ` real — which `theorem_2_8_15_eigenvalue_real` supplies — the operator
`λ - K` is self-adjoint, so `(λ - K)² v = 0` gives `‖(λ - K) v‖² = ⟪(λ - K)² v, v⟫ = 0`.

Compactness plays no part, so no compactness hypothesis is imposed. -/
theorem theorem_2_8_15_index {K : V →L[𝕜] V} (hK : IsSelfAdjoint K) {l : 𝕜}
    (hl : (starRingEnd 𝕜) l = l) :
    LinearMap.ker (((l • (1 : V →L[𝕜] V) - K) ^ 2 : V →L[𝕜] V) : V →ₗ[𝕜] V) =
      LinearMap.ker ((l • (1 : V →L[𝕜] V) - K : V →L[𝕜] V) : V →ₗ[𝕜] V) := by
  have hlsa : IsSelfAdjoint l := hl
  have hAsa : IsSelfAdjoint (l • (1 : V →L[𝕜] V) - K) :=
    (hlsa.smul (IsSelfAdjoint.one (V →L[𝕜] V))).sub hK
  have hadj : ContinuousLinearMap.adjoint (l • (1 : V →L[𝕜] V) - K) = l • 1 - K := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hAsa
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
    have hsq : ((l • (1 : V →L[𝕜] V) - K) ^ 2) v
        = (l • (1 : V →L[𝕜] V) - K) ((l • (1 : V →L[𝕜] V) - K) v) := by
      rw [pow_two]; rfl
    rw [hsq] at hv
    have hinner : ⟪(l • (1 : V →L[𝕜] V) - K) v, (l • (1 : V →L[𝕜] V) - K) v⟫_𝕜 = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hadj, hv, inner_zero_left]
    exact inner_self_eq_zero.1 hinner
  · simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
    rw [pow_two]
    change (l • (1 : V →L[𝕜] V) - K) ((l • (1 : V →L[𝕜] V) - K) v) = 0
    rw [hv, map_zero]

/-- The clause of Theorem 2.8.15 that locates the basis: for a self-adjoint operator the
orthogonal complement of the null space is the closure of the range, which is where the
eigenvectors for the nonzero eigenvalues live. -/
theorem theorem_2_8_15_closure_range {K : V →L[𝕜] V} (hK : IsSelfAdjoint K) :
    (LinearMap.ker (K : V →ₗ[𝕜] V))ᗮ =
      (LinearMap.range (K : V →ₗ[𝕜] V)).topologicalClosure := by
  have hadj : ContinuousLinearMap.adjoint K = K := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hK
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  congr 1
  rw [ContinuousLinearMap.orthogonal_range K, hadj]

/-- **Theorem 2.8.15**, the enumeration (2.8.31)–(2.8.32): the nonzero eigenvalues of a compact
self-adjoint operator can be listed with multiplicity in decreasing order of modulus,
`|λ₁| ≥ |λ₂| ≥ ⋯ > 0` with `λⱼ → 0`, together with an orthonormal family of eigenvectors
`K uⱼ = λⱼ uⱼ` whose closed span is `closure (range K)`.

Stated for an *injective* `K` on an *infinite-dimensional* space, which is where an enumeration by
`ℕ` exists; the backbone's `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` explains why
both are needed. If `K` has both infinitely many nonzero eigenvalues and a nontrivial kernel then a
decreasing enumeration would have to place `0` after infinitely many nonzero values and no listing
by `ℕ` exists; if `K` has finite rank the book's list is finite, which is Mathlib's
`LinearMap.IsSymmetric.eigenvalues` indexed by `Fin n`. The general statement, a list that is
finite or infinite according to the rank, is not stated here. Under the hypotheses taken,
`closure (range K) = V` by `theorem_2_8_15_closure_range`. -/
theorem theorem_2_8_15_enumeration {K : V →L[𝕜] V} (hKc : IsCompactOperator K)
    (hK : IsSelfAdjoint K) (hinj : LinearMap.ker (K : V →ₗ[𝕜] V) = ⊥)
    (hfin : ¬ FiniteDimensional 𝕜 V) :
    ∃ (l : ℕ → ℝ) (u : ℕ → V),
      Antitone (fun j => |l j|) ∧ (∀ j, l j ≠ 0) ∧ Tendsto l atTop (𝓝 0) ∧
        Orthonormal 𝕜 u ∧ (∀ j, K (u j) = ((l j : ℝ) : 𝕜) • u j) ∧
        (Submodule.span 𝕜 (Set.range u)).topologicalClosure =
          (LinearMap.range (K : V →ₗ[𝕜] V)).topologicalClosure := by
  have hsym : (K : V →ₗ[𝕜] V).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hK
  have horth := ContinuousLinearMap.IsSymmetric.orthonormal_eigenvector hsym hKc hfin
  have happ := ContinuousLinearMap.IsSymmetric.apply_eigenvector hsym hKc hfin
  refine ⟨ContinuousLinearMap.IsSymmetric.eigenvalueSeq hsym hKc,
    ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc,
    ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone hsym hKc, fun j h0 => ?_,
    ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero hsym hKc, horth, happ, ?_⟩
  · have hz : K (ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc j) = 0 := by
      rw [happ j, h0]; simp
    have hmem : ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc j ∈
        LinearMap.ker (K : V →ₗ[𝕜] V) := hz
    rw [hinj, Submodule.mem_bot] at hmem
    have hone := horth.1 j
    rw [hmem, norm_zero] at hone
    exact one_ne_zero hone.symm
  · have hbot : (Submodule.span 𝕜
        (Set.range (ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc)))ᗮ = ⊥ :=
      le_bot_iff.1 (hinj ▸
        ContinuousLinearMap.IsSymmetric.orthogonal_span_range_eigenvector_le_ker hsym hKc hfin)
    have hL : (Submodule.span 𝕜
        (Set.range (ContinuousLinearMap.IsSymmetric.eigenvector hsym hKc))).topologicalClosure
          = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
    have hR : (LinearMap.range (K : V →ₗ[𝕜] V)).topologicalClosure = ⊤ := by
      rw [← theorem_2_8_15_closure_range hK, hinj, Submodule.bot_orthogonal_eq_top]
    rw [hL, hR]

end Hilbert

end AtkinsonHan.Chapter02
