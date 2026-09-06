import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.Normed.Operator.Compact
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
* `theorem_2_8_10` — the Fredholm alternative, with `theorem_2_8_10_inverse` for the bounded
  inverse the book gets from its own Theorem 2.4.3.
* `theorem_2_8_12_1`, `theorem_2_8_12_2`, `theorem_2_8_12_4` — the eigenvalues accumulate only at
  `0`, the nonzero eigenspaces are finite-dimensional, and `range (λ - K)` is closed.
* `lemma_2_8_13` — Schauder's theorem.
* `theorem_2_8_14` — solvability of `(λ - K) u = f` and the decomposition it gives.
* `theorem_2_8_15` — the spectral theorem for compact self-adjoint operators.

## Conventions

The book writes `λ` for the scalar of the second-kind equation; `λ` is a keyword in Lean, so it is
written `l` below. The book states §2.8 over a general scalar field and specializes to real or
complex scalars; the statements here are over `RCLike 𝕜`, as elsewhere in this surface.

Not stated here: §2.8.1's conditions for an integral operator with a weakly singular kernel to be
compact, and the Examples that instantiate it; the parts of Theorem 2.8.12 and Theorem 2.8.14 that
need the Riesz ascent–descent theory, which the backbone module does not develop.

## References

* K. E. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*,
  3rd edition, Texts in Applied Mathematics 39, Springer, 2009.
-/

open Filter Topology Metric Module.End

namespace AtkinsonHan.Chapter02

section Banach

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Definition 2.8.1 and its sequential form -/

/-- Atkinson–Han Definition 2.8.1, with the sequential reading that follows it: a bounded operator
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

/-- Atkinson–Han Proposition 2.8.4: a bounded linear operator of finite rank — Definition 2.8.3 —
is compact. -/
theorem proposition_2_8_4 (K : V →L[𝕜] W)
    [FiniteDimensional 𝕜 (LinearMap.range (K : V →ₗ[𝕜] W))] : IsCompactOperator K :=
  IsCompactOperator.of_finiteDimensional_range K

/-- Atkinson–Han Proposition 2.8.6: a composition of bounded operators in which at least one
factor is compact is compact. -/
theorem proposition_2_8_6 {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (A : U →L[𝕜] V) (B : W →L[𝕜] U) {K : V →L[𝕜] W} (hK : IsCompactOperator K) :
    IsCompactOperator (K.comp A) ∧ IsCompactOperator (B.comp K) :=
  ⟨hK.comp_clm A, hK.clm_comp B⟩

/-- Atkinson–Han Proposition 2.8.7: with a complete codomain, an operator-norm limit of compact
operators is compact. This is what makes an integral operator whose kernel is a uniform limit of
degenerate kernels compact (the book's Example 2.8.8). -/
theorem proposition_2_8_7 [CompleteSpace W] {A : ℕ → V →L[𝕜] W} {K : V →L[𝕜] W}
    (hA : ∀ n, IsCompactOperator (A n)) (h : Tendsto (fun n => ‖A n - K‖) atTop (𝓝 0)) :
    IsCompactOperator K :=
  IsCompactOperator.of_tendsto hA h

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

/-- Atkinson–Han Theorem 2.8.10, the **Fredholm alternative** for an equation of the second kind:
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

/-- Atkinson–Han Theorem 2.8.12 (1): the eigenvalues of a compact operator can accumulate only at
`0` — for every `ε > 0` there are only finitely many eigenvalues of modulus at least `ε`. -/
theorem theorem_2_8_12_1 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | HasEigenvalue (K : Module.End 𝕜 V) μ ∧ ε ≤ ‖μ‖}.Finite :=
  hK.finite_setOf_hasEigenvalue_norm_le hε

/-- Atkinson–Han Theorem 2.8.12 (2): every nonzero eigenvalue of a compact operator on a Banach
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

/-- Atkinson–Han Theorem 2.8.12 (4): for a compact `K` and `l ≠ 0` the range of `l - K` is
closed. -/
theorem theorem_2_8_12_4 {K : V →L[𝕜] V} (hK : IsCompactOperator K) {l : 𝕜} (hl : l ≠ 0) :
    IsClosed ((LinearMap.range ((l • (1 : V →L[𝕜] V) - K) : V →ₗ[𝕜] V)) : Set V) :=
  hK.isClosed_range_smul_sub hl

end Banach

/-! ### Lemma 2.8.13, Theorem 2.8.14 and Theorem 2.8.15: the Hilbert space case -/

section Hilbert

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W]

/-- Atkinson–Han Lemma 2.8.13, **Schauder's theorem**: the adjoint of a compact operator between
Hilbert spaces is compact. -/
theorem lemma_2_8_13 {K : V →L[𝕜] W} (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) :=
  hK.adjoint

/-- Atkinson–Han Theorem 2.8.14 (2), the solvability criterion (2.8.29)–(2.8.30): for a compact
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

/-- Atkinson–Han Theorem 2.8.15, the **spectral theorem** for a compact self-adjoint operator on a
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

end Hilbert

end AtkinsonHan.Chapter02
