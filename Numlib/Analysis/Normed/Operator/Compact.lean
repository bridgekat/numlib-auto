/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Compact`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compact operators: closure properties, Schauder's theorem, and Riesz theory

What Mathlib's `Mathlib.Analysis.Normed.Operator.Compact` does not have, and the classical Riesz
theory of `μ - K` needs.

* `IsCompactOperator.of_finiteDimensional_range` — a bounded operator of finite rank is compact.
* `IsCompactOperator.of_tendsto` — an operator-norm limit of compact operators is compact, in the
  sequential form; Mathlib's `isCompactOperator_of_tendsto` is the general filter form.
* `IsCompactOperator.adjoint` — **Schauder's theorem**: the adjoint of a compact operator between
  Hilbert spaces is compact. The proof needs no finite-rank approximation: `K` composed with `K†`
  is compact, and `‖K† z‖² ≤ ‖K (K† z)‖ ‖z‖` turns a finite net for `K ∘ K†` on the unit ball into
  a finite net for `K†`.
* `IsCompactOperator.finite_setOf_hasEigenvalue_norm_le` — for `ε > 0` only finitely many
  eigenvalues have modulus at least `ε`, so the eigenvalues of a compact operator can accumulate
  only at `0`. Riesz's lemma applied to the strictly increasing chain of spans of eigenvectors
  for distinct eigenvalues.
* `IsCompactOperator.isClosed_range_smul_sub` — the range of `μ • 1 - K` is closed for `μ ≠ 0`.
* `IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint` — the solvability criterion on a
  Hilbert space: `range (μ • 1 - K) = (ker (conj μ • 1 - K†))ᗮ`, so `(μ • 1 - K) u = f` is solvable
  exactly when `f` is orthogonal to the kernel of the adjoint equation.

Neither the finiteness of the eigenvalues of modulus at least `ε` nor the closed range needs the
domain to be complete: Riesz's lemma and the compactness of `K` carry both arguments on their own.
The Riesz ascent–descent theory — that the chain of null spaces of `(μ - K)ⁿ` stabilises, and that
`ker (μ - K)` and `ker (conj μ - K†)` have equal dimension — is not developed here.

These are Atkinson–Han[^atkinson-han] Propositions 2.8.4 and 2.8.7, Lemma 2.8.13, Theorem 2.8.12
clauses (1) and (4), and Theorem 2.8.14 clause (2).

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Filter Topology Metric Set
open scoped InnerProductSpace

namespace IsCompactOperator

/-! ### Closure properties -/

section FiniteRange

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
  {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A bounded operator with finite-dimensional range is compact.** Corestricting to the range,
which is locally compact because it is finite dimensional over a locally compact complete field,
makes the operator a continuous linear map into a locally compact space. -/
theorem of_finiteDimensional_range (f : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (LinearMap.range (f : E →ₗ[𝕜] F))] : IsCompactOperator f := by
  have : LocallyCompactSpace (LinearMap.range (f : E →ₗ[𝕜] F)) :=
    LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 _
  have h := isCompactOperator_of_locallyCompactSpace_dom
    (f.codRestrict (LinearMap.range (f : E →ₗ[𝕜] F)) fun x => LinearMap.mem_range_self _ x)
  exact h.clm_comp (Submodule.subtypeL _)

end FiniteRange

section Limit

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **An operator-norm limit of compact operators is compact**, when the codomain is complete.
This is the sequential form; Mathlib's `isCompactOperator_of_tendsto` is the general filter form,
and `isClosed_setOfPred_isCompactOperator` the closedness that both rest on. -/
theorem of_tendsto {A : ℕ → E →L[𝕜] F} {f : E →L[𝕜] F} (hA : ∀ n, IsCompactOperator (A n))
    (h : Tendsto (fun n => ‖A n - f‖) atTop (𝓝 0)) : IsCompactOperator f :=
  isCompactOperator_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.2 h) (.of_forall hA)

end Limit

/-! ### Schauder's theorem -/

section Schauder

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Schauder's theorem**: the adjoint of a compact operator between Hilbert spaces is compact.

No approximation property is used. The composite `K ∘ K†` is compact, being a compact operator
preceded by a bounded one, and `‖K† z‖² ≤ ‖K (K† z)‖ ‖z‖` converts a finite net for `K ∘ K†` on the
unit ball into a finite net for `K†`. -/
theorem adjoint {K : E →L[𝕜] F} (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) := by
  have hest : ∀ y y' : F,
      ‖ContinuousLinearMap.adjoint K y - ContinuousLinearMap.adjoint K y'‖ ^ 2
        ≤ ‖K (ContinuousLinearMap.adjoint K y) - K (ContinuousLinearMap.adjoint K y')‖
          * ‖y - y'‖ := by
    intro y y'
    have hsub : ContinuousLinearMap.adjoint K y - ContinuousLinearMap.adjoint K y'
        = ContinuousLinearMap.adjoint K (y - y') := by simp
    have hsub' : K (ContinuousLinearMap.adjoint K y) - K (ContinuousLinearMap.adjoint K y')
        = K (ContinuousLinearMap.adjoint K (y - y')) := by simp
    rw [hsub, hsub']
    have hinner : ‖ContinuousLinearMap.adjoint K (y - y')‖ ^ 2
        = RCLike.re ⟪y - y', K (ContinuousLinearMap.adjoint K (y - y'))⟫_𝕜 := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜)]
      congr 1
      exact ContinuousLinearMap.adjoint_inner_left K _ _
    rw [hinner]
    exact (RCLike.re_le_norm _).trans <| (norm_inner_le_norm _ _).trans_eq (mul_comm _ _)
  have hcomp : IsCompactOperator
      ((K ∘L ContinuousLinearMap.adjoint K : F →L[𝕜] F) : F →ₗ[𝕜] F) :=
    hK.comp_clm (ContinuousLinearMap.adjoint K)
  have htb : TotallyBounded
      (((K ∘L ContinuousLinearMap.adjoint K : F →L[𝕜] F) : F →ₗ[𝕜] F) ''
        closedBall (0 : F) 1) :=
    (hcomp.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    ((ContinuousLinearMap.adjoint K : F →ₗ[𝕜] E)) one_pos).2 ?_
  refine TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure ?_) isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, htf, hts⟩ := Metric.totallyBounded_iff.1 htb (ε ^ 2 / 8) (by positivity)
  have hchoice : ∀ z : F, ∃ e : E, ∀ y ∈ closedBall (0 : F) 1,
      dist (K (ContinuousLinearMap.adjoint K y)) z < ε ^ 2 / 8 →
      dist (ContinuousLinearMap.adjoint K y) e < ε := by
    intro z
    by_cases hex : ∃ y ∈ closedBall (0 : F) 1,
        dist (K (ContinuousLinearMap.adjoint K y)) z < ε ^ 2 / 8
    · obtain ⟨y₀, hy₀, hdy₀⟩ := hex
      refine ⟨ContinuousLinearMap.adjoint K y₀, fun y hy hd => ?_⟩
      have h1 : ‖K (ContinuousLinearMap.adjoint K y) - K (ContinuousLinearMap.adjoint K y₀)‖
          < ε ^ 2 / 4 := by
        have htri := dist_triangle (K (ContinuousLinearMap.adjoint K y)) z
          (K (ContinuousLinearMap.adjoint K y₀))
        rw [dist_comm z] at htri
        rw [dist_eq_norm] at htri
        linarith
      have h2 : ‖y - y₀‖ ≤ 2 := by
        have h := norm_sub_le y y₀
        have hy1 := mem_closedBall_zero_iff.1 hy
        have hy2 := mem_closedBall_zero_iff.1 hy₀
        linarith
      have h3 : ‖ContinuousLinearMap.adjoint K y - ContinuousLinearMap.adjoint K y₀‖ ^ 2
          < ε ^ 2 := by
        refine lt_of_le_of_lt (hest y y₀) ?_
        calc ‖K (ContinuousLinearMap.adjoint K y) - K (ContinuousLinearMap.adjoint K y₀)‖
              * ‖y - y₀‖
            ≤ ‖K (ContinuousLinearMap.adjoint K y) - K (ContinuousLinearMap.adjoint K y₀)‖ * 2 :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ < ε ^ 2 / 4 * 2 := mul_lt_mul_of_pos_right h1 two_pos
          _ ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (ContinuousLinearMap.adjoint K y - ContinuousLinearMap.adjoint K y₀),
        hε.le]
    · exact ⟨0, fun y hy hd => absurd ⟨y, hy, hd⟩ hex⟩
  choose e he using hchoice
  refine ⟨e '' t, htf.image e, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hdz⟩ := mem_iUnion₂.1 (hts ⟨y, hy, rfl⟩)
  exact mem_iUnion₂.2 ⟨e z, ⟨z, hz, rfl⟩, he z y hy hdz⟩

end Schauder

/-! ### The eigenvalues accumulate only at zero -/

section Eigenvalues

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **The eigenvalues of a compact operator accumulate only at `0`**: for every `ε > 0` there are
only finitely many eigenvalues `μ` with `ε ≤ ‖μ‖`.

If there were infinitely many, the spans `Vₙ` of the first `n` eigenvectors would form a strictly
increasing chain of finite-dimensional, hence closed, subspaces; Riesz's lemma produces `wₙ ∈ Vₙ₊₁`
of bounded norm at distance at least `1` from `Vₙ`, and `(T - μₙ) Vₙ₊₁ ⊆ Vₙ` makes the points
`T wₙ` pairwise at distance at least `ε`, which no sequence in a compact set can be. -/
theorem finite_setOf_hasEigenvalue_norm_le {T : X →L[𝕜] X} (hT : IsCompactOperator T) {ε : ℝ}
    (hε : 0 < ε) :
    {μ : 𝕜 | Module.End.HasEigenvalue (T : Module.End 𝕜 X) μ ∧ ε ≤ ‖μ‖}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  -- an injective sequence of such eigenvalues, with eigenvectors
  obtain ⟨G⟩ : Nonempty (ℕ ↪ _) := ⟨Set.Infinite.natEmbedding _ hinf⟩
  set μ : ℕ → 𝕜 := fun n => (G n : 𝕜) with hμdef
  have hμinj : Function.Injective μ := fun a b hab => G.injective (Subtype.ext hab)
  have hμnorm : ∀ n, ε ≤ ‖μ n‖ := fun n => (G n).2.2
  have hμeig : ∀ n, Module.End.HasEigenvalue (T : Module.End 𝕜 X) (μ n) := fun n => (G n).2.1
  have hμ0 : ∀ n, μ n ≠ 0 := by
    intro n hn
    have h := hμnorm n
    rw [hn, norm_zero] at h
    linarith
  choose x hx using fun n => (hμeig n).exists_hasEigenvector
  have hTx : ∀ n, T (x n) = μ n • x n := fun n => Module.End.mem_eigenspace_iff.1 (hx n).1
  have hli : LinearIndependent 𝕜 x :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End 𝕜 X) μ hμinj x hx
  -- the increasing chain of spans of eigenvectors
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ → Submodule 𝕜 X, ∀ n, V n = Submodule.span 𝕜 (x '' Set.Iio n) :=
    ⟨_, fun _ => rfl⟩
  have hVfd : ∀ n, FiniteDimensional 𝕜 (V n) := by
    intro n
    rw [hVdef n]
    exact FiniteDimensional.span_of_finite 𝕜 ((Set.finite_Iio n).image x)
  have hVclosed : ∀ n, IsClosed ((V n : Set X)) := by
    intro n
    have := hVfd n
    exact Submodule.closed_of_finiteDimensional _
  have hVmono : ∀ {m n : ℕ}, m ≤ n → V m ≤ V n := by
    intro m n hmn
    rw [hVdef m, hVdef n]
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))
  have hxmemV : ∀ {i n : ℕ}, i < n → x i ∈ V n := by
    intro i n hin
    rw [hVdef n]
    exact Submodule.subset_span ⟨i, hin, rfl⟩
  have hxnot : ∀ n, x n ∉ V n := by
    intro n
    rw [hVdef n]
    exact hli.notMem_span_image (by simp)
  -- `T` preserves each `V n`, and `T - μ n` maps `V (n + 1)` into `V n`
  have hTV : ∀ n, ∀ z ∈ V n, T z ∈ V n := by
    intro n
    have hle : V n ≤ Submodule.comap (T : X →ₗ[𝕜] X) (V n) := by
      conv_lhs => rw [hVdef n]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, hTx i]
      exact Submodule.smul_mem _ _ (hxmemV hi)
    exact fun z hz => hle hz
  have hAV : ∀ n, ∀ z ∈ V (n + 1), T z - μ n • z ∈ V n := by
    intro n
    have hle : V (n + 1) ≤ Submodule.comap ((T : X →ₗ[𝕜] X) - μ n • LinearMap.id) (V n) := by
      conv_lhs => rw [hVdef (n + 1)]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, ContinuousLinearMap.coe_coe, hTx i]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · rw [← sub_smul]
        exact Submodule.smul_mem _ _ (hxmemV h)
      · subst h
        simp
    intro z hz
    have h := hle hz
    simpa using h
  -- Riesz's lemma inside `V (n + 1)`
  have hRc : ‖c‖ < ‖c‖ + 1 := by linarith
  have hriesz : ∀ n, ∃ w : X, w ∈ V (n + 1) ∧ ‖w‖ ≤ ‖c‖ + 1 ∧ ∀ z ∈ V n, 1 ≤ ‖w - z‖ := by
    intro n
    have h₁ : IsClosed ((↑((V n).comap (V (n + 1)).subtype) : Set ↥(V (n + 1)))) := by
      simpa using! (hVclosed n).preimage_val
    have h₂ : ∃ z : (V (n + 1) : Submodule 𝕜 X), z ∉ (V n).comap (V (n + 1)).subtype := by
      refine ⟨⟨x n, hxmemV (Nat.lt_succ_self n)⟩, ?_⟩
      simpa using hxnot n
    obtain ⟨w, hwnorm, hwsep⟩ := riesz_lemma_of_norm_lt hc hRc h₁ h₂
    refine ⟨(w : X), w.2, hwnorm, fun z hz => ?_⟩
    have h := hwsep ⟨z, hVmono (Nat.le_succ n) hz⟩ (by simpa using hz)
    simpa using h
  choose w hwmem hwnorm hwsep using hriesz
  -- the images `T (w n)` are pairwise `ε`-separated
  have hsep : ∀ m n : ℕ, m < n → ε ≤ ‖T (w n) - T (w m)‖ := by
    intro m n hmn
    obtain ⟨t, htdef⟩ : ∃ t : X, t = μ n • w n - T (w n) + T (w m) := ⟨_, rfl⟩
    have htV : t ∈ V n := by
      rw [htdef]
      refine Submodule.add_mem _ ?_ ?_
      · have h1 := hAV n (w n) (hwmem n)
        have h2 : μ n • w n - T (w n) = -(T (w n) - μ n • w n) := by abel
        rw [h2]
        exact Submodule.neg_mem _ h1
      · exact hVmono (Nat.succ_le_of_lt hmn) (hTV (m + 1) (w m) (hwmem m))
    have heq : T (w n) - T (w m) = μ n • (w n - (μ n)⁻¹ • t) := by
      rw [smul_sub, smul_inv_smul₀ (hμ0 n), htdef]
      abel
    rw [heq, norm_smul]
    have hge := hwsep n ((μ n)⁻¹ • t) (Submodule.smul_mem _ _ htV)
    calc ε ≤ ‖μ n‖ := hμnorm n
      _ = ‖μ n‖ * 1 := (mul_one _).symm
      _ ≤ ‖μ n‖ * ‖w n - (μ n)⁻¹ • t‖ := mul_le_mul_of_nonneg_left hge (norm_nonneg _)
  -- but they lie in a compact set, so some subsequence is Cauchy
  obtain ⟨Kc, hKc, hKcsub⟩ := hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, -, φ, hφ, hφy⟩ := hKc.tendsto_subseq (x := fun n => T (w n))
    fun n => hKcsub ⟨w n, mem_closedBall_zero_iff.2 (hwnorm n), rfl⟩
  have hcauchy := hφy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hlt := hN (N + 1) (Nat.le_succ N)
  rw [Function.comp_apply, Function.comp_apply, dist_eq_norm] at hlt
  exact absurd hlt (not_lt.2 (hsep (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))))

end Eigenvalues

/-! ### The range of `μ - K` is closed -/

section ClosedRange

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Every vector has a representative modulo a submodule whose norm is within `1` of the distance
to that submodule. -/
private theorem exists_almost_minimal (N : Submodule 𝕜 X) (v : X) :
    ∃ z ∈ N, ∀ t ∈ N, ‖v - z‖ ≤ ‖v - z - t‖ + 1 := by
  have hne : (N : Set X).Nonempty := ⟨0, N.zero_mem⟩
  obtain ⟨z, hz, hzlt⟩ := (Metric.infDist_lt_iff hne).1
    (lt_add_of_pos_right (Metric.infDist v (N : Set X)) one_pos)
  refine ⟨z, hz, fun t ht => ?_⟩
  have h1 : Metric.infDist v (N : Set X) ≤ ‖v - z - t‖ := by
    have h2 : v - z - t = v - (z + t) := by abel
    rw [h2, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (N.add_mem hz ht)
  rw [dist_eq_norm] at hzlt
  linarith

/-- An almost minimal representative modulo `ker (μ • 1 - K)` has norm controlled by the norm of
its image: `μ • 1 - K` is bounded below modulo its kernel. -/
private theorem exists_bound {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : X,
      (∀ t ∈ (μ • (1 : X →L[𝕜] X) - K).ker, ‖v‖ ≤ ‖v - t‖ + 1) →
      ‖v‖ ≤ C * (1 + ‖(μ • (1 : X →L[𝕜] X) - K) v‖) := by
  by_contra hcon
  push Not at hcon
  choose v hv1 hv2 using fun n : ℕ => hcon ((n : ℝ) + 1) (by positivity)
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : (0 : ℝ) < ‖c‖ := lt_trans one_pos hc
  have hvbig : ∀ n : ℕ, (n : ℝ) + 1 < ‖v n‖ := by
    intro n
    refine lt_of_le_of_lt ?_ (hv2 n)
    nlinarith [norm_nonneg ((μ • (1 : X →L[𝕜] X) - K) (v n)), (by positivity : (0:ℝ) ≤ (n:ℝ))]
  have hvne : ∀ n, v n ≠ 0 := by
    intro n hn
    have h := hvbig n
    rw [hn, norm_zero] at h
    nlinarith [(by positivity : (0:ℝ) ≤ (n:ℝ))]
  choose d hd0 hdlt hdge hdinv using fun n => rescale_to_shell (F := X) hc one_pos (hvne n)
  have hdnorm : ∀ n : ℕ, ‖d n‖ * ‖v n‖ < 1 := by
    intro n; simpa [norm_smul] using hdlt n
  have hdsmall : ∀ n : ℕ, ‖d n‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 := hdnorm n
    have h2 := hvbig n
    have h3 : ‖d n‖ * ((n : ℝ) + 1) ≤ ‖d n‖ * ‖v n‖ :=
      mul_le_mul_of_nonneg_left h2.le (norm_nonneg _)
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hSsmall : ∀ n : ℕ,
      ‖(μ • (1 : X →L[𝕜] X) - K) (d n • v n)‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hmap : (μ • (1 : X →L[𝕜] X) - K) (d n • v n)
        = d n • (μ • (1 : X →L[𝕜] X) - K) (v n) := ContinuousLinearMap.map_smul _ _ _
    rw [hmap, norm_smul, lt_div_iff₀ (show (0:ℝ) < (n : ℝ) + 1 by positivity)]
    have h1 := hdnorm n
    have h2 := hv2 n
    have h3 : ((n : ℝ) + 1) * ‖(μ • (1 : X →L[𝕜] X) - K) (v n)‖ ≤ ‖v n‖ := by
      nlinarith [(by positivity : (0:ℝ) ≤ (n:ℝ))]
    have h4 : ‖d n‖ * (((n : ℝ) + 1) * ‖(μ • (1 : X →L[𝕜] X) - K) (v n)‖) ≤ ‖d n‖ * ‖v n‖ :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    nlinarith
  have haminimal : ∀ (n : ℕ), ∀ t ∈ (μ • (1 : X →L[𝕜] X) - K).ker,
      ‖d n • v n‖ ≤ ‖d n • v n - t‖ + ‖d n‖ := by
    intro n t ht
    have h := hv1 n ((d n)⁻¹ • t) (Submodule.smul_mem _ _ ht)
    have h2 : ‖d n‖ * ‖v n - (d n)⁻¹ • t‖ = ‖d n • v n - t‖ := by
      rw [← norm_smul, smul_sub, smul_inv_smul₀ (hd0 n)]
    calc ‖d n • v n‖ = ‖d n‖ * ‖v n‖ := norm_smul _ _
      _ ≤ ‖d n‖ * (‖v n - (d n)⁻¹ • t‖ + 1) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = ‖d n • v n - t‖ + ‖d n‖ := by rw [mul_add, mul_one, h2]
  obtain ⟨Kc, hKc, hKcsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨q, -, φ, hφ, hφq⟩ := hKc.tendsto_subseq (x := fun n => K (d n • v n))
    fun n => hKcsub ⟨d n • v n, mem_closedBall_zero_iff.2 (hdlt n).le, rfl⟩
  have hφq' : Tendsto (fun k => K (d (φ k) • v (φ k))) atTop (𝓝 q) := hφq
  have hone : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h0.comp hφ.tendsto_atTop
  have hStendsto : Tendsto (fun k => (μ • (1 : X →L[𝕜] X) - K) (d (φ k) • v (φ k)))
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (hSsmall (φ k)).le) hone
  have hid : ∀ z : X, (μ • (1 : X →L[𝕜] X) - K) z + K z = μ • z := by intro z; simp
  have hutend : Tendsto (fun k => d (φ k) • v (φ k)) atTop (𝓝 (μ⁻¹ • q)) := by
    have hsum : Tendsto (fun k => μ • (d (φ k) • v (φ k))) atTop (𝓝 q) := by
      have h := hStendsto.add hφq'
      rw [zero_add] at h
      exact Filter.Tendsto.congr (fun k => hid _) h
    have h := hsum.const_smul (μ⁻¹)
    simpa [smul_smul, ← mul_assoc, inv_mul_cancel₀ hμ] using h
  have hcont : Tendsto (fun k => (μ • (1 : X →L[𝕜] X) - K) (d (φ k) • v (φ k))) atTop
      (𝓝 ((μ • (1 : X →L[𝕜] X) - K) (μ⁻¹ • q))) :=
    ((μ • (1 : X →L[𝕜] X) - K).continuous.tendsto _).comp hutend
  have hmem : μ⁻¹ • q ∈ (μ • (1 : X →L[𝕜] X) - K).ker :=
    LinearMap.mem_ker.2 (tendsto_nhds_unique hcont hStendsto)
  have hzero : Tendsto (fun k => ‖d (φ k) • v (φ k) - μ⁻¹ • q‖ + ‖d (φ k)‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ‖d (φ k) • v (φ k) - μ⁻¹ • q‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hutend
    have h2 : Tendsto (fun k => ‖d (φ k)‖) atTop (𝓝 0) :=
      squeeze_zero (fun k => norm_nonneg _) (fun k => (hdsmall (φ k)).le) hone
    simpa using h1.add h2
  have hle : 1 / ‖c‖ ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hzero
      (Eventually.of_forall fun k => le_trans (by simpa using hdge (φ k))
        (haminimal (φ k) (μ⁻¹ • q) hmem))
  have hpos : (0 : ℝ) < 1 / ‖c‖ := by positivity
  linarith

/-- **The range of `μ • 1 - K` is closed** for a compact operator `K` and `μ ≠ 0`.

An almost minimal representative of a coset of the kernel has norm bounded in terms of the norm of
its image (`exists_bound`), so a convergent sequence in the range comes from a bounded sequence;
compactness of `K` then produces a convergent subsequence, and the limit is attained. -/
theorem isClosed_range_smul_sub {K : X →L[𝕜] X} (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0) :
    IsClosed ((μ • (1 : X →L[𝕜] X) - K).range : Set X) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound hK hμ
  refine IsSeqClosed.isClosed ?_
  intro y p hy hlim
  choose a ha using fun n => LinearMap.mem_range.1 (SetLike.mem_coe.1 (hy n))
  have ha' : ∀ n, (μ • (1 : X →L[𝕜] X) - K) (a n) = y n := fun n => ha n
  choose r hr hrmin using
    fun n => exists_almost_minimal ((μ • (1 : X →L[𝕜] X) - K).ker) (a n)
  have hr' : ∀ n, (μ • (1 : X →L[𝕜] X) - K) (r n) = 0 :=
    fun n => LinearMap.mem_ker.1 (hr n)
  have hS : ∀ n, (μ • (1 : X →L[𝕜] X) - K) (a n - r n) = y n := by
    intro n
    rw [map_sub, ha' n, hr' n, sub_zero]
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hlim)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (y 0)) (hB _ ⟨0, rfl⟩)
  have hbdd : ∀ n, ‖a n - r n‖ ≤ C * (1 + B) := by
    intro n
    refine le_trans (hC (a n - r n) fun t ht => hrmin n t ht) ?_
    rw [hS n]
    exact mul_le_mul_of_nonneg_left (by linarith [hB (y n) ⟨n, rfl⟩]) hC0
  obtain ⟨Kc, hKc, hKcsub⟩ := hK.image_closedBall_subset_compact (C * (1 + B))
  obtain ⟨q, -, φ, hφ, hφq⟩ := hKc.tendsto_subseq (x := fun n => K (a n - r n))
    fun n => hKcsub ⟨a n - r n, mem_closedBall_zero_iff.2 (hbdd n), rfl⟩
  have hφq' : Tendsto (fun k => K (a (φ k) - r (φ k))) atTop (𝓝 q) := hφq
  have hytend : Tendsto (fun k => y (φ k)) atTop (𝓝 p) := hlim.comp hφ.tendsto_atTop
  have hatend : Tendsto (fun k => a (φ k) - r (φ k)) atTop (𝓝 (μ⁻¹ • (p + q))) := by
    have hid : ∀ z : X, (μ • (1 : X →L[𝕜] X) - K) z + K z = μ • z := by intro z; simp
    have hsum : Tendsto (fun k => μ • (a (φ k) - r (φ k))) atTop (𝓝 (p + q)) := by
      have h := hytend.add hφq'
      refine Filter.Tendsto.congr (fun k => ?_) h
      rw [← hS (φ k)]
      exact hid _
    have h := hsum.const_smul (μ⁻¹)
    simpa [smul_smul, ← mul_assoc, inv_mul_cancel₀ hμ] using h
  have hcont : Tendsto (fun k => (μ • (1 : X →L[𝕜] X) - K) (a (φ k) - r (φ k))) atTop
      (𝓝 ((μ • (1 : X →L[𝕜] X) - K) (μ⁻¹ • (p + q)))) :=
    ((μ • (1 : X →L[𝕜] X) - K).continuous.tendsto _).comp hatend
  refine SetLike.mem_coe.2 (LinearMap.mem_range.2 ⟨μ⁻¹ • (p + q), ?_⟩)
  refine tendsto_nhds_unique hcont ?_
  simpa only [hS] using hytend

end ClosedRange

/-! ### The solvability criterion on a Hilbert space -/

section Solvability

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]

/-- **The solvability criterion for a second-kind equation** (the "Fredholm alternative" in the
form used to solve `(μ - K) u = f`): on a Hilbert space, for a compact `K` and `μ ≠ 0`,
`range (μ • 1 - K) = (ker (conj μ • 1 - K†))ᗮ`. So the equation `(μ • 1 - K) u = f` is solvable
exactly when `f` is orthogonal to every solution of the homogeneous adjoint equation, and
`X = ker (conj μ • 1 - K†) ⊕ range (μ • 1 - K)`.

The inclusion of the range in the orthogonal complement is formal; equality is
`isClosed_range_smul_sub`. -/
theorem range_smul_sub_eq_orthogonal_ker_adjoint {K : X →L[𝕜] X} (hK : IsCompactOperator K)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    (μ • (1 : X →L[𝕜] X) - K).range =
      ((starRingEnd 𝕜) μ • (1 : X →L[𝕜] X) - ContinuousLinearMap.adjoint K).kerᗮ := by
  have hone : ContinuousLinearMap.adjoint (1 : X →L[𝕜] X) = 1 := by
    simpa [ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.adjoint_id (𝕜 := 𝕜) (E := X))
  have hadj : ContinuousLinearMap.adjoint (μ • (1 : X →L[𝕜] X) - K)
      = (starRingEnd 𝕜) μ • (1 : X →L[𝕜] X) - ContinuousLinearMap.adjoint K := by
    rw [map_sub, map_smulₛₗ, hone]
  have hclosed := hK.isClosed_range_smul_sub hμ
  have : CompleteSpace ((μ • (1 : X →L[𝕜] X) - K).range) :=
    completeSpace_coe_iff_isComplete.2 hclosed.isComplete
  rw [← hadj, ← ContinuousLinearMap.orthogonal_range, Submodule.orthogonal_orthogonal]

end Solvability

end IsCompactOperator
