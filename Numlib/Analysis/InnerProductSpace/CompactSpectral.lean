/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Spectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The eigenvalues of a compact self-adjoint operator, enumerated with multiplicity

Let $T$ be a compact self-adjoint operator on a Hilbert space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$. This module constructs the eigenvalue sequence $(\lambda_j)_{j \in \mathbb{N}}$ and
the orthonormal family of eigenvectors $(e_j)_{j \in \mathbb{N}}$ that the classical spectral
theorem for compact self-adjoint operators asserts, in the form that the convergence theory of
iterative methods uses: a sequence $\mathbb{N} \to \mathbb{R}$, and a Hilbert basis indexed by
$\mathbb{N}$. The eigenvalues are listed with multiplicity, $|\lambda_0| \ge |\lambda_1| \ge \dots$,
and $\lambda_j \to 0$. If $E$ is infinite-dimensional, then $|\lambda_0| = \|T\|$,
$Te_j = \lambda_j e_j$, the family $(e_j)$ is orthonormal, and every vector orthogonal to all $e_j$
lies in $\ker T$; if moreover $T$ is injective, $(e_j)$ is a Hilbert basis of $E$. The theorem is
classical; see [conway2007course], Chapter II §5, and [han2009theoretical], Section 2.8.

## Main definitions

* `ContinuousLinearMap.IsTopEigenpair`: a unit eigenvector $u$ in a subspace $W$ with a real
  eigenvalue $\mu$ such that $|\mu|$ bounds $T$ on $W$.
* `ContinuousLinearMap.IsSymmetric.eigenvalueSeq`: the eigenvalues of $T$, listed with multiplicity
  in decreasing order of modulus.
* `ContinuousLinearMap.IsSymmetric.eigenvector`: the unit eigenvectors chosen with them.
* `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis`: for injective $T$ on an
  infinite-dimensional space, the eigenvectors as a Hilbert basis indexed by $\mathbb{N}$.

## Main results

* `ContinuousLinearMap.IsSymmetric.exists_isTopEigenpair`: $T$ attains its norm at an eigenvector on
  every nonzero closed invariant subspace.
* `ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone`: the moduli $|\lambda_j|$ decrease.
* `ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero`: $\lambda_j \to 0$.
* `ContinuousLinearMap.IsSymmetric.abs_eigenvalueSeq_zero`: $|\lambda_0| = \|T\|$.
* `ContinuousLinearMap.IsSymmetric.apply_eigenvector` and
  `ContinuousLinearMap.IsSymmetric.orthonormal_eigenvector`: $Te_j = \lambda_j e_j$, and the $e_j$
  are orthonormal.
* `ContinuousLinearMap.IsSymmetric.orthogonal_span_range_eigenvector_le_ker`: a vector orthogonal to
  all $e_j$ is in $\ker T$.
* `ContinuousLinearMap.IsSymmetric.apply_eigenvectorHilbertBasis`: the vectors of the Hilbert basis
  are eigenvectors for the $\lambda_j$.

## Proof outline

The construction is greedy. The vector $e_j$ is a unit eigenvector at which $T$ attains its norm on
the orthogonal complement of $e_0, \dots, e_{j-1}$, and $\lambda_j$ is its eigenvalue. So
$|\lambda_j|$ is the norm of $T$ on a decreasing sequence of subspaces, and the moduli decrease by
construction, with no sorting argument. The greedy step
(`ContinuousLinearMap.IsSymmetric.exists_isTopEigenpair`) is the only place where the spectrum
appears: for a self-adjoint operator the spectral radius is $\|T\|$, the spectrum is compact so the
supremum is attained, and a nonzero point of the spectrum of a compact operator is an eigenvalue.
The limit $\lambda_j \to 0$ is the only other use of compactness: if the moduli stayed above
$\varepsilon > 0$, then $T$ would map the orthonormal sequence $(e_j)$ to a sequence of points at
pairwise distance at least $\varepsilon$, which has no convergent subsequence.

## Implementation notes

* An enumeration of all eigenvalues with multiplicity, in decreasing order of modulus and indexed by
  $\mathbb{N}$, does not always exist. The two extra hypotheses of
  `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` make it possible.
* The operator $T$ must be injective. Let $T = \operatorname{diag}(1, 1/2, 1/3, \dots) \oplus 0$ on
  $\ell^2 \oplus \ell^2$, which is compact and self-adjoint. It has infinitely many nonzero
  eigenvalues and a nontrivial kernel, so a decreasing enumeration would have to place the
  eigenvalue $0$ after infinitely many nonzero ones, and no such enumeration by $\mathbb{N}$ exists.
  The remaining case that can be enumerated, $T$ of finite rank with an infinite-dimensional
  separable kernel, is not treated here. In that case separability of the space is a real
  hypothesis, since the kernel of a compact operator on a non-separable space is non-separable.
  Under injectivity, separability of the space is a conclusion and not a hypothesis: the
  eigenvectors are a countable family with dense span.
* The space must be infinite-dimensional, since a finite-dimensional space has no Hilbert basis
  indexed by $\mathbb{N}$. In finite dimension the enumeration is Mathlib's
  `LinearMap.IsSymmetric.eigenvalues`, indexed by `Fin n` and already antitone.
* The recursion is a plain, non-dependent structural recursion on $\mathbb{N}$. Its value at each
  stage is the pair (eigenvector, eigenvalue) together with the subspace in which the next step
  works. The invariance and closedness of that subspace, which the greedy step needs, are proved
  afterwards by induction and are not part of the definition. Where no top eigenpair exists, the
  recursion takes the value $(0, 0)$.
* The Hilbert-basis form without injectivity, separability or dimension hypotheses, indexed by a set
  of vectors, is in `Numlib.Analysis.InnerProductSpace.CompactSpectral.Basis`.
-/

open Filter Module.End Submodule
open scoped ENNReal Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T : E →L[𝕜] E}

namespace ContinuousLinearMap

/-! ### One greedy step -/

/-- Let $T$ be a bounded operator on $E$ and let $W$ be a subspace of $E$. A pair
$(u, \mu) \in E \times \mathbb{R}$ is a **top eigenpair** of $T$ on $W$ if $u \in W$,
$\|u\| = 1$, $Tu = \mu u$, and $\|Tx\| \le |\mu| \|x\|$ for every $x \in W$. -/
def IsTopEigenpair (T : E →L[𝕜] E) (W : Submodule 𝕜 E) (p : E × ℝ) : Prop :=
  p.1 ∈ W ∧ ‖p.1‖ = 1 ∧ T p.1 = (p.2 : 𝕜) • p.1 ∧ ∀ x ∈ W, ‖T x‖ ≤ |p.2| * ‖x‖

/-- The **greedy step** of the spectral theorem. Let $E$ be a Hilbert space, let $T$ be a compact
symmetric operator on $E$, and let $W \neq \{0\}$ be a closed subspace of $E$ with
$TW \subseteq W$. Then $T$ has a top eigenpair on $W$: there are a unit vector $u \in W$ and
$\mu \in \mathbb{R}$ with $Tu = \mu u$ and $\|Tx\| \le |\mu| \|x\|$ for all $x \in W$.

So a compact self-adjoint operator attains its norm on a nonzero closed invariant subspace, at
an eigenvector. -/
theorem IsSymmetric.exists_isTopEigenpair [CompleteSpace E] (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) {W : Submodule 𝕜 E} (hW : ∀ x ∈ W, T x ∈ W)
    (hWc : IsClosed (W : Set E)) (hWne : W ≠ ⊥) : ∃ p, IsTopEigenpair T W p := by
  have : CompleteSpace W := hWc.completeSpace_coe
  set S : W →L[𝕜] W := T.restrict hW
  have hSapp : ∀ x : W, (S x : E) = T x := fun _ => rfl
  have hSsym : (S : W →ₗ[𝕜] W).IsSymmetric := hT.restrict_invariant hW
  have hScomp : IsCompactOperator S := hK.restrict' hW
  obtain ⟨w, hwW, hw0⟩ := W.ne_bot_iff.1 hWne
  by_cases hS0 : S = 0
  · refine ⟨((‖w‖⁻¹ : 𝕜) • w, 0), W.smul_mem _ hwW, norm_smul_inv_norm hw0, ?_, ?_⟩
    · have : T ((‖w‖⁻¹ : 𝕜) • w) = (S ⟨(‖w‖⁻¹ : 𝕜) • w, W.smul_mem _ hwW⟩ : E) := rfl
      rw [this, hS0]
      simp
    · intro x hx
      have : T x = (S ⟨x, hx⟩ : E) := rfl
      rw [this, hS0]
      simp
  · have hSpos : 0 < ‖S‖ := norm_pos_iff.2 hS0
    have hsr : spectralRadius 𝕜 S = ‖S‖₊ := S.spectralRadius_eq_nnnorm hSsym.isSelfAdjoint
    have hne : (spectrum 𝕜 S).Nonempty := by
      rcases Set.eq_empty_or_nonempty (spectrum 𝕜 S) with h | h
      · refine absurd ?_ hSpos.ne'
        have h0 : spectralRadius 𝕜 S = 0 := by rw [spectralRadius_eq_of_unital, h]; simp
        rw [h0] at hsr
        have h1 : ‖S‖₊ = 0 := by exact_mod_cast hsr.symm
        simpa using congrArg NNReal.toReal h1
      · exact h
    obtain ⟨μ, hμspec, hμ⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hne
    have hμnorm : ‖μ‖ = ‖S‖ := by
      have h2 : ‖μ‖₊ = ‖S‖₊ := by
        have : (‖μ‖₊ : ℝ≥0∞) = (‖S‖₊ : ℝ≥0∞) := hμ.trans hsr
        exact_mod_cast this
      simpa using congrArg NNReal.toReal h2
    have hμ0 : μ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hμnorm
      exact hSpos.ne hμnorm
    have hev : HasEigenvalue (S : Module.End 𝕜 W) μ :=
      (hScomp.hasEigenvalue_iff_mem_spectrum hμ0).2 hμspec
    obtain ⟨v, hv1, hv0⟩ := hev.exists_hasEigenvector
    have hvS : S v = μ • v := mem_genEigenspace_one.1 hv1
    have hreal : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
      RCLike.conj_eq_iff_re.1 (hSsym.conj_eigenvalue_eq_self hev)
    have habs : |RCLike.re μ| = ‖S‖ := by
      rw [← RCLike.norm_ofReal (K := 𝕜), hreal, hμnorm]
    have hvne : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨((‖(v : E)‖⁻¹ : 𝕜) • (v : E), RCLike.re μ),
      W.smul_mem _ v.2, norm_smul_inv_norm hvne, ?_, ?_⟩
    · have hTv : T (v : E) = μ • (v : E) := by
        rw [← hSapp v, hvS]; rfl
      rw [map_smul, hTv, hreal, smul_comm]
    · intro x hx
      have h1 : T x = (S ⟨x, hx⟩ : E) := rfl
      calc ‖T x‖ = ‖S ⟨x, hx⟩‖ := by rw [h1]; rfl
        _ ≤ ‖S‖ * ‖(⟨x, hx⟩ : W)‖ := S.le_opNorm _
        _ = |RCLike.re μ| * ‖x‖ := by rw [habs]; rfl

/-! ### The greedy recursion -/

/-- There is a pair that is a top eigenpair of $T$ on $W$ whenever one exists, and equals $(0, 0)$
otherwise. -/
private theorem exists_topEigen (T : E →L[𝕜] E) (W : Submodule 𝕜 E) :
    ∃ p : E × ℝ, ((∃ q, IsTopEigenpair T W q) → IsTopEigenpair T W p) ∧
      ((¬ ∃ q, IsTopEigenpair T W q) → p = (0, 0)) := by
  by_cases h : ∃ q, IsTopEigenpair T W q
  · exact ⟨h.choose, fun _ => h.choose_spec, fun h' => absurd h h'⟩
  · exact ⟨(0, 0), fun h' => absurd h' h, fun _ => rfl⟩

private noncomputable def topEigen (T : E →L[𝕜] E) (W : Submodule 𝕜 E) : E × ℝ :=
  (exists_topEigen T W).choose

private theorem topEigen_spec {W : Submodule 𝕜 E} (h : ∃ q, IsTopEigenpair T W q) :
    IsTopEigenpair T W (topEigen T W) :=
  (exists_topEigen T W).choose_spec.1 h

private theorem topEigen_junk {W : Submodule 𝕜 E} (h : ¬ ∃ q, IsTopEigenpair T W q) :
    topEigen T W = (0, 0) :=
  (exists_topEigen T W).choose_spec.2 h

/-- The greedy recursion: at stage `n` the current eigenpair together with the subspace it was
chosen from. -/
private noncomputable def eigenAux (T : E →L[𝕜] E) : ℕ → (E × ℝ) × Submodule 𝕜 E
  | 0 => (topEigen T ⊤, ⊤)
  | n + 1 =>
      ((topEigen T ((eigenAux T n).2 ⊓ (𝕜 ∙ (eigenAux T n).1.1)ᗮ)),
        (eigenAux T n).2 ⊓ (𝕜 ∙ (eigenAux T n).1.1)ᗮ)

/-- The `n`-th eigenvector produced by the greedy recursion. -/
private noncomputable def eigenVec (T : E →L[𝕜] E) (n : ℕ) : E := (eigenAux T n).1.1

/-- The `n`-th eigenvalue produced by the greedy recursion. -/
private noncomputable def eigenVal (T : E →L[𝕜] E) (n : ℕ) : ℝ := (eigenAux T n).1.2

/-- The subspace the `n`-th greedy step works in: the orthogonal complement of the first `n`
eigenvectors. -/
private noncomputable def eigenSpace (T : E →L[𝕜] E) (n : ℕ) : Submodule 𝕜 E := (eigenAux T n).2

private theorem eigenSpace_zero (T : E →L[𝕜] E) : eigenSpace T 0 = ⊤ := rfl

private theorem eigenSpace_succ (T : E →L[𝕜] E) (n : ℕ) :
    eigenSpace T (n + 1) = eigenSpace T n ⊓ (𝕜 ∙ eigenVec T n)ᗮ := rfl

private theorem topEigen_eigenSpace (T : E →L[𝕜] E) (n : ℕ) :
    topEigen T (eigenSpace T n) = (eigenVec T n, eigenVal T n) := by
  cases n <;> rfl

private theorem eigenSpace_antitone (T : E →L[𝕜] E) : Antitone (eigenSpace T) :=
  antitone_nat_of_succ_le fun n => by rw [eigenSpace_succ]; exact inf_le_left

private theorem isTopEigenpair_of_exists {n : ℕ}
    (h : ∃ p, IsTopEigenpair T (eigenSpace T n) p) :
    IsTopEigenpair T (eigenSpace T n) (eigenVec T n, eigenVal T n) := by
  rw [← topEigen_eigenSpace]
  exact topEigen_spec h

private theorem eigenVec_eq_zero {n : ℕ} (h : ¬ ∃ p, IsTopEigenpair T (eigenSpace T n) p) :
    eigenVec T n = 0 :=
  congrArg Prod.fst ((topEigen_eigenSpace T n).symm.trans (topEigen_junk h))

private theorem eigenVal_eq_zero {n : ℕ} (h : ¬ ∃ p, IsTopEigenpair T (eigenSpace T n) p) :
    eigenVal T n = 0 :=
  congrArg Prod.snd ((topEigen_eigenSpace T n).symm.trans (topEigen_junk h))

private theorem exists_isTopEigenpair_of_succ {n : ℕ}
    (h : ∃ p, IsTopEigenpair T (eigenSpace T (n + 1)) p) :
    ∃ p, IsTopEigenpair T (eigenSpace T n) p := by
  by_contra hn
  have hz : eigenSpace T (n + 1) = eigenSpace T n := by
    rw [eigenSpace_succ, eigenVec_eq_zero hn, Submodule.span_zero_singleton,
      Submodule.bot_orthogonal_eq_top, inf_top_eq]
  exact hn (hz ▸ h)

private theorem abs_eigenVal_antitone (T : E →L[𝕜] E) : Antitone fun n => |eigenVal T n| := by
  refine antitone_nat_of_succ_le fun n => ?_
  by_cases h : ∃ p, IsTopEigenpair T (eigenSpace T (n + 1)) p
  · obtain ⟨hmem, hnorm, heq, -⟩ := isTopEigenpair_of_exists h
    obtain ⟨-, -, -, hbd⟩ := isTopEigenpair_of_exists (exists_isTopEigenpair_of_succ h)
    have hle : eigenSpace T (n + 1) ≤ eigenSpace T n := eigenSpace_antitone T (Nat.le_succ n)
    have h1 : ‖T (eigenVec T (n + 1))‖ = |eigenVal T (n + 1)| := by
      rw [heq, norm_smul, RCLike.norm_ofReal, hnorm, mul_one]
    have h2 := hbd (eigenVec T (n + 1)) (hle hmem)
    rw [h1, hnorm, mul_one] at h2
    exact h2
  · rw [eigenVal_eq_zero h, abs_zero]
    exact abs_nonneg _

private theorem inner_eigenVec_eq_zero {m n : ℕ} (hmn : m < n)
    (h : ∃ p, IsTopEigenpair T (eigenSpace T n) p) :
    inner 𝕜 (eigenVec T m) (eigenVec T n) = 0 := by
  have hv : eigenVec T n ∈ eigenSpace T n := (isTopEigenpair_of_exists h).1
  have h1 : eigenSpace T n ≤ eigenSpace T (m + 1) := eigenSpace_antitone T hmn
  have h2 : eigenSpace T (m + 1) ≤ (𝕜 ∙ eigenVec T m)ᗮ := by
    rw [eigenSpace_succ]; exact inf_le_right
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 (h1 hv))

private theorem tendsto_abs_eigenVal (hK : IsCompactOperator T) :
    Tendsto (fun n => |eigenVal T n|) atTop (𝓝 0) := by
  have hanti : Antitone fun n => |eigenVal T n| := abs_eigenVal_antitone T
  have hbdd : BddBelow (Set.range fun n => |eigenVal T n|) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact abs_nonneg _⟩
  have htend := tendsto_atTop_ciInf hanti hbdd
  set c := ⨅ n, |eigenVal T n|
  have hc0 : (0 : ℝ) ≤ c := le_ciInf fun n => abs_nonneg _
  rcases eq_or_lt_of_le hc0 with h | h
  · rwa [← h] at htend
  exfalso
  have hge : ∀ n, c ≤ |eigenVal T n| := fun n => ciInf_le hbdd n
  have hstep : ∀ n, ∃ p, IsTopEigenpair T (eigenSpace T n) p := by
    intro n
    by_contra hn
    have hn' := hge n
    rw [eigenVal_eq_zero hn, abs_zero] at hn'
    exact absurd hn' (not_le.2 h)
  have hsep : ∀ m n : ℕ, m ≠ n → c ≤ ‖T (eigenVec T n) - T (eigenVec T m)‖ := by
    intro m n hmn
    obtain ⟨-, hnorm, heq, -⟩ := isTopEigenpair_of_exists (hstep n)
    obtain ⟨-, -, heqm, -⟩ := isTopEigenpair_of_exists (hstep m)
    have hor : inner 𝕜 (eigenVec T n) (eigenVec T m) = 0 := by
      rcases lt_or_gt_of_ne hmn with h' | h'
      · rw [← inner_conj_symm, inner_eigenVec_eq_zero h' (hstep n), map_zero]
      · exact inner_eigenVec_eq_zero h' (hstep m)
    have hcalc : inner 𝕜 (eigenVec T n) (T (eigenVec T n) - T (eigenVec T m))
        = ((eigenVal T n : ℝ) : 𝕜) := by
      rw [inner_sub_right, heq, heqm, inner_smul_right, inner_smul_right, hor, mul_zero, sub_zero,
        inner_self_eq_norm_sq_to_K, hnorm]
      simp
    have hcs := norm_inner_le_norm (𝕜 := 𝕜) (eigenVec T n)
      (T (eigenVec T n) - T (eigenVec T m))
    rw [hcalc, RCLike.norm_ofReal, hnorm, one_mul] at hcs
    exact (hge n).trans hcs
  obtain ⟨Kc, hKcc, hKc⟩ := hK.image_closedBall_subset_compact 1
  have hmem : ∀ n, T (eigenVec T n) ∈ Kc := fun n => hKc ⟨eigenVec T n, by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (isTopEigenpair_of_exists (hstep n)).2.1, rfl⟩
  obtain ⟨y, -, ψ, hψ, hψy⟩ := hKcc.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hψy.cauchySeq c h
  have hlt := hN (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply, dist_eq_norm] at hlt
  have hne : ψ N ≠ ψ (N + 1) := fun he => by simpa using hψ.injective he
  exact absurd hlt (not_lt.2 (hsep _ _ hne))

/-- Let $E$ be an infinite-dimensional inner product space and let $S$ be a finite-dimensional
subspace of $E$. Then $S^\perp \neq \{0\}$. -/
theorem _root_.Submodule.orthogonal_ne_bot_of_not_finiteDimensional
    (hfin : ¬ FiniteDimensional 𝕜 E) {S : Submodule 𝕜 E} [FiniteDimensional 𝕜 S] : Sᗮ ≠ ⊥ := by
  intro h
  have htop : S = ⊤ := by
    have h2 : Sᗮᗮ = S := Submodule.orthogonal_orthogonal S
    rw [h, Submodule.bot_orthogonal_eq_top] at h2
    exact h2.symm
  refine hfin (Module.Finite.of_surjective S.subtype ?_)
  rw [← LinearMap.range_eq_top, Submodule.range_subtype]
  exact htop

private theorem exists_isTopEigenpair_eigenSpace [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hfin : ¬ FiniteDimensional 𝕜 E) (n : ℕ) :
    (∃ S : Submodule 𝕜 E, FiniteDimensional 𝕜 S ∧ eigenSpace T n = Sᗮ) ∧
      (∀ x ∈ eigenSpace T n, T x ∈ eigenSpace T n) ∧
      ∃ p, IsTopEigenpair T (eigenSpace T n) p := by
  induction n with
  | zero =>
    have hS : eigenSpace T 0 = (⊥ : Submodule 𝕜 E)ᗮ := by
      rw [eigenSpace_zero, Submodule.bot_orthogonal_eq_top]
    have hinv : ∀ x ∈ eigenSpace T 0, T x ∈ eigenSpace T 0 := by
      intro x _; rw [eigenSpace_zero]; trivial
    refine ⟨⟨⊥, inferInstance, hS⟩, hinv,
      IsSymmetric.exists_isTopEigenpair hT hK hinv ?_ ?_⟩
    · rw [hS]; exact Submodule.isClosed_orthogonal _
    · rw [hS]; exact Submodule.orthogonal_ne_bot_of_not_finiteDimensional hfin
  | succ n ih =>
    obtain ⟨⟨S, hSfin, hSeq⟩, hinvn, hstepn⟩ := ih
    have _ : FiniteDimensional 𝕜 S := hSfin
    obtain ⟨-, -, heq, -⟩ := isTopEigenpair_of_exists hstepn
    have hS' : eigenSpace T (n + 1) = (S ⊔ 𝕜 ∙ eigenVec T n)ᗮ := by
      rw [eigenSpace_succ, hSeq, Submodule.inf_orthogonal]
    have hinv : ∀ x ∈ eigenSpace T (n + 1), T x ∈ eigenSpace T (n + 1) := by
      intro x hx
      rw [eigenSpace_succ] at hx ⊢
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx2
      refine ⟨hinvn x hx1, Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_⟩
      rw [← hT.apply_clm (eigenVec T n) x, heq, inner_smul_left, hx2, mul_zero]
    refine ⟨⟨_, inferInstance, hS'⟩, hinv,
      IsSymmetric.exists_isTopEigenpair hT hK hinv ?_ ?_⟩
    · rw [hS']; exact Submodule.isClosed_orthogonal _
    · rw [hS']; exact Submodule.orthogonal_ne_bot_of_not_finiteDimensional hfin

private theorem orthogonal_span_range_le (T : E →L[𝕜] E) (n : ℕ) :
    (Submodule.span 𝕜 (Set.range (eigenVec T)))ᗮ ≤ eigenSpace T n := by
  induction n with
  | zero => rw [eigenSpace_zero]; exact le_top
  | succ n ih =>
    have hmem : eigenVec T n ∈ Submodule.span 𝕜 (Set.range (eigenVec T)) :=
      Submodule.subset_span ⟨n, rfl⟩
    rw [eigenSpace_succ]
    refine le_inf ih fun x hx =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
    exact (Submodule.mem_orthogonal _ x).1 hx _ hmem

/-! ### The eigenvalue sequence and the eigenvector basis -/

/-- The **eigenvalues** $\lambda_0, \lambda_1, \dots$ of a compact symmetric operator $T$, listed
with multiplicity in decreasing order of modulus.

The sequence is built greedily: $|\lambda_n|$ is the norm of $T$ on the orthogonal complement of
the first $n$ eigenvectors, so `ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone` holds by
construction. Each eigenvalue is therefore repeated as often as the dimension of its eigenspace,
which is what a sum over the sequence needs. Where the construction finds no top eigenpair, the
value is $0$; on an infinite-dimensional Hilbert space this does not happen. -/
noncomputable def IsSymmetric.eigenvalueSeq (_hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (_hK : IsCompactOperator T) : ℕ → ℝ := eigenVal T

/-- The unit **eigenvectors** $e_0, e_1, \dots$ of a compact symmetric operator $T$, chosen together
with `ContinuousLinearMap.IsSymmetric.eigenvalueSeq`.

On an infinite-dimensional Hilbert space, $e_n$ is an eigenvector for the eigenvalue $\lambda_n$
(`ContinuousLinearMap.IsSymmetric.apply_eigenvector`) and the family is orthonormal
(`ContinuousLinearMap.IsSymmetric.orthonormal_eigenvector`). Where the construction finds no top
eigenpair, the value is $0$. -/
noncomputable def IsSymmetric.eigenvector (_hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (_hK : IsCompactOperator T) : ℕ → E := eigenVec T

private theorem eigenvalueSeq_eq (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) : IsSymmetric.eigenvalueSeq hT hK = eigenVal T := rfl

private theorem eigenvector_eq (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) : IsSymmetric.eigenvector hT hK = eigenVec T := rfl

/-- Let $T$ be a compact symmetric operator on $E$. Its eigenvalue sequence is decreasing in
modulus: $|\lambda_j| \ge |\lambda_{j+1}|$ for every $j$. -/
theorem IsSymmetric.eigenvalueSeq_antitone (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) : Antitone fun j => |eigenvalueSeq hT hK j| :=
  abs_eigenVal_antitone T

/-- Let $T$ be a compact symmetric operator on $E$. Its eigenvalue sequence tends to zero:
$\lambda_j \to 0$ as $j \to \infty$.

This is where compactness is used. If the moduli stayed above $\varepsilon > 0$, the operator
would map the orthonormal sequence of eigenvectors to a sequence of points at pairwise distance
at least $\varepsilon$, and such a sequence has no convergent subsequence. -/
theorem IsSymmetric.tendsto_eigenvalueSeq_zero (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) : Tendsto (eigenvalueSeq hT hK) atTop (𝓝 0) := by
  rw [eigenvalueSeq_eq]
  exact squeeze_zero_norm (fun n => le_of_eq (Real.norm_eq_abs _)) (tendsto_abs_eigenVal hK)

/-- Let $E$ be an infinite-dimensional Hilbert space and let $T$ be a compact symmetric operator on
$E$. Then $Te_j = \lambda_j e_j$ for every $j$, where $e_j$ and $\lambda_j$ are the greedily
chosen eigenvectors and eigenvalues. -/
theorem IsSymmetric.apply_eigenvector [CompleteSpace E] (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) (hfin : ¬ FiniteDimensional 𝕜 E) (j : ℕ) :
    T (eigenvector hT hK j) = ((eigenvalueSeq hT hK j : ℝ) : 𝕜) • eigenvector hT hK j :=
  (isTopEigenpair_of_exists (exists_isTopEigenpair_eigenSpace hT hK hfin j).2.2).2.2.1

/-- Let $E$ be an infinite-dimensional Hilbert space and let $T$ be a compact symmetric operator on
$E$. Then the first eigenvalue of the greedy enumeration has modulus $|\lambda_0| = \|T\|$.

So a compact self-adjoint operator attains its norm. -/
theorem IsSymmetric.abs_eigenvalueSeq_zero [CompleteSpace E] (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hK : IsCompactOperator T) (hfin : ¬ FiniteDimensional 𝕜 E) :
    |eigenvalueSeq hT hK 0| = ‖T‖ := by
  obtain ⟨-, hnorm, heq, hbd⟩ :=
    isTopEigenpair_of_exists (exists_isTopEigenpair_eigenSpace hT hK hfin 0).2.2
  have htop : ∀ x : E, x ∈ eigenSpace T 0 := by
    intro x; rw [eigenSpace_zero]; trivial
  rw [eigenvalueSeq_eq]
  refine le_antisymm ?_ (T.opNorm_le_bound (abs_nonneg _) fun x => hbd x (htop x))
  have h1 : ‖T (eigenVec T 0)‖ = |eigenVal T 0| := by
    rw [heq, norm_smul, RCLike.norm_ofReal, hnorm, mul_one]
  calc |eigenVal T 0| = ‖T (eigenVec T 0)‖ := h1.symm
    _ ≤ ‖T‖ * ‖eigenVec T 0‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [hnorm, mul_one]

/-- Let $E$ be an infinite-dimensional Hilbert space and let $T$ be a compact symmetric operator on
$E$. Then the greedily chosen eigenvectors $e_0, e_1, \dots$ are orthonormal. -/
theorem IsSymmetric.orthonormal_eigenvector [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hfin : ¬ FiniteDimensional 𝕜 E) : Orthonormal 𝕜 (eigenvector hT hK) := by
  rw [eigenvector_eq]
  refine ⟨fun i => ?_, fun {i j} hij => ?_⟩
  · exact (isTopEigenpair_of_exists (exists_isTopEigenpair_eigenSpace hT hK hfin i).2.2).2.1
  · rcases lt_or_gt_of_ne hij with h | h
    · exact inner_eigenVec_eq_zero h (exists_isTopEigenpair_eigenSpace hT hK hfin j).2.2
    · rw [← inner_conj_symm,
        inner_eigenVec_eq_zero h (exists_isTopEigenpair_eigenSpace hT hK hfin i).2.2, map_zero]

/-- Let $E$ be an infinite-dimensional Hilbert space and let $T$ be a compact symmetric operator on
$E$. Then every vector orthogonal to all the greedily chosen eigenvectors $e_j$ is annihilated
by $T$:
$$\bigl(\operatorname{span} \{e_j : j \in \mathbb{N}\}\bigr)^\perp \subseteq \ker T.$$

This holds whatever the kernel of $T$ is. It is why injectivity is exactly the extra hypothesis
that `ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` needs. -/
theorem IsSymmetric.orthogonal_span_range_eigenvector_le_ker [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hfin : ¬ FiniteDimensional 𝕜 E) :
    (Submodule.span 𝕜 (Set.range (eigenvector hT hK)))ᗮ ≤ LinearMap.ker (T : E →ₗ[𝕜] E) := by
  rw [eigenvector_eq]
  intro x hx
  have hb : ∀ n, ‖T x‖ ≤ |eigenVal T n| * ‖x‖ := fun n =>
    (isTopEigenpair_of_exists (exists_isTopEigenpair_eigenSpace hT hK hfin n).2.2).2.2.2 x
      (orthogonal_span_range_le T n hx)
  have hlim : Tendsto (fun n => |eigenVal T n| * ‖x‖) atTop (𝓝 0) := by
    simpa using (tendsto_abs_eigenVal hK).mul_const ‖x‖
  exact norm_le_zero_iff.1 (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb)

private theorem orthogonal_span_range_eq_bot [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hinj : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) (hfin : ¬ FiniteDimensional 𝕜 E) :
    (Submodule.span 𝕜 (Set.range (eigenVec T)))ᗮ = ⊥ :=
  le_bot_iff.1 (hinj ▸ IsSymmetric.orthogonal_span_range_eigenvector_le_ker hT hK hfin)

/-- The **spectral theorem for compact self-adjoint operators**, in the form of an orthonormal basis
of eigenvectors indexed by $\mathbb{N}$. Let $E$ be an infinite-dimensional Hilbert space and
let $T$ be an injective compact symmetric operator on $E$. Then the greedily chosen eigenvectors
$e_0, e_1, \dots$ form a Hilbert basis of $E$.

Both extra hypotheses are needed; see the module documentation. Since a Hilbert basis indexed by
$\mathbb{N}$ exists, the space is separable. Injectivity is the hypothesis $\ker T = \{0\}$. -/
noncomputable def IsSymmetric.eigenvectorHilbertBasis [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hinj : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) (hfin : ¬ FiniteDimensional 𝕜 E) :
    HilbertBasis ℕ 𝕜 E :=
  HilbertBasis.mkOfOrthogonalEqBot (IsSymmetric.orthonormal_eigenvector hT hK hfin)
    (orthogonal_span_range_eq_bot hT hK hinj hfin)

/-- Let $E$ be an infinite-dimensional Hilbert space and let $T$ be an injective compact symmetric
operator on $E$. The vectors of the Hilbert basis
`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` are the greedily chosen eigenvectors
`ContinuousLinearMap.IsSymmetric.eigenvector`. -/
@[simp]
theorem IsSymmetric.coe_eigenvectorHilbertBasis [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hinj : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) (hfin : ¬ FiniteDimensional 𝕜 E) :
    ⇑(eigenvectorHilbertBasis hT hK hinj hfin) = eigenvector hT hK :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- Let $E$ be an infinite-dimensional Hilbert space and let $T$ be an injective compact symmetric
operator on $E$. Then the $j$-th vector $e_j$ of the Hilbert basis
`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis` satisfies $Te_j = \lambda_j e_j$,
where $\lambda_j$ is `ContinuousLinearMap.IsSymmetric.eigenvalueSeq`.

Together with `ContinuousLinearMap.IsSymmetric.eigenvalueSeq_antitone` and
`ContinuousLinearMap.IsSymmetric.tendsto_eigenvalueSeq_zero`, this is the eigendecomposition
that a superlinear convergence theorem for the conjugate gradient method uses. -/
theorem IsSymmetric.apply_eigenvectorHilbertBasis [CompleteSpace E]
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hK : IsCompactOperator T)
    (hinj : LinearMap.ker (T : E →ₗ[𝕜] E) = ⊥) (hfin : ¬ FiniteDimensional 𝕜 E) (j : ℕ) :
    T (eigenvectorHilbertBasis hT hK hinj hfin j)
      = ((eigenvalueSeq hT hK j : ℝ) : 𝕜) • eigenvectorHilbertBasis hT hK hinj hfin j := by
  simp only [coe_eigenvectorHilbertBasis]
  exact apply_eigenvector hT hK hfin j

end ContinuousLinearMap
