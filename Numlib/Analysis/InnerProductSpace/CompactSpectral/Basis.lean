/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Spectrum` (the Hilbert basis of eigenvectors)
and `Mathlib.Analysis.InnerProductSpace.Rayleigh` (the spectral bounds).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Hilbert basis of eigenvectors of a compact self-adjoint operator

Let $T$ be a bounded operator on a Hilbert space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
and let
$$m = \inf_{x \neq 0} R_T(x), \qquad M = \sup_{x \neq 0} R_T(x), \qquad R_T(x) =
  \frac{\operatorname{Re} \langle Tx, x \rangle}{\|x\|^2},$$
be the bounds of its Rayleigh quotient. This module proves the spectral decomposition of a compact
self-adjoint operator in its classical form: a Hilbert basis of eigenvectors, indexed by a set of
vectors, with no injectivity, separability or dimension hypothesis. It also proves the description
of the spectrum of a bounded self-adjoint operator by the bounds of the quadratic form:
$\sigma(T) \subseteq [m, M]$, $m, M \in \sigma(T)$, $\|T\| = \max(|m|, |M|)$, and a self-adjoint
operator whose spectrum is contained in $\{0\}$ is zero. This is §6.4 of [brezis2011functional]
(Proposition 6.9, Corollary 6.10, Theorem 6.11).

## Main results

* `ContinuousLinearMap.IsPositive.norm_apply_sq_le_norm_mul_re_inner`: the Cauchy–Schwarz inequality
  $\|Sx\|^2 \le \|S\| \operatorname{Re} \langle Sx, x \rangle$ for a positive operator $S$, on which
  $M \in \sigma(T)$ rests.
* `ContinuousLinearMap.mem_Icc_of_ofReal_mem_spectrum`: every real point of the spectrum of $T$ lies
  in $[m, M]$, without self-adjointness (Proposition 6.9 of [brezis2011functional]).
* `IsSelfAdjoint.ofReal_iSup_rayleighQuotient_mem_spectrum` and
  `IsSelfAdjoint.ofReal_iInf_rayleighQuotient_mem_spectrum`: for self-adjoint $T$ on a nontrivial
  space, $M \in \sigma(T)$ and $m \in \sigma(T)$ (Proposition 6.9 of [brezis2011functional]).
* `IsSelfAdjoint.norm_eq_max_abs_iInf_abs_iSup`: for self-adjoint $T$ on a nontrivial space,
  $\|T\| = \max(|m|, |M|)$ (Proposition 6.9 of [brezis2011functional]).
* `IsSelfAdjoint.eq_zero_of_spectrum_subset_zero`: a self-adjoint operator with
  $\sigma(T) \subseteq \{0\}$ is zero (Corollary 6.10 of [brezis2011functional]).
* `ContinuousLinearMap.exists_hilbertBasis_eigenvectors_of_orthogonalFamily`: an operator whose
  eigenspaces are pairwise orthogonal and have dense span has a Hilbert basis of eigenvectors,
  indexed by a set of vectors.
* `ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors`: a compact symmetric operator
  has a Hilbert basis of eigenvectors with real eigenvalues (Theorem 6.11 of
  [brezis2011functional]). `ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors`
  is the same statement with an arbitrary index type in the universe of $E$.

## Proof outline

The real points $t < m$ are outside the spectrum, because then $T - tI$ is coercive and hence
invertible by the Lax–Milgram theorem; the same argument applied to $-T$ treats $t > M$. For
$M \in \sigma(T)$, the operator $S = MI - T$ is positive, so the Cauchy–Schwarz inequality for $S$
gives $\|Sx\|^2 \le \|S\| (M \|x\|^2 - \operatorname{Re} \langle Tx, x \rangle)$; vectors whose
Rayleigh quotient approaches $M$ show that $S$ is not bounded below. The statement $m \in \sigma(T)$
is $M \in \sigma(-T)$. For the Hilbert basis, the eigenspaces of a symmetric operator are
orthogonal, and for a compact one their span is dense; the union of Hilbert bases of the eigenspaces
is then a Hilbert basis of $E$.

## Implementation notes

* The numbers $m$ and $M$ are the infimum and supremum of Mathlib's
  `ContinuousLinearMap.rayleighQuotient` over the nonzero vectors, the indexing of
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`. [brezis2011functional] takes them
  over the unit sphere; the two agree by
  `ContinuousLinearMap.iSup_rayleigh_eq_iSup_rayleigh_sphere`.
* The spectral bounds are stated for the real points of the spectrum: $t \in \mathbb{R}$ with
  $t \in \sigma(T)$. Over $\mathbb{R}$ this is the statement of the source. Over $\mathbb{C}$ the
  spectrum of a self-adjoint operator is real by the C⋆-algebra theory of Mathlib
  (`IsSelfAdjoint.mem_spectrum_eq_re`). The inclusion $\sigma(T) \cap \mathbb{R} \subseteq [m, M]$
  needs no self-adjointness, since it is the real part of the inclusion of $\sigma(T)$ in the
  closure of the numerical range, and it is stated without it.
* The resolvent bounds use Mathlib's Lax–Milgram criterion
  `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`, so no coercivity vocabulary is needed.
* Where [brezis2011functional] assumes $E$ separable for Theorem 6.11, no hypothesis is needed here.
  The index set of the basis is a set of vectors, as in Mathlib's `exists_hilbertBasis`, and
  separability of $E$ is then equivalent to countability of that set.
* The parent module `Numlib.Analysis.InnerProductSpace.CompactSpectral` builds the enumerated form
  (`ContinuousLinearMap.IsSymmetric.eigenvalueSeq` and a Hilbert basis indexed by $\mathbb{N}$),
  which needs $T$ injective and $E$ infinite-dimensional. The two forms complement each other, and
  neither is derived from the other.
-/

open Module.End Filter Topology RCLike
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

/-! ### Cauchy–Schwarz for a positive operator -/

/-- The form $(x, y) \mapsto \langle Sx, y \rangle$ of a positive operator $S$, as a
pre-inner-product core, so that the Cauchy–Schwarz inequality of Mathlib for such cores applies
to it. -/
@[instance_reducible]
private noncomputable def IsPositive.preCore {S : E →L[𝕜] E} (hS : S.IsPositive) :
    PreInnerProductSpace.Core 𝕜 E where
  inner x y := ⟪S x, y⟫_𝕜
  conj_inner_symm x y := by rw [inner_conj_symm, hS.inner_left_eq_inner_right x y]
  re_inner_nonneg x := hS.re_inner_nonneg_left x
  add_left x y z := by simp [inner_add_left]
  smul_left x y r := by simp [inner_smul_left]

/-- The **Cauchy–Schwarz inequality for a positive operator**. Let $S$ be a bounded positive
operator on an inner product space $E$. Then for every $x \in E$
$$\|Sx\|^2 \le \|S\| \operatorname{Re} \langle Sx, x \rangle.$$
This is inequality (7) in the proof of Proposition 6.9 of [brezis2011functional].

The form $(u, v) \mapsto \operatorname{Re} \langle Su, v \rangle$ is symmetric and positive
semidefinite, so $\|Sx\|^4 = (\operatorname{Re} \langle Sx, Sx \rangle)^2 \le \operatorname{Re}
\langle Sx, x \rangle \operatorname{Re} \langle S(Sx), Sx \rangle \le \operatorname{Re} \langle
Sx, x \rangle \|S\| \|Sx\|^2$. -/
theorem IsPositive.norm_apply_sq_le_norm_mul_re_inner {S : E →L[𝕜] E} (hS : S.IsPositive)
    (x : E) : ‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫_𝕜 := by
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 E _ _ _ hS.preCore x (S x)
  change ‖⟪S x, S x⟫_𝕜‖ * ‖⟪S (S x), x⟫_𝕜‖ ≤ re ⟪S x, x⟫_𝕜 * re ⟪S (S x), S x⟫_𝕜 at hcs
  have h1 : ‖⟪S x, S x⟫_𝕜‖ = ‖S x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, norm_ofReal, abs_norm]
  have h2 : ‖⟪S (S x), x⟫_𝕜‖ = ‖S x‖ ^ 2 := by rw [hS.inner_left_eq_inner_right (S x) x, h1]
  have h3 : re ⟪S (S x), S x⟫_𝕜 ≤ ‖S‖ * ‖S x‖ ^ 2 := by
    calc re ⟪S (S x), S x⟫_𝕜 ≤ ‖⟪S (S x), S x⟫_𝕜‖ := re_le_norm _
      _ ≤ ‖S (S x)‖ * ‖S x‖ := norm_inner_le_norm _ _
      _ ≤ ‖S‖ * ‖S x‖ * ‖S x‖ := by gcongr; exact S.le_opNorm _
      _ = ‖S‖ * ‖S x‖ ^ 2 := by ring
  have h0 : 0 ≤ re ⟪S x, x⟫_𝕜 := hS.re_inner_nonneg_left x
  rw [h1, h2] at hcs
  rcases (sq_nonneg ‖S x‖).eq_or_lt with hx | hx
  · rw [← hx]
    positivity
  · refine le_of_mul_le_mul_right ?_ hx
    calc ‖S x‖ ^ 2 * ‖S x‖ ^ 2 ≤ re ⟪S x, x⟫_𝕜 * re ⟪S (S x), S x⟫_𝕜 := hcs
      _ ≤ re ⟪S x, x⟫_𝕜 * (‖S‖ * ‖S x‖ ^ 2) := by gcongr
      _ = ‖S‖ * re ⟪S x, x⟫_𝕜 * ‖S x‖ ^ 2 := by ring

end ContinuousLinearMap

/-! ### The spectral bounds of a self-adjoint operator -/

namespace ContinuousLinearMap

variable [CompleteSpace E] {T : E →L[𝕜] E}

omit [CompleteSpace E] in
/-- For real $c$, $\operatorname{Re} \langle (cI - T) x, x \rangle = c \|x\|^2 - \operatorname{Re}
\langle Tx, x \rangle$. -/
private theorem re_inner_smul_one_sub_apply (T : E →L[𝕜] E) (c : ℝ) (x : E) :
    re ⟪((c : 𝕜) • (1 : E →L[𝕜] E) - T) x, x⟫_𝕜 = c * ‖x‖ ^ 2 - re ⟪T x, x⟫_𝕜 := by
  simp [inner_sub_left, inner_smul_left]

omit [CompleteSpace E] in
/-- For $x \neq 0$, the quadratic form $\operatorname{Re} \langle Tx, x \rangle$ is the Rayleigh
quotient of $x$ times $\|x\|^2$. -/
private theorem re_inner_eq_rayleighQuotient_mul (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    re ⟪T x, x⟫_𝕜 = T.rayleighQuotient x * ‖x‖ ^ 2 := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    div_mul_cancel₀ _ hx2]

omit [CompleteSpace E] in
/-- Let $T$ be a bounded operator on an inner product space $E$. The Rayleigh quotients
$\operatorname{Re} \langle Tx, x \rangle / \|x\|^2$ of the nonzero vectors $x$ form a set that
is bounded below. -/
theorem bddBelow_rayleighQuotient_subtype (T : E →L[𝕜] E) :
    BddBelow (Set.range fun x : { x : E // x ≠ 0 } => T.rayleighQuotient x) :=
  ⟨-‖T‖, by
    rintro _ ⟨x, rfl⟩
    exact (abs_le.1 (T.rayleighQuotient_le_norm x)).1⟩

omit [CompleteSpace E] in
/-- Let $T$ be a bounded operator on an inner product space $E$. The Rayleigh quotients
$\operatorname{Re} \langle Tx, x \rangle / \|x\|^2$ of the nonzero vectors $x$ form a set that
is bounded above. -/
theorem bddAbove_rayleighQuotient_subtype (T : E →L[𝕜] E) :
    BddAbove (Set.range fun x : { x : E // x ≠ 0 } => T.rayleighQuotient x) :=
  ⟨‖T‖, by
    rintro _ ⟨x, rfl⟩
    exact (abs_le.1 (T.rayleighQuotient_le_norm x)).2⟩

/-- Let $T$ be a bounded operator on a Hilbert space $E$, and let $c \in \mathbb{R}$ satisfy $c
\|x\|^2 \le \operatorname{Re} \langle Tx, x \rangle$ for all $x \in E$. Then every real number
$t < c$ is outside the spectrum of $T$. No symmetry is needed.

The operator $T - tI$ is coercive with constant $c - t > 0$, hence invertible by the Lax–Milgram
criterion `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`. -/
theorem ofReal_notMem_spectrum_of_lt (T : E →L[𝕜] E) {c t : ℝ}
    (hc : ∀ x, c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫_𝕜) (ht : t < c) : (t : 𝕜) ∉ spectrum 𝕜 T := by
  rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one]
  have hpos : (0 : ℝ) < c - t := sub_pos.2 ht
  refine isUnit_of_forall_le_norm_inner_map _ (c := ⟨c - t, hpos.le⟩)
    (by exact_mod_cast hpos) fun x => ?_
  have h := re_inner_smul_one_sub_apply T t x
  have hcx := hc x
  calc ‖x‖ ^ 2 * ((⟨c - t, hpos.le⟩ : NNReal) : ℝ)
      = -(t * ‖x‖ ^ 2 - re ⟪T x, x⟫_𝕜) - (re ⟪T x, x⟫_𝕜 - c * ‖x‖ ^ 2) := by
        change ‖x‖ ^ 2 * (c - t) = _
        ring
    _ ≤ -(t * ‖x‖ ^ 2 - re ⟪T x, x⟫_𝕜) := by linarith
    _ = -re ⟪((t : 𝕜) • (1 : E →L[𝕜] E) - T) x, x⟫_𝕜 := by rw [h]
    _ ≤ |re ⟪((t : 𝕜) • (1 : E →L[𝕜] E) - T) x, x⟫_𝕜| := neg_le_abs _
    _ ≤ ‖⟪((t : 𝕜) • (1 : E →L[𝕜] E) - T) x, x⟫_𝕜‖ := abs_re_le_norm _

/-- **The real spectrum of an operator lies between the bounds of its Rayleigh quotient.** Let $T$
be a bounded operator on a Hilbert space $E$, and let $m$ and $M$ be the infimum and the
supremum of the Rayleigh quotient $\operatorname{Re} \langle Tx, x \rangle / \|x\|^2$ over the
nonzero vectors $x$. If $t \in \mathbb{R}$ lies in the spectrum of $T$, then $m \le t \le M$.
This is the inclusion $\sigma(T) \subseteq [m, M]$ of Proposition 6.9 of [brezis2011functional].

The source states the inclusion for self-adjoint $T$; the proof, by the Lax–Milgram theorem,
uses no symmetry. Over $\mathbb{R}$ this is the statement of the source; over $\mathbb{C}$ the
spectrum of a self-adjoint operator is real (`IsSelfAdjoint.mem_spectrum_eq_re`). No
nontriviality of $E$ is needed: on the trivial space the spectrum is empty. The Rayleigh
quotient is `ContinuousLinearMap.rayleighQuotient`. -/
theorem mem_Icc_of_ofReal_mem_spectrum (T : E →L[𝕜] E) {t : ℝ}
    (ht : (t : 𝕜) ∈ spectrum 𝕜 T) :
    t ∈ Set.Icc (⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x)
      (⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x) := by
  constructor
  · by_contra h
    push Not at h
    refine T.ofReal_notMem_spectrum_of_lt (fun x => ?_) h ht
    by_cases hx : x = 0
    · simp [hx]
    · have h1 := ciInf_le (bddBelow_rayleighQuotient_subtype T) ⟨x, hx⟩
      rw [re_inner_eq_rayleighQuotient_mul T hx]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  · by_contra h
    push Not at h
    refine (-T).ofReal_notMem_spectrum_of_lt (t := -t)
      (c := -⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x) (fun x => ?_) (by linarith) ?_
    · rw [neg_apply, inner_neg_left, map_neg]
      by_cases hx : x = 0
      · simp [hx]
      · have h1 := le_ciSup (bddAbove_rayleighQuotient_subtype T) ⟨x, hx⟩
        rw [re_inner_eq_rayleighQuotient_mul T hx]
        nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)]
    · rw [ofReal_neg, ← spectrum.neg_eq, Set.neg_mem_neg]
      exact ht

end ContinuousLinearMap

namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] {T : E →L[𝕜] E}

/-- **The supremum of the Rayleigh quotient of a self-adjoint operator lies in its spectrum.** Let
$E$ be a nontrivial Hilbert space, let $T$ be a bounded self-adjoint operator on $E$, and let
$M$ be the supremum of the Rayleigh quotient $\operatorname{Re} \langle Tx, x \rangle / \|x\|^2$
over the nonzero vectors $x$. Then $M \in \sigma(T)$. This is part of Proposition 6.9 of
[brezis2011functional].

The operator $S = MI - T$ is positive, so $\|Sx\|^2 \le \|S\| (M \|x\|^2 - \operatorname{Re}
\langle Tx, x \rangle)$ by `ContinuousLinearMap.IsPositive.norm_apply_sq_le_norm_mul_re_inner`.
Vectors whose Rayleigh quotient approaches $M$ make the right side arbitrarily small relative to
$\|x\|^2$, which is impossible for an invertible $S$. -/
theorem ofReal_iSup_rayleighQuotient_mem_spectrum [Nontrivial E] (hT : IsSelfAdjoint T) :
    ((⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) : 𝕜) ∈ spectrum 𝕜 T := by
  have : Nonempty { x : E // x ≠ 0 } := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  set M := ⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x with hM
  -- the quadratic form is bounded by `M`
  have hle : ∀ x, re ⟪T x, x⟫_𝕜 ≤ M * ‖x‖ ^ 2 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · rw [re_inner_eq_rayleighQuotient_mul T hx]
      exact mul_le_mul_of_nonneg_right (le_ciSup (bddAbove_rayleighQuotient_subtype T) ⟨x, hx⟩)
        (sq_nonneg _)
  set S : E →L[𝕜] E := (M : 𝕜) • (1 : E →L[𝕜] E) - T with hS
  have hSpos : S.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · have h := hT.isSymmetric x y
      change ⟪T x, y⟫_𝕜 = ⟪x, T y⟫_𝕜 at h
      simp only [hS, ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_ofReal, h]
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, hS, re_inner_smul_one_sub_apply]
      linarith [hle x]
  by_contra hM'
  -- `S` is invertible, hence bounded below
  have hunit : IsUnit S := by
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hM'
    exact hM'
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (S.antilipschitz_of_isEmbedding (ContinuousLinearMap.isHomeomorph_of_isUnit hunit).isEmbedding)
  -- a nonzero vector whose Rayleigh quotient is within `ε` of `M`
  set ε : ℝ := c ^ 2 / (‖S‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (f := fun x : { x : E // x ≠ 0 } => T.rayleighQuotient x)
    (show M - ε < M by linarith)
  have hx2 : 0 < ‖(x : E)‖ ^ 2 := by have := x.2; positivity
  have h1 : ‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫_𝕜 := hSpos.norm_apply_sq_le_norm_mul_re_inner x
  have h2 : re ⟪S x, x⟫_𝕜 = (M - T.rayleighQuotient x) * ‖(x : E)‖ ^ 2 := by
    rw [hS, re_inner_smul_one_sub_apply, re_inner_eq_rayleighQuotient_mul T x.2]
    ring
  have h3 : (c * ‖(x : E)‖) ^ 2 ≤ ‖S x‖ ^ 2 := by
    have := hc x
    gcongr
  -- `c ^ 2 ≤ ‖S‖ * ε < c ^ 2`
  have h4 : c ^ 2 ≤ ‖S‖ * ε := by
    refine le_of_mul_le_mul_right ?_ hx2
    calc c ^ 2 * ‖(x : E)‖ ^ 2 = (c * ‖(x : E)‖) ^ 2 := by ring
      _ ≤ ‖S x‖ ^ 2 := h3
      _ ≤ ‖S‖ * ((M - T.rayleighQuotient x) * ‖(x : E)‖ ^ 2) := by rw [← h2]; exact h1
      _ ≤ ‖S‖ * (ε * ‖(x : E)‖ ^ 2) := by
          gcongr
          linarith
      _ = ‖S‖ * ε * ‖(x : E)‖ ^ 2 := by ring
  have h5 : ‖S‖ * ε < c ^ 2 := by
    rw [hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hc0 2]
  exact absurd (h4.trans_lt h5) (lt_irrefl _)

/-- **The infimum of the Rayleigh quotient of a self-adjoint operator lies in its spectrum.** Let
$E$ be a nontrivial Hilbert space, let $T$ be a bounded self-adjoint operator on $E$, and let
$m$ be the infimum of the Rayleigh quotient $\operatorname{Re} \langle Tx, x \rangle / \|x\|^2$
over the nonzero vectors $x$. Then $m \in \sigma(T)$. This is part of Proposition 6.9 of
[brezis2011functional].

This is $-m \in \sigma(-T)$ for the self-adjoint operator $-T$, whose Rayleigh quotient is the
negative of that of $T$. -/
theorem ofReal_iInf_rayleighQuotient_mem_spectrum [Nontrivial E] (hT : IsSelfAdjoint T) :
    ((⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) : 𝕜) ∈ spectrum 𝕜 T := by
  have h := hT.neg.ofReal_iSup_rayleighQuotient_mem_spectrum
  have heq : (⨆ x : { x : E // x ≠ 0 }, (-T).rayleighQuotient x)
      = -⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x := by
    simp_rw [ContinuousLinearMap.rayleighQuotient_neg_apply]
    rw [iSup, iInf, ← Set.neg_range, Real.sSup_neg]
  rw [heq, ofReal_neg, ← spectrum.neg_eq, Set.neg_mem_neg] at h
  exact h

/-- Let $E$ be a nontrivial Hilbert space, let $T$ be a bounded self-adjoint operator on $E$, and
let $m$ and $M$ be the infimum and the supremum of the Rayleigh quotient $\operatorname{Re}
\langle Tx, x \rangle / \|x\|^2$ over the nonzero vectors $x$. Then
$$\|T\| = \max(|m|, |M|).$$
This is the last part of Proposition 6.9 of [brezis2011functional].

Mathlib's `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` gives $\|T\| = \sup_x |R_T(x)|$,
and the rest is real arithmetic. -/
theorem norm_eq_max_abs_iInf_abs_iSup [Nontrivial E] (hT : IsSelfAdjoint T) :
    ‖T‖ = max |⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x|
      |⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x| := by
  have : Nonempty { x : E // x ≠ 0 } := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  set m := ⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x with hm
  set M := ⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x with hM
  have hmle : ∀ x : { x : E // x ≠ 0 }, m ≤ T.rayleighQuotient x := fun x =>
    ciInf_le (bddBelow_rayleighQuotient_subtype T) x
  have hleM : ∀ x : { x : E // x ≠ 0 }, T.rayleighQuotient x ≤ M := fun x =>
    le_ciSup (bddAbove_rayleighQuotient_subtype T) x
  have hle : ∀ x : { x : E // x ≠ 0 },
      |T.rayleighQuotient x| ≤ ⨆ y : E, |T.rayleighQuotient y| := fun x =>
    le_ciSup T.bddAbove_rayleighQuotient (x : E)
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    by_cases hx : x = 0
    · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
      exact le_max_of_le_left (abs_nonneg _)
    · exact abs_le_max_abs_abs (hmle ⟨x, hx⟩) (hleM ⟨x, hx⟩)
  · obtain ⟨x₀⟩ := ‹Nonempty { x : E // x ≠ 0 }›
    refine max_le (abs_le.2 ⟨?_, ?_⟩) (abs_le.2 ⟨?_, ?_⟩)
    · exact le_ciInf fun x => (neg_le_neg (hle x)).trans (neg_abs_le _)
    · exact (hmle x₀).trans ((le_abs_self _).trans (hle x₀))
    · exact ((neg_le_neg (hle x₀)).trans (neg_abs_le _)).trans (hleM x₀)
    · exact ciSup_le fun x => (le_abs_self _).trans (hle x)

/-- **A self-adjoint operator whose spectrum is contained in $\{0\}$ is zero.** Let $T$ be a bounded
self-adjoint operator on a Hilbert space $E$ with $\sigma(T) \subseteq \{0\}$. Then $T = 0$.
This is Corollary 6.10 of [brezis2011functional].

The source states the corollary with $\sigma(T) = \{0\}$; the inclusion also covers the trivial
space, whose spectrum is empty. The spectral radius of $T$ vanishes, and it equals the norm by
`ContinuousLinearMap.spectralRadius_eq_nnnorm`. -/
theorem eq_zero_of_spectrum_subset_zero (hT : IsSelfAdjoint T) (h : spectrum 𝕜 T ⊆ {0}) :
    T = 0 := by
  have h1 : spectralRadius 𝕜 T = 0 := by
    rw [spectralRadius_eq_of_unital]
    refine le_antisymm (iSup₂_le fun k hk => ?_) zero_le
    rw [Set.mem_singleton_iff.1 (h hk)]
    simp
  rw [T.spectralRadius_eq_nnnorm hT] at h1
  have h2 : ‖T‖₊ = 0 := by exact_mod_cast h1
  exact nnnorm_eq_zero.1 h2

end IsSelfAdjoint

/-! ### The Hilbert basis of eigenvectors -/

namespace ContinuousLinearMap

variable [CompleteSpace E] {T : E →L[𝕜] E}

/-- **Assembly of a Hilbert basis of eigenvectors.** Let $T$ be a bounded operator on a Hilbert
space $E$ whose eigenspaces are pairwise orthogonal and whose eigenspaces together span a dense
subspace, that is, $\bigl(\bigvee_\mu \ker(T - \mu I)\bigr)^\perp = \{0\}$. Then there are a set
$w \subseteq E$ and a Hilbert basis of $E$ indexed by $w$ whose vectors are the elements of $w$,
such that every element of $w$ is an eigenvector of $T$.

This is the last step of the proof of Theorem 6.11 of [brezis2011functional] and of its compact
normal analogue, Proposition 11.36. The basis is the union of Hilbert bases of the eigenspaces,
which are closed and hence complete. It is orthonormal by
`OrthogonalFamily.orthonormal_sigma_orthonormal`, and its span is dense because a vector
orthogonal to it has zero projection onto every eigenspace. No separability is assumed. The
index set is a set of vectors, as in Mathlib's `exists_hilbertBasis`. -/
theorem exists_hilbertBasis_eigenvectors_of_orthogonalFamily
    (hV : OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace (T : Module.End 𝕜 E) μ)
      fun μ => (eigenspace (T : Module.End 𝕜 E) μ).subtypeₗᵢ)
    (hd : (⨆ μ : 𝕜, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E),
      ⇑b = ((↑) : w → E) ∧ ∀ i : w, ∃ μ : 𝕜, T i = μ • (i : E) := by
  classical
  set V : 𝕜 → Submodule 𝕜 E := fun μ => eigenspace (T : Module.End 𝕜 E) μ with hVdef
  have hVc : ∀ μ, CompleteSpace (V μ) := fun μ => (isClosed_eigenspace T μ).completeSpace_coe
  choose s b hb using fun μ => exists_hilbertBasis 𝕜 (V μ)
  -- the union of the bases of the eigenspaces, as the range of a `Σ`-indexed family
  set f : (Σ μ : 𝕜, s μ) → E := fun a => (V a.1).subtypeₗᵢ (b a.1 a.2) with hf
  have hf_on : Orthonormal 𝕜 f := hV.orthonormal_sigma_orthonormal fun μ => (b μ).orthonormal
  have hw_on : Orthonormal 𝕜 ((↑) : Set.range f → E) := hf_on.toSubtypeRange
  -- a vector orthogonal to every basis vector is orthogonal to every eigenspace, hence zero
  have hsp : (Submodule.span 𝕜 (Set.range ((↑) : Set.range f → E)))ᗮ = ⊥ := by
    rw [Subtype.range_coe, Submodule.eq_bot_iff]
    intro x hx
    have hx' : x ∈ (⨆ μ, V μ)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro μ
      rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
      set P := (V μ).orthogonalProjectionOnto x with hP
      have hcoef : ∀ i : s μ, (b μ).repr P i = 0 := by
        intro i
        rw [HilbertBasis.repr_apply_apply, hP,
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
        refine Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span ?_) hx
        exact ⟨⟨μ, i⟩, rfl⟩
      have h1 := (b μ).hasSum_repr P
      simp only [hcoef, zero_smul] at h1
      exact h1.unique hasSum_zero
    rw [hd] at hx'
    exact hx'
  refine ⟨Set.range f, HilbertBasis.mkOfOrthogonalEqBot hw_on hsp,
    HilbertBasis.coe_mkOfOrthogonalEqBot hw_on hsp, fun i => ?_⟩
  obtain ⟨a, ha⟩ := i.2
  refine ⟨a.1, ?_⟩
  have hmem : f a ∈ V a.1 := (b a.1 a.2).2
  rw [← ha]
  exact mem_eigenspace_iff.1 hmem

/-- The **spectral theorem for compact self-adjoint operators**, Hilbert-basis form. Let $T$ be a
compact symmetric operator on a Hilbert space $E$. Then there are a set $w \subseteq E$, a
Hilbert basis $(b_i)_{i \in w}$ of $E$ with $b_i = i$, and real numbers $(\mu_i)_{i \in w}$ such
that
$$T b_i = \mu_i b_i \quad \text{for every } i \in w.$$
This is Theorem 6.11 of [brezis2011functional].

No injectivity, separability or dimension hypothesis is needed; the source assumes $E$
separable. The index set is a set of vectors, as in Mathlib's `exists_hilbertBasis`. The
eigenspaces are orthogonal (`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`) and span a
dense subspace (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`); the
eigenvalues are real by `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/
theorem IsSymmetric.exists_hilbertBasis_eigenvectors (hT : T.IsSymmetric)
    (hK : IsCompactOperator T) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E) (μ : w → ℝ),
      ⇑b = ((↑) : w → E) ∧ ∀ i, T (b i) = (μ i : 𝕜) • b i := by
  obtain ⟨w, b, hb, hμ⟩ := exists_hilbertBasis_eigenvectors_of_orthogonalFamily
    hT.orthogonalFamily_eigenspaces (orthogonalComplement_iSup_eigenspaces_eq_bot hK hT)
  choose μ hμ using hμ
  refine ⟨w, b, fun i => re (μ i), hb, fun i => ?_⟩
  have hne : (i : E) ≠ 0 := by
    have := b.orthonormal.ne_zero i
    rwa [hb] at this
  have hev : HasEigenvalue (T : Module.End 𝕜 E) (μ i) :=
    hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.2 (hμ i), hne⟩
  have hreal : ((re (μ i) : ℝ) : 𝕜) = μ i := conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self hev)
  rw [hb, hreal]
  exact hμ i

end ContinuousLinearMap

section TypeIndexed

universe u

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The **spectral theorem for compact self-adjoint operators** with an arbitrary index type. Let
$F$ be a Hilbert space in the universe `u` and let $T$ be a compact symmetric operator on $F$.
Then there are a type $\iota$ in the universe `u` and a Hilbert basis $(b_i)_{i \in \iota}$ of
$F$ such that each $b_i$ is an eigenvector of $T$ with a real eigenvalue: $T b_i = \mu b_i$ for
some $\mu \in \mathbb{R}$. This is Theorem 6.11 of [brezis2011functional].

The index type is the set $w$ of
`ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors`. -/
theorem ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors {T : F →L[𝕜] F}
    (hT : T.IsSymmetric) (hK : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι 𝕜 F), ∀ i, ∃ μ : ℝ, T (b i) = (μ : 𝕜) • b i := by
  obtain ⟨w, b, μ, -, hb⟩ := ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors hT hK
  exact ⟨w, b, fun i => ⟨μ i, hb i⟩⟩

end TypeIndexed
