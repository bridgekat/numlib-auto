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

The spectral decomposition of a compact self-adjoint operator in its classical form — a Hilbert
basis of eigenvectors indexed by a set of vectors, with no injectivity, separability or
dimension hypothesis — and the numerical-range description of the spectrum of a bounded
self-adjoint operator: with `m = inf ⟪T u, u⟫` and `M = sup ⟪T u, u⟫` over the unit sphere,
`σ(T) ⊆ [m, M]`, `m, M ∈ σ(T)`, `‖T‖ = max (|m|, |M|)`, and a self-adjoint operator whose
spectrum is contained in `{0}` is zero. This is [brezis2011functional] §6.4 (Proposition 6.9,
Corollary 6.10, Theorem 6.11).

## Main results

* `ContinuousLinearMap.IsPositive.norm_apply_sq_le_norm_mul_re_inner`: the Cauchy–Schwarz
  inequality `‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫` for a positive operator `S`, the estimate on which
  `M ∈ σ(T)` rests.
* `ContinuousLinearMap.mem_Icc_of_ofReal_mem_spectrum`,
  `IsSelfAdjoint.ofReal_iSup_rayleighQuotient_mem_spectrum`,
  `IsSelfAdjoint.ofReal_iInf_rayleighQuotient_mem_spectrum`,
  `IsSelfAdjoint.norm_eq_max_abs_iInf_abs_iSup`: [brezis2011functional] Proposition 6.9, with `m`
  and `M` written as the infimum and supremum of Mathlib's `ContinuousLinearMap.rayleighQuotient`
  over the nonzero vectors (the indexing of
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`; the sphere form is
  `ContinuousLinearMap.iSup_rayleigh_eq_iSup_rayleigh_sphere`). The bounds are stated for the
  *real* points of the spectrum, `(t : 𝕜) ∈ spectrum 𝕜 T → t ∈ Icc m M`: over `ℝ` this is the
  book's statement on the nose, and over `ℂ` the spectrum of a self-adjoint operator is real by
  Mathlib's C⋆-algebra theory (`IsSelfAdjoint.mem_spectrum_eq_re`). The inclusion `σ(T) ⊆ [m, M]`
  needs no self-adjointness at all — it is the real slice of `σ(T) ⊆ closure W(T)` — and is
  stated without it.
* `IsSelfAdjoint.eq_zero_of_spectrum_subset_zero`: [brezis2011functional] Corollary 6.10, from
  `ContinuousLinearMap.spectralRadius_eq_nnnorm`.
* `ContinuousLinearMap.exists_hilbertBasis_eigenvectors_of_orthogonalFamily`: the assembly step
  of the spectral theorem — an operator whose eigenspaces are pairwise orthogonal and span densely
  has a Hilbert basis of eigenvectors indexed by a set of vectors. It is stated for an arbitrary
  operator so that it serves both the self-adjoint case here and the compact normal case.
* `ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors`: [brezis2011functional]
  Theorem 6.11. The eigenspaces of a symmetric operator are orthogonal
  (`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`) and, for a compact one, span densely
  (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`); the eigenvalue of each
  basis vector is real (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`).
  `ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors` is the same statement
  with an arbitrary index type in the universe of `E`.

## Design

The spectral bounds use Mathlib's Lax–Milgram criterion
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` for the resolvent, so no coercivity
vocabulary is needed. `m ∈ σ(T)` is `M ∈ σ(−T)`; the negation of a bounded infimum is a supremum
(`csSup_neg`). Where the book assumes `H` separable, no hypothesis is needed: the index set of
the basis is a set of vectors, as in Mathlib's `exists_hilbertBasis`, and separability of `E`
is then equivalent to countability of that set. The parent module
`Numlib.Analysis.InnerProductSpace.CompactSpectral` builds the *enumerated* form
(`eigenvalueSeq`, `eigenvectorHilbertBasis : HilbertBasis ℕ 𝕜 E`) and needs `T` injective and `E`
infinite dimensional for that; the two forms are complementary and neither derives from the other.
-/

open Module.End Filter Topology RCLike
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ContinuousLinearMap

/-! ### Cauchy–Schwarz for a positive operator -/

/-- The form `⟪S x, y⟫` of a positive operator as a pre-inner-product core, so that Mathlib's
Cauchy–Schwarz inequality for such cores applies to it. -/
@[instance_reducible]
private noncomputable def IsPositive.preCore {S : E →L[𝕜] E} (hS : S.IsPositive) :
    PreInnerProductSpace.Core 𝕜 E where
  inner x y := ⟪S x, y⟫_𝕜
  conj_inner_symm x y := by rw [inner_conj_symm, hS.inner_left_eq_inner_right x y]
  re_inner_nonneg x := hS.re_inner_nonneg_left x
  add_left x y z := by simp [inner_add_left]
  smul_left x y r := by simp [inner_smul_left]

/-- **Cauchy–Schwarz for a positive operator**: `‖S x‖ ^ 2 ≤ ‖S‖ * re ⟪S x, x⟫`. The form
`(u, v) ↦ re ⟪S u, v⟫` is symmetric and positive semidefinite, so
`‖S x‖ ^ 4 = (re ⟪S x, S x⟫) ^ 2 ≤ re ⟪S x, x⟫ * re ⟪S (S x), S x⟫ ≤ re ⟪S x, x⟫ * ‖S‖ * ‖S x‖ ^ 2`.
This is inequality (7) in the proof of [brezis2011functional] Proposition 6.9. -/
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
/-- `re ⟪(c • 1 - T) x, x⟫ = c * ‖x‖ ^ 2 - re ⟪T x, x⟫` for a real `c`. -/
private theorem re_inner_smul_one_sub_apply (T : E →L[𝕜] E) (c : ℝ) (x : E) :
    re ⟪((c : 𝕜) • (1 : E →L[𝕜] E) - T) x, x⟫_𝕜 = c * ‖x‖ ^ 2 - re ⟪T x, x⟫_𝕜 := by
  simp [inner_sub_left, inner_smul_left]

omit [CompleteSpace E] in
/-- The Rayleigh quotient of a nonzero vector times the squared norm is the quadratic form. -/
private theorem re_inner_eq_rayleighQuotient_mul (T : E →L[𝕜] E) {x : E} (hx : x ≠ 0) :
    re ⟪T x, x⟫_𝕜 = T.rayleighQuotient x * ‖x‖ ^ 2 := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    div_mul_cancel₀ _ hx2]

omit [CompleteSpace E] in
/-- The Rayleigh quotient over the nonzero vectors is bounded below. -/
private theorem bddBelow_rayleighQuotient_subtype (T : E →L[𝕜] E) :
    BddBelow (Set.range fun x : { x : E // x ≠ 0 } => T.rayleighQuotient x) :=
  ⟨-‖T‖, by
    rintro _ ⟨x, rfl⟩
    exact (abs_le.1 (T.rayleighQuotient_le_norm x)).1⟩

omit [CompleteSpace E] in
/-- The Rayleigh quotient over the nonzero vectors is bounded above. -/
private theorem bddAbove_rayleighQuotient_subtype (T : E →L[𝕜] E) :
    BddAbove (Set.range fun x : { x : E // x ≠ 0 } => T.rayleighQuotient x) :=
  ⟨‖T‖, by
    rintro _ ⟨x, rfl⟩
    exact (abs_le.1 (T.rayleighQuotient_le_norm x)).2⟩

/-- A real number strictly below a lower bound `c` of the quadratic form of an operator,
`c * ‖x‖ ^ 2 ≤ re ⟪T x, x⟫`, is in the resolvent set: `T - t • 1` is then coercive with
constant `c - t`, hence invertible by the Lax–Milgram criterion
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`. No symmetry is needed. -/
private theorem ofReal_notMem_spectrum_of_lt (T : E →L[𝕜] E) {c t : ℝ}
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

/-- **The real spectrum of an operator lies between the bounds of its Rayleigh quotient**
([brezis2011functional] Proposition 6.9, `σ(T) ⊆ [m, M]`, stated there for self-adjoint `T`; the
proof, by Lax–Milgram, uses no symmetry): for `t : ℝ` with `(t : 𝕜) ∈ spectrum 𝕜 T`,
`m ≤ t ≤ M` where `m` and `M` are the infimum and supremum of `T.rayleighQuotient` over the
nonzero vectors. Over `ℝ` this is the book's statement; over `ℂ` the spectrum of a self-adjoint
operator is real (`IsSelfAdjoint.mem_spectrum_eq_re`). No nontriviality of `E` is needed: on the
trivial space the spectrum is empty. -/
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

/-- **The supremum of the Rayleigh quotient of a self-adjoint operator belongs to its spectrum**
([brezis2011functional] Proposition 6.9, `M ∈ σ(T)`), on a nontrivial Hilbert space. The
operator `S = M • 1 - T` is positive, so `‖S x‖ ^ 2 ≤ ‖S‖ * (M ‖x‖ ^ 2 - re ⟪T x, x⟫)` by
`ContinuousLinearMap.IsPositive.norm_apply_sq_le_norm_mul_re_inner`; vectors whose Rayleigh
quotient approaches `M` make the right side arbitrarily small relative to `‖x‖ ^ 2`, which no
invertible `S` allows. -/
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

omit [CompleteSpace E] in
/-- The supremum of the negatives of a bounded-below real family is the negative of its
infimum. -/
private theorem ciSup_neg_eq_neg_ciInf {ι : Type*} [Nonempty ι] {f : ι → ℝ}
    (hf : BddBelow (Set.range f)) : ⨆ i, -f i = -⨅ i, f i := by
  rw [iSup, iInf, ← Set.neg_range, csSup_neg (Set.range_nonempty f) hf]

/-- **The infimum of the Rayleigh quotient of a self-adjoint operator belongs to its spectrum**
([brezis2011functional] Proposition 6.9, `m ∈ σ(T)`), on a nontrivial Hilbert space: this is
`M ∈ σ(-T)` for the self-adjoint operator `-T`, whose Rayleigh quotient is `-T.rayleighQuotient`.
-/
theorem ofReal_iInf_rayleighQuotient_mem_spectrum [Nontrivial E] (hT : IsSelfAdjoint T) :
    ((⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) : 𝕜) ∈ spectrum 𝕜 T := by
  have : Nonempty { x : E // x ≠ 0 } := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  have h := hT.neg.ofReal_iSup_rayleighQuotient_mem_spectrum
  have heq : (⨆ x : { x : E // x ≠ 0 }, (-T).rayleighQuotient x)
      = -⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x := by
    simp_rw [ContinuousLinearMap.rayleighQuotient_neg_apply]
    exact ciSup_neg_eq_neg_ciInf (bddBelow_rayleighQuotient_subtype T)
  rw [heq, ofReal_neg, ← spectrum.neg_eq, Set.neg_mem_neg] at h
  exact h

/-- **`‖T‖ = max (|m|, |M|)`** for a self-adjoint operator on a nontrivial Hilbert space, `m` and
`M` being the infimum and supremum of its Rayleigh quotient over the nonzero vectors: the last
clause of [brezis2011functional] Proposition 6.9. Mathlib's
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` gives `‖T‖ = ⨆ x, |T.rayleighQuotient x|`,
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

/-- **A self-adjoint operator whose spectrum is contained in `{0}` is zero**
([brezis2011functional] Corollary 6.10, stated there with `σ(T) = {0}`; the inclusion covers
the trivial space, whose spectrum is empty): its spectral radius vanishes, and equals its norm by
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

/-- **Assembling a Hilbert basis of eigenvectors** — the last step of the proof of
[brezis2011functional] Theorem 6.11 (and of its compact normal analogue, Proposition 11.36): an
operator whose eigenspaces are pairwise orthogonal and span a dense subspace has a Hilbert basis
of eigenvectors, indexed by a set of vectors as in Mathlib's `exists_hilbertBasis`. The basis is
the union of Hilbert bases of the (closed, hence complete) eigenspaces: orthonormal by
`OrthogonalFamily.orthonormal_sigma_orthonormal`, and with dense span because a vector orthogonal
to it has zero projection onto every eigenspace. No separability is assumed. -/
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

/-- **The spectral theorem for compact self-adjoint operators, Hilbert-basis form**
([brezis2011functional] Theorem 6.11): a compact symmetric operator `T` on a Hilbert space has a
Hilbert basis of eigenvectors, indexed by a set of vectors `w` as in Mathlib's
`exists_hilbertBasis`, with real eigenvalues `μ : w → ℝ`. No injectivity, separability or
dimension hypothesis. The eigenspaces are orthogonal
(`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`) and span densely
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`); the eigenvalues are real
by `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/
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

/-- **The spectral theorem with an arbitrary index type**: a compact symmetric operator on a
Hilbert space `F : Type u` has a Hilbert basis of eigenvectors indexed by some type in the
universe of `F`, each with a real eigenvalue ([brezis2011functional] Theorem 6.11). The index
type is the set `w` of `ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors`. -/
theorem ContinuousLinearMap.IsSymmetric.exists_type_hilbertBasis_eigenvectors {T : F →L[𝕜] F}
    (hT : T.IsSymmetric) (hK : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι 𝕜 F), ∀ i, ∃ μ : ℝ, T (b i) = (μ : 𝕜) • b i := by
  obtain ⟨w, b, μ, -, hb⟩ := ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors hT hK
  exact ⟨w, b, fun i => ⟨μ i, hb i⟩⟩

end TypeIndexed
