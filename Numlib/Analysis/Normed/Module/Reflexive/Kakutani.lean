/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Reflexive`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Module.DualSeparable
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Module.WeakClosed

/-!
# Kakutani's theorem, and the lemmas of Helly and Goldstine

A normed space `E` is reflexive (`NormedSpace.IsReflexive 𝕜 E`, the parent module) iff its closed
unit ball is compact in the weak topology: this is Kakutani's theorem,
`NormedSpace.isReflexive_iff_isCompact_image_toWeakSpace_closedBall`. The forward direction is the
Banach–Alaoglu theorem in the bidual transported along the canonical embedding, all of which
Mathlib has (`NormedSpace.isCompact_closure_of_isBounded`, whose range condition is trivial when
the embedding is onto). The converse is **Goldstine's lemma** (`NormedSpace.goldstine`): the image
`J(B_E)` of the unit ball is weak-∗ dense in the unit ball of the bidual, so if it is also weak-∗
compact — hence closed — it is the whole bidual ball, and `J` is onto.

Goldstine's lemma is proved here by separation rather than through Helly's lemma: a point `ξ` of
the bidual ball outside the weak-∗ closure `K` of `J(B_E)` — a closed convex subset of the locally
convex space `WeakDual 𝕜 (StrongDual 𝕜 E)` — is strictly separated from `K` by an evaluation at
some `f ∈ E'` (`WeakDual.geometric_hahn_banach_closed_point`, the weak-∗ Hahn–Banach theorem
of `Numlib.Analysis.Normed.Module.WeakClosed`); then `re (f x) < α` on the ball gives `‖f‖ ≤ α`
(`ContinuousLinearMap.opNorm_le_of_forall_re_apply_lt`, the rotation argument), whereas
`α < re (ξ f) ≤ ‖ξ‖ ‖f‖ ≤ ‖f‖`. Helly's lemma (`NormedSpace.helly_iff`) is proved by the same
separation argument in `ι → 𝕜`; nothing here depends on it.

## Main statements

* `NormedSpace.goldstine`, `NormedSpace.denseRange_toWeakDual_inclusionInDoubleDual` — `J(B_E)`
  is weak-∗ dense in the bidual ball, and `J(E)` in the bidual.
* `NormedSpace.isCompact_image_toWeakSpace_closedBall`,
  `NormedSpace.isReflexive_of_isCompact_image_toWeakSpace_closedBall`,
  `NormedSpace.isReflexive_iff_isCompact_image_toWeakSpace_closedBall` — **Kakutani's theorem**,
  both directions and the equivalence, for any normed space (a space with weakly compact ball is
  reflexive, hence complete, so completeness need not be assumed).
* `Convex.isCompact_image_toWeakSpace_of_isBounded_of_isClosed` — a bounded closed convex subset
  of a reflexive space is weakly compact.
* `NormedSpace.instIsReflexiveStrongDual`, `NormedSpace.isReflexive_of_isReflexive_strongDual`,
  `NormedSpace.isReflexive_strongDual_iff` — a Banach space is reflexive iff its dual is; the
  backward direction is where completeness enters, through the norm closedness of `J(E)`
  (`NormedSpace.isClosed_range_inclusionInDoubleDual`).
* `NormedSpace.helly_iff` — **Helly's lemma**: `γ` is approximable by `(f i x)ᵢ` with `‖x‖ ≤ 1`
  iff `‖∑ β i γ i‖ ≤ ‖∑ β i • f i‖` for all `β`.

## Implementation notes

"Weakly compact" is `IsCompact (toWeakSpace 𝕜 E '' s)`; the bidual with its weak-∗ topology is
`WeakDual 𝕜 (StrongDual 𝕜 E)`, and the image of `E` in it is
`(StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) '' s`. Everything is over
`RCLike 𝕜`; the real convexity that the separation arguments need is obtained inside the proofs
by restricting scalars (`NormedSpace.restrictScalars ℝ 𝕜 E`), so no `[NormedSpace ℝ E]` hypothesis
appears except in the corollary about convex sets, where the convexity is a hypothesis.

## References

[brezis2011functional] §3.5: Lemma 3.3 (Helly), Lemma 3.4 (Goldstine), Theorem 3.17 (Kakutani),
Corollaries 3.21 and 3.22, Remarks 15 and 16, Problem 9.
-/

open Filter Topology Metric Set Function

section OpNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A functional whose real part is bounded by `u` on the closed unit ball has norm at most
`u`**: rotating `x` by the unimodular scalar `‖f x‖ / f x` makes `f x` a nonnegative real, so the
real-part bound is a modulus bound on the ball. This is the step that turns a Hahn–Banach
separation into a norm estimate. -/
theorem ContinuousLinearMap.opNorm_le_of_forall_re_apply_lt {f : StrongDual 𝕜 E} {u : ℝ}
    (h : ∀ x, ‖x‖ ≤ 1 → RCLike.re (f x) < u) : ‖f‖ ≤ u := by
  have hu : 0 < u := by simpa using h 0 (by simp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hu.le fun x hx => ?_
  rcases eq_or_ne (f x) 0 with h0 | h0
  · rw [h0, norm_zero]; exact hu.le
  set c : 𝕜 := (‖f x‖ : 𝕜) / f x with hc
  have hc1 : ‖c‖ = 1 := by
    rw [hc, norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 h0)]
  have hcx : ‖c • x‖ ≤ 1 := by rw [norm_smul, hc1, hx, one_mul]
  have := h (c • x) hcx
  rw [map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ h0, RCLike.ofReal_re] at this
  exact this.le

end OpNorm

namespace NormedSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
### The image of a Banach space in its bidual is norm closed
-/

section Range

variable [CompleteSpace E]

/-- **The image of a Banach space in its bidual is norm closed**: the canonical embedding is an
isometry from a complete space, hence a closed embedding. -/
theorem isClosed_range_inclusionInDoubleDual :
    IsClosed (Set.range (inclusionInDoubleDual 𝕜 E)) :=
  (inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isClosedEmbedding.isClosed_range

/-- `J(B_E)` is norm closed in the bidual of a Banach space, being the image of a closed set
under a closed embedding. It is therefore not norm dense in the bidual ball unless `E` is
reflexive, in contrast with its weak-∗ density (`goldstine`). -/
theorem isClosed_image_inclusionInDoubleDual_closedBall (r : ℝ) :
    IsClosed (inclusionInDoubleDual 𝕜 E '' closedBall 0 r) :=
  (inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isClosedEmbedding.isClosed_iff_image_isClosed.1
    isClosed_closedBall

end Range

/-!
### Helly's lemma
-/

/-- **Helly's lemma.** For finitely many functionals `f i` and scalars `γ i`, the following are
equivalent: for every `ε > 0` some `x` with `‖x‖ ≤ 1` has `‖f i x - γ i‖ < ε` for all `i`; and
`‖∑ β i * γ i‖ ≤ ‖∑ β i • f i‖` for every `β`.

The first implies the second by the triangle inequality. Conversely, the first condition says
that `γ` lies in the closure of the image of the unit ball under `x ↦ (f i x)ᵢ`; if it does not,
that closed convex subset of `ι → 𝕜` is separated from `γ` by a functional `z ↦ ∑ β i * z i`, and
the rotation argument `ContinuousLinearMap.opNorm_le_of_forall_re_apply_lt` gives
`‖∑ β i • f i‖ ≤ u < ‖∑ β i * γ i‖`, contradicting the second condition. No completeness is used,
and the complex case reads as the real one with moduli. -/
theorem helly_iff {ι : Type*} [Fintype ι] (f : ι → StrongDual 𝕜 E) (γ : ι → 𝕜) :
    (∀ ε > 0, ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ i, ‖f i x - γ i‖ < ε) ↔
      ∀ β : ι → 𝕜, ‖∑ i, β i * γ i‖ ≤ ‖∑ i, β i • f i‖ := by
  classical
  constructor
  · intro h β
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set S : ℝ := ∑ i, ‖β i‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
    obtain ⟨x, hx, hxε⟩ := h (ε / (S + 1)) (by positivity)
    have h1 : ‖(∑ i, β i • f i) x‖ ≤ ‖∑ i, β i • f i‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by
        simpa using mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have h2 : ‖∑ i, β i * (γ i - f i x)‖ ≤ ε := by
      calc ‖∑ i, β i * (γ i - f i x)‖ ≤ ∑ i, ‖β i * (γ i - f i x)‖ := norm_sum_le _ _
        _ ≤ ∑ i, ‖β i‖ * (ε / (S + 1)) := by
            gcongr with i
            rw [norm_mul, norm_sub_rev]
            exact mul_le_mul_of_nonneg_left (hxε i).le (norm_nonneg _)
        _ = S * (ε / (S + 1)) := by rw [← Finset.sum_mul]
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith
    calc ‖∑ i, β i * γ i‖ = ‖(∑ i, β i • f i) x + ∑ i, β i * (γ i - f i x)‖ := by
          congr 1
          simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, mul_sub]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ‖(∑ i, β i • f i) x‖ + ‖∑ i, β i * (γ i - f i x)‖ := norm_add_le _ _
      _ ≤ ‖∑ i, β i • f i‖ + ε := add_le_add h1 h2
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hall⟩ := hcon
    -- `γ` is not in the closure of the image of the unit ball under `x ↦ (f i x)ᵢ`
    set φ : E →L[𝕜] (ι → 𝕜) := ContinuousLinearMap.pi f with hφ
    have hγ : γ ∉ closure (φ '' closedBall (0 : E) 1) := by
      intro hγ
      obtain ⟨z, hz, hzγ⟩ := Metric.mem_closure_iff.1 hγ ε hε
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨i, hi⟩ := hall x (mem_closedBall_zero_iff.1 hx)
      rw [dist_comm, dist_eq_norm, pi_norm_lt_iff hε] at hzγ
      have := hzγ i
      simp only [Pi.sub_apply, hφ, ContinuousLinearMap.pi_apply] at this
      linarith
    -- separate `γ` from this closed convex set
    let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    have : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hconv : Convex ℝ (φ '' closedBall (0 : E) 1) :=
      (convex_closedBall (0 : E) 1).linear_image (φ.toLinearMap.restrictScalars ℝ)
    obtain ⟨g, u, hgu, huγ⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hconv.closure isClosed_closure hγ
    -- the separating functional is `z ↦ ∑ β i * z i`
    set β : ι → 𝕜 := fun i => g (fun j => if i = j then 1 else 0) with hβ
    have hg : ∀ z : ι → 𝕜, g z = ∑ i, β i * z i := fun z => by
      rw [← ContinuousLinearMap.coe_coe g, LinearMap.pi_apply_eq_sum_univ]
      simp only [smul_eq_mul, hβ, ContinuousLinearMap.coe_coe, mul_comm]
    have hnorm : ‖∑ i, β i • f i‖ ≤ u := by
      refine ContinuousLinearMap.opNorm_le_of_forall_re_apply_lt fun x hx => ?_
      have := hgu (φ x) (subset_closure ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
      rw [hg] at this
      simpa [hφ] using this
    have hγ' : u < ‖∑ i, β i * γ i‖ := by
      rw [← hg]
      exact huγ.trans_le (RCLike.re_le_norm _)
    linarith [h β]

/-!
### Goldstine's lemma
-/

/-- **Goldstine's lemma**: the image `J(B_E)` of the closed unit ball is weak-∗ dense in the
closed unit ball of the bidual, `closure (J '' B_E) = B_{E''}` in `WeakDual 𝕜 (StrongDual 𝕜 E)`.

`⊆` holds because the bidual ball is weak-∗ closed and `J` is an isometry. For `⊇`, a `ξ` of norm
at most `1` outside the closed convex set `K = closure (J '' B_E)` is separated from `K` by an
evaluation at some `f ∈ E'` (`WeakDual.geometric_hahn_banach_closed_point`): `re (η f) < α` on
`K` and `α < re (ξ f)`. The first gives `re (f x) < α` on the ball, hence `‖f‖ ≤ α` by
`ContinuousLinearMap.opNorm_le_of_forall_re_apply_lt`; but `α < re (ξ f) ≤ ‖ξ‖ ‖f‖ ≤ ‖f‖`. No
completeness is needed. -/
theorem goldstine :
    closure ((StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E) '' closedBall (0 : E) 1) =
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 := by
  set J : E → WeakDual 𝕜 (StrongDual 𝕜 E) := StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E
    with hJ
  have hJnorm : ∀ x : E, ‖WeakDual.toStrongDual (J x)‖ = ‖x‖ := fun x =>
    (inclusionInDoubleDualLi 𝕜).norm_map x
  refine le_antisymm (closure_minimal ?_ (WeakDual.isClosed_closedBall 0 1)) fun ξ hξ => ?_
  · rintro _ ⟨x, hx, rfl⟩
    simp only [mem_preimage, mem_closedBall_zero_iff, hJnorm]
    exact mem_closedBall_zero_iff.1 hx
  by_contra hcl
  -- the weak-∗ closure of `J(B_E)` is closed and convex
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hconv : Convex ℝ (J '' closedBall (0 : E) 1) := by
    intro a ha b hb s t hs ht hst
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    refine ⟨s • x + t • y, convex_closedBall (0 : E) 1 hx hy hs ht hst, ?_⟩
    simp only [hJ, comp_apply, map_add]
    rw [← algebraMap_smul 𝕜 s x, ← algebraMap_smul 𝕜 t y, map_smul, map_smul, map_smul, map_smul,
      algebraMap_smul, algebraMap_smul]
  obtain ⟨f, α, hα, hξα⟩ :=
    WeakDual.geometric_hahn_banach_closed_point hconv.closure isClosed_closure hcl
  have hfα : ‖f‖ ≤ α := ContinuousLinearMap.opNorm_le_of_forall_re_apply_lt fun x hx =>
    hα (J x) (subset_closure ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
  have hξ1 : ‖WeakDual.toStrongDual ξ‖ ≤ 1 := mem_closedBall_zero_iff.1 hξ
  have : RCLike.re (ξ f) ≤ α := by
    calc RCLike.re (ξ f) ≤ ‖ξ f‖ := RCLike.re_le_norm _
      _ = ‖WeakDual.toStrongDual ξ f‖ := rfl
      _ ≤ ‖WeakDual.toStrongDual ξ‖ * ‖f‖ := (WeakDual.toStrongDual ξ).le_opNorm f
      _ ≤ 1 * α := by gcongr
      _ = α := one_mul α
  linarith

/-- **`J(E)` is weak-∗ dense in the bidual**: every `ξ` is `r • η` with `η` in the bidual ball,
where Goldstine's lemma applies, and scaling is a weak-∗ homeomorphism preserving the range. -/
theorem denseRange_toWeakDual_inclusionInDoubleDual :
    DenseRange (StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E) := by
  intro ξ
  set J : E → WeakDual 𝕜 (StrongDual 𝕜 E) := StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E
    with hJ
  set r : ℝ := ‖WeakDual.toStrongDual ξ‖ + 1 with hr
  have hr0 : 0 < r := by positivity
  have hmem : ((r⁻¹ : ℝ) : 𝕜) • ξ ∈ closure (J '' closedBall (0 : E) 1) := by
    rw [goldstine]
    simp only [mem_preimage, map_smul, mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.2 hr0)]
    rw [inv_mul_le_iff₀ hr0, mul_one]
    linarith
  have hsmul : ξ = ((r : ℝ) : 𝕜) • (((r⁻¹ : ℝ) : 𝕜) • ξ) := by
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hr0.ne', RCLike.ofReal_one, one_smul]
  rw [hsmul]
  have hcont : Continuous fun η : WeakDual 𝕜 (StrongDual 𝕜 E) => ((r : ℝ) : 𝕜) • η :=
    continuous_const_smul _
  have h1 := image_closure_subset_closure_image hcont ⟨_, hmem, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  exact ⟨((r : ℝ) : 𝕜) • x, by rw [hJ, comp_apply, map_smul, map_smul]; rfl⟩

/-!
### Kakutani's theorem
-/

/-- **Kakutani, forward direction: the closed balls of a reflexive space are weakly compact.**
Mathlib's `isCompact_closure_of_isBounded` gives weak compactness of the closure of a bounded set
whose weak-∗ closure in the bidual lies in the range of the embedding; the range is everything by
reflexivity, and the ball is weakly closed (`isClosed_image_toWeakSpace_closedBall`). -/
theorem isCompact_image_toWeakSpace_closedBall [IsReflexive 𝕜 E] (r : ℝ) :
    IsCompact (toWeakSpace 𝕜 E '' closedBall (0 : E) r) := by
  have h := isCompact_closure_of_isBounded 𝕜 E (toWeakSpace 𝕜 E '' closedBall (0 : E) r)
    (by rw [Set.preimage_image_eq _ (toWeakSpace 𝕜 E).injective]; exact isBounded_closedBall)
    (by
      rw [Set.range_eq_univ.2]
      · exact subset_univ _
      intro ξ
      obtain ⟨x, hx⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := E)
        (WeakDual.toStrongDual ξ)
      exact ⟨toWeakSpace 𝕜 E x, by
        rw [← (WeakDual.toStrongDual (𝕜 := 𝕜) (E := StrongDual 𝕜 E)).injective.eq_iff]
        exact hx⟩)
  rwa [(isClosed_image_toWeakSpace_closedBall 0 r).closure_eq] at h

/-- **Kakutani, converse direction: a normed space whose closed unit ball is weakly compact is
reflexive.** The embedding of the weak space into the weak-∗ bidual is continuous, so `J(B_E)`
is weak-∗ compact, hence closed, hence equal to its weak-∗ closure, which is the bidual ball by
Goldstine's lemma; scaling then puts every element of the bidual in the range of `J`. No
completeness is assumed (it follows). -/
theorem isReflexive_of_isCompact_image_toWeakSpace_closedBall
    (h : IsCompact (toWeakSpace 𝕜 E '' closedBall (0 : E) 1)) : IsReflexive 𝕜 E := by
  set J : E → WeakDual 𝕜 (StrongDual 𝕜 E) := StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E
    with hJ
  have hcpt : IsCompact (J '' closedBall (0 : E) 1) := by
    have := h.image (inclusionInDoubleDualWeak 𝕜 E).continuous
    rwa [Set.image_image] at this
  have hball : WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 ⊆
      J '' closedBall (0 : E) 1 := by
    rw [← goldstine, hcpt.isClosed.closure_eq]
  refine ⟨fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact ⟨0, map_zero _⟩
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hmem : StrongDual.toWeakDual (((‖ξ‖⁻¹ : ℝ) : 𝕜) • ξ) ∈
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 := by
    simp only [mem_preimage, StrongDual.toStrongDual_toWeakDual, mem_closedBall_zero_iff,
      norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hξ0), inv_mul_cancel₀ hξ0.ne', le_refl]
  obtain ⟨x, -, hx⟩ := hball hmem
  refine ⟨((‖ξ‖ : ℝ) : 𝕜) • x, ?_⟩
  have hx' : inclusionInDoubleDual 𝕜 E x = ((‖ξ‖⁻¹ : ℝ) : 𝕜) • ξ :=
    (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 E)).injective hx
  rw [map_smul, hx', smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hξ0.ne', RCLike.ofReal_one,
    one_smul]

/-- **Kakutani's theorem**: a normed space is reflexive iff its closed unit ball is weakly
compact. -/
theorem isReflexive_iff_isCompact_image_toWeakSpace_closedBall :
    IsReflexive 𝕜 E ↔ IsCompact (toWeakSpace 𝕜 E '' closedBall (0 : E) 1) :=
  ⟨fun _ => isCompact_image_toWeakSpace_closedBall 1,
    isReflexive_of_isCompact_image_toWeakSpace_closedBall⟩

/-- **A bounded closed convex subset of a reflexive space is weakly compact**: it is weakly
closed by Mazur's theorem and contained in a weakly compact ball. -/
theorem _root_.Convex.isCompact_image_toWeakSpace_of_isBounded_of_isClosed [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] [IsReflexive 𝕜 E] {K : Set E} (hK : Convex ℝ K)
    (hb : Bornology.IsBounded K) (hc : IsClosed K) : IsCompact (toWeakSpace 𝕜 E '' K) := by
  obtain ⟨m, hm⟩ := hb.subset_closedBall 0
  exact (isCompact_image_toWeakSpace_closedBall m).of_isClosed_subset
    (hK.isClosed_image_toWeakSpace_iff.2 hc) (image_mono hm)

/-!
### Reflexivity of the dual
-/

/-- **The dual of a reflexive space is reflexive.** A functional `φ` on `E''` restricts along `J`
to `f := φ ∘ J ∈ E'`, and since every `ξ ∈ E''` is some `J x`, `φ ξ = f x = ξ f`: `φ` is the
evaluation at `f`. -/
instance instIsReflexiveStrongDual [IsReflexive 𝕜 E] : IsReflexive 𝕜 (StrongDual 𝕜 E) := by
  refine ⟨fun φ => ⟨φ.comp (inclusionInDoubleDual 𝕜 E), ?_⟩⟩
  ext ξ
  obtain ⟨x, rfl⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := E) ξ
  rfl

/-- **A Banach space whose dual is reflexive is reflexive.** The bidual is then reflexive, `J(E)`
is a closed subspace of it (this is where completeness enters), hence reflexive, and `E` is
isometrically isomorphic to `J(E)`. -/
theorem isReflexive_of_isReflexive_strongDual [CompleteSpace E]
    [IsReflexive 𝕜 (StrongDual 𝕜 E)] : IsReflexive 𝕜 E := by
  have : IsReflexive 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) := instIsReflexiveStrongDual
  set M : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    LinearMap.range (inclusionInDoubleDualLi 𝕜 (E := E)).toLinearMap with hM
  have hMc : IsClosed (M : Set (StrongDual 𝕜 (StrongDual 𝕜 E))) := by
    rw [hM, LinearMap.coe_range]
    exact isClosed_range_inclusionInDoubleDual
  have : IsReflexive 𝕜 M := isReflexive_of_isClosed M hMc
  exact (isReflexive_congr
    (inclusionInDoubleDualLi 𝕜 (E := E)).equivRange.toContinuousLinearEquiv).2 this

/-- **A Banach space is reflexive iff its dual is.** -/
theorem isReflexive_strongDual_iff [CompleteSpace E] :
    IsReflexive 𝕜 (StrongDual 𝕜 E) ↔ IsReflexive 𝕜 E :=
  ⟨fun _ => isReflexive_of_isReflexive_strongDual, fun _ => instIsReflexiveStrongDual⟩

end NormedSpace
