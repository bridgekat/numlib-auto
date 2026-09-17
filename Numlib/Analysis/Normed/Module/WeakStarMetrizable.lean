/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.WeakDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani

/-!
# Metrizability of the weak and weak-∗ topologies

On bounded sets the weak topologies are metrizable exactly when the right space is separable,
and on the whole space they are never metrizable in infinite dimension.

## Main statements

* `WeakDual.metrizableSpace_closedBall` and `separableSpace_of_metrizableSpace_weakDual_closedBall`
  — **the closed unit ball of `E'` is weak-∗ metrizable iff `E` is separable**. The forward half
  is Mathlib's `WeakDual.metrizable_of_isCompact` on the Banach–Alaoglu ball; for the converse, a
  countable neighbourhood basis of `0` in the ball is cut out by countably many points of `E`, and
  a functional vanishing on them lies in every neighbourhood of `0`, so their closed span is
  everything by Hahn–Banach (`Submodule.exists_dual_eq_zero_of_notMem`).
* `WeakSpace.metrizableSpace_image_closedBall` and
  `separableSpace_strongDual_of_metrizableSpace_weakSpace_closedBall` — **the closed unit ball
  of `E` is weakly metrizable iff `E'` is separable**. The forward half restricts the embedding of
  the weak space into the weak-∗ bidual to the balls; the converse is the same argument with the
  roles exchanged, except that the functional Hahn–Banach produces lives in `E''`, and Goldstine's
  lemma (`NormedSpace.goldstine`) brings it back to a point of the ball of `E`.
* `not_firstCountableTopology_weakSpace`, `not_metrizableSpace_weakSpace`,
  `not_firstCountableTopology_weakDual`, `not_metrizableSpace_weakDual` — **in infinite dimension
  neither weak topology is metrizable on the whole space, nor even first countable.** A countable
  neighbourhood basis of `0` would make every functional (resp. every evaluation at a point of
  `E`) continuous for the topology induced by countably many functionals (resp. points), hence a
  finite linear combination of them (`LinearMap.mem_span_iff_continuous`), so the dual (resp.
  `E`) would be spanned by a countable set; by Baire, a Banach space spanned by a countable set is
  finite-dimensional (`FiniteDimensional.of_span_eq_top_of_countable`). The weak case applies
  Baire in the complete dual and needs no completeness of `E`; the weak-∗ case applies it in `E`.

## Implementation notes

The balls are `WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r : Set (WeakDual 𝕜 E)` (Mathlib's
spelling in `WeakDual.isCompact_closedBall`) and `toWeakSpace 𝕜 E '' Metric.closedBall 0 r :
Set (WeakSpace 𝕜 E)`; "metrizable" is `TopologicalSpace.MetrizableSpace` of the subtype. The
neighbourhood-basis extraction is done once, for the filter `𝓝[S] 0` of an arbitrary subset of
`WeakBilin B` (`WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhdsWithin`), because stating
it for the subtype would tie it to the subtype's topology instance, which the `def`s `WeakDual`
and `WeakSpace` hide from instance search.

## References

[brezis2011functional] Theorems 3.28 and 3.29, Exercise 3.24, Remarks 3 and 20, Exercise 3.8.
-/

open Filter Topology Metric Set Function TopologicalSpace

/-!
### Countable neighbourhood bases of `0` in a weak topology
-/

section Basic

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- If `𝓝 0` in `WeakBilin B` is countably generated, a sequence of basic sets
`{x | ∀ y ∈ Φ n, ‖B x y‖ < ε n}` is a neighbourhood basis of `0`. -/
theorem WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhds_zero
    {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (h : (𝓝 (0 : WeakBilin B)).IsCountablyGenerated) :
    ∃ (Φ : ℕ → Finset F) (ε : ℕ → ℝ), (∀ n, 0 < ε n) ∧
      ∀ U ∈ 𝓝 (0 : WeakBilin B), ∃ n, {x : WeakBilin B | ∀ y ∈ Φ n, ‖B x y‖ < ε n} ⊆ U := by
  obtain ⟨u, hu⟩ := (𝓝 (0 : WeakBilin B)).exists_antitone_basis
  have hV : ∀ n, ∃ (Φ : Finset F) (ε : ℝ), 0 < ε ∧
      {x : WeakBilin B | ∀ y ∈ Φ, ‖B x y‖ < ε} ⊆ u n := fun n =>
    WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero (hu.mem n)
  choose Φ ε hε hΦ using hV
  refine ⟨Φ, ε, hε, fun U hU => ?_⟩
  obtain ⟨n, hn⟩ := hu.mem_iff.1 hU
  exact ⟨n, (hΦ n).trans hn⟩

/-- If the filter `𝓝[S] 0` of neighbourhoods of `0` within a subset `S` of `WeakBilin B` is
countably generated (as it is when `S` is first countable, e.g. metrizable, in the subspace
topology), a sequence of basic sets intersected with `S` is a basis of it. -/
theorem WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhdsWithin
    {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {S : Set (WeakBilin B)}
    (h : (𝓝[S] (0 : WeakBilin B)).IsCountablyGenerated) :
    ∃ (Φ : ℕ → Finset F) (ε : ℕ → ℝ), (∀ n, 0 < ε n) ∧
      ∀ U ∈ 𝓝[S] (0 : WeakBilin B), ∃ n,
        {x : WeakBilin B | x ∈ S ∧ ∀ y ∈ Φ n, ‖B x y‖ < ε n} ⊆ U := by
  obtain ⟨u, hu⟩ := (𝓝[S] (0 : WeakBilin B)).exists_antitone_basis
  have hV : ∀ n, ∃ (Φ : Finset F) (ε : ℝ), 0 < ε ∧
      {x : WeakBilin B | x ∈ S ∧ ∀ y ∈ Φ, ‖B x y‖ < ε} ⊆ u n := by
    intro n
    obtain ⟨V, hV, hVu⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hu.mem n)
    obtain ⟨Φ, ε, hε, hΦ⟩ := WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero hV
    exact ⟨Φ, ε, hε, fun x hx => hVu ⟨hΦ hx.2, hx.1⟩⟩
  choose Φ ε hε hΦ using hV
  refine ⟨Φ, ε, hε, fun U hU => ?_⟩
  obtain ⟨n, hn⟩ := hu.mem_iff.1 hU
  exact ⟨n, (hΦ n).trans hn⟩

/-- **A linear functional dominated near `0` by finitely many members of a family `g` of linear
functionals is continuous for the topology induced by the family**, hence (by Mathlib's
`LinearMap.mem_span_iff_continuous`) a linear combination of finitely many of them. -/
theorem LinearMap.continuous_iInf_induced_of_forall_exists_finset {ι : Type*}
    (g : ι → E →ₗ[𝕜] 𝕜) (φ : E →ₗ[𝕜] 𝕜)
    (h : ∀ δ > 0, ∃ (s : Finset ι) (ε : ℝ), 0 < ε ∧ ∀ x, (∀ i ∈ s, ‖g i x‖ < ε) → ‖φ x‖ < δ) :
    Continuous[⨅ i, induced (g i) inferInstance, inferInstance] φ := by
  let t : TopologicalSpace E := ⨅ i, induced (g i) inferInstance
  have : IsTopologicalAddGroup E :=
    isTopologicalAddGroup_iInf fun _ => isTopologicalAddGroup_induced _
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨s, ε, hε, hs⟩ := h δ hδ
  have hbasic : {x : E | ∀ i ∈ s, ‖g i x‖ < ε} ∈ 𝓝 (0 : E) := by
    have : {x : E | ∀ i ∈ s, ‖g i x‖ < ε} = ⋂ i ∈ s, {x : E | ‖g i x‖ < ε} := by
      ext x; simp
    rw [this]
    refine (Filter.biInter_finset_mem _).2 fun i _ => ?_
    have hc : Continuous (g i) := continuous_iInf_dom continuous_induced_dom
    exact IsOpen.mem_nhds (isOpen_lt hc.norm continuous_const) (by simp [hε])
  filter_upwards [hbasic] with x hx
  rw [dist_zero_right]
  exact hs x hx

end Basic

/-!
### Baire: a Banach space spanned by a countable set is finite-dimensional
-/

section Span

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A module spanned by a sequence is the union of the spans of the initial segments of the
sequence. -/
theorem Submodule.iUnion_coe_span_image_Iic_eq_univ {g : ℕ → M}
    (h : Submodule.span R (Set.range g) = ⊤) :
    ⋃ n, ((Submodule.span R (g '' Set.Iic n) : Submodule R M) : Set M) = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have hx : x ∈ Submodule.span R (Set.range g) := h ▸ Submodule.mem_top
  have hrange : Set.range g = ⋃ n, g '' Set.Iic n := by
    ext y
    simp only [mem_range, mem_iUnion, mem_image, mem_Iic]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  rw [hrange, Submodule.span_iUnion] at hx
  have hdir : Directed (· ≤ ·) fun n => Submodule.span R (g '' Set.Iic n) :=
    (Monotone.directed_le fun m n hmn => Submodule.span_mono (image_mono (Iic_subset_Iic.2 hmn)))
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hx
  exact mem_iUnion.2 ⟨n, hn⟩

end Span

section Baire

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **A Banach space that is a countable union of finite-dimensional subspaces is
finite-dimensional**: finite-dimensional subspaces are closed, so by Baire one of them has
nonempty interior, and a subspace with nonempty interior is everything. -/
theorem FiniteDimensional.of_iUnion_eq_univ {ι : Type*} [Countable ι] (p : ι → Submodule 𝕜 E)
    (hp : ∀ i, FiniteDimensional 𝕜 (p i)) (h : ⋃ i, (p i : Set E) = univ) :
    FiniteDimensional 𝕜 E := by
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed
    (fun i => (p i).closed_of_finiteDimensional) h
  have htop : p i = ⊤ := (p i).eq_top_of_nonempty_interior' hi
  have := hp i
  rw [htop] at this
  exact Module.Finite.equiv (Submodule.topEquiv (R := 𝕜) (M := E))

/-- **A Banach space spanned by a sequence is finite-dimensional**: it is the union of the
finite-dimensional spans of the initial segments. -/
theorem FiniteDimensional.of_span_range_eq_top {g : ℕ → E}
    (h : Submodule.span 𝕜 (Set.range g) = ⊤) : FiniteDimensional 𝕜 E :=
  FiniteDimensional.of_iUnion_eq_univ (fun n => Submodule.span 𝕜 (g '' Set.Iic n))
    (fun n => FiniteDimensional.span_of_finite 𝕜 ((Set.finite_Iic n).image g))
    (Submodule.iUnion_coe_span_image_Iic_eq_univ h)

/-- **A Banach space spanned by a countable set is finite-dimensional.** -/
theorem FiniteDimensional.of_span_eq_top_of_countable {D : Set E} (hD : D.Countable)
    (h : Submodule.span 𝕜 D = ⊤) : FiniteDimensional 𝕜 E := by
  obtain ⟨g, hg⟩ := (hD.insert 0).exists_eq_range ⟨0, mem_insert 0 _⟩
  refine FiniteDimensional.of_span_range_eq_top (g := g) ?_
  rw [← hg, Submodule.span_insert_zero, h]

end Baire

/-!
### Metrizability of the balls
-/

section Metrizable

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The closed balls of the dual of a separable space are weak-∗ metrizable**: they are
weak-∗ compact (Banach–Alaoglu) and a compact subset of the weak-∗ dual of a separable space is
metrizable (`WeakDual.metrizable_of_isCompact`). -/
theorem WeakDual.metrizableSpace_closedBall [SeparableSpace E] (r : ℝ) :
    MetrizableSpace (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) :=
  WeakDual.metrizable_of_isCompact 𝕜 E _ (WeakDual.isCompact_closedBall 0 r)

/-- **If the closed unit ball of the dual is weak-∗ metrizable, the space is separable.** A
countable neighbourhood basis of `0` in the ball is cut out by countably many points of `E`; a
functional of norm `1` vanishing on all of them would lie in every neighbourhood of `0` within
the ball, hence be `0`, so the closed span of these points is everything. No completeness is
needed. -/
theorem separableSpace_of_metrizableSpace_weakDual_closedBall
    (h : MetrizableSpace (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)) :
    SeparableSpace E := by
  set S : Set (WeakDual 𝕜 E) := WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1
    with hS
  have h0 : (0 : WeakDual 𝕜 E) ∈ S := by simp [hS]
  have hcg : (𝓝[S] (0 : WeakDual 𝕜 E)).IsCountablyGenerated := by
    have := h
    rw [← map_nhds_subtype_val (⟨0, h0⟩ : S)]
    infer_instance
  obtain ⟨Φ, ε, hε, hΦ⟩ :=
    WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhdsWithin (B := topDualPairing 𝕜 E) hcg
  set D : Set E := ⋃ n, (Φ n : Set E) with hD
  have hDc : D.Countable := Set.countable_iUnion fun n => (Φ n).countable_toSet
  -- the closed span of `D` is everything
  have htop : (Submodule.span 𝕜 D).topologicalClosure = ⊤ := by
    by_contra hne
    obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨f, hf1, hf0, -⟩ :=
      (Submodule.span 𝕜 D).topologicalClosure.exists_dual_eq_zero_of_notMem
        (Submodule.isClosed_topologicalClosure _) hz
    have hfS : StrongDual.toWeakDual f ∈ S := by simp [hS, hf1]
    -- `f` lies in every neighbourhood of `0` within the ball, so `f = 0`
    have hspec : StrongDual.toWeakDual f ⤳ (0 : WeakDual 𝕜 E) := by
      rw [specializes_iff_pure]
      refine le_trans ?_ (nhdsWithin_le_nhds (s := S))
      intro U hU
      obtain ⟨n, hn⟩ := hΦ U hU
      refine hn ⟨hfS, fun y hy => ?_⟩
      have : f y = 0 := hf0 y (Submodule.le_topologicalClosure _ (Submodule.subset_span
        (mem_iUnion.2 ⟨n, hy⟩)))
      change ‖f y‖ < ε n
      rw [this, norm_zero]
      exact hε n
    have : f = 0 :=
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)).injective (specializes_iff_eq.1 hspec)
    rw [this, norm_zero] at hf1
    exact zero_ne_one hf1
  rw [← isSeparable_univ_iff, ← Submodule.top_coe (R := 𝕜) (M := E), ← htop,
    Submodule.topologicalClosure_coe]
  exact hDc.isSeparable.span.closure

/-- **The closed balls of a space with separable dual are weakly metrizable**: the embedding of
the weak space into the weak-∗ bidual (`NormedSpace.isEmbedding_inclusionInDoubleDualWeak`) maps
a ball of `E` into a ball of `E''`, which is metrizable by `WeakDual.metrizableSpace_closedBall`
applied to the separable `E'`. -/
theorem WeakSpace.metrizableSpace_image_closedBall [SeparableSpace (StrongDual 𝕜 E)] (r : ℝ) :
    MetrizableSpace (toWeakSpace 𝕜 E '' closedBall (0 : E) r) := by
  have hT := WeakDual.metrizableSpace_closedBall (𝕜 := 𝕜) (E := StrongDual 𝕜 E) r
  set e := NormedSpace.inclusionInDoubleDualWeak 𝕜 E
  have hmaps : ∀ x : toWeakSpace 𝕜 E '' closedBall (0 : E) r, e x ∈
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) r := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    simp only [mem_preimage, mem_closedBall_zero_iff] at hx ⊢
    refine le_trans (le_of_eq ?_) hx
    exact (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x
  exact ((NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 E).comp
    Topology.IsEmbedding.subtypeVal).codRestrict _ hmaps |>.metrizableSpace

/-- **If the closed unit ball is weakly metrizable, the dual is separable.** A countable
neighbourhood basis of `0` in the ball is cut out by countably many functionals; if their closed
span were not everything, Hahn–Banach would give `ξ ∈ E''` of norm `1` vanishing on it and some
`f₁` with `ξ f₁ = 2`, and Goldstine's lemma would give `x₁` in the ball of `E` with `f x₁ ≈ ξ f = 0`
on the finitely many functionals of one basic neighbourhood and `f₁ x₁ ≈ ξ f₁ = 2` — but the
basic neighbourhood sits inside `{x | ‖f₁ x‖ < 1/2}`. No completeness is needed. -/
theorem separableSpace_strongDual_of_metrizableSpace_weakSpace_closedBall
    (h : MetrizableSpace (toWeakSpace 𝕜 E '' closedBall (0 : E) 1)) :
    SeparableSpace (StrongDual 𝕜 E) := by
  set S : Set (WeakSpace 𝕜 E) := toWeakSpace 𝕜 E '' closedBall (0 : E) 1 with hS
  have h0 : (0 : WeakSpace 𝕜 E) ∈ S := ⟨0, by simp, map_zero _⟩
  have hcg : (𝓝[S] (0 : WeakSpace 𝕜 E)).IsCountablyGenerated := by
    have := h
    rw [← map_nhds_subtype_val (⟨0, h0⟩ : S)]
    infer_instance
  obtain ⟨Φ, ε, hε, hΦ⟩ := WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhdsWithin
    (B := (topDualPairing 𝕜 E).flip) hcg
  set D : Set (StrongDual 𝕜 E) := ⋃ n, (Φ n : Set (StrongDual 𝕜 E)) with hD
  have hDc : D.Countable := Set.countable_iUnion fun n => (Φ n).countable_toSet
  have htop : (Submodule.span 𝕜 D).topologicalClosure = ⊤ := by
    by_contra hne
    obtain ⟨f₀, -, hf₀⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨ξ, hξ1, hξ0, hξf₀⟩ :=
      (Submodule.span 𝕜 D).topologicalClosure.exists_dual_eq_zero_of_notMem
        (Submodule.isClosed_topologicalClosure _) hf₀
    -- normalize `f₀` so that `ξ f₁ = 2`
    set f₁ : StrongDual 𝕜 E := (2 / ξ f₀) • f₀ with hf₁
    have hξf₁ : ξ f₁ = 2 := by
      rw [hf₁, map_smul, smul_eq_mul, div_mul_cancel₀ _ hξf₀]
    -- the weak neighbourhood `W` of `0` where `‖f₁ x‖ < 1/2`, and a basic set inside it
    have hW : {x : WeakSpace 𝕜 E | ‖f₁ ((toWeakSpace 𝕜 E).symm x)‖ < 1 / 2} ∈
        𝓝[S] (0 : WeakSpace 𝕜 E) := by
      refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ (by simp))
      exact isOpen_lt (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f₁).norm
        continuous_const
    obtain ⟨n₀, hn₀⟩ := hΦ _ hW
    -- Goldstine: a point `J x₁` of `J(B_E)` close to `ξ` on `Φ n₀ ∪ {f₁}`
    have hgold : StrongDual.toWeakDual ξ ∈ closure
        ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
          closedBall (0 : E) 1) := by
      rw [NormedSpace.goldstine]
      simp [hξ1]
    have hN : (⋂ f ∈ Φ n₀, {η : WeakDual 𝕜 (StrongDual 𝕜 E) | ‖η f - ξ f‖ < ε n₀}) ∩
        {η : WeakDual 𝕜 (StrongDual 𝕜 E) | ‖η f₁ - ξ f₁‖ < 1 / 2} ∈
          𝓝 (StrongDual.toWeakDual ξ) := by
      refine IsOpen.mem_nhds ?_ ⟨Set.mem_iInter₂.2 fun f _ => by simp [hε n₀], by simp⟩
      refine IsOpen.inter ?_ ?_
      · refine isOpen_biInter_finset fun f _ => ?_
        exact isOpen_lt ((WeakDual.eval_continuous f).sub continuous_const).norm continuous_const
      · exact isOpen_lt ((WeakDual.eval_continuous f₁).sub continuous_const).norm continuous_const
    obtain ⟨_, ⟨hN1, hN2⟩, ⟨x₁, hx₁, rfl⟩⟩ := mem_closure_iff_nhds.1 hgold _ hN
    rw [Set.mem_iInter₂] at hN1
    simp only [comp_apply, StrongDual.toWeakDual_apply, NormedSpace.dual_def,
      mem_ofPred_eq] at hN1 hN2
    -- `x₁` is in the basic neighbourhood, hence in `W`
    have hmem := hn₀ ⟨⟨x₁, hx₁, rfl⟩, fun f hf => by
      have hξf : ξ f = 0 := hξ0 f (Submodule.le_topologicalClosure _ (Submodule.subset_span
        (mem_iUnion.2 ⟨n₀, hf⟩)))
      have := hN1 f hf
      rw [hξf, sub_zero] at this
      exact this⟩
    have hmem' : ‖f₁ x₁‖ < 1 / 2 := hmem
    -- but `f₁ x₁` is close to `ξ f₁ = 2`
    rw [hξf₁] at hN2
    have := norm_sub_norm_le (2 : 𝕜) (f₁ x₁)
    rw [RCLike.norm_ofNat, norm_sub_rev] at this
    linarith
  rw [← isSeparable_univ_iff, ← Submodule.top_coe (R := 𝕜) (M := StrongDual 𝕜 E), ← htop,
    Submodule.topologicalClosure_coe]
  exact hDc.isSeparable.span.closure

end Metrizable

/-!
### Non-metrizability on the whole space
-/

section NotMetrizable

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The weak topology of an infinite-dimensional normed space is not first countable.** A
countable neighbourhood basis of `0` is cut out by a countable set `D` of functionals; every
functional is then continuous for the topology induced by `D`, hence in the span of `D`
(`LinearMap.mem_span_iff_continuous`), so the complete dual is spanned by a countable set and is
finite-dimensional by Baire; then so is `E`. No completeness of `E` is needed. -/
theorem not_firstCountableTopology_weakSpace (h : ¬ FiniteDimensional 𝕜 E) :
    ¬ FirstCountableTopology (WeakSpace 𝕜 E) := by
  classical
  intro hfc
  have hcg : (𝓝 (0 : WeakSpace 𝕜 E)).IsCountablyGenerated := inferInstance
  obtain ⟨Φ, ε, hε, hΦ⟩ := WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhds_zero
    (B := (topDualPairing 𝕜 E).flip) hcg
  -- the countable set of functionals occurring in the basic sets
  set D : Set (StrongDual 𝕜 E) := ⋃ n, (Φ n : Set (StrongDual 𝕜 E)) with hD
  have hDc : D.Countable := Set.countable_iUnion fun n => (Φ n).countable_toSet
  -- every functional is continuous for the topology induced by `D`, hence in its span
  have hspan : Submodule.span 𝕜 D = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    have hcont : Continuous[⨅ y : D, induced ((y : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜) inferInstance,
        inferInstance] (f : E →ₗ[𝕜] 𝕜) := by
      refine LinearMap.continuous_iInf_induced_of_forall_exists_finset _ _ fun δ hδ => ?_
      have hw : {x : WeakSpace 𝕜 E | ‖f ((toWeakSpace 𝕜 E).symm x)‖ < δ} ∈
          𝓝 (0 : WeakSpace 𝕜 E) :=
        IsOpen.mem_nhds (isOpen_lt (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).norm
          continuous_const) (by simp [hδ])
      obtain ⟨n, hn⟩ := hΦ _ hw
      refine ⟨(Φ n).subtype (· ∈ D), ε n, hε n, fun x hx => hn fun y hy => ?_⟩
      exact hx ⟨y, mem_iUnion.2 ⟨n, hy⟩⟩ (Finset.mem_subtype.2 hy)
    have h1 := (LinearMap.mem_span_iff_continuous _).2 hcont
    have hr : (Set.range fun y : D => ((y : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜)) =
        (ContinuousLinearMap.coeLM 𝕜 : StrongDual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜) '' D := by
      rw [show (Set.range fun y : D => ((y : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜)) = Set.range
        ((ContinuousLinearMap.coeLM 𝕜 : StrongDual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜) ∘ Subtype.val) from rfl,
        Set.range_comp, Subtype.range_coe]
    rw [hr, Submodule.span_image] at h1
    obtain ⟨f', hf', hff'⟩ := Submodule.mem_map.1 h1
    exact (ContinuousLinearMap.coe_injective hff') ▸ hf'
  have hfd : FiniteDimensional 𝕜 (StrongDual 𝕜 E) :=
    FiniteDimensional.of_span_eq_top_of_countable hDc hspan
  exact h (Module.Finite.of_injective (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi 𝕜).injective)

/-- **The weak topology of an infinite-dimensional normed space is not metrizable**, not being
first countable. -/
theorem not_metrizableSpace_weakSpace (h : ¬ FiniteDimensional 𝕜 E) :
    ¬ MetrizableSpace (WeakSpace 𝕜 E) := fun hm => by
  have := hm
  exact not_firstCountableTopology_weakSpace h inferInstance

/-- **The weak-∗ topology on the dual of an infinite-dimensional Banach space is not first
countable.** A countable neighbourhood basis of `0` is cut out by a countable set `D` of points of
`E`; every evaluation at a point of `E` is then continuous for the topology induced by the
evaluations at `D`, hence a linear combination of them, and since `y ↦ (f ↦ f y)` is injective
(`SeparatingDual`) `E` is spanned by `D`, so it is finite-dimensional by Baire. This is where
completeness of `E` is used. -/
theorem not_firstCountableTopology_weakDual [CompleteSpace E] (h : ¬ FiniteDimensional 𝕜 E) :
    ¬ FirstCountableTopology (WeakDual 𝕜 E) := by
  classical
  intro hfc
  have hcg : (𝓝 (0 : WeakDual 𝕜 E)).IsCountablyGenerated := inferInstance
  obtain ⟨Φ, ε, hε, hΦ⟩ := WeakBilin.exists_seq_finset_of_isCountablyGenerated_nhds_zero
    (B := topDualPairing 𝕜 E) hcg
  -- the countable set of points occurring in the basic sets
  set D : Set E := ⋃ n, (Φ n : Set E) with hD
  have hDc : D.Countable := Set.countable_iUnion fun n => (Φ n).countable_toSet
  -- the evaluations at points of `E`, as linear functionals on the dual
  set ev : E →ₗ[𝕜] (StrongDual 𝕜 E →ₗ[𝕜] 𝕜) := (topDualPairing 𝕜 E).flip with hev
  have hinj : Function.Injective ev := by
    intro y₁ y₂ hy
    have : ∀ f : StrongDual 𝕜 E, f (y₁ - y₂) = 0 := fun f => by
      have := LinearMap.congr_fun hy f
      simp only [hev, LinearMap.flip_apply, topDualPairing_apply] at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 (SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) this)
  -- every evaluation is continuous for the topology induced by `ev '' D`, hence in its span
  have hspan : Submodule.span 𝕜 D = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have hcont : Continuous[⨅ z : D, induced (ev z) inferInstance, inferInstance] (ev y) := by
      refine LinearMap.continuous_iInf_induced_of_forall_exists_finset _ _ fun δ hδ => ?_
      have hw : {f : WeakDual 𝕜 E | ‖f y‖ < δ} ∈ 𝓝 (0 : WeakDual 𝕜 E) :=
        IsOpen.mem_nhds (isOpen_lt (WeakDual.eval_continuous y).norm continuous_const)
          (by simpa [show ((0 : WeakDual 𝕜 E) y) = 0 from rfl] using hδ)
      obtain ⟨n, hn⟩ := hΦ _ hw
      refine ⟨(Φ n).subtype (· ∈ D), ε n, hε n, fun f hf => hn fun z hz => ?_⟩
      exact hf ⟨z, mem_iUnion.2 ⟨n, hz⟩⟩ (Finset.mem_subtype.2 hz)
    have h1 := (LinearMap.mem_span_iff_continuous _).2 hcont
    have hr : (Set.range fun z : D => ev z) = ev '' D := by
      rw [show (Set.range fun z : D => ev z) = Set.range (ev ∘ Subtype.val) from rfl,
        Set.range_comp, Subtype.range_coe]
    rw [hr, Submodule.span_image] at h1
    obtain ⟨y', hy', hyy'⟩ := Submodule.mem_map.1 h1
    exact (hinj hyy') ▸ hy'
  exact h (FiniteDimensional.of_span_eq_top_of_countable hDc hspan)

/-- **The weak-∗ topology on the dual of an infinite-dimensional Banach space is not
metrizable**, not being first countable. In particular no norm on `E'` induces the weak-∗
topology on all of `E'`, only on its bounded sets when `E` is separable. -/
theorem not_metrizableSpace_weakDual [CompleteSpace E] (h : ¬ FiniteDimensional 𝕜 E) :
    ¬ MetrizableSpace (WeakDual 𝕜 E) := fun hm => by
  have := hm
  exact not_firstCountableTopology_weakDual h inferInstance

end NotMetrizable
