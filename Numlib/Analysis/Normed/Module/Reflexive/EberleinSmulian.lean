/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Reflexive`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Module.DualSeparable
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.Analysis.Normed.Module.WeakDual

/-!
# The Eberlein–Šmulian theorem

For a subset `A` of a normed space `E`, with `B` its closure in the weak topology, the following
are equivalent, and either implies the third:

* (P) `B` is weakly compact;
* (Q) every sequence in `A` has a weakly convergent subsequence;
* (R) every point of `B` is the weak limit of a sequence in `A`.

The consequence for reflexivity is the converse of the weak sequential compactness of the unit
ball of a reflexive space (`NormedSpace.exists_subseq_forall_dual_tendsto`, the parent module):
**a normed space in which every bounded sequence has a weakly convergent subsequence is
reflexive** (`NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto`), so that
reflexivity is characterized by weak sequential compactness of the closed unit ball
(`NormedSpace.isReflexive_iff_forall_exists_subseq_forall_dual_tendsto`). No completeness is
assumed anywhere: a space with the property is reflexive, hence complete.

## The proof

* **(P) ⇒ (Q)** (`IsCompact.isSeqCompact_weakSpace`): a sequence lives in the closed span `N` of
  its terms, a separable closed subspace, which is weakly closed by Mazur's theorem. The compact
  set `K ∩ N` carries a countable family of weakly continuous functions separating its points —
  a norming sequence of functionals of `N` (`exists_seq_strongDual_norming_of_separableSpace`)
  extended to `E` by Hahn–Banach — so it is metrizable
  (`Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating`, which is what the
  explicit metric `∑ 2⁻ᵏ |⟨bₖ, x - y⟩|` of the textbook proof builds), hence sequentially compact.
* **The norming lemma** (`NormedSpace.exists_finset_norm_le_two_mul_sup_of_finiteDimensional`):
  a finite-dimensional subspace `M` of a dual space is normed, up to the factor `2`, by finitely
  many vectors of the unit ball, since its unit sphere is totally bounded.
* **The heart, (Q) ⇒ points of the weak-∗ closure of `J(A)` come from `E`**
  (`NormedSpace.exists_seq_tendsto_toWeakSpace_of_mem_closure_image_of_isSeqCompact`): given `ξ`
  in the weak-∗ closure of `J(A)`, one builds `x_k ∈ A` and finite sets `Ψ_k` of functionals of
  the unit ball such that `Ψ_k` norms (up to `2`) the span `M_k` of `ξ, J x_0, …, J x_{k-1}`, and
  `x_k` approximates `ξ` within `1/(k+1)` on `Ψ_0 ∪ … ∪ Ψ_k`. The union `F` of the `Ψ_k` then
  norms the norm closure of `M = ⋃ M_k` (the norming inequality passes to the closure because the
  `Ψ_k` lie in the unit ball). A weak limit `u` of a subsequence of the `x_k` lies in the closed
  span of the `x_k` (Mazur), so `ξ - J u ∈ closure M`; the approximation property forces
  `ξ f = f u` for every `f ∈ F`, and the norming inequality forces `ξ = J u`. The recursion
  carries the finite data as a pair (points chosen so far, functionals chosen so far), built by
  `Nat.rec` from a choice function.
* **(Q) ⇒ (P)** (`NormedSpace.isCompact_closure_image_toWeakSpace_of_isSeqCompact`): (Q) makes `A`
  bounded, so the weak-∗ closure of `J(A)` is compact by Banach–Alaoglu, and the previous item
  puts it inside the range of the embedding of the weak space into the weak-∗ bidual; Mathlib's
  `NormedSpace.isCompact_closure_of_isBounded` transfers the compactness back. **(Q) ⇒ (R)**
  (`NormedSpace.exists_seq_tendsto_toWeakSpace_of_mem_closure_image_toWeakSpace`) is the previous
  item read on `J(B)`.

## References

[brezis2011functional] Theorem 3.19 and Problem 10 (Eberlein–Šmulian).
-/

open Filter Topology Metric Set Function TopologicalSpace

namespace NormedSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
### The norming lemma
-/

/-- **A finite-dimensional subspace of a dual space is normed, up to the factor `2`, by finitely
many vectors of the unit ball**: the unit sphere of `M` is totally bounded, so finitely many
`g ∈ M` are within `1/8` of every point of it; almost-norming vectors `a` of these `g`
(`‖g a‖ ≥ ‖g‖ - 1/8`) then satisfy `‖h a‖ ≥ 1/2` for every `h` on the sphere. -/
theorem exists_finset_norm_le_two_mul_sup_of_finiteDimensional
    (M : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 M] :
    ∃ s : Finset E, (∀ a ∈ s, ‖a‖ ≤ 1) ∧ ∀ g ∈ M, ∃ a ∈ s, ‖g‖ ≤ 2 * ‖g a‖ := by
  classical
  -- the unit sphere of `M` is compact, hence totally bounded
  have hcpt : IsCompact ((M : Set (StrongDual 𝕜 E)) ∩ sphere 0 1) := by
    have : (M : Set (StrongDual 𝕜 E)) ∩ sphere 0 1 = Subtype.val '' sphere (0 : M) 1 := by
      ext g
      simp only [mem_inter_iff, SetLike.mem_coe, mem_sphere_zero_iff_norm, mem_image,
        Subtype.exists, exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨hg, hn⟩; exact ⟨hg, (Submodule.norm_coe (⟨g, hg⟩ : M)).symm.trans hn⟩
      · rintro ⟨hg, hn⟩; exact ⟨hg, (Submodule.norm_coe (⟨g, hg⟩ : M)).trans hn⟩
    rw [this]
    exact (isCompact_sphere (0 : M) 1).image continuous_subtype_val
  obtain ⟨t, htf, htc⟩ := Metric.totallyBounded_iff.1 hcpt.totallyBounded (1 / 8) (by norm_num)
  -- almost norming vectors for the centres
  have hex : ∀ g : StrongDual 𝕜 E, ∃ a : E, ‖a‖ ≤ 1 ∧ ‖g‖ - 1 / 8 ≤ ‖g a‖ := fun g => by
    rcases le_or_gt ‖g‖ (1 / 8) with h | h
    · exact ⟨0, by simp, by simp; linarith⟩
    · obtain ⟨a, ha, hga⟩ := g.exists_lt_apply_of_lt_opNorm (r := ‖g‖ - 1 / 8) (by linarith)
      exact ⟨a, ha.le, hga.le⟩
  choose a ha1 ha2 using hex
  refine ⟨insert 0 (htf.toFinset.image a), ?_, fun g hg => ?_⟩
  · intro b hb
    rw [Finset.mem_insert, Finset.mem_image] at hb
    rcases hb with rfl | ⟨c, -, rfl⟩
    · simp
    · exact ha1 c
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨0, Finset.mem_insert_self _ _, by simp⟩
  -- normalize `g` onto the sphere and find a centre within `1/8`
  have hgn : 0 < ‖g‖ := norm_pos_iff.2 hg0
  set h : StrongDual 𝕜 E := ((‖g‖⁻¹ : ℝ) : 𝕜) • g with hh
  have hhM : h ∈ M := M.smul_mem _ hg
  have hhn : ‖h‖ = 1 := by
    rw [hh, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hgn), inv_mul_cancel₀ hgn.ne']
  obtain ⟨c, hct, hhc⟩ := mem_iUnion₂.1 (htc ⟨hhM, mem_sphere_zero_iff_norm.2 hhn⟩)
  rw [mem_ball, dist_eq_norm] at hhc
  refine ⟨a c, Finset.mem_insert_of_mem (Finset.mem_image_of_mem a (htf.mem_toFinset.2 hct)),
    ?_⟩
  -- `‖h (a c)‖ ≥ 1/2`, and `h (a c) = ‖g‖⁻¹ • g (a c)`
  have hcn : 7 / 8 ≤ ‖c‖ := by
    have := norm_sub_norm_le h c
    linarith
  have h1 : ‖h (a c)‖ ≥ 1 / 2 := by
    have h2 : ‖h (a c) - c (a c)‖ ≤ 1 / 8 := by
      rw [← sub_apply]
      exact ((h - c).le_opNorm (a c)).trans (by
        calc ‖h - c‖ * ‖a c‖ ≤ (1 / 8) * 1 := by gcongr; exact ha1 c
          _ = 1 / 8 := by norm_num)
    have h3 := norm_sub_norm_le (c (a c)) (h (a c))
    rw [norm_sub_rev] at h3
    linarith [ha2 c]
  have hha : ‖h (a c)‖ = ‖g‖⁻¹ * ‖g (a c)‖ := by
    rw [hh, smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hgn)]
  rw [hha] at h1
  rw [ge_iff_le, inv_mul_eq_div, le_div_iff₀ hgn] at h1
  linarith

/-!
### The heart: (Q) brings the weak-∗ closure of `J(A)` back to `E`
-/

/-- **The heart of the Eberlein–Šmulian theorem.** If every sequence in `A` has a weakly
convergent subsequence, then every point `ξ` of the weak-∗ closure of `J(A)` in the bidual is
`J x` for some `x`, which is the weak limit of a sequence in `A`. The proof is the interleaved
construction of the module doc: points `x_k ∈ A` approximating `ξ` on finite sets `Ψ_k` of
functionals of the unit ball that norm the spans of `ξ, J x_0, …, J x_{k-1}`. -/
theorem exists_seq_tendsto_toWeakSpace_of_mem_closure_image_of_isSeqCompact {A : Set E}
    (hA : ∀ x : ℕ → E, (∀ n, x n ∈ A) → ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => toWeakSpace 𝕜 E (x (φ k))) atTop (𝓝 (toWeakSpace 𝕜 E u)))
    {ξ : WeakDual 𝕜 (StrongDual 𝕜 E)}
    (hξ : ξ ∈ closure ((StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E) '' A)) :
    ∃ x : E, ξ = StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 E x) ∧
      ∃ y : ℕ → E, (∀ n, y n ∈ A) ∧
        Tendsto (fun n => toWeakSpace 𝕜 E (y n)) atTop (𝓝 (toWeakSpace 𝕜 E x)) := by
  classical
  set J : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) := inclusionInDoubleDual 𝕜 E with hJ
  set ξ' : StrongDual 𝕜 (StrongDual 𝕜 E) := WeakDual.toStrongDual ξ with hξ'
  -- `ξ` is approximated on finitely many functionals by points of `A`
  have hF1 : ∀ (Φ : Finset (StrongDual 𝕜 E)) (δ : ℝ), 0 < δ →
      ∃ x ∈ A, ∀ f ∈ Φ, ‖ξ f - f x‖ < δ := by
    intro Φ δ hδ
    have hN : (⋂ f ∈ Φ, {η : WeakDual 𝕜 (StrongDual 𝕜 E) | ‖η f - ξ f‖ < δ}) ∈ 𝓝 ξ := by
      refine IsOpen.mem_nhds ?_ (Set.mem_iInter₂.2 fun f _ => by simp [hδ])
      refine isOpen_biInter_finset fun f _ => ?_
      exact isOpen_lt ((WeakDual.eval_continuous f).sub continuous_const).norm continuous_const
    obtain ⟨_, hN', ⟨x, hx, rfl⟩⟩ := mem_closure_iff_nhds.1 hξ _ hN
    refine ⟨x, hx, fun f hf => ?_⟩
    have := Set.mem_iInter₂.1 hN' f hf
    simp only [comp_apply, StrongDual.toWeakDual_apply, mem_ofPred_eq] at this
    rwa [norm_sub_rev]
  -- the norming lemma for the span of `ξ` and finitely many points of `A`
  have hF2 : ∀ P : Finset E, ∃ Ψ : Finset (StrongDual 𝕜 E), (∀ f ∈ Ψ, ‖f‖ ≤ 1) ∧
      ∀ η ∈ Submodule.span 𝕜 (insert ξ' (J '' (P : Set E))), ∃ f ∈ Ψ, ‖η‖ ≤ 2 * ‖η f‖ := by
    intro P
    have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (insert ξ' (J '' (P : Set E)))) :=
      FiniteDimensional.span_of_finite 𝕜 ((P.finite_toSet.image J).insert ξ')
    exact exists_finset_norm_le_two_mul_sup_of_finiteDimensional _
  -- one step of the construction
  have hstep : ∀ (k : ℕ) (P : Finset E) (Ψ : Finset (StrongDual 𝕜 E)),
      ∃ (x : E) (Ψ' : Finset (StrongDual 𝕜 E)), x ∈ A ∧ (∀ f ∈ Ψ', ‖f‖ ≤ 1) ∧
        (∀ η ∈ Submodule.span 𝕜 (insert ξ' (J '' (P : Set E))), ∃ f ∈ Ψ', ‖η‖ ≤ 2 * ‖η f‖) ∧
        ∀ f ∈ Ψ ∪ Ψ', ‖ξ f - f x‖ < 1 / (k + 1) := by
    intro k P Ψ
    obtain ⟨Ψ', hΨ'1, hΨ'2⟩ := hF2 P
    obtain ⟨x, hxA, hx⟩ := hF1 (Ψ ∪ Ψ') (1 / (k + 1)) (by positivity)
    exact ⟨x, Ψ', hxA, hΨ'1, hΨ'2, hx⟩
  choose! xs Ψs hxA hΨ1 hΨ2 hxΨ using hstep
  -- the accumulated state: points chosen so far, functionals chosen so far
  let acc : ℕ → Finset E × Finset (StrongDual 𝕜 E) := fun k =>
    Nat.rec (∅, ∅) (fun k st => (insert (xs k st.1 st.2) st.1, st.2 ∪ Ψs k st.1 st.2)) k
  set x : ℕ → E := fun k => xs k (acc k).1 (acc k).2 with hx
  set Ψ : ℕ → Finset (StrongDual 𝕜 E) := fun k => Ψs k (acc k).1 (acc k).2 with hΨ
  have hacc1 : ∀ k, (acc k).1 = (Finset.range k).image x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Finset.range_add_one, Finset.image_insert, ← ih]
  have hacc2 : ∀ k, (acc k).2 = (Finset.range k).biUnion Ψ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Finset.range_add_one, Finset.biUnion_insert, ← ih, Finset.union_comm]
  have hxA' : ∀ k, x k ∈ A := fun k => hxA k _ _
  have hΨle : ∀ k, ∀ f ∈ Ψ k, ‖f‖ ≤ 1 := fun k => hΨ1 k _ _
  have ha : ∀ k, ∀ η ∈ Submodule.span 𝕜 (insert ξ' (J '' ((acc k).1 : Set E))),
      ∃ f ∈ Ψ k, ‖η‖ ≤ 2 * ‖η f‖ := fun k => hΨ2 k _ _
  have hb : ∀ k, ∀ f ∈ (Finset.range (k + 1)).biUnion Ψ, ‖ξ f - f (x k)‖ < 1 / (k + 1) := by
    intro k f hf
    obtain ⟨j, hj, hfj⟩ := Finset.mem_biUnion.1 hf
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    refine hxΨ k (acc k).1 (acc k).2 f (Finset.mem_union.2 ?_)
    rcases hj.lt_or_eq with hjk | rfl
    · left; rw [hacc2]; exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hjk, hfj⟩
    · right; exact hfj
  -- the countable norming family `F` and the span `M` of `ξ` and the `J x k`
  set Fset : Set (StrongDual 𝕜 E) := ⋃ k, (Ψ k : Set (StrongDual 𝕜 E)) with hFset
  set M : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    Submodule.span 𝕜 (insert ξ' (J '' Set.range x)) with hM
  have hQ : ∀ η ∈ M, ∀ s : ℝ, (∀ f ∈ Fset, ‖η f‖ ≤ s) → ‖η‖ ≤ 2 * s := by
    intro η hη s hs
    -- `η` lies in the span over finitely many of the `x k`
    have hunion : insert ξ' (J '' Set.range x) =
        ⋃ k, insert ξ' (J '' ((Finset.range k).image x : Set E)) := by
      ext η
      simp only [mem_insert_iff, mem_image, mem_range, mem_iUnion, Finset.coe_image,
        Finset.coe_range, mem_Iio]
      constructor
      · rintro (rfl | ⟨_, ⟨n, rfl⟩, rfl⟩)
        · exact ⟨0, Or.inl rfl⟩
        · exact ⟨n + 1, Or.inr ⟨x n, ⟨n, Nat.lt_succ_self n, rfl⟩, rfl⟩⟩
      · rintro ⟨k, rfl | ⟨_, ⟨n, -, rfl⟩, rfl⟩⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨x n, ⟨n, rfl⟩, rfl⟩
    rw [hM, hunion, Submodule.span_iUnion] at hη
    have hdir : Directed (· ≤ ·) fun k =>
        Submodule.span 𝕜 (insert ξ' (J '' ((Finset.range k).image x : Set E))) :=
      Monotone.directed_le fun m n hmn => Submodule.span_mono (insert_subset_insert
        (image_mono (Finset.coe_subset.2 (Finset.image_subset_image (Finset.range_mono hmn)))))
    obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hη
    rw [← hacc1 k] at hk
    obtain ⟨f, hf, hηf⟩ := ha k η hk
    calc ‖η‖ ≤ 2 * ‖η f‖ := hηf
      _ ≤ 2 * s := by gcongr; exact hs f (mem_iUnion.2 ⟨k, hf⟩)
  -- the norming inequality passes to the norm closure of `M`
  have hQc : ∀ η ∈ M.topologicalClosure, ∀ s : ℝ, (∀ f ∈ Fset, ‖η f‖ ≤ s) → ‖η‖ ≤ 2 * s := by
    intro η hη s hs
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hη
    obtain ⟨η', hη', hd⟩ := hη (ε / 3) (by positivity)
    rw [dist_eq_norm] at hd
    have h1 : ‖η'‖ ≤ 2 * (s + ε / 3) := by
      refine hQ η' hη' _ fun f hf => ?_
      have hf1 : ‖f‖ ≤ 1 := by
        obtain ⟨k, hk⟩ := mem_iUnion.1 hf
        exact hΨle k f hk
      calc ‖η' f‖ = ‖η f + (η' - η) f‖ := by congr 1; simp
        _ ≤ ‖η f‖ + ‖(η' - η) f‖ := norm_add_le _ _
        _ ≤ s + ‖η' - η‖ * ‖f‖ := add_le_add (hs f hf) ((η' - η).le_opNorm f)
        _ ≤ s + ε / 3 := by
            rw [norm_sub_rev]
            nlinarith [norm_nonneg (η - η'), norm_nonneg f]
    calc ‖η‖ = ‖η' + (η - η')‖ := by congr 1; abel
      _ ≤ ‖η'‖ + ‖η - η'‖ := norm_add_le _ _
      _ ≤ 2 * (s + ε / 3) + ε / 3 := by linarith
      _ = 2 * s + ε := by ring
  -- the weakly convergent subsequence and its limit `u`
  obtain ⟨u, φ, hφ, hlim⟩ := hA x hxA'
  -- `J u ∈ closure M`: by Mazur, `u` is in the closed span of the `x k`
  have hu : u ∈ (Submodule.span 𝕜 (Set.range x)).topologicalClosure := by
    have hcl := Submodule.isClosed_image_toWeakSpace_topologicalClosure
      (Submodule.span 𝕜 (Set.range x))
    have hmem : toWeakSpace 𝕜 E u ∈ toWeakSpace 𝕜 E ''
        ((Submodule.span 𝕜 (Set.range x)).topologicalClosure : Set E) :=
      hcl.mem_of_tendsto hlim (Eventually.of_forall fun k =>
        ⟨x (φ k), Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self _)),
          rfl⟩)
    obtain ⟨u', hu', hu'u⟩ := hmem
    rwa [(toWeakSpace 𝕜 E).injective hu'u] at hu'
  have hJu : J u ∈ M.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hu ⊢
    have h1 : J u ∈ closure (J '' (Submodule.span 𝕜 (Set.range x) : Set E)) :=
      image_closure_subset_closure_image J.continuous ⟨u, hu, rfl⟩
    refine closure_mono ?_ h1
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.span_mono (subset_insert _ _) (Submodule.apply_mem_span_image_of_mem_span _ hz)
  have hξM : ξ' ∈ M.topologicalClosure :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_insert _ _))
  -- `ξ` and `J u` agree on the norming family
  have hzero : ∀ f ∈ Fset, (ξ' - J u) f = 0 := by
    intro f hf
    obtain ⟨j, hj⟩ := mem_iUnion.1 hf
    have hlim1 : Tendsto (fun k => f (x (φ k))) atTop (𝓝 (f u)) :=
      (tendsto_toWeakSpace_iff.1 hlim) f
    have hlim2 : Tendsto (fun k => f (x (φ k))) atTop (𝓝 (ξ f)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop j] with k hk
      have hjk : f ∈ (Finset.range (φ k + 1)).biUnion Ψ :=
        Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le (hk.trans (hφ.id_le k))), hj⟩
      have := hb (φ k) f hjk
      rw [norm_sub_rev] at this
      refine this.le.trans ?_
      gcongr
      exact_mod_cast hφ.id_le k
    have := tendsto_nhds_unique hlim1 hlim2
    change ξ f - f u = 0
    rw [← this, sub_self]
  -- hence `ξ = J u`
  have hdiff : ξ' - J u ∈ M.topologicalClosure := sub_mem hξM hJu
  have hnorm : ‖ξ' - J u‖ ≤ 2 * 0 := hQc _ hdiff 0 fun f hf => by rw [hzero f hf, norm_zero]
  have hξJ : ξ' = J u := by
    rw [mul_zero] at hnorm
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hnorm)
  refine ⟨u, ?_, x ∘ φ, fun k => hxA' _, hlim⟩
  rw [← hξJ, hξ']
  rfl

/-!
### (Q) ⇒ (P) and (Q) ⇒ (R)
-/

/-- **(Q) ⇒ (P): if every sequence in `A` has a weakly convergent subsequence, the weak closure
of `A` is weakly compact.** (Q) makes `A` bounded, the weak-∗ closure of `J(A)` is then compact
by Banach–Alaoglu and lies in the range of the embedding of the weak space by
`exists_seq_tendsto_toWeakSpace_of_mem_closure_image_of_isSeqCompact`, and Mathlib's
`isCompact_closure_of_isBounded` transfers the compactness back. -/
theorem isCompact_closure_image_toWeakSpace_of_isSeqCompact {A : Set E}
    (hA : ∀ x : ℕ → E, (∀ n, x n ∈ A) → ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => toWeakSpace 𝕜 E (x (φ k))) atTop (𝓝 (toWeakSpace 𝕜 E u))) :
    IsCompact (closure (toWeakSpace 𝕜 E '' A)) := by
  -- `A` is bounded: an unbounded sequence has no weakly convergent subsequence
  have hb : Bornology.IsBounded A := by
    by_contra hnb
    rw [isBounded_iff_forall_norm_le] at hnb
    push Not at hnb
    choose a haA ha using fun n : ℕ => hnb n
    obtain ⟨u, φ, hφ, hlim⟩ := hA a haA
    obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace hlim
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have h1 := hC n
    have h2 := ha (φ n)
    have h3 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith
  refine isCompact_closure_of_isBounded 𝕜 E (toWeakSpace 𝕜 E '' A)
    (by rwa [Set.preimage_image_eq _ (toWeakSpace 𝕜 E).injective]) fun ξ hξ => ?_
  rw [Set.image_image] at hξ
  obtain ⟨x, hx, -⟩ := exists_seq_tendsto_toWeakSpace_of_mem_closure_image_of_isSeqCompact hA
    (ξ := ξ) hξ
  exact ⟨toWeakSpace 𝕜 E x, hx.symm⟩

/-- **(Q) ⇒ (R): if every sequence in `A` has a weakly convergent subsequence, every point of
the weak closure of `A` is the weak limit of a sequence in `A`.** -/
theorem exists_seq_tendsto_toWeakSpace_of_mem_closure_image_toWeakSpace {A : Set E}
    (hA : ∀ x : ℕ → E, (∀ n, x n ∈ A) → ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => toWeakSpace 𝕜 E (x (φ k))) atTop (𝓝 (toWeakSpace 𝕜 E u)))
    {u : E} (hu : toWeakSpace 𝕜 E u ∈ closure (toWeakSpace 𝕜 E '' A)) :
    ∃ y : ℕ → E, (∀ n, y n ∈ A) ∧
      Tendsto (fun n => toWeakSpace 𝕜 E (y n)) atTop (𝓝 (toWeakSpace 𝕜 E u)) := by
  have hξ : inclusionInDoubleDualWeak 𝕜 E (toWeakSpace 𝕜 E u) ∈
      closure ((StrongDual.toWeakDual ∘ inclusionInDoubleDual 𝕜 E) '' A) := by
    have := image_closure_subset_closure_image (inclusionInDoubleDualWeak 𝕜 E).continuous
      ⟨_, hu, rfl⟩
    rwa [Set.image_image] at this
  obtain ⟨x, hx, y, hyA, hy⟩ :=
    exists_seq_tendsto_toWeakSpace_of_mem_closure_image_of_isSeqCompact hA hξ
  have hxu : x = u := by
    have h1 : inclusionInDoubleDual 𝕜 E x = inclusionInDoubleDual 𝕜 E u :=
      (StrongDual.toWeakDual (𝕜 := 𝕜) (E := StrongDual 𝕜 E)).injective hx.symm
    exact (inclusionInDoubleDualLi 𝕜 (E := E)).injective h1
  exact ⟨y, hyA, hxu ▸ hy⟩

/-!
### Reflexivity by weak sequential compactness
-/

/-- **Eberlein–Šmulian for reflexivity: a normed space whose closed unit ball is weakly
sequentially compact is reflexive.** The ball is then weakly compact
(`isCompact_closure_image_toWeakSpace_of_isSeqCompact`, the ball being weakly closed) and
Kakutani's converse applies. Completeness follows, so it is not assumed. -/
theorem isReflexive_of_isSeqCompact_image_toWeakSpace_closedBall
    (h : IsSeqCompact (toWeakSpace 𝕜 E '' closedBall (0 : E) 1)) : IsReflexive 𝕜 E := by
  refine isReflexive_of_isCompact_image_toWeakSpace_closedBall ?_
  have hA : ∀ x : ℕ → E, (∀ n, x n ∈ closedBall (0 : E) 1) → ∃ (u : E) (φ : ℕ → ℕ),
      StrictMono φ ∧
        Tendsto (fun k => toWeakSpace 𝕜 E (x (φ k))) atTop (𝓝 (toWeakSpace 𝕜 E u)) := by
    intro x hx
    obtain ⟨a, -, φ, hφ, hlim⟩ :=
      h (x := fun n => toWeakSpace 𝕜 E (x n)) fun n => ⟨x n, hx n, rfl⟩
    refine ⟨(toWeakSpace 𝕜 E).symm a, φ, hφ, ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    exact hlim
  have := isCompact_closure_image_toWeakSpace_of_isSeqCompact hA
  rwa [(isClosed_image_toWeakSpace_closedBall 0 1).closure_eq] at this

/-- **A normed space in which every bounded sequence has a weakly convergent subsequence is
reflexive**, the converse of `exists_subseq_forall_dual_tendsto`. The hypothesis makes the
closed unit ball weakly sequentially compact — the limit stays in the ball because the norm is
weakly sequentially lower semicontinuous (`norm_le_liminf_norm_of_weak_tendsto`). -/
theorem isReflexive_of_forall_exists_subseq_forall_dual_tendsto
    (h : ∀ (v : ℕ → E) (C : ℝ), (∀ n, ‖v n‖ ≤ C) → ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ℓ : StrongDual 𝕜 E, Tendsto (fun k => ℓ (v (φ k))) atTop (𝓝 (ℓ u))) :
    IsReflexive 𝕜 E := by
  refine isReflexive_of_isSeqCompact_image_toWeakSpace_closedBall fun x hx => ?_
  set v : ℕ → E := fun n => (toWeakSpace 𝕜 E).symm (x n) with hv
  have hvb : ∀ n, ‖v n‖ ≤ 1 := fun n => by
    obtain ⟨z, hz, hzx⟩ := hx n
    rw [hv]
    simp only [← hzx, LinearEquiv.symm_apply_apply]
    exact mem_closedBall_zero_iff.1 hz
  obtain ⟨u, φ, hφ, hlim⟩ := h v 1 hvb
  have hlim' : Tendsto (fun k => toWeakSpace 𝕜 E (v (φ k))) atTop (𝓝 (toWeakSpace 𝕜 E u)) :=
    tendsto_toWeakSpace_iff.2 hlim
  refine ⟨toWeakSpace 𝕜 E u, ⟨u, mem_closedBall_zero_iff.2 ?_, rfl⟩, φ, hφ, ?_⟩
  · refine (norm_le_liminf_norm_of_weak_tendsto hlim').trans ?_
    refine Filter.liminf_le_of_le (isBoundedUnder_of ⟨0, fun k => norm_nonneg _⟩) fun b hb => ?_
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hvb (φ n))
  · have : (fun k => toWeakSpace 𝕜 E (v (φ k))) = x ∘ φ := by
      ext k; simp [hv]
    rwa [this] at hlim'

/-- **A normed space is reflexive iff every bounded sequence has a weakly convergent
subsequence** (Kakutani + Eberlein–Šmulian). -/
theorem isReflexive_iff_forall_exists_subseq_forall_dual_tendsto :
    IsReflexive 𝕜 E ↔ ∀ (v : ℕ → E) (C : ℝ), (∀ n, ‖v n‖ ≤ C) → ∃ (u : E) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ ℓ : StrongDual 𝕜 E, Tendsto (fun k => ℓ (v (φ k))) atTop (𝓝 (ℓ u)) :=
  ⟨fun _ _ _ hv => exists_subseq_forall_dual_tendsto hv,
    isReflexive_of_forall_exists_subseq_forall_dual_tendsto⟩

/-!
### (P) ⇒ (Q): weakly compact sets are weakly sequentially compact
-/

/-- **A weakly compact subset of a normed space is weakly sequentially compact.** A sequence in
`K` lies in the closed span `N` of its terms, a separable closed subspace, weakly closed by
Mazur's theorem; on the compact set `K ∩ N` a norming sequence of functionals of `N`, extended to
`E` by Hahn–Banach, is a countable separating family of continuous functions, so `K ∩ N` is
metrizable (`Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating`) and
hence sequentially compact. -/
theorem _root_.IsCompact.isSeqCompact_weakSpace {K : Set (WeakSpace 𝕜 E)} (hK : IsCompact K) :
    IsSeqCompact K := by
  intro x hx
  -- the closed span of the sequence, a separable closed subspace
  set N : Submodule 𝕜 E :=
    (Submodule.span 𝕜 (Set.range fun n => (toWeakSpace 𝕜 E).symm (x n))).topologicalClosure
    with hN
  have hNsep : SeparableSpace N := by
    have : IsSeparable (N : Set E) := by
      rw [hN, Submodule.topologicalClosure_coe]
      exact ((Set.countable_range _).isSeparable.span).closure
    exact this.separableSpace
  have hxN : ∀ n, x n ∈ toWeakSpace 𝕜 E '' (N : Set E) := fun n =>
    ⟨(toWeakSpace 𝕜 E).symm (x n), Submodule.le_topologicalClosure _
      (Submodule.subset_span (mem_range_self n)), by simp⟩
  -- `K' := K ∩ N` is compact
  set K' : Set (WeakSpace 𝕜 E) := K ∩ toWeakSpace 𝕜 E '' (N : Set E) with hK'
  have hK'c : IsCompact K' :=
    hK.inter_right (Submodule.isClosed_image_toWeakSpace_topologicalClosure _)
  -- a countable separating family of continuous functions on `K'`
  obtain ⟨f, -, hf2⟩ := exists_seq_strongDual_norming_of_separableSpace (𝕜 := 𝕜) (E := N)
  have hext : ∀ n, ∃ g : StrongDual 𝕜 E, ∀ z : N, g z = f n z := fun n => by
    obtain ⟨g, hg, -⟩ := exists_extension_norm_eq N (f n)
    exact ⟨g, hg⟩
  choose g hg using hext
  have : CompactSpace K' := isCompact_iff_compactSpace.1 hK'c
  have hmetr : MetrizableSpace K' := by
    refine Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
      (Y := fun _ => 𝕜)
      (fun n (y : K') => g n ((toWeakSpace 𝕜 E).symm (y : WeakSpace 𝕜 E))) (fun n => ?_) ?_
    · exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (g n)).comp
        continuous_subtype_val
    · intro y₁ y₂ hne
      obtain ⟨-, z₁, hz₁, hz₁y⟩ := y₁.2
      obtain ⟨-, z₂, hz₂, hz₂y⟩ := y₂.2
      have hz : (⟨z₁, hz₁⟩ : N) - ⟨z₂, hz₂⟩ ≠ 0 := by
        intro h0
        apply hne
        have : z₁ = z₂ := by simpa [sub_eq_zero] using congrArg Subtype.val h0
        exact Subtype.ext (by rw [← hz₁y, ← hz₂y, this])
      obtain ⟨n, hn⟩ := hf2 (⟨z₁, hz₁⟩ - ⟨z₂, hz₂⟩)
      refine ⟨n, fun heq => ?_⟩
      have hfz : f n (⟨z₁, hz₁⟩ - ⟨z₂, hz₂⟩) = 0 := by
        rw [map_sub, ← hg n, ← hg n]
        simp only [← hz₁y, ← hz₂y, LinearEquiv.symm_apply_apply] at heq ⊢
        rw [heq, sub_self]
      rw [hfz, norm_zero, mul_zero] at hn
      exact hz (norm_le_zero_iff.1 hn)
  -- a compact metrizable space is sequentially compact
  have hseq : IsSeqCompact K' := by
    have : SeqCompactSpace K' := inferInstance
    simpa using IsSeqCompact.range
      (continuous_iff_seqContinuous.mp (continuous_subtype_val (p := (· ∈ K'))))
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hseq (x := x) fun n => ⟨hx n, hxN n⟩
  exact ⟨a, ha.1, φ, hφ, hlim⟩

/-- **Eberlein–Šmulian, (P) ⇔ (Q)**: the weak closure of `A` is weakly compact iff it is weakly
sequentially compact. -/
theorem isCompact_closure_image_toWeakSpace_iff_isSeqCompact (A : Set E) :
    IsCompact (closure (toWeakSpace 𝕜 E '' A)) ↔
      IsSeqCompact (closure (toWeakSpace 𝕜 E '' A)) := by
  refine ⟨fun h => h.isSeqCompact_weakSpace, fun h => ?_⟩
  refine isCompact_closure_image_toWeakSpace_of_isSeqCompact fun x hx => ?_
  obtain ⟨a, -, φ, hφ, hlim⟩ := h (x := fun n => toWeakSpace 𝕜 E (x n))
    fun n => subset_closure ⟨x n, hx n, rfl⟩
  refine ⟨(toWeakSpace 𝕜 E).symm a, φ, hφ, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact hlim

end NormedSpace
