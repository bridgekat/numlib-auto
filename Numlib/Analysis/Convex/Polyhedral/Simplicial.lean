import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Simplicial
import Numlib.Analysis.Convex.Caratheodory

/-!
# Polytopes, triangulation, and local simpliciality

Every polyhedral convex set is locally simplicial. This is the result that supplies instances of
`LocallySimplicial`, and with them the continuity theorems that consume it.

Around a point `x` of a polyhedral set `C`, cut out a *bounded* polyhedral neighbourhood `V`; then
`V ∩ C` is a bounded polyhedral convex set, hence a polytope — the direction part of
`conv P + cone D` has to vanish — hence, by Carathéodory's theorem, a finite union of simplices,
all of them inside `C`.

## Main results

* `exists_polyhedral_isBounded_mem_nhds` — every point has a bounded polyhedral neighbourhood: a
  coordinate cube for a basis. This is the only place a basis is used.
* `Polyhedral.exists_finset_convexHull` — a bounded polyhedral convex set is the convex hull of a
  finite set.
* `isSimplex_convexHull_coe` — the convex hull of an affinely independent `Finset` is a simplex.
* `Polyhedral.locallySimplicial` — every polyhedral convex set is locally simplicial
  ([rockafellar1970convex] Theorem 20.5).
* `exists_polyhedral_between` — a compact set inside `int D` is inside `int P` for some polyhedral
  `P ⊆ int D`.

## Implementation notes

The classical proof takes `V` to be a simplex; here it is a cube, cheaper to build and all the
argument needs — `2 n` inequalities `± bᵢ* (y - x) ≤ 1` for a basis `b`, bounded because
`‖y - x‖ ≤ ∑ ‖bᵢ‖` on it, and a neighbourhood because the strict version is open. The
triangulation is Mathlib's `convexHull_eq_union` read as a *finite* union: for a finite generating
set the index set is `P.powerset`, and `Finset.equivFin` turns it into the `Fin n`-indexed family
`LocallySimplicial` asks for.

## References

* [rockafellar1970convex] §20.
-/

open Set Filter Topology
open scoped Pointwise

namespace ConvexAnalysis

section Polytope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every point of a finite-dimensional space has arbitrarily small bounded polyhedral
neighbourhoods: the coordinate cubes `{y | ∀ i, |bᵢ* (y - x)| ≤ c}` of a basis `b`. -/
theorem exists_polyhedral_mem_nhds_subset_ball (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, Polyhedral V ∧ Bornology.IsBounded V ∧ V ∈ 𝓝 x ∧ V ⊆ Metric.ball x ε := by
  classical
  set b := Module.finBasis ℝ E with hb
  set N : ℝ := ∑ i, ‖b i‖ with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => norm_nonneg _
  set c : ℝ := ε / (2 * (1 + N)) with hc
  have hc0 : 0 < c := by
    rw [hc]
    apply div_pos hε
    linarith
  have hcN : c * N < ε := by
    have h1 : c * N ≤ c * (1 + N) := by nlinarith
    have h2 : c * (1 + N) = ε / 2 := by
      rw [hc]
      field_simp
    linarith
  set W : Set E := {z : E | ∀ i, |b.coord i z| ≤ c} with hW
  have hWpoly : Polyhedral W := by
    refine ⟨(Finset.univ.image fun i => (b.coord i, c))
      ∪ (Finset.univ.image fun i => (-(b.coord i), c)), ?_⟩
    ext z
    simp only [hW, Set.mem_ofPred_eq, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro h q (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact (abs_le.1 (h i)).2
      · have h1 := (abs_le.1 (h i)).1
        have h2 : (-(b.coord i)) z ≤ c := by rw [LinearMap.neg_apply]; linarith
        exact h2
    · intro h i
      refine abs_le.2 ⟨?_, h _ (Or.inl ⟨i, rfl⟩)⟩
      have hneg : (-(b.coord i)) z ≤ c := h _ (Or.inr ⟨i, rfl⟩)
      rw [LinearMap.neg_apply] at hneg
      linarith
  have hWnorm : ∀ z ∈ W, ‖z‖ ≤ c * N := by
    intro z hz
    have hzr : ∀ i, |b.repr z i| ≤ c := fun i => hz i
    calc ‖z‖ = ‖∑ i, b.repr z i • b i‖ := by rw [b.sum_repr z]
      _ ≤ ∑ i, ‖b.repr z i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, c * ‖b i‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          nlinarith [norm_nonneg (b i), hzr i]
      _ = c * N := by rw [hN, Finset.mul_sum]
  have hWbdd : Bornology.IsBounded W :=
    isBounded_iff_forall_norm_le.2 ⟨c * N, hWnorm⟩
  set V : Set E := (fun y : E => y - x) ⁻¹' W with hV
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have h := Polyhedral.comap_affine hWpoly (LinearMap.id : E →ₗ[ℝ] E) (-x)
    have hset : ((fun y => (LinearMap.id : E →ₗ[ℝ] E) y + (-x)) ⁻¹' W) = V := by
      ext y
      rw [Set.mem_preimage, LinearMap.id_apply, ← sub_eq_add_neg]
      rfl
    rwa [hset] at h
  · obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hWbdd
    refine isBounded_iff_forall_norm_le.2 ⟨M + ‖x‖, fun y hy => ?_⟩
    have h := hM _ hy
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ M + ‖x‖ := by linarith
  · refine mem_nhds_iff.2 ⟨{y : E | ∀ i, |b.coord i (y - x)| < c}, fun y hy i => (hy i).le, ?_, ?_⟩
    · have hEq : {y : E | ∀ i, |b.coord i (y - x)| < c}
          = ⋂ i, {y : E | |b.coord i (y - x)| < c} := by
        ext y; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      rw [hEq]
      refine isOpen_iInter_of_finite fun i => ?_
      have hcont : Continuous fun y : E => |b.coord i (y - x)| :=
        continuous_abs.comp ((b.coord i).continuous_of_finiteDimensional.comp
          (continuous_id.sub continuous_const))
      exact isOpen_lt hcont continuous_const
    · intro i
      simpa using hc0
  · intro y hy
    have h := hWnorm _ hy
    rw [Metric.mem_ball, dist_eq_norm]
    linarith

/-- Every point of a finite-dimensional space has a bounded polyhedral neighbourhood. -/
theorem exists_polyhedral_isBounded_mem_nhds (x : E) :
    ∃ V : Set E, Polyhedral V ∧ Bornology.IsBounded V ∧ V ∈ 𝓝 x := by
  obtain ⟨V, h₁, h₂, h₃, -⟩ := exists_polyhedral_mem_nhds_subset_ball x (ε := 1) one_pos
  exact ⟨V, h₁, h₂, h₃⟩

/-- A bounded polyhedral convex set is a *polytope*: the convex hull of a finite set of points.
Minkowski–Weyl writes it as `conv P + cone D`, and boundedness kills every generator of the
cone. -/
theorem Polyhedral.exists_finset_convexHull {C : Set E} (hC : Polyhedral C)
    (hbdd : Bornology.IsBounded C) : ∃ P : Finset E, C = convexHull ℝ (P : Set E) := by
  classical
  obtain ⟨P, D, hPD⟩ := hC.finitelyGenerated
  refine ⟨P, ?_⟩
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · rw [hPD, Finset.coe_empty, convexHull_empty, Set.empty_add]
  obtain ⟨p₀, hp₀⟩ := hPne
  have hp₀C : p₀ ∈ convexHull ℝ (P : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.2 hp₀)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hbdd
  -- every generating direction is zero
  have hD : ∀ d ∈ D, d = 0 := by
    intro d hd
    by_contra hdne
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hdne
    set t : ℝ := (|M| + ‖p₀‖ + 1) / ‖d‖ with ht
    have ht0 : 0 ≤ t := by positivity
    have hmem : p₀ + t • d ∈ C := by
      rw [hPD]
      exact Set.add_mem_add hp₀C
        (Submodule.smul_mem (PointedCone.hull ℝ (D : Set E)) (⟨t, ht0⟩ : {c : ℝ // 0 ≤ c})
          (PointedCone.subset_hull (Finset.mem_coe.2 hd)))
    have hnorm := hM _ hmem
    have hts : ‖t • d‖ = |M| + ‖p₀‖ + 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ht, div_mul_cancel₀ _ (ne_of_gt hdpos)]
    have hlow : ‖t • d‖ ≤ ‖p₀ + t • d‖ + ‖p₀‖ := by
      have h4 : ‖p₀ + t • d - p₀‖ ≤ ‖p₀ + t • d‖ + ‖p₀‖ := norm_sub_le _ _
      rwa [add_sub_cancel_left] at h4
    rw [hts] at hlow
    have hMabs : M ≤ |M| := le_abs_self M
    linarith
  -- so the cone they generate is trivial
  have hcone : (PointedCone.hull ℝ (D : Set E) : Set E) = {0} := by
    refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · have hsub : (D : Set E) ⊆ ((⊥ : Submodule {c : ℝ // 0 ≤ c} E) : Set E) := by
        intro d hd
        rw [SetLike.mem_coe, Submodule.mem_bot]
        exact hD d (Finset.mem_coe.1 hd)
      have hle : PointedCone.hull ℝ (D : Set E) ≤ ⊥ := Submodule.span_le.2 hsub
      have := hle hz
      rw [Submodule.mem_bot] at this
      exact this
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (PointedCone.hull ℝ (D : Set E)).zero_mem
  rw [hPD, hcone]
  ext y
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hv
    subst hv
    simpa using hu
  · intro hy
    exact ⟨y, hy, 0, rfl, add_zero y⟩

end Polytope

section Simplicial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The convex hull of an affinely independent `Finset` is a simplex. The index type of
`IsSimplex` is a `Type` (universe `0`), so the subtype `↥t` is transported to `Fin t.card`. -/
theorem isSimplex_convexHull_coe {t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E)) :
    IsSimplex (convexHull ℝ (t : Set E)) := by
  classical
  refine ⟨Fin t.card, inferInstance, fun i => ((t.equivFin.symm i : { y // y ∈ t }) : E), ?_, ?_⟩
  · exact ht.comp_embedding t.equivFin.symm.toEmbedding
  · have hrange : Set.range (fun i : Fin t.card => ((t.equivFin.symm i : { y // y ∈ t }) : E))
        = (t : Set E) := by
      ext y
      simp only [Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨i, rfl⟩
        exact (t.equivFin.symm i).2
      · intro hy
        exact ⟨t.equivFin ⟨y, hy⟩, by rw [Equiv.symm_apply_apply]⟩
    rw [hrange]

/-- Every polyhedral convex set is locally simplicial — and in particular every polytope is.

This is what makes the continuity results of `Simplicial.lean` usable: until now
`LocallySimplicial` had no supply of instances beyond simplices themselves. -/
theorem Polyhedral.locallySimplicial {C : Set E} (hC : Polyhedral C) : LocallySimplicial C := by
  classical
  intro x _
  obtain ⟨V, hVpoly, hVbdd, hVnhds⟩ := exists_polyhedral_isBounded_mem_nhds x
  have hQpoly : Polyhedral (V ∩ C) := Polyhedral.inter hVpoly hC
  have hQbdd : Bornology.IsBounded (V ∩ C) := hVbdd.subset Set.inter_subset_left
  obtain ⟨P, hP⟩ := hQpoly.exists_finset_convexHull hQbdd
  set T : Finset (Finset E) :=
    P.powerset.filter (fun t => AffineIndependent ℝ ((↑) : t → E)) with hT
  have hmemT : ∀ t ∈ T, t ⊆ P ∧ AffineIndependent ℝ ((↑) : t → E) := by
    intro t ht
    have h := Finset.mem_filter.1 ht
    exact ⟨Finset.mem_powerset.1 h.1, h.2⟩
  refine ⟨T.card, fun i => convexHull ℝ ((T.equivFin.symm i : Finset E) : Set E), ?_, ?_, ?_⟩
  · exact fun i => isSimplex_convexHull_coe (hmemT _ (T.equivFin.symm i).2).2
  · intro i
    calc convexHull ℝ ((T.equivFin.symm i : Finset E) : Set E)
        ⊆ convexHull ℝ (P : Set E) :=
          convexHull_mono (Finset.coe_subset.2 (hmemT _ (T.equivFin.symm i).2).1)
      _ = V ∩ C := hP.symm
      _ ⊆ C := Set.inter_subset_right
  · refine ⟨V, hVnhds, ?_⟩
    have hunion : (⋃ i : Fin T.card, convexHull ℝ ((T.equivFin.symm i : Finset E) : Set E))
        = convexHull ℝ (P : Set E) := by
      rw [convexHull_eq_union]
      ext y
      simp only [Set.mem_iUnion]
      constructor
      · intro hy
        obtain ⟨i, hi⟩ := hy
        exact ⟨(T.equivFin.symm i : Finset E),
          Finset.coe_subset.2 (hmemT _ (T.equivFin.symm i).2).1,
          (hmemT _ (T.equivFin.symm i).2).2, hi⟩
      · rintro ⟨u, hsub, hai, hy⟩
        have huT : u ∈ T := Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.coe_subset.1 hsub),
          hai⟩
        refine ⟨T.equivFin ⟨u, huT⟩, ?_⟩
        rwa [Equiv.symm_apply_apply]
    rw [hunion, ← hP, ← Set.inter_assoc, Set.inter_self]

/-- A compact set inside the interior of a convex set can be separated from the boundary by a
polyhedral convex set: there is a polyhedral `P` with `C ⊆ int P` and `P ⊆ int D`.

The classical proof covers `C` by simplices; a cover by coordinate cubes does the same job and is
what `exists_polyhedral_mem_nhds_subset_ball` already supplies. The polyhedral set is then the
convex hull of the finitely many cubes' vertex sets, polyhedral because a convex hull of a
finite set is.

Convexity of `C` is *not* used, and neither is nonemptiness — the classical statement assumes
both, but the covering argument needs only that `C` is compact. -/
theorem exists_polyhedral_between {C D : Set E} (hCcl : IsClosed C)
    (hCbdd : Bornology.IsBounded C) (hD : Convex ℝ D) (hCD : C ⊆ interior D) :
    ∃ P : Set E, Polyhedral P ∧ P ⊆ interior D ∧ C ⊆ interior P := by
  classical
  have hCcompact : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCcl hCbdd
  have hstep : ∀ i : C, ∃ Q : Finset E,
      convexHull ℝ (Q : Set E) ⊆ interior D ∧
        (i : E) ∈ interior (convexHull ℝ (Q : Set E)) := by
    rintro ⟨x, hx⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x (hCD hx)
    obtain ⟨V, hVpoly, hVbdd, hVnhds, hVsub⟩ := exists_polyhedral_mem_nhds_subset_ball x hε
    obtain ⟨Q, hQ⟩ := hVpoly.exists_finset_convexHull hVbdd
    refine ⟨Q, ?_, ?_⟩
    · rw [← hQ]; exact hVsub.trans hball
    · rw [← hQ]; exact mem_interior_iff_mem_nhds.2 hVnhds
  choose Q hQD hQx using hstep
  have hcover : C ⊆ ⋃ i : C, interior (convexHull ℝ (Q i : Set E)) :=
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hQx ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ :=
    hCcompact.elim_finite_subcover (fun i : C => interior (convexHull ℝ (Q i : Set E)))
      (fun _ => isOpen_interior) hcover
  refine ⟨convexHull ℝ ((t.biUnion fun i => Q i : Finset E) : Set E),
    polyhedral_convexHull_finset _, ?_, ?_⟩
  · refine convexHull_min (fun y hy => ?_) hD.interior
    rw [Finset.coe_biUnion] at hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 hy
    exact hQD i (subset_convexHull ℝ _ hyi)
  · refine ht.trans (Set.iUnion₂_subset fun i hi => interior_mono (convexHull_mono ?_))
    intro y hy
    rw [Finset.coe_biUnion]
    exact Set.mem_iUnion₂.2 ⟨i, hi, hy⟩

end Simplicial

end ConvexAnalysis
