import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Join
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Recession.Cone

/-!
# Relative interiors of convex sets

The theory of relative interiors of convex sets in a finite-dimensional real normed space. The
*relative interior* `ri C` is the interior of `C` taken relative to its affine hull; it is Mathlib's
`intrinsicInterior ℝ C`, so no new definition is introduced, and what this file adds is the
convexity theory that `Mathlib.Analysis.Convex.Intrinsic` does not carry. Finite dimension also
sharpens several statements about convex functions and about separation that the topological
modules `Closure.lean` and `Separation.lean` can state only in dimension-free form.

## Main definitions

* `ri` — scoped notation for `intrinsicInterior ℝ`, matching Rockafellar's usage.

## Main results

* `mem_intrinsicInterior_iff` — the metric description of `ri s`: a point of the affine hull lies
  in `ri s` exactly when some ball of the affine hull around it is contained in `s`. This is the
  cornerstone from which the rest of the file is derived.
* `Convex.subset_closure_inter_setOf_pos`, `Convex.closure_inter_setOf_pos` — a convex set on which
  a linear functional is non-negative and somewhere positive is the closure of the part where the
  functional is positive; a segment argument with no relative interiors in it, here because it is
  the density step of the cross-section arguments.
* `Convex.segment_mem_relint` — the *line segment principle*: the half-open segment from a
  relative interior point towards a point of the closure stays in `ri C` (Theorem 6.1 in [^1]).
* `Convex.relint_nonempty`, `Convex.affineSpan_relint` — a nonempty convex set has a nonempty
  relative interior, and the same affine hull as it.
* `Convex.interior_subset_relint` — the full-dimensional collapse `ri C = int C`, in the direction
  every caller uses.
* `Convex.closure_relint`, `Convex.relint_closure` — `C`, `ri C` and `cl C` share a closure and a
  relative interior, whence `Convex.closure_eq_iff_relint_eq` and
  `Convex.relint_inter_nonempty_of_isOpen`.
* `Convex.mem_relint_iff_prolong` — the *prolongation principle*: `z ∈ ri C` exactly when every
  segment of `C` ending at `z` continues past it (Theorem 6.4 in [^1]).
* `Convex.closure_iInter`, `Convex.relint_iInter` — closure and relative interior commute with an
  intersection whose relative interiors meet, with `Convex.relint_inter_affine` and
  `Convex.relint_subset_relint_of_subset_closure`.
* `Convex.relint_image` — linear images commute with `ri`, with `Convex.relint_smul` and
  `Convex.relint_add`; `Convex.relint_preimage` and `Convex.closure_preimage` do the same for
  inverse images, provided some point is carried into `ri D`.
* `Convex.mem_relint_prod_iff` — relative interior points of a convex set in a product, read off
  from the projection and the slice; `Convex.relint_cone_prodMk_one` applies it to the cone over
  `C`, and `Convex.relint_convexHull_union` to the convex hull of a union.
* `ConvexFn.relint_epi` — the relative interior of an epigraph, whence
  `ConvexFn.exists_mem_relint_dom_lt` and `ConvexFn.le_of_mem_closure`.
* `ConvexFn.eq_bot_of_mem_relint_dom` — an improper convex function is `−∞` on `ri (dom f)`.
* `ConvexFn.proper_clFn`, `ConvexFn.clFn_eq_of_mem_relint_dom` — the closure of a proper convex
  function is proper and agrees with it on `ri (dom f)`; with `ConvexFn.relint_dom_clFn` and
  `ConvexFn.interior_dom_clFn`, `dom (cl f)` has the same relative interior *and* the same
  interior as `dom f`.
* `ConvexFn.tendsto_lscHull_along_segment_relint` — the closure of `f` at `y` as a limit of `f`
  along a segment towards `y` from a relative interior point of `dom f`.
* `ConvexFn.relint_setOf_le`, `ConvexFn.closure_setOf_le` — the relative interior and the closure
  of a level set, with `ConvexFn.relint_setOf_lt_eq`, `ConvexFn.closure_setOf_lt_eq` and the
  relatively open and closed special cases.
* `exists_separatesProperly_iff_disjoint_relint` — two nonempty convex sets separate properly
  exactly when their relative interiors are disjoint (Theorem 11.3 in [^1]).

## Implementation notes

Everything rests on `mem_intrinsicInterior_iff`, which converts `x ∈ ri s` — defined in Mathlib
through the subspace topology on `affineSpan ℝ s` — into a statement about distances in the ambient
space. Rockafellar instead reduces to the full-dimensional case by transporting along an affine
isomorphism; the metric description avoids that transport, and the `AddTorsor` bookkeeping a change
of ambient space would force on every proof. Finite-dimensionality enters through
`intrinsicClosure_eq_closure` and through closedness of affine subspaces; results not needing it
carry `omit [FiniteDimensional ℝ E]`.

The convexity lemmas are named `Convex.*` and shadow the root namespace `Convex`. Generalised field
notation resolves `hC.segment_mem_relint` against the *root* `Convex` namespace only, so these
lemmas must be applied by their explicit names, `Convex.segment_mem_relint hC …`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §6, §7 and §11.
-/

open Set Filter Topology Pointwise

namespace ConvexAnalysis

/-- Rockafellar's `ri C`, the *relative interior* of `C`: Mathlib's `intrinsicInterior ℝ C`. -/
scoped notation "ri" => intrinsicInterior ℝ

/-! ### The positive part of a convex set

A convex set on which a continuous linear functional is non-negative and somewhere positive is the
closure of the part where the functional is *strictly* positive. This is a segment argument in a
topological vector space — no relative interiors, no finite dimension — and it is the density step
that every "a closed convex cone is the closure of the cone generated by one of its cross-sections"
argument runs on. -/

section Positive

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {C : Set E} {ℓ : E →ₗ[ℝ] ℝ} {x₀ : E}

/-- **The strictly positive part of a convex set is dense in it.** If a continuous linear functional
`ℓ` is non-negative on a convex set `C` and positive at one of its points `x₀`, then every point `x`
of `C` is a limit of points of `C` at which `ℓ` is positive: the segment points
`(1 - t) x + t x₀` have `ℓ` value `(1 - t) ℓ x + t ℓ x₀ > 0` for `0 < t ≤ 1`. No continuity of `ℓ`
is needed, the approximating points being produced explicitly. -/
theorem Convex.subset_closure_inter_setOf_pos (hC : Convex ℝ C)
    (hnn : ∀ x ∈ C, 0 ≤ ℓ x) (hx₀ : x₀ ∈ C) (hpos : 0 < ℓ x₀) :
    C ⊆ closure (C ∩ {x | 0 < ℓ x}) := by
  intro x hx
  have hseg : Continuous fun t : ℝ => x + t • (x₀ - x) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have htend : Tendsto (fun t : ℝ => x + t • (x₀ - x)) (𝓝[>] (0 : ℝ)) (𝓝 x) :=
    (hseg.tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend
    (eventually_iff_exists_mem.2 ⟨Ioc 0 1, Ioc_mem_nhdsGT one_pos, fun t ht => ⟨?_, ?_⟩⟩)
  · exact Convex.add_smul_sub_mem hC hx hx₀ ⟨ht.1.le, ht.2⟩
  · have hval : ℓ (x + t • (x₀ - x)) = (1 - t) * ℓ x + t * ℓ x₀ := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
      ring
    have h₁ : 0 ≤ (1 - t) * ℓ x := mul_nonneg (by linarith [ht.2]) (hnn x hx)
    have h₂ : 0 < t * ℓ x₀ := mul_pos ht.1 hpos
    have : (0 : ℝ) < ℓ (x + t • (x₀ - x)) := by rw [hval]; linarith
    exact this

/-- **A convex set is the closure of its strictly positive part**, under the hypotheses of
`Convex.subset_closure_inter_setOf_pos`. -/
theorem Convex.closure_inter_setOf_pos (hC : Convex ℝ C)
    (hnn : ∀ x ∈ C, 0 ≤ ℓ x) (hx₀ : x₀ ∈ C) (hpos : 0 < ℓ x₀) :
    closure (C ∩ {x | 0 < ℓ x}) = closure C :=
  subset_antisymm (closure_mono Set.inter_subset_left)
    (closure_minimal (Convex.subset_closure_inter_setOf_pos hC hnn hx₀ hpos) isClosed_closure)

end Positive

/-! ### The metric description of `ri` -/

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {x : E}

/-- **Rockafellar's definition of `ri`**, recovered from Mathlib's `intrinsicInterior`: a point of
`ri s` is a point of the affine hull of `s` around which every point of the affine hull that is
close enough already lies in `s`. -/
theorem mem_intrinsicInterior_iff :
    x ∈ ri s ↔ x ∈ affineSpan ℝ s ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ s, dist y x < ε → y ∈ s := by
  constructor
  · rintro ⟨⟨y, hy⟩, hint, rfl⟩
    refine ⟨hy, ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨ε, hε, hsub⟩ := hint
    refine ⟨ε, hε, fun z hz hd => ?_⟩
    exact hsub (show (⟨z, hz⟩ : affineSpan ℝ s) ∈ Metric.ball _ ε by
      simpa [Metric.mem_ball, Subtype.dist_eq] using hd)
  · rintro ⟨hx, ε, hε, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    exact ⟨ε, hε, fun z hz => h z z.2 (by simpa [Metric.mem_ball, Subtype.dist_eq] using hz)⟩

/-- A set whose affine hull is everything has `ri s = int s`. In particular this is the case for a
full-dimensional convex set, which is why `ri` is only interesting in lower dimensions. -/
theorem intrinsicInterior_eq_interior (h : affineSpan ℝ s = ⊤) : ri s = interior s := by
  ext x
  rw [mem_intrinsicInterior_iff, h, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  simp only [AffineSubspace.mem_top, true_and, true_implies]
  constructor
  · rintro ⟨ε, hε, h'⟩
    exact ⟨ε, hε, fun y hy => h' y (by simpa [Metric.mem_ball] using hy)⟩
  · rintro ⟨ε, hε, h'⟩
    exact ⟨ε, hε, fun y hy => h' (by simpa [Metric.mem_ball] using hy)⟩

/-- The relative interior of an affine set is the set itself: an affine set is relatively open. -/
@[simp]
theorem AffineSubspace.intrinsicInterior_coe (M : AffineSubspace ℝ E) : ri (M : Set E) = M := by
  ext x
  rw [mem_intrinsicInterior_iff, AffineSubspace.affineSpan_coe]
  exact ⟨And.left, fun h => ⟨h, 1, one_pos, fun _ hy _ => hy⟩⟩

@[simp]
theorem intrinsicInterior_univ : ri (univ : Set E) = univ := by
  simpa using AffineSubspace.intrinsicInterior_coe (⊤ : AffineSubspace ℝ E)

/-- An affine combination of two points of an affine subspace lies in it. -/
theorem AffineSubspace.combo_mem {M : AffineSubspace ℝ E} {p q : E} (hp : p ∈ M) (hq : q ∈ M)
    (t : ℝ) : (1 - t) • p + t • q ∈ M := by
  simpa [AffineMap.lineMap_apply_module] using AffineMap.lineMap_mem (k := ℝ) t hp hq

end Metric

/-! ### The line segment principle -/

section Layer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C₁ C₂ : Set E} {x y : E}

/-- In finite dimensions an affine subspace is closed, so the closure of a set stays inside its
affine hull. -/
theorem closure_subset_affineSpan (s : Set E) : closure s ⊆ affineSpan ℝ s :=
  closure_minimal (subset_affineSpan ℝ s) (affineSpan ℝ s).closed_of_finiteDimensional

/-- **The line segment principle**, the engine of the whole section: the half-open segment from a
relative interior point of a convex set towards a point of its closure stays in the relative
interior. -/
theorem Convex.segment_mem_relint (hC : Convex ℝ C) (hx : x ∈ ri C) (hy : y ∈ closure C)
    {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) : (1 - a) • x + a • y ∈ ri C := by
  rw [mem_intrinsicInterior_iff] at hx ⊢
  obtain ⟨hxA, ε₀, hε₀, hball⟩ := hx
  have hyA : y ∈ affineSpan ℝ C := closure_subset_affineSpan C hy
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1a' : (1 : ℝ) - a ≠ 0 := ne_of_gt h1a
  refine ⟨AffineSubspace.combo_mem hxA hyA a, ε₀ * (1 - a) / 2 / (a + 1) * (a + 1),
    by positivity, fun w hwA hwz => ?_⟩
  set δ : ℝ := ε₀ * (1 - a) / 2 / (a + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨c, hcC, hyc⟩ := Metric.mem_closure_iff.1 hy δ hδ0
  set u : E := (1 - a)⁻¹ • (w - a • c) with hu
  have huA : u ∈ affineSpan ℝ C := by
    have : u = (1 - (1 - a)⁻¹) • c + (1 - a)⁻¹ • w := by
      rw [hu]
      match_scalars <;> field_simp
      ring
    rw [this]
    exact AffineSubspace.combo_mem (subset_affineSpan ℝ C hcC) hwA _
  have hwu : w = (1 - a) • u + a • c := by
    rw [hu, smul_inv_smul₀ h1a']; abel
  have key : u - x = (1 - a)⁻¹ • ((w - ((1 - a) • x + a • y)) + a • (y - c)) := by
    rw [hu]
    match_scalars <;> field_simp
    ring
  have hnorm : ‖u - x‖ ≤ (1 - a)⁻¹ * (‖w - ((1 - a) • x + a • y)‖ + a * ‖y - c‖) := by
    rw [key, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    calc ‖(w - ((1 - a) • x + a • y)) + a • (y - c)‖
        ≤ ‖w - ((1 - a) • x + a • y)‖ + ‖a • (y - c)‖ := norm_add_le _ _
      _ = ‖w - ((1 - a) • x + a • y)‖ + a * ‖y - c‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have h1 : ‖w - ((1 - a) • x + a • y)‖ < δ * (a + 1) := by
    rw [← dist_eq_norm]; exact hwz
  have h2 : a * ‖y - c‖ ≤ a * δ := by
    have : ‖y - c‖ ≤ δ := by rw [← dist_eq_norm]; exact hyc.le
    exact mul_le_mul_of_nonneg_left this ha
  have hux : dist u x < ε₀ := by
    rw [dist_eq_norm]
    have hlt : ‖w - ((1 - a) • x + a • y)‖ + a * ‖y - c‖ < (1 - a) * ε₀ := by
      have hsum : δ * (a + 1) + a * δ < (1 - a) * ε₀ := by
        rw [hδ]; field_simp; nlinarith [hε₀, h1a, hδ0]
      linarith
    calc ‖u - x‖ ≤ (1 - a)⁻¹ * (‖w - ((1 - a) • x + a • y)‖ + a * ‖y - c‖) := hnorm
      _ < (1 - a)⁻¹ * ((1 - a) * ε₀) := by
          exact mul_lt_mul_of_pos_left hlt (by positivity)
      _ = ε₀ := by field_simp
  rw [hwu]
  exact hC (hball u huA hux) hcC h1a.le ha (by ring)

/-! ### Convexity and the affine hull of the relative interior -/

/-- The relative interior of a convex set is convex. -/
protected theorem Convex.relint (hC : Convex ℝ C) : Convex ℝ (ri C) := by
  intro u hu v hv a b ha hb hab
  rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with rfl | hb1
  · have hazero : a = 0 := by linarith
    simpa [hazero] using hv
  · have hab' : a = 1 - b := by linarith
    subst hab'
    exact Convex.segment_mem_relint hC hu (subset_closure (intrinsicInterior_subset hv)) hb hb1

/-- A nonempty convex set has a nonempty relative interior: Mathlib's
`Set.Nonempty.intrinsicInterior`, restated with the argument order the rest of the file uses. -/
theorem Convex.relint_nonempty (hC : Convex ℝ C) (hne : C.Nonempty) : (ri C).Nonempty :=
  hne.intrinsicInterior hC

/-- Taking the closure never changes the affine hull. No convexity is needed; this is
`affineSpan_intrinsicClosure` together with `intrinsicClosure_eq_closure`. -/
@[simp]
theorem affineSpan_closure (s : Set E) : affineSpan ℝ (closure s) = affineSpan ℝ s := by
  rw [← intrinsicClosure_eq_closure ℝ s, affineSpan_intrinsicClosure]

/-- Passing to the relative interior does not change the affine hull, hence does not change the
dimension. -/
@[simp]
theorem Convex.affineSpan_relint (hC : Convex ℝ C) : affineSpan ℝ (ri C) = affineSpan ℝ C := by
  refine le_antisymm (affineSpan_mono ℝ intrinsicInterior_subset) ?_
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hC hne
  rw [affineSpan_le]
  intro w hw
  have hm : (1 - (2 : ℝ)⁻¹) • z + (2 : ℝ)⁻¹ • w ∈ ri C :=
    Convex.segment_mem_relint hC hz (subset_closure hw) (by norm_num) (by norm_num)
  have hrw : w = (1 - (2 : ℝ)) • z + (2 : ℝ) • ((1 - (2 : ℝ)⁻¹) • z + (2 : ℝ)⁻¹ • w) := by
    match_scalars <;> norm_num
  rw [hrw]
  exact AffineSubspace.combo_mem (subset_affineSpan ℝ _ hz) (subset_affineSpan ℝ _ hm) 2

/-- For a full-dimensional convex set the affine hull is the whole space and `ri C = int C`. A
convex set with an interior point is full-dimensional, so the two interiors agree; `int C ⊆ ri C`
is the half every caller uses, since it makes the relative-interior theorems applicable at an
ordinary interior point. -/
theorem Convex.interior_subset_relint (hC : Convex ℝ C) (hne : (interior C).Nonempty) :
    interior C ⊆ ri C :=
  le_of_eq (intrinsicInterior_eq_interior
    ((Convex.interior_nonempty_iff_affineSpan_eq_top hC).1 hne)).symm

/-! ### Interchanging closure and relative interior -/

omit [FiniteDimensional ℝ E] in
/-- The algebraic identity behind every prolongation argument: prolonging the segment from `x` past
`z` by a factor `μ ≠ 0` and then travelling from `x` to that point at parameter `μ⁻¹` returns
to `z`. -/
theorem combo_prolong (x z : E) {μ : ℝ} (hμ : μ ≠ 0) :
    (1 - μ⁻¹) • x + μ⁻¹ • ((1 - μ) • x + μ • z) = z := by
  match_scalars <;> field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- Every segment ending at a relative interior point `z` and starting from a point of the affine
hull can be prolonged slightly beyond `z` without leaving `C`. This is the easy half of the
prolongation criterion, stated for the affine hull rather than for `C` because that is what the
closure results below need. -/
theorem exists_one_lt_smul_mem_of_mem_relint {z : E} (hz : z ∈ ri C)
    (hx : x ∈ affineSpan ℝ C) : ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ C := by
  rw [mem_intrinsicInterior_iff] at hz
  obtain ⟨hzA, ε, hε, hball⟩ := hz
  rcases eq_or_ne x z with rfl | hxz
  · refine ⟨2, one_lt_two, ?_⟩
    have hxx : (1 - (2 : ℝ)) • x + (2 : ℝ) • x = x := by module
    rw [hxx]
    exact hball x hx (by simpa using hε)
  have hpos : 0 < ‖z - x‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hxz h.symm
  refine ⟨1 + ε / (2 * ‖z - x‖), by
    have : 0 < ε / (2 * ‖z - x‖) := by positivity
    linarith, hball _ (AffineSubspace.combo_mem hx hzA _) ?_⟩
  have hd : dist ((1 - (1 + ε / (2 * ‖z - x‖))) • x + (1 + ε / (2 * ‖z - x‖)) • z) z
      = ε / (2 * ‖z - x‖) * ‖z - x‖ := by
    rw [dist_eq_norm]
    have : (1 - (1 + ε / (2 * ‖z - x‖))) • x + (1 + ε / (2 * ‖z - x‖)) • z - z
        = (ε / (2 * ‖z - x‖)) • (z - x) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hd, div_mul_eq_mul_div, mul_comm, mul_div_assoc]
  calc ‖z - x‖ * (ε / (2 * ‖z - x‖)) = ε / 2 := by field_simp
    _ < ε := by linarith

omit [FiniteDimensional ℝ E] in
/-- **A linear function that attains its maximum over `C` at a relative interior point is constant
on `C`** — the half of the relative-boundary criterion below that does not need separation.
Prolonging the segment from `x` past `z` stays in `C`, and a linear function cannot be maximal at
an interior point of a segment without being constant along it. Neither convexity of `C` nor
continuity of `φ` is used. -/
theorem eq_of_isMaxOn_of_mem_relint {φ : E →ₗ[ℝ] ℝ} {z : E}
    (hz : z ∈ ri C) (hmax : ∀ x ∈ C, φ x ≤ φ z) : ∀ x ∈ C, φ x = φ z := by
  intro x hx
  refine le_antisymm (hmax x hx) ?_
  obtain ⟨μ, hμ, hw⟩ := exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  have hval : φ ((1 - μ) • x + μ • z) = (1 - μ) * φ x + μ * φ z := by
    simp [map_add, map_smul]
  have hcon := hmax _ hw
  rw [hval] at hcon
  nlinarith [hcon, hμ]

omit [FiniteDimensional ℝ E] in
/-- The sign form of the preceding lemma: a linear function that is `≤ 0` on `C` and vanishes at a
relative interior point vanishes on all of `C`. -/
theorem eq_zero_of_nonpos_of_mem_relint {φ : E →ₗ[ℝ] ℝ} {z : E}
    (hz : z ∈ ri C) (hnonpos : ∀ x ∈ C, φ x ≤ 0) (hz0 : φ z = 0) : ∀ x ∈ C, φ x = 0 := by
  intro x hx
  have hconst :=
    eq_of_isMaxOn_of_mem_relint hz (fun w hw => by rw [hz0]; exact hnonpos w hw) x hx
  rwa [hz0] at hconst

/-- A convex set and its relative interior have the same closure: `cl (ri C) = cl C`. -/
theorem Convex.closure_relint (hC : Convex ℝ C) : closure (ri C) = closure C := by
  refine Subset.antisymm (closure_mono intrinsicInterior_subset) ?_
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hC hne
  intro w hw
  have hopen : openSegment ℝ z w ⊆ ri C := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    have hab' : a = 1 - b := by linarith
    subst hab'
    exact Convex.segment_mem_relint hC hz hw hb.le (by linarith)
  exact closure_mono hopen (segment_subset_closure_openSegment (right_mem_segment ℝ z w))

/-- A convex set and its closure have the same relative interior: `ri (cl C) = ri C`. -/
theorem Convex.relint_closure (hC : Convex ℝ C) : ri (closure C) = ri C := by
  refine Subset.antisymm ?_ (fun z hz => ?_)
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨x, hx⟩ := Convex.relint_nonempty hC hne
    intro z hz
    obtain ⟨μ, hμ, hy⟩ := exists_one_lt_smul_mem_of_mem_relint hz
      (by rw [affineSpan_closure]; exact subset_affineSpan ℝ C (intrinsicInterior_subset hx))
    have hμ0 : μ ≠ 0 := by positivity
    rw [← combo_prolong x z hμ0]
    exact Convex.segment_mem_relint hC hx hy (by positivity)
      (by rw [inv_lt_one_iff₀]; exact Or.inr hμ)
  · rw [mem_intrinsicInterior_iff] at hz ⊢
    obtain ⟨hzA, ε, hε, hball⟩ := hz
    rw [affineSpan_closure]
    exact ⟨hzA, ε, hε, fun y hy hd => subset_closure (hball y hy hd)⟩

/-- The relative interior is idempotent: `ri (ri C) = ri C`, so `ri C` is relatively open. -/
theorem Convex.relint_relint (hC : Convex ℝ C) : ri (ri C) = ri C := by
  calc ri (ri C) = ri (closure (ri C)) := (Convex.relint_closure (Convex.relint hC)).symm
    _ = ri (closure C) := by rw [Convex.closure_relint hC]
    _ = ri C := Convex.relint_closure hC

/-- Two convex sets have the same closure exactly when they have the same relative interior. -/
theorem Convex.closure_eq_iff_relint_eq (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    closure C₁ = closure C₂ ↔ ri C₁ = ri C₂ := by
  constructor
  · intro h
    rw [← Convex.relint_closure h₁, ← Convex.relint_closure h₂, h]
  · intro h
    rw [← Convex.closure_relint h₁, ← Convex.closure_relint h₂, h]

/-- A set sandwiched between `ri C` and `cl C` has the same closure as `C`. -/
theorem Convex.closure_eq_of_relint_subset_of_subset_closure (h₁ : Convex ℝ C₁)
    (hsub : ri C₁ ⊆ C₂) (hsup : C₂ ⊆ closure C₁) : closure C₂ = closure C₁ :=
  Subset.antisymm (closure_minimal hsup isClosed_closure)
    (Convex.closure_relint h₁ ▸ closure_mono hsub)

/-- An open set meeting `cl C` already meets `ri C`. -/
theorem Convex.relint_inter_nonempty_of_isOpen (hC : Convex ℝ C) {U : Set E} (hU : IsOpen U)
    (h : (U ∩ closure C).Nonempty) : (U ∩ ri C).Nonempty := by
  rw [← Convex.closure_relint hC] at h
  obtain ⟨p, hpU, hpC⟩ := h
  exact closure_nonempty_iff.1 ⟨p, hU.inter_closure ⟨hpU, hpC⟩⟩

/-! ### The prolongation criterion -/

/-- **The prolongation principle**: `z` is a relative interior point of a nonempty convex set `C`
exactly when every segment in `C` ending at `z` can be prolonged slightly beyond `z` inside `C`. -/
theorem Convex.mem_relint_iff_prolong (hC : Convex ℝ C) (hne : C.Nonempty) {z : E} :
    z ∈ ri C ↔ ∀ x ∈ C, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ C := by
  constructor
  · intro hz x hx
    exact exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  · intro h
    obtain ⟨x, hx⟩ := Convex.relint_nonempty hC hne
    obtain ⟨μ, hμ, hy⟩ := h x (intrinsicInterior_subset hx)
    have hμ0 : μ ≠ 0 := ne_of_gt (by linarith)
    rw [← combo_prolong x z hμ0]
    exact Convex.segment_mem_relint hC hx (subset_closure hy) (inv_nonneg.2 (by linarith))
      (by rw [inv_lt_one_iff₀]; exact Or.inr hμ)

/-- A point is *interior* to a convex set exactly when the set absorbs every direction at that
point. The prolongation principle gives the relative-interior version; absorbing every direction
forces the affine hull to be everything, where `ri` and `int` agree. -/
theorem Convex.mem_interior_iff_absorbs (hC : Convex ℝ C) {z : E} :
    z ∈ interior C ↔ ∀ y : E, ∃ ε : ℝ, 0 < ε ∧ z + ε • y ∈ C := by
  constructor
  · intro hz y
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨1, one_pos, by simpa using interior_subset hz⟩
    have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
    refine ⟨δ / (2 * ‖y‖), by positivity, interior_subset (hball ?_)⟩
    have hlt : ‖(δ / (2 * ‖y‖)) • y‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hval : δ / (2 * ‖y‖) * ‖y‖ = δ / 2 := by field_simp
      rw [hval]; linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  · intro h
    have hzC : z ∈ C := by simpa using (h 0).choose_spec.2
    have hspan : affineSpan ℝ C = ⊤ := by
      rw [eq_top_iff]
      rintro w -
      obtain ⟨ε, hε, hmem⟩ := h (w - z)
      have hp : z + ε • (w - z) ∈ affineSpan ℝ C := subset_affineSpan ℝ C hmem
      have hz' : z ∈ affineSpan ℝ C := subset_affineSpan ℝ C hzC
      have hcomb := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ C) ε⁻¹ hp hz' hz'
      simpa [smul_smul, inv_mul_cancel₀ hε.ne'] using hcomb
    rw [← intrinsicInterior_eq_interior hspan]
    refine (Convex.mem_relint_iff_prolong hC ⟨z, hzC⟩).2 fun x hx => ?_
    obtain ⟨ε, hε, hmem⟩ := h (z - x)
    refine ⟨1 + ε, by linarith, ?_⟩
    have hrw : (1 - (1 + ε)) • x + (1 + ε) • z = z + ε • (z - x) := by module
    rw [hrw]
    exact hmem

/-! ### Intersections -/

/-- The technical core of the intersection theorem: from a common relative interior point, every
point common to all the closures is a limit of points common to all the relative interiors. -/
theorem Convex.iInter_closure_subset_closure_iInter_relint {ι : Type*} {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) (h : (⋂ i, ri (C i)).Nonempty) :
    ⋂ i, closure (C i) ⊆ closure (⋂ i, ri (C i)) := by
  obtain ⟨x, hx⟩ := h
  rw [mem_iInter] at hx
  intro y hy
  rw [mem_iInter] at hy
  have hopen : openSegment ℝ x y ⊆ ⋂ i, ri (C i) := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    refine mem_iInter.2 fun i => ?_
    have hab2 : a = 1 - b := by linarith
    subst hab2
    exact Convex.segment_mem_relint (hC i) (hx i) (hy i) hb.le (by linarith)
  exact closure_mono hopen (segment_subset_closure_openSegment (right_mem_segment ℝ x y))

/-- When the relative interiors have a common point, closure commutes with intersection. No
finiteness is needed. -/
theorem Convex.closure_iInter {ι : Type*} {C : ι → Set E} (hC : ∀ i, Convex ℝ (C i))
    (h : (⋂ i, ri (C i)).Nonempty) : closure (⋂ i, C i) = ⋂ i, closure (C i) := by
  refine Subset.antisymm (fun p hp => mem_iInter.2 fun i => closure_mono (iInter_subset _ i) hp) ?_
  exact (Convex.iInter_closure_subset_closure_iInter_relint hC h).trans
    (closure_mono (iInter_mono fun _ => intrinsicInterior_subset))

/-- The easy inclusion `ri (⋂ i, C i) ⊆ ⋂ i, ri (C i)`, valid for an arbitrary index set. -/
theorem Convex.relint_iInter_subset {ι : Type*} {C : ι → Set E} (hC : ∀ i, Convex ℝ (C i))
    (h : (⋂ i, ri (C i)).Nonempty) : ri (⋂ i, C i) ⊆ ⋂ i, ri (C i) := by
  have hcl : closure (⋂ i, ri (C i)) = closure (⋂ i, C i) :=
    Subset.antisymm (closure_mono (iInter_mono fun _ => intrinsicInterior_subset))
      ((Convex.closure_iInter hC h).subset.trans
        (Convex.iInter_closure_subset_closure_iInter_relint hC h))
  have heq := (Convex.closure_eq_iff_relint_eq
    (convex_iInter fun i => Convex.relint (hC i)) (convex_iInter hC)).1 hcl
  rw [← heq]
  exact intrinsicInterior_subset

/-- The relative interior commutes with a finite intersection whose relative interiors have a
common point. Finiteness is essential: the intersection of `ri [0, 1 + α]` over `α > 0` is `(0, 1]`,
not `ri [0, 1]`. -/
theorem Convex.relint_iInter {ι : Type*} [Finite ι] {C : ι → Set E} (hC : ∀ i, Convex ℝ (C i))
    (h : (⋂ i, ri (C i)).Nonempty) : ri (⋂ i, C i) = ⋂ i, ri (C i) := by
  refine Subset.antisymm (Convex.relint_iInter_subset hC h) fun z hz => ?_
  rw [mem_iInter] at hz
  have hne : (⋂ i, C i).Nonempty := ⟨z, mem_iInter.2 fun i => intrinsicInterior_subset (hz i)⟩
  rw [Convex.mem_relint_iff_prolong (convex_iInter hC) hne]
  intro x hx
  rw [mem_iInter] at hx
  choose μ hμ1 hμ2 using fun i =>
    exists_one_lt_smul_mem_of_mem_relint (hz i) (subset_affineSpan ℝ _ (hx i))
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨2, one_lt_two, by simp⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min μ
  refine ⟨μ i₀, hμ1 i₀, mem_iInter.2 fun i => ?_⟩
  have hμi : 0 < μ i := by linarith [hμ1 i]
  have ht0 : (0 : ℝ) ≤ μ i₀ / μ i := div_nonneg (by linarith [hμ1 i₀]) hμi.le
  have ht1 : μ i₀ / μ i ≤ 1 := by rw [div_le_one hμi]; exact hi₀ i
  have heq : (1 - μ i₀ / μ i) • x + (μ i₀ / μ i) • ((1 - μ i) • x + μ i • z)
      = (1 - μ i₀) • x + μ i₀ • z := by
    match_scalars <;> field_simp
    ring
  rw [← heq]
  exact hC i (hx i) (hμ2 i) (by linarith) ht0 (by ring)

/-! ### Binary intersections, and intersections with an affine set -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `Bool` is the finite index type that specialises an indexed intersection to a binary one:
Mathlib's `iInf_bool_eq` read in the complete lattice `Set α`, restated in `⋂`/`∩` form. -/
theorem iInter_bool {α : Type*} (D : Bool → Set α) : (⋂ b, D b) = D true ∩ D false :=
  iInf_bool_eq (f := D)

/-- Closure commutes with the intersection of two convex sets whose relative interiors meet. -/
theorem Convex.closure_inter (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (h : (ri C₁ ∩ ri C₂).Nonempty) : closure (C₁ ∩ C₂) = closure C₁ ∩ closure C₂ := by
  have key := Convex.closure_iInter (C := fun b : Bool => bif b then C₁ else C₂)
    (fun b => by cases b <;> assumption) (by rw [iInter_bool]; exact h)
  rw [iInter_bool, iInter_bool] at key
  exact key

/-- The relative interior commutes with the intersection of two convex sets whose relative
interiors meet. -/
theorem Convex.relint_inter (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (h : (ri C₁ ∩ ri C₂).Nonempty) : ri (C₁ ∩ C₂) = ri C₁ ∩ ri C₂ := by
  have key := Convex.relint_iInter (C := fun b : Bool => bif b then C₁ else C₂)
    (fun b => by cases b <;> assumption) (by rw [iInter_bool]; exact h)
  rw [iInter_bool, iInter_bool] at key
  exact key

/-- Intersecting with an affine set that meets `ri C` commutes with the relative interior. This is
the workhorse of the theory of convex functions and of recession cones. -/
theorem Convex.relint_inter_affine (hC : Convex ℝ C) {M : AffineSubspace ℝ E}
    (h : ((M : Set E) ∩ ri C).Nonempty) : ri ((M : Set E) ∩ C) = (M : Set E) ∩ ri C := by
  have key := Convex.relint_inter M.convex hC (by rwa [AffineSubspace.intrinsicInterior_coe])
  rwa [AffineSubspace.intrinsicInterior_coe] at key

/-- Intersecting with an affine set that meets `ri C` commutes with the closure. -/
theorem Convex.closure_inter_affine (hC : Convex ℝ C) {M : AffineSubspace ℝ E}
    (h : ((M : Set E) ∩ ri C).Nonempty) :
    closure ((M : Set E) ∩ C) = (M : Set E) ∩ closure C := by
  have key := Convex.closure_inter M.convex hC (by rwa [AffineSubspace.intrinsicInterior_coe])
  rwa [M.closed_of_finiteDimensional.closure_eq] at key

/-- A convex subset of `cl C₁` that is not entirely contained in the relative boundary of `C₁` has
its relative interior inside `ri C₁`. -/
theorem Convex.relint_subset_relint_of_subset_closure (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hsub : C₂ ⊆ closure C₁) (h : (C₂ ∩ ri C₁).Nonempty) : ri C₂ ⊆ ri C₁ := by
  have hfr : IsClosed (intrinsicFrontier ℝ C₁) :=
    isClosed_intrinsicFrontier (affineSpan ℝ C₁).closed_of_finiteDimensional
  have hmem : ∀ p : E, p ∈ intrinsicFrontier ℝ C₁ ↔ p ∈ closure C₁ ∧ p ∉ ri C₁ := by
    intro p
    rw [← closure_sdiff_intrinsicInterior (𝕜 := ℝ) C₁]
    exact Iff.rfl
  have hne : (ri C₂ ∩ ri C₁).Nonempty := by
    rcases eq_empty_or_nonempty (ri C₂ ∩ ri C₁) with hem | hne
    · exfalso
      have hsubF : ri C₂ ⊆ intrinsicFrontier ℝ C₁ := fun p hp =>
        (hmem p).2 ⟨hsub (intrinsicInterior_subset hp),
          fun hp1 => absurd (hem ▸ mem_inter hp hp1 : p ∈ (∅ : Set E)) (notMem_empty p)⟩
      have hC₂F : C₂ ⊆ intrinsicFrontier ℝ C₁ :=
        calc C₂ ⊆ closure (ri C₂) := by rw [Convex.closure_relint h₂]; exact subset_closure
          _ ⊆ closure (intrinsicFrontier ℝ C₁) := closure_mono hsubF
          _ = intrinsicFrontier ℝ C₁ := hfr.closure_eq
      obtain ⟨p, hp2, hp1⟩ := h
      exact ((hmem p).1 (hC₂F hp2)).2 hp1
    · exact hne
  have key : ri (C₂ ∩ closure C₁) = ri C₂ ∩ ri C₁ := by
    rw [Convex.relint_inter h₂ h₁.closure (by rwa [Convex.relint_closure h₁]),
      Convex.relint_closure h₁]
  rw [inter_eq_self_of_subset_left hsub] at key
  rw [key]
  exact inter_subset_right

/-! ### Images under a linear map -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A linear image commutes with the relative interior. Continuity of `A` is automatic in finite
dimensions, which is why no hypothesis on `A` appears. -/
theorem Convex.relint_image (hC : Convex ℝ C) (A : E →ₗ[ℝ] F) : ri (A '' C) = A '' ri C := by
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hcl : closure (A '' ri C) = closure (A '' C) := by
    refine Subset.antisymm (closure_mono (image_mono intrinsicInterior_subset))
      (closure_minimal ?_ isClosed_closure)
    calc A '' C ⊆ A '' closure (ri C) := by
          rw [Convex.closure_relint hC]; exact image_mono subset_closure
      _ ⊆ closure (A '' ri C) := image_closure_subset_closure_image hAc
  have heq : ri (A '' C) = ri (A '' ri C) :=
    (Convex.closure_eq_iff_relint_eq (hC.linear_image A)
      ((Convex.relint hC).linear_image A)).1 hcl.symm
  refine Subset.antisymm (by rw [heq]; exact intrinsicInterior_subset) ?_
  rintro w ⟨z, hz, rfl⟩
  have hCne : C.Nonempty := ⟨z, intrinsicInterior_subset hz⟩
  rw [Convex.mem_relint_iff_prolong (hC.linear_image A) (hCne.image A)]
  rintro w ⟨x, hx, rfl⟩
  obtain ⟨μ, hμ, hmem⟩ := exists_one_lt_smul_mem_of_mem_relint hz (subset_affineSpan ℝ C hx)
  exact ⟨μ, hμ, ⟨(1 - μ) • x + μ • z, hmem, by simp⟩⟩

omit [FiniteDimensional ℝ F] in
/-- A linear map carries the closure of a set into the closure of its image: just continuity of
`A`, needing no convexity. -/
theorem image_closure_subset (s : Set E) (A : E →ₗ[ℝ] F) :
    A '' closure s ⊆ closure (A '' s) :=
  image_closure_subset_closure_image A.continuous_of_finiteDimensional

/-- Scaling commutes with the relative interior: `ri (a • C) = a • ri C` for every real `a`,
including `a = 0`. -/
theorem Convex.relint_smul (hC : Convex ℝ C) (a : ℝ) : ri (a • C) = a • ri C := by
  have himg : ∀ D : Set E, (a • LinearMap.id : E →ₗ[ℝ] E) '' D = a • D := fun D => by
    rw [show ⇑(a • LinearMap.id : E →ₗ[ℝ] E) = fun x : E => a • x from rfl]
    exact Set.image_smul
  have h := Convex.relint_image hC (a • LinearMap.id : E →ₗ[ℝ] E)
  rwa [himg, himg] at h

/-- The relative interior of a sum is the sum of the relative interiors. Mathlib's
`intrinsicInterior_prod_eq` supplies the direct-sum half. -/
theorem Convex.relint_add (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    ri (C₁ + C₂) = ri C₁ + ri C₂ := by
  have hA : ∀ D₁ D₂ : Set E,
      (LinearMap.fst ℝ E E + LinearMap.snd ℝ E E) '' (D₁ ×ˢ D₂) = D₁ + D₂ := fun D₁ D₂ => by
    rw [show ⇑(LinearMap.fst ℝ E E + LinearMap.snd ℝ E E) = fun p : E × E => p.1 + p.2 from rfl]
    exact Set.add_image_prod
  have h := Convex.relint_image (h₁.prod h₂) (LinearMap.fst ℝ E E + LinearMap.snd ℝ E E)
  rwa [hA, intrinsicInterior_prod_eq, hA] at h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The sum of the closures is contained in the closure of the sum. -/
theorem closure_add_subset (D₁ D₂ : Set E) :
    closure D₁ + closure D₂ ⊆ closure (D₁ + D₂) := by
  rw [← Set.add_image_prod, ← Set.add_image_prod, ← closure_prod_eq]
  exact image_closure_subset_closure_image (by fun_prop)

/-! ### Inverse images under a linear map -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The set-level identity behind the inverse-image theorem: the graph of `A` meets the horizontal
slab `univ ×ˢ T` exactly over `A ⁻¹' T`. Stated for an arbitrary set `M` presented as the graph, so
the caller may keep whichever coercion of `LinearMap.graph A` it already has. -/
theorem image_fst_inter_prod_univ {A : E →ₗ[ℝ] F} {M : Set (E × F)}
    (hM : M = {p : E × F | p.2 = A p.1}) (T : Set F) :
    ⇑(LinearMap.fst ℝ E F) '' (M ∩ (univ : Set E) ×ˢ T) = A ⁻¹' T := by
  subst hM
  ext x
  constructor
  · rintro ⟨⟨y, z⟩, ⟨hg, -, hz⟩, rfl⟩
    have hg' : z = A y := hg
    exact hg' ▸ hz
  · intro hx
    exact ⟨(x, A x), ⟨rfl, mem_univ _, hx⟩, rfl⟩

/-- An inverse image under a linear map commutes with the relative interior, provided some point is
carried into `ri D`. `A ⁻¹' D` is the projection of `graph A ∩ (univ ×ˢ D)`, so intersection with
an affine set and the image theorem do all the work, the relative interior hypothesis feeding the
former. -/
theorem Convex.relint_preimage {D : Set F} (hD : Convex ℝ D) (A : E →ₗ[ℝ] F)
    (h : (A ⁻¹' ri D).Nonempty) : ri (A ⁻¹' D) = A ⁻¹' ri D := by
  obtain ⟨x₀, hx₀⟩ := h
  set M : AffineSubspace ℝ (E × F) := Submodule.toAffineSubspace (LinearMap.graph A) with hMdef
  have hMset : (M : Set (E × F)) = {p : E × F | p.2 = A p.1} := rfl
  have hriS : ri ((univ : Set E) ×ˢ D) = (univ : Set E) ×ˢ ri D := by
    rw [intrinsicInterior_prod_eq, intrinsicInterior_univ]
  have hne : ((M : Set (E × F)) ∩ ri ((univ : Set E) ×ˢ D)).Nonempty := by
    refine ⟨(x₀, A x₀), ?_, ?_⟩
    · rw [hMset]; rfl
    · rw [hriS]; exact ⟨mem_univ _, hx₀⟩
  have hconv : Convex ℝ ((M : Set (E × F)) ∩ (univ : Set E) ×ˢ D) :=
    M.convex.inter (convex_univ.prod hD)
  have himg := Convex.relint_image hconv (LinearMap.fst ℝ E F)
  rw [Convex.relint_inter_affine (convex_univ.prod hD) hne, hriS] at himg
  rwa [image_fst_inter_prod_univ hMset, image_fst_inter_prod_univ hMset] at himg

/-- The same for closures. One inclusion is continuity of `A`; the other runs through the same
projection of the graph. -/
theorem Convex.closure_preimage {D : Set F} (hD : Convex ℝ D) (A : E →ₗ[ℝ] F)
    (h : (A ⁻¹' ri D).Nonempty) : closure (A ⁻¹' D) = A ⁻¹' closure D := by
  obtain ⟨x₀, hx₀⟩ := h
  refine Subset.antisymm (closure_minimal (preimage_mono subset_closure)
    (isClosed_closure.preimage A.continuous_of_finiteDimensional)) ?_
  set M : AffineSubspace ℝ (E × F) := Submodule.toAffineSubspace (LinearMap.graph A) with hMdef
  have hMset : (M : Set (E × F)) = {p : E × F | p.2 = A p.1} := rfl
  have hriS : ri ((univ : Set E) ×ˢ D) = (univ : Set E) ×ˢ ri D := by
    rw [intrinsicInterior_prod_eq, intrinsicInterior_univ]
  have hne : ((M : Set (E × F)) ∩ ri ((univ : Set E) ×ˢ D)).Nonempty := by
    refine ⟨(x₀, A x₀), ?_, ?_⟩
    · rw [hMset]; rfl
    · rw [hriS]; exact ⟨mem_univ _, hx₀⟩
  have hsub : ⇑(LinearMap.fst ℝ E F) '' closure ((M : Set (E × F)) ∩ (univ : Set E) ×ˢ D)
      ⊆ closure (⇑(LinearMap.fst ℝ E F) '' ((M : Set (E × F)) ∩ (univ : Set E) ×ˢ D)) :=
    image_closure_subset_closure_image continuous_fst
  rw [Convex.closure_inter_affine (convex_univ.prod hD) hne, closure_prod_eq, closure_univ,
    image_fst_inter_prod_univ hMset, image_fst_inter_prod_univ hMset] at hsub
  exact hsub

/-! ### Indexed intersections: the `Finset` and `Set.pi` forms -/

section Indexed

variable {ι : Type*}

omit [FiniteDimensional ℝ E] in
/-- A product set is the intersection of the preimages of its factors under the coordinate
projections. -/
theorem univ_pi_eq_iInter_proj_preimage (C : ι → Set E) :
    univ.pi C = ⋂ i, (LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' C i := by
  ext x
  simp [Set.mem_pi]

/-- Over a `Finset`: the relative interior of a finite intersection is the intersection of the
relative interiors, as soon as the latter has a point in common. This is `Convex.relint_iInter`
read over the subtype `↥s`. -/
theorem Convex.relint_biInter_finset {s : Finset ι} {C : ι → Set E} (hC : ∀ i ∈ s, Convex ℝ (C i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i)) : ri (⋂ i ∈ s, C i) = ⋂ i ∈ s, ri (C i) := by
  have hbi : ∀ D : ι → Set E, (⋂ i ∈ s, D i) = ⋂ i : {j // j ∈ s}, D i := by
    intro D
    ext x
    simp
  rw [hbi C, hbi fun i => ri (C i)]
  exact Convex.relint_iInter (fun i => hC i i.2) ⟨x₀, Set.mem_iInter.2 fun i => hx₀ i i.2⟩

/-- **The relative interior of a product of convex sets is the product of the relative interiors.**
This is the `Set.pi` form of `intrinsicInterior_prod_eq`; unlike that one it needs finite dimension,
being `Convex.relint_iInter` applied to the coordinate preimages. -/
theorem Convex.relint_univ_pi [Finite ι] (C : ι → Set E) (hC : ∀ i, Convex ℝ (C i)) :
    ri (univ.pi C) = univ.pi fun i => ri (C i) := by
  obtain ⟨hι⟩ := nonempty_fintype ι
  by_cases hne : ∀ i, (C i).Nonempty
  · have hproj : ∀ i, ri ((LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' C i)
        = (LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' ri (C i) := by
      intro i
      refine Convex.relint_preimage (hC i) _ ?_
      obtain ⟨z, hz⟩ := Convex.relint_nonempty (hC i) (hne i)
      exact ⟨fun _ => z, hz⟩
    choose z hz using fun i => Convex.relint_nonempty (hC i) (hne i)
    have hnonempty : (⋂ i, ri ((LinearMap.proj i : (ι → E) →ₗ[ℝ] E) ⁻¹' C i)).Nonempty := by
      refine ⟨z, mem_iInter.2 fun i => ?_⟩
      rw [hproj i]
      exact hz i
    rw [univ_pi_eq_iInter_proj_preimage C, univ_pi_eq_iInter_proj_preimage fun i => ri (C i),
      Convex.relint_iInter (fun i => Convex.linear_preimage (hC i) _) hnonempty]
    exact iInter_congr hproj
  · simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hleft : univ.pi C = ∅ := Set.univ_pi_eq_empty_iff.2 ⟨i₀, hi₀⟩
    have hright : (univ.pi fun i => ri (C i)) = ∅ :=
      Set.univ_pi_eq_empty_iff.2 ⟨i₀, by rw [hi₀]; exact intrinsicInterior_empty⟩
    rw [hleft, hright, intrinsicInterior_empty]

end Indexed

/-! ### Slices of a convex set in a product -/

/-- A point of a convex subset of a product is a relative interior point exactly when its first
coordinate is a relative interior point of the projection and its second coordinate is a relative
interior point of the corresponding slice. -/
theorem Convex.mem_relint_prod_iff {S : Set (E × F)} (hS : Convex ℝ S) {y : E} {z : F} :
    (y, z) ∈ ri S ↔ y ∈ ri (Prod.fst '' S) ∧ z ∈ ri {w | (y, w) ∈ S} := by
  have hfst : ri (Prod.fst '' S) = Prod.fst '' ri S := by
    have h := Convex.relint_image hS (LinearMap.fst ℝ E F)
    rwa [show ⇑(LinearMap.fst ℝ E F) = Prod.fst from rfl] at h
  have hVconv : Convex ℝ (({y} : Set E) ×ˢ (univ : Set F)) := (convex_singleton y).prod convex_univ
  have hVri : ri (({y} : Set E) ×ˢ (univ : Set F)) = ({y} : Set E) ×ˢ (univ : Set F) := by
    rw [intrinsicInterior_prod_eq, intrinsicInterior_singleton, intrinsicInterior_univ]
  have hVS : (({y} : Set E) ×ˢ (univ : Set F)) ∩ S = ({y} : Set E) ×ˢ {w | (y, w) ∈ S} := by
    ext ⟨u, v⟩
    simp only [mem_inter_iff, Set.mem_prod, mem_singleton_iff, mem_univ, and_true]
    constructor
    · rintro ⟨rfl, hmem⟩
      exact ⟨rfl, hmem⟩
    · rintro ⟨rfl, hmem⟩
      exact ⟨rfl, hmem⟩
  have hslice : ((({y} : Set E) ×ˢ (univ : Set F)) ∩ ri S).Nonempty →
      (({y} : Set E) ×ˢ (univ : Set F)) ∩ ri S = ({y} : Set E) ×ˢ ri {w | (y, w) ∈ S} := by
    intro hne
    have h := Convex.relint_inter hVconv hS (by rwa [hVri])
    rw [hVri] at h
    rw [← h, hVS, intrinsicInterior_prod_eq, intrinsicInterior_singleton]
  constructor
  · intro hmem
    have hy : y ∈ ri (Prod.fst '' S) := by rw [hfst]; exact ⟨(y, z), hmem, rfl⟩
    have hne : ((({y} : Set E) ×ˢ (univ : Set F)) ∩ ri S).Nonempty :=
      ⟨(y, z), ⟨rfl, mem_univ z⟩, hmem⟩
    have hmem' : (y, z) ∈ ({y} : Set E) ×ˢ ri {w | (y, w) ∈ S} :=
      hslice hne ▸ (⟨⟨rfl, mem_univ z⟩, hmem⟩ :
        (y, z) ∈ (({y} : Set E) ×ˢ (univ : Set F)) ∩ ri S)
    exact ⟨hy, hmem'.2⟩
  · rintro ⟨hy, hz⟩
    rw [hfst] at hy
    obtain ⟨p, hp, hpy⟩ := hy
    have hne : ((({y} : Set E) ×ˢ (univ : Set F)) ∩ ri S).Nonempty :=
      ⟨p, ⟨hpy, mem_univ p.2⟩, hp⟩
    have hmem : (y, z) ∈ (({y} : Set E) ×ˢ (univ : Set F)) ∩ ri S := by
      rw [hslice hne]; exact ⟨rfl, hz⟩
    exact hmem.2

/-! ### Recession cones -/

/-! ### The cone over a convex set, and convex hulls of unions

Rockafellar's `K`, the convex cone in `ℝ × E` generated by `{1} × C`, is written out here as the
explicit set `insert 0 {p | 0 < p.1 ∧ p.2 ∈ p.1 • C}`; `coe_hull_prodMk_one` in
`Numlib/Analysis/Convex/Recession/ConeHull.lean` identifies it with
`PointedCone.hull ℝ ({1} × C)`. -/

section Cone

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The relative interior of a closed half-line of `ℝ` is the corresponding open half-line. -/
theorem intrinsicInterior_Ici (α : ℝ) : ri (Ici α) = Ioi α := by
  have hspan : affineSpan ℝ (Ici α) = ⊤ := by
    rw [← (convex_Ici α).interior_nonempty_iff_affineSpan_eq_top, interior_Ici]
    exact ⟨α + 1, by simp⟩
  rw [intrinsicInterior_eq_interior hspan, interior_Ici]

omit [FiniteDimensional ℝ E] in
/-- The cone `{(λ, x) | λ > 0, x ∈ λC} ∪ {0}` over a convex set is convex. The convex combination is
checked directly, `Convex.add_smul` (`(s + t) • C = s • C + t • C`) carrying the only interesting
case. -/
theorem convex_cone_prodMk_one (hC : Convex ℝ C) :
    Convex ℝ (insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C}) := by
  have hsmul : ∀ (t : ℝ) (w : E) (a : ℝ), w ∈ t • C → a • w ∈ (a * t) • C := by
    rintro t w a ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [smul_smul]⟩
  intro p hp q hq a b ha hb hab
  refine combo_of_pos (P := fun r : ℝ × E =>
      r ∈ insert (0 : ℝ × E) {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C})
    hp hq ha hb hab fun ha' hb' => ?_
  have h1 : (a • p + b • q).1 = a * p.1 + b * q.1 := by simp [smul_eq_mul]
  have h2 : (a • p + b • q).2 = a • p.2 + b • q.2 := by simp
  rcases hp with hp0 | ⟨hp1, hp2⟩
  · rcases hq with hq0 | ⟨hq1, hq2⟩
    · exact Or.inl (by rw [hp0, hq0, smul_zero, smul_zero, add_zero])
    · refine Or.inr ⟨?_, ?_⟩
      · rw [h1, hp0]; simpa using mul_pos hb' hq1
      · rw [h1, h2, hp0]; simpa using hsmul q.1 q.2 b hq2
  · rcases hq with hq0 | ⟨hq1, hq2⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [h1, hq0]; simpa using mul_pos ha' hp1
      · rw [h1, h2, hq0]; simpa using hsmul p.1 p.2 a hp2
    · refine Or.inr ⟨?_, ?_⟩
      · rw [h1]; exact add_pos (mul_pos ha' hp1) (mul_pos hb' hq1)
      · rw [h1, h2, _root_.Convex.add_smul hC (by positivity) (by positivity)]
        exact Set.add_mem_add (hsmul p.1 p.2 a hp2) (hsmul q.1 q.2 b hq2)

omit [FiniteDimensional ℝ E] in
/-- The horizontal slices of the cone over `C`, above a *positive* height. -/
theorem slice_cone_prodMk_one {t : ℝ} (ht : 0 < t) (C : Set E) :
    {w : E | ((t, w) : ℝ × E) ∈ insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C}} = t • C := by
  ext w
  refine ⟨?_, fun hw => Or.inr ⟨ht, hw⟩⟩
  rintro (h0 | ⟨-, h2⟩)
  · exact absurd (congrArg Prod.fst h0 : t = 0) ht.ne'
  · exact h2

omit [FiniteDimensional ℝ E] in
/-- The projection of the cone over a nonempty `C` on the homogenising coordinate. -/
theorem image_fst_cone_prodMk_one (hne : C.Nonempty) :
    Prod.fst '' insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C} = Ici (0 : ℝ) := by
  obtain ⟨x, hx⟩ := hne
  ext t
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with hp0 | ⟨hp1, -⟩
    · exact le_of_eq (congrArg Prod.fst hp0 : p.1 = 0).symm
    · exact hp1.le
  · intro ht
    have ht0 : (0 : ℝ) ≤ t := ht
    rcases eq_or_lt_of_le ht0 with rfl | ht'
    · exact ⟨0, Or.inl rfl, rfl⟩
    · exact ⟨(t, t • x), Or.inr ⟨ht', Set.smul_mem_smul_set hx⟩, rfl⟩

/-- The relative interior of the convex cone generated by `{1} × C` consists of the pairs `(λ, x)`
with `λ > 0` and `x ∈ λ (ri C)`. This is the product criterion with the first factor `ℝ`: the
projection of the cone is `[0, ∞)`, whose relative interior is `(0, ∞)`, and the slice above
`λ > 0` is `λ C`. -/
theorem Convex.relint_cone_prodMk_one (hC : Convex ℝ C) (hne : C.Nonempty) :
    ri (insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C})
      = {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • ri C} := by
  ext p
  obtain ⟨t, w⟩ := p
  rw [Convex.mem_relint_prod_iff (convex_cone_prodMk_one hC), image_fst_cone_prodMk_one hne,
    intrinsicInterior_Ici]
  constructor
  · rintro ⟨ht, hw⟩
    have ht' : (0 : ℝ) < t := ht
    rw [slice_cone_prodMk_one ht' C, Convex.relint_smul hC] at hw
    exact ⟨ht', hw⟩
  · rintro ⟨ht, hw⟩
    refine ⟨ht, ?_⟩
    rw [slice_cone_prodMk_one ht C, Convex.relint_smul hC]
    exact hw

/-- A point of `C` lies in `ri C` exactly when its lift to height one lies in the relative
interior of the cone over `C`. -/
theorem Convex.mem_relint_iff_mk_one_mem_relint_cone (hC : Convex ℝ C) (hne : C.Nonempty)
    {x : E} :
    x ∈ ri C ↔ ((1, x) : ℝ × E) ∈ ri (insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C}) := by
  rw [Convex.relint_cone_prodMk_one hC hne]
  simp

omit [FiniteDimensional ℝ E] in
/-- The cone over `conv (C₁ ∪ C₂)` is the sum of the cones over `C₁` and over `C₂`: the convex hull
of a union becomes a sum one dimension up. -/
theorem cone_prodMk_one_convexHull_union (h₁ : Convex ℝ C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • convexHull ℝ (C₁ ∪ C₂)}
      = insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C₁}
        + insert 0 {p : ℝ × E | 0 < p.1 ∧ p.2 ∈ p.1 • C₂} := by
  have hsub₁ : C₁ ⊆ convexHull ℝ (C₁ ∪ C₂) :=
    (subset_union_left).trans (subset_convexHull ℝ _)
  have hsub₂ : C₂ ⊆ convexHull ℝ (C₁ ∪ C₂) :=
    (subset_union_right).trans (subset_convexHull ℝ _)
  refine subset_antisymm ?_ ?_
  · rintro r (hr0 | ⟨hr1, x, hx, hxr⟩)
    · refine ⟨0, Or.inl rfl, 0, Or.inl rfl, ?_⟩
      change (0 : ℝ × E) + 0 = r
      rw [add_zero, hr0]
    · rw [_root_.Convex.convexHull_union h₁ h₂ hne₁ hne₂, mem_convexJoin] at hx
      obtain ⟨u, hu, v, hv, a, b, ha, hb, hab, huv⟩ := hx
      have hxr' : r.1 • x = r.2 := hxr
      refine ⟨(r.1 * a, (r.1 * a) • u), ?_, (r.1 * b, (r.1 * b) • v), ?_, ?_⟩
      · rcases eq_or_lt_of_le (mul_nonneg hr1.le ha) with h | h
        · exact Or.inl (by rw [Prod.ext_iff]; exact ⟨h.symm, by rw [← h, zero_smul]; rfl⟩)
        · exact Or.inr ⟨h, Set.smul_mem_smul_set hu⟩
      · rcases eq_or_lt_of_le (mul_nonneg hr1.le hb) with h | h
        · exact Or.inl (by rw [Prod.ext_iff]; exact ⟨h.symm, by rw [← h, zero_smul]; rfl⟩)
        · exact Or.inr ⟨h, Set.smul_mem_smul_set hv⟩
      · refine Prod.ext ?_ ?_
        · change r.1 * a + r.1 * b = r.1
          rw [← mul_add, hab, mul_one]
        · change (r.1 * a) • u + (r.1 * b) • v = r.2
          rw [← hxr', ← huv, mul_smul, mul_smul, ← smul_add]
  · rintro _ ⟨p, hp, q, hq, rfl⟩
    have h1 : (p + q).1 = p.1 + q.1 := rfl
    have h2 : (p + q).2 = p.2 + q.2 := rfl
    rcases hp with hp0 | ⟨hp1, hp2⟩
    · rcases hq with hq0 | ⟨hq1, hq2⟩
      · refine Or.inl ?_
        change (p : ℝ × E) + q = 0
        rw [hp0, hq0, add_zero]
      · refine Or.inr ⟨?_, ?_⟩
        · rw [h1, hp0]; simpa using hq1
        · rw [h1, h2, hp0]
          simpa using Set.smul_set_mono hsub₂ hq2
    · rcases hq with hq0 | ⟨hq1, hq2⟩
      · refine Or.inr ⟨?_, ?_⟩
        · rw [h1, hq0]; simpa using hp1
        · rw [h1, h2, hq0]
          simpa using Set.smul_set_mono hsub₁ hp2
      · refine Or.inr ⟨?_, ?_⟩
        · rw [h1]; exact add_pos hp1 hq1
        · rw [h1, h2, _root_.Convex.add_smul (convex_convexHull ℝ (C₁ ∪ C₂)) hp1.le hq1.le]
          exact Set.add_mem_add (Set.smul_set_mono hsub₁ hp2) (Set.smul_set_mono hsub₂ hq2)

/-- The relative interior of the convex hull of a union of two nonempty convex sets is the union of
the relative interiors of the convex combinations. The proof passes to the cones one dimension up,
where the convex hull of the union becomes a *sum*, applies the formula for the relative interior
of a sum, and reads the answer off the cone description. -/
theorem Convex.relint_convexHull_union (h₁ : Convex ℝ C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    ri (convexHull ℝ (C₁ ∪ C₂)) = ⋃ a ∈ Ioo (0 : ℝ) 1, ((1 - a) • ri C₁ + a • ri C₂) := by
  have hne₀ : (convexHull ℝ (C₁ ∪ C₂)).Nonempty :=
    (hne₁.mono subset_union_left).mono (subset_convexHull ℝ _)
  ext x
  rw [Convex.mem_relint_iff_mk_one_mem_relint_cone (convex_convexHull ℝ (C₁ ∪ C₂)) hne₀,
    cone_prodMk_one_convexHull_union h₁ hne₁ h₂ hne₂,
    Convex.relint_add (convex_cone_prodMk_one h₁) (convex_cone_prodMk_one h₂),
    Convex.relint_cone_prodMk_one h₁ hne₁, Convex.relint_cone_prodMk_one h₂ hne₂]
  constructor
  · rintro ⟨p, ⟨hp1, hp2⟩, q, ⟨hq1, hq2⟩, hpq⟩
    have hsum : p.1 + q.1 = 1 := congrArg Prod.fst hpq
    have hvec : p.2 + q.2 = x := congrArg Prod.snd hpq
    refine mem_iUnion₂.2 ⟨q.1, ⟨hq1, by linarith⟩, ?_⟩
    refine ⟨p.2, ?_, q.2, hq2, hvec⟩
    have : (1 : ℝ) - q.1 = p.1 := by linarith
    rw [this]
    exact hp2
  · intro hx
    obtain ⟨a, ha, u, hu, v, hv, huv⟩ := mem_iUnion₂.1 hx
    exact ⟨(1 - a, u), ⟨by linarith [ha.2], hu⟩, (a, v), ⟨ha.1, hv⟩,
      Prod.ext (by simp) (by simpa using huv)⟩

end Cone

/-- The relative interior and the closure of a convex set have the same directions of recession.
This is the statement `Numlib/Analysis/Convex/Recession/Cone.lean` defers, where
`recessionCone_interior_eq_recessionCone_closure` is proved instead. -/
theorem Convex.recessionCone_relint (hC : Convex ℝ C) :
    recessionCone (ri C) = recessionCone (closure C) := by
  refine Subset.antisymm ?_ fun y hy x hx a ha => ?_
  · rw [← Convex.closure_relint hC]
    exact recessionCone_subset_recessionCone_closure _
  · have h2 : x + (2 * a) • y ∈ closure C :=
      hy x (subset_closure (intrinsicInterior_subset hx)) (2 * a) (by linarith)
    have hcombo := Convex.segment_mem_relint hC hx h2 (a := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)
    have heq : (1 - (1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • (x + (2 * a) • y) = x + a • y := by
      match_scalars <;> ring
    rwa [heq] at hcombo

/-! ### The relative interior of an epigraph -/

section Functions

variable {f : E → EReal}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The vertical sections of an epigraph are closed. -/
theorem isClosed_setOf_le (z : EReal) : IsClosed {ν : ℝ | z ≤ (ν : EReal)} :=
  isClosed_le continuous_const continuous_coe_real_ereal

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The relative interior of a vertical section of an epigraph: `ri [f x, ∞) = (f x, ∞)`, with the
degenerate values of `f x` included. -/
theorem intrinsicInterior_setOf_le (z : EReal) :
    ri {ν : ℝ | z ≤ (ν : EReal)} = {ν : ℝ | z < (ν : EReal)} := by
  induction z with
  | bot =>
    have h1 : {ν : ℝ | (⊥ : EReal) ≤ (ν : EReal)} = univ := by ext ν; simp
    have h2 : {ν : ℝ | (⊥ : EReal) < (ν : EReal)} = univ := by ext ν; simp
    rw [h1, h2, intrinsicInterior_univ]
  | coe r =>
    have h1 : {ν : ℝ | (r : EReal) ≤ (ν : EReal)} = Ici r := by ext ν; simp
    have h2 : {ν : ℝ | (r : EReal) < (ν : EReal)} = Ioi r := by ext ν; simp
    have hspan : affineSpan ℝ (Ici r) = ⊤ := by
      rw [← (convex_Ici r).interior_nonempty_iff_affineSpan_eq_top, interior_Ici]
      exact ⟨r + 1, by simp⟩
    rw [h1, h2, intrinsicInterior_eq_interior hspan, interior_Ici]
  | top =>
    have h1 : {ν : ℝ | (⊤ : EReal) ≤ (ν : EReal)} = ∅ := by
      ext ν; simp
    have h2 : {ν : ℝ | (⊤ : EReal) < (ν : EReal)} = ∅ := by
      ext ν; simp
    rw [h1, h2, intrinsicInterior_empty]

/-- The relative interior of an epigraph consists of the pairs `(x, μ)` with `x ∈ ri (dom f)` and
`f x < μ < ∞`. This is the product criterion in which the second factor is `ℝ`. -/
theorem ConvexFn.relint_epi (hf : ConvexFn f) :
    ri (epi f) = {p : E × ℝ | p.1 ∈ ri (dom f) ∧ f p.1 < (p.2 : EReal)} := by
  ext p
  obtain ⟨x, μ⟩ := p
  have hsec : {w : ℝ | (x, w) ∈ epi f} = {ν : ℝ | f x ≤ (ν : EReal)} := rfl
  rw [Convex.mem_relint_prod_iff hf.convex_epi, ← dom_eq_fst_image_epi, hsec,
    intrinsicInterior_setOf_le]
  exact Iff.rfl

/-! ### Improper convex functions -/

omit [FiniteDimensional ℝ E] in
/-- An improper convex function takes the value `−∞` at every relative interior point of its
effective domain — so it is infinite except perhaps at relative boundary points of `dom f`.
`ConvexFn.eq_bot_or_eq_top` in `Numlib/Analysis/Convex/Closure.lean` is the dimension-free
replacement, valid in any topological vector space; this is the finite-dimensional statement, which
needs no hypothesis on `dom f` and locates the `⊥` values precisely. -/
theorem ConvexFn.eq_bot_of_mem_relint_dom (hf : ConvexFn f) (hp : ¬ Proper f) {x : E}
    (hx : x ∈ ri (dom f)) : f x = ⊥ := by
  have hxd : x ∈ dom f := intrinsicInterior_subset hx
  have hbot : ∃ u, f u = ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hp ⟨⟨x, hxd⟩, hcon⟩
  obtain ⟨u, hu⟩ := hbot
  have hud : u ∈ dom f := mem_dom.2 (by rw [hu]; exact bot_lt_top)
  obtain ⟨μ, hμ, hy⟩ :=
    exists_one_lt_smul_mem_of_mem_relint hx (subset_affineSpan ℝ (dom f) hud)
  have hμ0 : μ ≠ 0 := ne_of_gt (by linarith)
  have hkey := hf.eq_bot_of_lt_one hu hy (inv_nonneg.2 (by linarith))
    (by rw [inv_lt_one_iff₀]; exact Or.inr hμ)
  rwa [combo_prolong u x hμ0] at hkey

/-- A lower semicontinuous improper convex function is `−∞` on the whole closure of its effective
domain — the finite-dimensional sharpening of the preceding statement. -/
theorem ConvexFn.eq_bot_of_mem_closure_dom (hf : ConvexFn f) (hl : LowerSemicontinuous f)
    (hp : ¬ Proper f) {x : E} (hx : x ∈ closure (dom f)) : f x = ⊥ := by
  by_contra hne
  obtain ⟨U, hU, hxU, hUlt⟩ : ∃ U, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (⊥ : EReal) < f y := by
    obtain ⟨U, hUmem, hU, hxU⟩ := mem_nhds_iff.1 (hl x ⊥ (bot_lt_iff_ne_bot.2 hne))
    exact ⟨U, hU, hxU, fun y hy => hUmem hy⟩
  obtain ⟨y, hyU, hy⟩ := Convex.relint_inter_nonempty_of_isOpen hf.convex_dom hU ⟨x, hxU, hx⟩
  exact absurd (hf.eq_bot_of_mem_relint_dom hp hy) (hUlt y hyU).ne'

omit [FiniteDimensional ℝ E] in
/-- A convex function whose effective domain is relatively open is either nowhere `−∞`, or
everywhere infinite. -/
theorem ConvexFn.forall_ne_bot_or_forall_infinite (hf : ConvexFn f) (hopen : ri (dom f) = dom f) :
    (∀ x, f x ≠ ⊥) ∨ ∀ x, f x = ⊥ ∨ f x = ⊤ := by
  by_cases hp : Proper f
  · exact Or.inl hp.ne_bot
  · refine Or.inr fun x => ?_
    rcases eq_top_or_lt_top (f x) with h | h
    · exact Or.inr h
    · exact Or.inl (hf.eq_bot_of_mem_relint_dom hp (by rw [hopen]; exact h))

/-! ### The closure of a proper convex function -/

/-- The key step: the lower semicontinuous hull agrees with `f` at every relative interior point of
`dom f`. The vertical line over `x` meets `ri (epi f)`, so intersecting with an affine set lets the
closure be computed inside that line, where the epigraph section is already closed. -/
theorem ConvexFn.lscHull_eq_of_mem_relint_dom (hf : ConvexFn f) {x : E}
    (hx : x ∈ ri (dom f)) : lscHull f x = f x := by
  have hVconv : Convex ℝ (({x} : Set E) ×ˢ (univ : Set ℝ)) := (convex_singleton x).prod convex_univ
  have hVri : ri (({x} : Set E) ×ˢ (univ : Set ℝ)) = ({x} : Set E) ×ˢ (univ : Set ℝ) := by
    rw [intrinsicInterior_prod_eq, intrinsicInterior_singleton, intrinsicInterior_univ]
  have hVcl : closure (({x} : Set E) ×ˢ (univ : Set ℝ)) = ({x} : Set E) ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_singleton, closure_univ]
  have hVe : (({x} : Set E) ×ˢ (univ : Set ℝ)) ∩ epi f
      = ({x} : Set E) ×ˢ {ν : ℝ | f x ≤ (ν : EReal)} := by
    ext q
    obtain ⟨u, v⟩ := q
    simp only [mem_inter_iff, Set.mem_prod, mem_singleton_iff, mem_univ, and_true]
    constructor
    · rintro ⟨rfl, hmem⟩; exact ⟨rfl, hmem⟩
    · rintro ⟨rfl, hmem⟩; exact ⟨rfl, hmem⟩
  have hxd : x ∈ dom f := intrinsicInterior_subset hx
  obtain ⟨μ₀, hμ₀, -⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (mem_dom.1 hxd)
  have hne : (ri (({x} : Set E) ×ˢ (univ : Set ℝ)) ∩ ri (epi f)).Nonempty :=
    ⟨(x, μ₀), by rw [hVri]; exact ⟨rfl, mem_univ _⟩, by rw [hf.relint_epi]; exact ⟨hx, hμ₀⟩⟩
  have hkey := Convex.closure_inter hVconv hf.convex_epi hne
  rw [hVcl, (by rw [hVe]; exact isClosed_singleton.prod (isClosed_setOf_le (f x)) :
    IsClosed ((({x} : Set E) ×ˢ (univ : Set ℝ)) ∩ epi f)).closure_eq] at hkey
  refine le_antisymm (lscHull_le f x) ?_
  refine le_ofEpi fun μ hμ => ?_
  have hmem : (x, μ) ∈ (({x} : Set E) ×ˢ (univ : Set ℝ)) ∩ closure (epi f) :=
    ⟨⟨rfl, mem_univ _⟩, hμ⟩
  rw [← hkey] at hmem
  exact hmem.2

/-- The lower semicontinuous hull of a *proper* convex function is nowhere `−∞`. This is what makes
`clFn f` the hull rather than the constant `⊥`, and it is finite-dimensional. -/
theorem ConvexFn.lscHull_ne_bot (hf : ConvexFn f) (hp : Proper f) (x : E) : lscHull f x ≠ ⊥ := by
  intro hbot
  have hgp : ¬ Proper (lscHull f) := fun hpr => hpr.ne_bot x hbot
  have hcl : closure (dom (lscHull f)) = closure (dom f) :=
    Convex.closure_eq_of_relint_subset_of_subset_closure hf.convex_dom
      (intrinsicInterior_subset.trans (dom_subset_dom_lscHull f))
      (dom_lscHull_subset_closure_dom f)
  have hdom : ri (dom (lscHull f)) = ri (dom f) :=
    (Convex.closure_eq_iff_relint_eq (convexFn_lscHull hf).convex_dom hf.convex_dom).1 hcl
  obtain ⟨z, hz⟩ := Convex.relint_nonempty hf.convex_dom hp.dom_nonempty
  have h1 : lscHull f z = ⊥ :=
    (convexFn_lscHull hf).eq_bot_of_mem_relint_dom hgp (by rw [hdom]; exact hz)
  exact hp.ne_bot z (hf.lscHull_eq_of_mem_relint_dom hz ▸ h1)

/-- For a proper convex function the closure *is* the lower semicontinuous hull; the exceptional
branch of `clFn` is never taken. -/
theorem ConvexFn.clFn_eq_lscHull (hf : ConvexFn f) (hp : Proper f) : clFn f = lscHull f :=
  clFn_of_forall_ne_bot (hf.lscHull_ne_bot hp)

/-- The closure of a proper convex function is proper (and hence, by `closedFn_clFn`, a closed
proper convex function). -/
theorem ConvexFn.proper_clFn (hf : ConvexFn f) (hp : Proper f) : Proper (clFn f) := by
  rw [hf.clFn_eq_lscHull hp]
  exact ⟨hp.dom_nonempty.mono (dom_subset_dom_lscHull f), hf.lscHull_ne_bot hp⟩

/-- `cl f` agrees with `f` at every relative interior point of `dom f`, whether or not `f` is
proper. -/
theorem ConvexFn.clFn_eq_of_mem_relint_dom (hf : ConvexFn f) {x : E} (hx : x ∈ ri (dom f)) :
    clFn f x = f x := by
  by_cases hp : Proper f
  · rw [hf.clFn_eq_lscHull hp]
    exact hf.lscHull_eq_of_mem_relint_dom hx
  · have hbot : f x = ⊥ := hf.eq_bot_of_mem_relint_dom hp hx
    have hl : lscHull f x = ⊥ := le_bot_iff.1 (hbot ▸ lscHull_le f x)
    rw [clFn_of_exists_eq_bot ⟨x, hl⟩, hbot]

/-- `cl f` also agrees with `f` off the closure of `dom f`, where both are `+∞`. Together with
`ConvexFn.clFn_eq_of_mem_relint_dom` this is the assertion that `cl f` differs from `f` at most at
relative boundary points of `dom f`. -/
theorem ConvexFn.clFn_eq_of_notMem_closure_dom (hf : ConvexFn f) (hp : Proper f) {x : E}
    (hx : x ∉ closure (dom f)) : clFn f x = f x := by
  rw [hf.clFn_eq_lscHull hp]
  have h1 : lscHull f x = ⊤ := by
    by_contra h
    exact hx (dom_lscHull_subset_closure_dom f (mem_dom.2 (lt_of_le_of_ne le_top h)))
  have h2 : f x = ⊤ := by
    by_contra h
    exact hx (subset_closure (mem_dom.2 (lt_of_le_of_ne le_top h)))
  rw [h1, h2]

/-- `dom (cl f)` is squeezed between `dom f` and its closure, so the two domains have the same
closure and the same relative interior. -/
theorem ConvexFn.relint_dom_clFn (hf : ConvexFn f) (hp : Proper f) :
    ri (dom (clFn f)) = ri (dom f) := by
  rw [hf.clFn_eq_lscHull hp]
  exact (Convex.closure_eq_iff_relint_eq (convexFn_lscHull hf).convex_dom hf.convex_dom).1
    (Convex.closure_eq_of_relint_subset_of_subset_closure hf.convex_dom
      (intrinsicInterior_subset.trans (dom_subset_dom_lscHull f))
      (dom_lscHull_subset_closure_dom f))

/-- The companion statement for *interiors*: `dom (cl f)` has the same plain interior as `dom f`,
not only the same relative interior. The inclusion `⊇` is `cl f ≤ f`; for `⊆`,
`interior (dom (cl f))` is an *open* set inside `ri (dom (cl f)) = ri (dom f) ⊆ dom f`, and an open
subset of a set is inside its interior. -/
theorem ConvexFn.interior_dom_clFn (hf : ConvexFn f) (hp : Proper f) :
    interior (dom (clFn f)) = interior (dom f) := by
  refine Set.Subset.antisymm ?_ (interior_mono fun z hz =>
    mem_dom.2 (lt_of_le_of_lt (clFn_le f z) (mem_dom.1 hz)))
  rcases Set.eq_empty_or_nonempty (interior (dom (clFn f))) with hemp | hne
  · rw [hemp]
    exact Set.empty_subset _
  refine interior_maximal ?_ isOpen_interior
  refine (Convex.interior_subset_relint (convexFn_clFn hf).convex_dom hne).trans ?_
  rw [hf.relint_dom_clFn hp]
  exact intrinsicInterior_subset

/-- A proper convex function whose effective domain is an affine set — in particular one that is
finite everywhere — is closed. -/
theorem ConvexFn.closedFn_of_dom_eq_coe (hf : ConvexFn f) (hp : Proper f)
    {M : AffineSubspace ℝ E} (hdom : dom f = (M : Set E)) : ClosedFn f := by
  refine funext fun x => ?_
  by_cases hx : x ∈ dom f
  · refine hf.clFn_eq_of_mem_relint_dom ?_
    rw [hdom, AffineSubspace.intrinsicInterior_coe]
    rwa [hdom] at hx
  · refine hf.clFn_eq_of_notMem_closure_dom hp ?_
    rw [hdom, M.closed_of_finiteDimensional.closure_eq]
    rwa [hdom] at hx

/-- A convex function bounded below by a real constant on a convex set on which it is finite is
bounded below by that same constant on the closure of the set. The line segment principle plus one
limit: from a relative interior point `y` of `D` the whole half-open segment towards `x ∈ cl D`
stays in `D`, so the affine bound is `≥ c` for every `t < 1`. Rockafellar carries no hypothesis at
`−∞`; here `g` is asked never to take that value, which is how the result is used and what makes
the statement true as it stands. -/
theorem ConvexFn.le_of_mem_closure (hf : ConvexFn f) (hbot : ∀ z, f z ≠ ⊥) {D : Set E}
    (hD : Convex ℝ D) (hfin : ∀ z ∈ D, f z ≠ ⊤) {c : ℝ} (h : ∀ z ∈ D, (c : EReal) ≤ f z)
    {x : E} (hx : x ∈ closure D) : (c : EReal) ≤ f x := by
  by_cases hxt : f x = ⊤
  · rw [hxt]; exact le_top
  obtain ⟨y, hy⟩ := Convex.relint_nonempty hD (Set.Nonempty.of_closure ⟨x, hx⟩)
  have hyD : y ∈ D := intrinsicInterior_subset hy
  obtain ⟨a, hay⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hbot y) (lt_top_iff_ne_top.2 (hfin y hyD))
  obtain ⟨b, hbx⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) (lt_top_iff_ne_top.2 hxt)
  have key : ∀ t : ℝ, 0 ≤ t → t < 1 → c ≤ (1 - t) * a + t * b := by
    intro t ht0 ht1
    have hmem : (1 - t) • y + t • x ∈ ri D := Convex.segment_mem_relint hD hy hx ht0 ht1
    have hle : f ((1 - t) • y + t • x) ≤ (((1 - t) * a + t * b : ℝ) : EReal) :=
      hf.epi_combo (le_of_eq hay) (le_of_eq hbx) (by linarith) ht0 (by ring)
    exact_mod_cast (h _ (intrinsicInterior_subset hmem)).trans hle
  rw [hbx]
  have hcb : c ≤ b := by
    refine ge_of_tendsto (tendsto_affine_nhdsLT_one a b) ?_
    filter_upwards [eventually_mem_Ico_nhdsLT_one] with t ht
    exact key t ht.1 ht.2
  exact_mod_cast hcb

end Functions

/-! ### Limits along a segment from a relative interior point -/

section SegmentLimits

variable {f : E → EReal}

/-- The lower semicontinuous hull of `f` at `y` is the limit of `f` along the segment running from
a *relative interior* point of `dom f` towards `y`. `Numlib/Analysis/Convex/Closure.lean` proves
`tendsto_lscHull_along_segment`, where the segment must start at an interior point of `epi f`; here
the description of `ri (epi f)` supplies a relative interior point instead, and the line segment
principle replaces Mathlib's `Convex.combo_interior_closure_mem_interior`. -/
theorem ConvexFn.tendsto_lscHull_along_segment_relint (hf : ConvexFn f) {x : E}
    (hx : x ∈ ri (dom f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (lscHull f y)) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [(tendsto_segment x y).eventually (lowerSemicontinuous_lscHull f y b hb)]
      with a ha
    exact lt_of_lt_of_le ha (lscHull_le f _)
  · obtain ⟨β, hβ1, hβ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hb
    obtain ⟨γ, hγ1, hγ2⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hβ2
    have hβγ : β < γ := by exact_mod_cast hγ1
    have hyβ : ((y, β) : E × ℝ) ∈ closure (epi f) := by
      rw [← epi_lscHull]; exact hβ1.le
    obtain ⟨α, hα, -⟩ :=
      _root_.EReal.lt_iff_exists_real_btwn.1 (mem_dom.1 (intrinsicInterior_subset hx))
    have hxα : ((x, α) : E × ℝ) ∈ ri (epi f) := by rw [hf.relint_epi]; exact ⟨hx, hα⟩
    filter_upwards [(tendsto_affine_nhdsLT_one α β).eventually_lt_const hβγ,
      eventually_mem_Ico_nhdsLT_one] with a hlt ha
    have hcombo := Convex.segment_mem_relint hf.convex_epi hxα hyβ ha.1 ha.2
    have hpair : (1 - a) • ((x, α) : E × ℝ) + a • (y, β)
        = ((1 - a) • x + a • y, (1 - a) * α + a * β) := by
      simp [smul_eq_mul]
    rw [hpair] at hcombo
    have hle : f ((1 - a) • x + a • y) ≤ (((1 - a) * α + a * β : ℝ) : EReal) :=
      mk_mem_epi.1 (intrinsicInterior_subset hcombo)
    exact lt_of_le_of_lt hle (lt_trans (by exact_mod_cast hlt) hγ2)

/-- The same limit for `clFn`. Properness is what rules out the exceptional branch of `clFn`;
compare `clFn_eq_limit_along_segment`, which has to assume it directly. -/
theorem ConvexFn.tendsto_clFn_along_segment_relint (hf : ConvexFn f) (hp : Proper f) {x : E}
    (hx : x ∈ ri (dom f)) (y : E) :
    Tendsto (fun a : ℝ => f ((1 - a) • x + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (clFn f y)) := by
  rw [hf.clFn_eq_lscHull hp]
  exact hf.tendsto_lscHull_along_segment_relint hx y

end SegmentLimits

/-! ### The level sets of a convex function -/

section LevelSets

variable {f : E → EReal}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The relative interior of a closed half-line of `ℝ` is the corresponding open half-line. -/
theorem intrinsicInterior_Iic (α : ℝ) : ri (Iic α) = Iio α := by
  have hspan : affineSpan ℝ (Iic α) = ⊤ := by
    rw [← (convex_Iic α).interior_nonempty_iff_affineSpan_eq_top, interior_Iic]
    exact ⟨α - 1, by simp⟩
  rw [intrinsicInterior_eq_interior hspan, interior_Iic]

/-- If a convex function is anywhere below a real level, then it is already below that level at
some *relative interior* point of its effective domain. The open half-space `{(x, μ) | μ < α}`
meets `epi f`, hence meets `ri (epi f)`, and the description of `ri (epi f)` reads off the
point. -/
theorem ConvexFn.exists_mem_relint_dom_lt (hf : ConvexFn f) {α : ℝ}
    (hα : ∃ x, f x < (α : EReal)) : ∃ x ∈ ri (dom f), f x < (α : EReal) := by
  obtain ⟨x, hx⟩ := hα
  obtain ⟨μ, hxμ, hμα⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hx
  have hU : IsOpen {p : E × ℝ | p.2 < α} := isOpen_lt continuous_snd continuous_const
  have hmeets : ({p : E × ℝ | p.2 < α} ∩ closure (epi f)).Nonempty :=
    ⟨(x, μ), by exact_mod_cast hμα, subset_closure (mk_mem_epi.2 hxμ.le)⟩
  obtain ⟨p, hpU, hpri⟩ := Convex.relint_inter_nonempty_of_isOpen hf.convex_epi hU hmeets
  rw [hf.relint_epi] at hpri
  have hpα : p.2 < α := hpU
  exact ⟨p.1, hpri.1, hpri.2.trans (by exact_mod_cast hpα)⟩

/-- The relative interior of a level set: `ri {x | f x ≤ α} = {x ∈ ri (dom f) | f x < α}`, whenever
`α` exceeds the infimum of `f`. The horizontal hyperplane `{(x, α)}` of the textbook argument is
replaced by the *slab* `E × (-∞, α]`, whose relative interior is `E × (-∞, α)`. Properness is not
needed. -/
theorem ConvexFn.relint_setOf_le (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    ri {x | f x ≤ (α : EReal)} = {x ∈ ri (dom f) | f x < (α : EReal)} := by
  obtain ⟨y, hy, hyα⟩ := hf.exists_mem_relint_dom_lt (iInf_lt_iff.1 hα)
  set T : Set (E × ℝ) := (univ : Set E) ×ˢ Iic α with hT
  have hTconv : Convex ℝ T := convex_univ.prod (convex_Iic α)
  have hTri : ri T = (univ : Set E) ×ˢ Iio α := by
    rw [hT, intrinsicInterior_prod_eq, intrinsicInterior_univ, intrinsicInterior_Iic]
  obtain ⟨μ, hyμ, hμα⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hyα
  have hne : (ri (epi f) ∩ ri T).Nonempty := by
    refine ⟨(y, μ), ?_, ?_⟩
    · rw [hf.relint_epi]; exact ⟨hy, hyμ⟩
    · rw [hTri]; exact ⟨mem_univ _, by exact_mod_cast hμα⟩
  have himg : Prod.fst '' (epi f ∩ T) = {x | f x ≤ (α : EReal)} := by
    ext z
    refine ⟨?_, fun hz => ⟨(z, α), ⟨hz, mem_univ _, (le_rfl : α ≤ α)⟩, rfl⟩⟩
    rintro ⟨q, ⟨hq1, -, hq2⟩, rfl⟩
    exact (mk_mem_epi.1 hq1).trans (by exact_mod_cast hq2)
  have hfst : ri (Prod.fst '' (epi f ∩ T)) = Prod.fst '' ri (epi f ∩ T) := by
    have h := Convex.relint_image (hf.convex_epi.inter hTconv) (LinearMap.fst ℝ E ℝ)
    rwa [show ⇑(LinearMap.fst ℝ E ℝ) = Prod.fst from rfl] at h
  rw [← himg, hfst, Convex.relint_inter hf.convex_epi hTconv hne, hf.relint_epi, hTri]
  ext z
  constructor
  · rintro ⟨q, ⟨⟨hq1, hq2⟩, -, hq3⟩, rfl⟩
    exact ⟨hq1, hq2.trans (by exact_mod_cast (hq3 : q.2 < α))⟩
  · rintro ⟨hz1, hz2⟩
    obtain ⟨ν, hzν, hνα⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hz2
    exact ⟨(z, ν), ⟨⟨hz1, hzν⟩, mem_univ _, by exact_mod_cast hνα⟩, rfl⟩

/-- The closure of a level set: `cl {x | f x ≤ α} = {x | (cl f) x ≤ α}`, stated for the lower
semicontinuous hull, which carries the content. `⊆` is `closure_le_subset_lscHull_le` and needs no
hypothesis; for `⊇`, `exists_mem_relint_dom_lt` supplies a point `y ∈ ri (dom f)` with `f y < α`,
and the line segment principle runs the segment from `(y, α) ∈ ri (epi f)` to `(x, α) ∈ cl (epi f)`
inside `ri (epi f)`. -/
theorem ConvexFn.closure_setOf_le (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x ≤ (α : EReal)} = {x | lscHull f x ≤ (α : EReal)} := by
  refine subset_antisymm (closure_le_subset_lscHull_le f α) fun x hx => ?_
  obtain ⟨y, hy, hyα⟩ := hf.exists_mem_relint_dom_lt (iInf_lt_iff.1 hα)
  have hyri : ((y, α) : E × ℝ) ∈ ri (epi f) := by rw [hf.relint_epi]; exact ⟨hy, hyα⟩
  have hxcl : ((x, α) : E × ℝ) ∈ closure (epi f) := by
    rw [← epi_lscHull]; exact mk_mem_epi.2 hx
  refine mem_closure_of_tendsto (tendsto_segment y x) ?_
  filter_upwards [eventually_mem_Ico_nhdsLT_one] with a ha
  have hcombo := Convex.segment_mem_relint hf.convex_epi hyri hxcl ha.1 ha.2
  have hpair : (1 - a) • ((y, α) : E × ℝ) + a • (x, α)
      = ((1 - a) • y + a • x, (1 - a) * α + a * α) := by simp [smul_eq_mul]
  rw [hpair] at hcombo
  have hle := mk_mem_epi.1 (intrinsicInterior_subset hcombo)
  have harith : (1 - a) * α + a * α = α := by ring
  rw [harith] at hle
  exact hle

/-- The two level sets `{f ≤ α}` and `{f < α}` have the same closure. -/
theorem ConvexFn.closure_setOf_lt_eq (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x < (α : EReal)} = closure {x | f x ≤ (α : EReal)} :=
  Convex.closure_eq_of_relint_subset_of_subset_closure (hf.convex_le (α : EReal))
    (by rw [hf.relint_setOf_le hα]; exact fun _ hz => hz.2)
    (fun z hz => subset_closure (show f z ≤ (α : EReal) from le_of_lt hz))

/-- The two level sets `{f ≤ α}` and `{f < α}` have the same relative interior. -/
theorem ConvexFn.relint_setOf_lt_eq (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    ri {x | f x < (α : EReal)} = ri {x | f x ≤ (α : EReal)} :=
  (Convex.closure_eq_iff_relint_eq (hf.convex_lt (α : EReal))
    (hf.convex_le (α : EReal))).1 (hf.closure_setOf_lt_eq hα)

/-- The relative interior of the strict level set `{f < α}`. -/
theorem ConvexFn.relint_setOf_lt (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    ri {x | f x < (α : EReal)} = {x ∈ ri (dom f) | f x < (α : EReal)} :=
  (hf.relint_setOf_lt_eq hα).trans (hf.relint_setOf_le hα)

/-- The closure of the strict level set `{f < α}`, in terms of the lower semicontinuous hull. -/
theorem ConvexFn.closure_setOf_lt (hf : ConvexFn f) {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x < (α : EReal)} = {x | lscHull f x ≤ (α : EReal)} :=
  (hf.closure_setOf_lt_eq hα).trans (hf.closure_setOf_le hα)

/-- The closure formula for a *proper* convex function, where the hull is the closure `cl f`. -/
theorem ConvexFn.closure_setOf_le_clFn (hf : ConvexFn f) (hp : Proper f) {α : ℝ}
    (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x ≤ (α : EReal)} = {x | clFn f x ≤ (α : EReal)} := by
  rw [hf.closure_setOf_le hα, hf.clFn_eq_lscHull hp]

/-- For a convex function whose effective domain is relatively open, the relative interior of a
level set is the corresponding strict level set. Rockafellar assumes `f` closed as well; closedness
is not used. -/
theorem ConvexFn.relint_setOf_le_of_relint_dom_eq (hf : ConvexFn f) (hopen : ri (dom f) = dom f)
    {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    ri {x | f x ≤ (α : EReal)} = {x | f x < (α : EReal)} := by
  rw [hf.relint_setOf_le hα, hopen]
  exact Set.ext fun z =>
    ⟨fun hz => hz.2, fun hz => ⟨mem_dom.2 (hz.trans (_root_.EReal.coe_lt_top α)), hz⟩⟩

/-- For a closed proper convex function the closure of a strict level set is the corresponding
level set. Rockafellar assumes in addition that `dom f` is relatively open; that hypothesis is
needed only for the companion formula above. -/
theorem ConvexFn.closure_setOf_lt_of_closedFn (hf : ConvexFn f) (hp : Proper f) (hc : ClosedFn f)
    {α : ℝ} (hα : ⨅ x, f x < (α : EReal)) :
    closure {x | f x < (α : EReal)} = {x | f x ≤ (α : EReal)} := by
  rw [hf.closure_setOf_lt hα, ← hf.clFn_eq_lscHull hp, hc]

end LevelSets

/-! ### Proper separation, and normals at a boundary point -/

section Separation

/-! ### Transversal thickening

Rockafellar's device for turning a relative-interior statement into an interior statement: add to
`C` a complement `W'` of the direction of its affine hull. The thickened set `C + W'` is convex, its
affine hull is everything (so it has nonempty interior), and it meets `aff C` in `C` again — so
`x ∉ ri C` becomes `x ∉ int (C + W')` and Mathlib's separation theorems for *open* convex sets
apply. The three lemmas below need the topology but not `[FiniteDimensional ℝ E]`, which is why
each carries an `omit`; finite-dimensionality enters only in `exists_lt_of_notMem_relint`, through
`Convex.interior_nonempty_iff_affineSpan_eq_top` and closedness of an affine subspace. -/

omit [FiniteDimensional ℝ E] in
/-- **Transversal thickening, trace.** The thickened set meets the affine hull of `C` in `C`. -/
theorem add_submodule_inter_affineSpan {W' : Submodule ℝ E}
    (hcompl : IsCompl (affineSpan ℝ C).direction W') :
    (C + (W' : Set E)) ∩ (affineSpan ℝ C : Set E) = C := by
  ext p
  refine ⟨fun ⟨hpD, hpA⟩ => ?_, fun hp =>
    ⟨Set.mem_add.2 ⟨p, hp, 0, W'.zero_mem, add_zero p⟩, subset_affineSpan ℝ C hp⟩⟩
  obtain ⟨c, hc, w, hw, rfl⟩ := Set.mem_add.1 hpD
  have hwW : w ∈ (affineSpan ℝ C).direction := by
    simpa using AffineSubspace.vsub_mem_direction hpA (subset_affineSpan ℝ C hc)
  have hw0 : w = 0 := by
    have hmem : w ∈ (affineSpan ℝ C).direction ⊓ W' := ⟨hwW, hw⟩
    rw [hcompl.inf_eq_bot] at hmem
    simpa using hmem
  rw [hw0, add_zero]
  exact hc

omit [FiniteDimensional ℝ E] in
/-- **Transversal thickening, span.** The thickened set is affinely spanning. -/
theorem affineSpan_add_submodule_eq_top (hne : C.Nonempty) {W' : Submodule ℝ E}
    (hcompl : IsCompl (affineSpan ℝ C).direction W') :
    affineSpan ℝ (C + (W' : Set E)) = ⊤ := by
  obtain ⟨c₀, hc₀⟩ := hne
  have hCD : C ⊆ C + (W' : Set E) := fun p hp =>
    Set.mem_add.2 ⟨p, hp, 0, W'.zero_mem, add_zero p⟩
  refine eq_top_iff.2 fun p _ => ?_
  have hmem : p - c₀ ∈ (affineSpan ℝ C).direction ⊔ W' := by
    rw [hcompl.sup_eq_top]; trivial
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 hmem
  have hwA : w + c₀ ∈ affineSpan ℝ C := by
    have hv := AffineSubspace.vadd_mem_of_mem_direction hw (subset_affineSpan ℝ C hc₀)
    simpa using hv
  have h1 : w + c₀ ∈ affineSpan ℝ (C + (W' : Set E)) := affineSpan_mono ℝ hCD hwA
  have h2 : w' ∈ (affineSpan ℝ (C + (W' : Set E))).direction := by
    have hc₀w'D : w' + c₀ ∈ C + (W' : Set E) :=
      Set.mem_add.2 ⟨c₀, hc₀, w', hw', add_comm c₀ w'⟩
    simpa using AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hc₀w'D) (subset_affineSpan ℝ _ (hCD hc₀))
  have hp : p = w' +ᵥ (w + c₀) := by
    rw [vadd_eq_add, sub_eq_iff_eq_add.1 hsum.symm]
    abel
  rw [hp]
  exact AffineSubspace.vadd_mem_of_mem_direction h2 h1

omit [FiniteDimensional ℝ E] in
/-- **Transversal thickening, relative interior.** A point of `aff C` outside `ri C` is outside the
interior of the thickening. This is the step that lets an *open*-set separation theorem be used. -/
theorem notMem_interior_add_submodule {x₀ : E} {W' : Submodule ℝ E}
    (hcompl : IsCompl (affineSpan ℝ C).direction W') (hx₀A : x₀ ∈ affineSpan ℝ C)
    (hx₀ : x₀ ∉ ri C) : x₀ ∉ interior (C + (W' : Set E)) := by
  intro hint
  refine hx₀ (mem_intrinsicInterior_iff.2 ⟨hx₀A, ?_⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  refine ⟨ε, hε, fun y hy hd => ?_⟩
  have hmem : y ∈ (C + (W' : Set E)) ∩ (affineSpan ℝ C : Set E) :=
    ⟨hball (by simpa [Metric.mem_ball] using hd), hy⟩
  rwa [add_submodule_inter_affineSpan hcompl] at hmem

/-- A point outside `ri C` is *properly* separated from `C` by a hyperplane through it. The proof
thickens `C` transversally to its affine hull, so that `x₀ ∉ ri C` becomes `x₀ ∉ int (C + W')` and
Mathlib's separation of a point from an open convex set applies. -/
theorem exists_lt_of_notMem_relint (hC : Convex ℝ C) (hne : C.Nonempty) {x₀ : E}
    (hx₀ : x₀ ∉ ri C) :
    ∃ g : E →L[ℝ] ℝ, (∀ x ∈ C, g x ≤ g x₀) ∧ ∃ x ∈ C, g x < g x₀ := by
  obtain ⟨c₀, hc₀⟩ := hne
  by_cases hx₀A : x₀ ∈ affineSpan ℝ C
  · obtain ⟨W', hcompl⟩ := (affineSpan ℝ C).direction.exists_isCompl
    have hCD : C ⊆ C + (W' : Set E) := fun p hp =>
      Set.mem_add.2 ⟨p, hp, 0, W'.zero_mem, add_zero p⟩
    have hDconv : Convex ℝ (C + (W' : Set E)) := hC.add W'.convex
    have hint : (interior (C + (W' : Set E))).Nonempty :=
      hDconv.interior_nonempty_iff_affineSpan_eq_top.2
        (affineSpan_add_submodule_eq_top ⟨c₀, hc₀⟩ hcompl)
    obtain ⟨g, hg⟩ := geometric_hahn_banach_open_point hDconv.interior isOpen_interior
      (notMem_interior_add_submodule hcompl hx₀A hx₀)
    have hle : ∀ x ∈ C + (W' : Set E), g x ≤ g x₀ := by
      intro x hx
      have hsub : closure (interior (C + (W' : Set E))) ⊆ {y | g y ≤ g x₀} :=
        closure_minimal (fun y hy => (hg y hy).le) (isClosed_le g.continuous continuous_const)
      refine hsub ?_
      rw [hDconv.closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure hx
    refine ⟨g, fun x hx => hle x (hCD hx), ?_⟩
    by_contra hcon
    push Not at hcon
    have hconst : ∀ x ∈ C, g x = g x₀ := fun x hx => le_antisymm (hle x (hCD hx)) (hcon x hx)
    -- `g` agrees on `C` with the constant map `g x₀`, so their linear parts — `g` itself and `0` —
    -- agree on `vectorSpan ℝ C`, which is `(affineSpan ℝ C).direction`.
    have hEqOn : Set.EqOn (g : E →ₗ[ℝ] ℝ).toAffineMap (AffineMap.const ℝ E (g x₀)) C :=
      fun x hx => hconst x hx
    have hWzero : ∀ w ∈ (affineSpan ℝ C).direction, g w = 0 := by
      intro w hw
      rw [direction_affineSpan] at hw
      simpa using AffineMap.linear_eqOn_vectorSpan hEqOn hw
    have hW'zero : ∀ w' ∈ W', g w' = 0 := by
      intro w' hw'
      by_contra hne0
      have hbdd : ∀ t : ℝ, g c₀ + t * g w' ≤ g x₀ := by
        intro t
        have hmem : c₀ + t • w' ∈ C + (W' : Set E) :=
          Set.mem_add.2 ⟨c₀, hc₀, t • w', W'.smul_mem t hw', rfl⟩
        simpa [map_add, map_smul] using hle _ hmem
      have hb := hbdd ((g x₀ - g c₀ + 1) / g w')
      rw [div_mul_cancel₀ _ hne0] at hb
      linarith
    have hgzero : g = 0 := by
      ext p
      have hmem : p ∈ (affineSpan ℝ C).direction ⊔ W' := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 hmem
      rw [← hsum, map_add, hWzero w hw, hW'zero w' hw']
      simp
    obtain ⟨a, ha⟩ := hint
    have hcontra := hg a ha
    rw [hgzero] at hcontra
    simp at hcontra
  · obtain ⟨g, u, v, hgs, huv, hgt⟩ := geometric_hahn_banach_compact_closed
      (convex_singleton x₀) isCompact_singleton (affineSpan ℝ C).convex
      (affineSpan ℝ C).closed_of_finiteDimensional
      (Set.disjoint_singleton_left.2 hx₀A)
    have h₂ : g x₀ < u := hgs x₀ rfl
    refine ⟨-g, fun x hx => ?_, c₀, hc₀, ?_⟩
    · have h₁ : v < g x := hgt x (subset_affineSpan ℝ C hx)
      simp only [neg_apply]
      linarith
    · have h₁ : v < g c₀ := hgt c₀ (subset_affineSpan ℝ C hc₀)
      simp only [neg_apply]
      linarith

/-- A point of a convex set is a *relative boundary* point exactly when some linear function that
is not constant on `C` attains its maximum over `C` there. -/
theorem notMem_relint_iff_exists_isMaxOn (hC : Convex ℝ C) {x : E} (hx : x ∈ C) :
    x ∉ ri C ↔ ∃ g : E →L[ℝ] ℝ, (∀ y ∈ C, g y ≤ g x) ∧ ∃ y ∈ C, g y ≠ g x := by
  constructor
  · intro hnot
    obtain ⟨g, hle, y, hy, hlt⟩ := exists_lt_of_notMem_relint hC ⟨x, hx⟩ hnot
    exact ⟨g, hle, y, hy, hlt.ne⟩
  · rintro ⟨g, hle, y, hy, hne⟩ hmem
    obtain ⟨μ, hμ, hw⟩ :=
      exists_one_lt_smul_mem_of_mem_relint hmem (subset_affineSpan ℝ C hy)
    have hylt : g y < g x := lt_of_le_of_ne (hle y hy) hne
    have hgw : g ((1 - μ) • y + μ • x) = (1 - μ) * g y + μ * g x := by
      simp [map_add, map_smul]
    have hcon := hle _ hw
    rw [hgw] at hcon
    nlinarith [mul_pos (sub_pos.2 hμ) (sub_pos.2 hylt)]

/-- A convex set has a nonzero normal at each of its boundary points. -/
theorem exists_ne_zero_isMaxOn_of_mem_frontier (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    (hfr : x ∈ frontier C) : ∃ g : E →L[ℝ] ℝ, g ≠ 0 ∧ ∀ y ∈ C, g y ≤ g x := by
  have hnotint : x ∉ interior C := hfr.2
  by_cases hmem : x ∈ ri C
  · have hspan : affineSpan ℝ C ≠ ⊤ := fun htop =>
      hnotint (by rwa [← intrinsicInterior_eq_interior htop])
    obtain ⟨p, hp⟩ : ∃ p : E, p ∉ affineSpan ℝ C := by
      by_contra hcon
      push Not at hcon
      exact hspan (eq_top_iff.2 fun q _ => hcon q)
    obtain ⟨g, u, v, hgs, huv, hgt⟩ := geometric_hahn_banach_compact_closed
      (convex_singleton p) isCompact_singleton (affineSpan ℝ C).convex
      (affineSpan ℝ C).closed_of_finiteDimensional (Set.disjoint_singleton_left.2 hp)
    have hconst : ∀ y ∈ affineSpan ℝ C, g y = g x :=
      fun y hy => eq_of_le_on_affineSubspace (fun z hz => (hgt z hz).le) hy
        (subset_affineSpan ℝ C hx)
    refine ⟨g, ?_, fun y hy => le_of_eq (hconst y (subset_affineSpan ℝ C hy))⟩
    intro hzero
    have h₁ : g p < u := hgs p rfl
    have h₂ : v < g x := hgt x (subset_affineSpan ℝ C hx)
    rw [hzero] at h₁ h₂
    simp only [zero_apply] at h₁ h₂
    linarith
  · obtain ⟨g, hle, y, hy, hlt⟩ := exists_lt_of_notMem_relint hC ⟨x, hx⟩ hmem
    refine ⟨g, ?_, hle⟩
    intro hzero
    rw [hzero] at hlt
    simp at hlt

/-- Two nonempty convex sets can be separated properly exactly when their relative interiors are
disjoint. It is proved here rather than in `Numlib/Analysis/Convex/Separation.lean` because it rests
on the line segment principle and on `ri C ≠ ∅` for nonempty convex `C`, both
finite-dimensional. -/
theorem exists_separatesProperly_iff_disjoint_relint (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    (∃ (g : E →L[ℝ] ℝ) (c : ℝ), SeparatesProperly g c C₁ C₂) ↔ Disjoint (ri C₁) (ri C₂) := by
  constructor
  · rintro ⟨g, c, hsep⟩
    rw [Set.disjoint_left]
    intro p hp₁ hp₂
    have hgp : g p = c :=
      le_antisymm (hsep.le_of_mem_left (intrinsicInterior_subset hp₁))
        (hsep.le_of_mem_right (intrinsicInterior_subset hp₂))
    obtain ⟨q, hq, hqc⟩ : ∃ q, q ∈ C₁ ∪ C₂ ∧ g q ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_subset fun q hq => hcon q hq
    rcases hq with hq | hq
    · have hlt : g q < c := lt_of_le_of_ne (hsep.le_of_mem_left hq) hqc
      obtain ⟨μ, hμ, hw⟩ :=
        exists_one_lt_smul_mem_of_mem_relint hp₁ (subset_affineSpan ℝ C₁ hq)
      have hgw : g ((1 - μ) • q + μ • p) = (1 - μ) * g q + μ * c := by
        simp [map_add, map_smul, hgp]
      have hcon := hsep.le_of_mem_left hw
      rw [hgw] at hcon
      nlinarith [mul_pos (sub_pos.2 hμ) (sub_pos.2 hlt)]
    · have hlt : c < g q := lt_of_le_of_ne (hsep.le_of_mem_right hq) (Ne.symm hqc)
      obtain ⟨μ, hμ, hw⟩ :=
        exists_one_lt_smul_mem_of_mem_relint hp₂ (subset_affineSpan ℝ C₂ hq)
      have hgw : g ((1 - μ) • q + μ • p) = (1 - μ) * g q + μ * c := by
        simp [map_add, map_smul, hgp]
      have hcon := hsep.le_of_mem_right hw
      rw [hgw] at hcon
      nlinarith [mul_pos (sub_pos.2 hμ) (sub_pos.2 hlt)]
  · intro hdisj
    have hneg : ∀ S : Set E, ((-1 : ℝ) • S) = -S := by
      intro S
      ext p
      simp only [Set.mem_smul_set, Set.mem_neg, neg_smul, one_smul]
      exact ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun hp => ⟨-p, hp, by simp⟩⟩
    have hri : ri (C₁ - C₂) = ri C₁ - ri C₂ := by
      rw [sub_eq_add_neg, ← hneg, Convex.relint_add h₁ (h₂.smul (-1 : ℝ)),
        Convex.relint_smul h₂, hneg, ← sub_eq_add_neg]
    have hzero : (0 : E) ∉ ri (C₁ - C₂) := by
      rw [hri]
      intro hmem
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.1 hmem
      exact Set.disjoint_left.1 hdisj ha (by rw [sub_eq_zero.1 hab]; exact hb)
    have hCsub : (C₁ - C₂).Nonempty := by
      obtain ⟨a, ha⟩ := hne₁
      obtain ⟨b, hb⟩ := hne₂
      exact ⟨a - b, Set.mem_sub.2 ⟨a, ha, b, hb, rfl⟩⟩
    obtain ⟨g, hle, w, hw, hlt⟩ := exists_lt_of_notMem_relint (h₁.sub h₂) hCsub hzero
    simp only [map_zero] at hle hlt
    have hkey : ∀ x ∈ C₁, ∀ y ∈ C₂, g x ≤ g y := by
      intro x hx y hy
      have hmem := hle (x - y) (Set.mem_sub.2 ⟨x, hx, y, hy, rfl⟩)
      simp only [map_sub] at hmem
      linarith
    obtain ⟨x₁, hx₁, x₂, hx₂, hsub⟩ := Set.mem_sub.1 hw
    have hstrict : g x₁ < g x₂ := by
      rw [← hsub] at hlt
      simp only [map_sub] at hlt
      linarith
    refine ⟨g, ?_⟩
    rw [exists_separatesProperly_iff_iSup_le_iInf hne₁ hne₂]
    refine ⟨iSup₂_le fun x hx => le_iInf₂ fun y hy => ?_, ?_⟩
    · exact_mod_cast hkey x hx y hy
    · exact lt_of_le_of_lt (iInf₂_le_coe_apply hx₁)
        (lt_of_lt_of_le (by exact_mod_cast hstrict) (coe_apply_le_iSup₂ hx₂))

end Separation

end Layer

end ConvexAnalysis
