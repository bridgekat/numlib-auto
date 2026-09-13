import Numlib.Analysis.Convex.Polyhedral.Conjugate
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Indicator

/-!
# Polyhedral constraint qualifications

The constraint qualifications for exact conjugate addition weaken when one of the two functions is
polyhedral: where `Duality/Relint.lean` asks for a *common relative interior point* of the two
effective domains, the polyhedral side here contributes only a point of its effective domain.

## Main results

* `IsExactSum.of_polyhedral_pair` — both functions polyhedral: no relative interiors at all, only
  `dom f ∩ dom g ≠ ∅`.
* `IsExactSum.of_polyhedral` — a proper polyhedral `f` and a proper convex `g` add exactly as soon
  as `dom f` meets `ri (dom g)` (Theorem 20.1 in [^1]). `IsExactSum.of_polyhedral_closed` is the
  closed case, which carries the argument, and
  `relint_inter_relint_nonempty_of_subset_affineSpan` is the relative-interior step it turns on.
* `IsExactFinsetSum.of_polyhedral` — the same for `m` summands; `polyhedralFn_finsetSum`, a finite
  sum of proper polyhedral functions being polyhedral, makes the polyhedral block one summand.
* `IsExactImage.of_polyhedral` — the same weakening on the *image* side: a proper polyhedral `g`
  pulls back exactly as soon as the range of `A` meets `dom g`. This is what gives the general
  image and subgradient rules their polyhedral clauses.
* `epi_mapLin_of_polyhedralFn`, `polyhedralFn_mapLin`, `exists_mapLin_eq_of_polyhedralFn`,
  `polyhedralFn_compLin` — the image `Af` is polyhedral, the infimum defining it is attained, and
  the composite `gA` is polyhedral.

## Implementation notes

The pair case is the proof of `of_relint` with its closedness criterion replaced by polyhedrality:
both need `epi f* + epi g*` closed, and here that is free, a sum of polyhedral sets being
polyhedral and closed. `ClosedFn` is a hypothesis on neither side, a proper polyhedral convex
function being automatically closed. The general case is the classical reduction, run on an
indicator: with `M = aff (dom g)` and `δ = δ(· | M)`, the function `δ + f` is polyhedral and
`M ∩ dom f` does meet `ri (dom g)`, so `of_relint` applies to `δ + f` and `g`; the leftover `δ*`
is then re-absorbed, since `δ + g = g` and `δ + (f + g) = f + g`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §20.
-/

open Set
open scoped Pointwise

namespace ConvexAnalysis

section Sum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ F] in
/-- A proper polyhedral convex function is a closed proper convex function. -/
theorem PolyhedralFn.closedProperConvexFn (hf : PolyhedralFn f) (hpf : Proper f) :
    ClosedProperConvexFn f :=
  ⟨hf.convexFn, hf.closedFn hpf.ne_bot, hpf⟩

/-- **The all-polyhedral case**: two proper polyhedral convex functions add exactly as soon as
their effective domains meet, with no relative interior on either side. This is the case `k = m`,
to which the general form is reduced. -/
theorem IsExactSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : Proper f) (hg : PolyhedralFn g) (hpg : Proper g)
    {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ dom g) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hgc : ClosedProperConvexFn g := hg.closedProperConvexFn hpg
  have hup : Proper (conj B f) := proper_conj hfc
  have hvp : Proper (conj B g) := proper_conj hgc
  -- the sum of the two dual epigraphs is polyhedral, hence closed
  have hclosed : IsClosed (epi (conj B f) + epi (conj B g)) :=
    Polyhedral.isClosed (Polyhedral.add (PolyhedralFn.conj hf) (PolyhedralFn.conj hg))
  -- so that sum *is* the epigraph of the infimal convolute
  have hepiEq : epi (infConv (conj B f) (conj B g)) = epi (conj B f) + epi (conj B g) :=
    epi_infConv_of_polyhedralFn (PolyhedralFn.conj hf) (PolyhedralFn.conj hg)
  have hdomne : (dom (f + g)).Nonempty :=
    ⟨x₀, by
      rw [mem_dom, Pi.add_apply]
      exact EReal.add_lt_top (mem_dom.1 hxf).ne (mem_dom.1 hxg).ne⟩
  have hproper : Proper (infConv (conj B f) (conj B g)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := hup.dom_nonempty
      obtain ⟨q, hq⟩ := hvp.dom_nonempty
      exact ⟨p + q, by rw [dom_infConv]; exact Set.add_mem_add hp hq⟩
    · have hle := conj_add_le_infConv B f g y
      rw [hy, le_bot_iff] at hle
      exact conj_ne_bot hdomne y hle
  have hclosedFn : ClosedFn (infConv (conj B f) (conj B g)) :=
    (ClosedProperConvexFn.of_isClosed_epi
      (convexFn_infConv (convexFn_conj B f) (convexFn_conj B g))
      (by rw [hepiEq]; exact hclosed) hproper).closed
  have hconjadd : conj B (f + g) = infConv (conj B f) (conj B g) := by
    rw [conj_add_eq_clFn_infConv hfc.convex hfc.closed hgc.convex hgc.closed]
    exact hclosedFn
  refine ⟨hpf, hpg, fun y => ?_⟩
  rw [hconjadd]
  rcases eq_top_or_lt_top (infConv (conj B f) (conj B g) y) with htop | htop
  · exact ⟨y, 0, add_zero y, by rw [htop]; exact le_top⟩
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hproper.ne_bot y) htop
  have hmem : ((y, μ) : F × ℝ) ∈ epi (conj B f) + epi (conj B g) := by
    rw [← hepiEq]; exact mk_mem_epi.2 hμ.le
  obtain ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ := hmem
  refine ⟨y₁, y₂, congrArg Prod.fst heq, ?_⟩
  have hab : a + b = μ := congrArg Prod.snd heq
  rw [hμ]
  calc conj B f y₁ + conj B g y₂ ≤ ((a : ℝ) : EReal) + ((b : ℝ) : EReal) :=
        add_le_add (mk_mem_epi.1 h₁) (mk_mem_epi.1 h₂)
    _ = ((μ : ℝ) : EReal) := by rw [← EReal.coe_add, hab]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- An indicator function is absorbed by any function whose effective domain it contains. This is
the algebraic device the reduction below runs on: with `M = aff (dom g)` both
`indicatorFn M + g` and `indicatorFn M + (f + g)` collapse. No properness is needed — off `C` the
sum is `⊤ + ⊤`. -/
theorem indicatorFn_add_eq_self {C : Set E} {k : E → EReal}
    (hsub : dom k ⊆ C) : indicatorFn C + k = k := by
  funext x
  by_cases hx : x ∈ C
  · rw [Pi.add_apply, indicatorFn_of_mem hx, zero_add]
  · have hxk : k x = ⊤ := by
      by_contra hcon
      exact hx (hsub (mem_dom.2 (lt_top_iff_ne_top.2 hcon)))
    rw [Pi.add_apply, indicatorFn_of_notMem hx, hxk]
    simp

omit [FiniteDimensional ℝ F] in
/-- **The relative-interior step** the reduction below turns on. If a convex set `D₁` lies in the
affine hull of a convex set `D₂` and the two share a point `x₀` of `ri D₂`, then `ri D₁` and
`ri D₂` already share a point.

`x₀` need not itself be in `ri D₁`, but `ri D₂` is a relatively open neighbourhood of `x₀` inside
`aff D₂ ⊇ aff D₁`, so a small push from `x₀` towards any point of `ri D₁` lands in both. -/
theorem relint_inter_relint_nonempty_of_subset_affineSpan {D₁ D₂ : Set E}
    (h₁ : Convex ℝ D₁) (h₂ : Convex ℝ D₂) (hsub : D₁ ⊆ (affineSpan ℝ D₂ : Set E))
    {x₀ : E} (hx₁ : x₀ ∈ D₁) (hx₂ : x₀ ∈ ri D₂) : (ri D₁ ∩ ri D₂).Nonempty := by
  obtain ⟨z, hz⟩ := Convex.relint_nonempty h₁ ⟨x₀, hx₁⟩
  have hzD₁ : z ∈ D₁ := intrinsicInterior_subset hz
  have hzM : z ∈ affineSpan ℝ D₂ := hsub hzD₁
  have hx₀D₂ : x₀ ∈ D₂ := intrinsicInterior_subset hx₂
  have hx₀M : x₀ ∈ affineSpan ℝ D₂ := subset_affineSpan ℝ D₂ hx₀D₂
  -- the reflection of `z` in `x₀` still lies in the affine hull of `D₂`
  have hyM : (1 : ℝ) • (x₀ -ᵥ z) +ᵥ x₀ ∈ affineSpan ℝ D₂ :=
    AffineSubspace.smul_vsub_vadd_mem _ 1 hx₀M hzM hx₀M
  obtain ⟨μ, hμ, hmem⟩ := exists_one_lt_smul_mem_of_mem_relint hx₂ hyM
  set t : ℝ := μ - 1 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have hxt : (1 - t) • x₀ + t • z ∈ D₂ := by
    have heq : (1 - μ) • ((1 : ℝ) • (x₀ -ᵥ z) +ᵥ x₀) + μ • x₀ = (1 - t) • x₀ + t • z := by
      simp only [vsub_eq_sub, vadd_eq_add, one_smul, ht]
      module
    rwa [heq] at hmem
  set s : ℝ := min (t / 2) 1 with hs
  have hs0 : 0 < s := lt_min (by linarith) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hst : s < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨(1 - s) • x₀ + s • z, ?_, ?_⟩
  · have hseg := Convex.segment_mem_relint h₁ hz (subset_closure hx₁)
      (a := 1 - s) (by linarith) (by linarith)
    have heq : (1 - (1 - s)) • z + (1 - s) • x₀ = (1 - s) • x₀ + s • z := by module
    rwa [heq] at hseg
  · have hseg := Convex.segment_mem_relint h₂ hx₂ (subset_closure hxt)
      (a := s / t) (by positivity) ((div_lt_one ht0).2 hst)
    have heq : (1 - s / t) • x₀ + (s / t) • ((1 - t) • x₀ + t • z) = (1 - s) • x₀ + s • z := by
      match_scalars <;> (field_simp; try ring)
    rwa [heq] at hseg

/-- A proper polyhedral convex function and a closed proper convex function add exactly as soon as
`dom f` meets `ri (dom g)`: the polyhedral side contributes only a point of its effective domain,
not of its relative interior.

With `M = aff (dom g)`, `δ = δ(· | M)` and `h = δ + f`, `ri (dom h)` does meet `ri (dom g)`, so
`of_relint` splits `(h + g)* = (f + g)*` exactly; the pair case splits `h*` as `δ* □ f*`, and
`δ* □ g* = (δ + g)* = g*` re-absorbs the leftover `δ*`. -/
theorem IsExactSum.of_polyhedral_closed [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : Proper f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ ri (dom g)) : IsExactSum B f g := by
  classical
  have hx₀g : x₀ ∈ dom g := intrinsicInterior_subset hxg
  set MA : AffineSubspace ℝ E := affineSpan ℝ (dom g) with hMA
  have hx₀M : x₀ ∈ MA := subset_affineSpan ℝ (dom g) hx₀g
  have hdomgM : dom g ⊆ (MA : Set E) := subset_affineSpan ℝ (dom g)
  set δ : E → EReal := indicatorFn (MA : Set E) with hδdef
  have hδbot : ∀ x, δ x ≠ ⊥ := fun x => indicatorFn_ne_bot _ x
  have hδdom : dom δ = (MA : Set E) := dom_indicatorFn _
  have hδpoly : PolyhedralFn δ :=
    polyhedralFn_indicatorFn (polyhedral_coe_affineSubspace hx₀M)
  have hδproper : Proper δ := ⟨⟨x₀, by rw [hδdom]; exact hx₀M⟩, hδbot⟩
  have hδcpc : ClosedProperConvexFn δ := hδpoly.closedProperConvexFn hδproper
  have hx₀δ : x₀ ∈ dom δ := by rw [hδdom]; exact hx₀M
  -- `h = δ + f` is polyhedral and proper, with `dom h = M ∩ dom f`
  have hhpoly : PolyhedralFn (δ + f) := PolyhedralFn.add hδpoly hf hδbot hpf.ne_bot
  have hhbot : ∀ x, (δ + f) x ≠ ⊥ := fun x =>
    EReal.add_ne_bot_iff.2 ⟨hδbot x, hpf.ne_bot x⟩
  have hhdom : dom (δ + f) = (MA : Set E) ∩ dom f := by
    rw [dom_add hδbot hpf.ne_bot, hδdom]
  have hx₀h : x₀ ∈ dom (δ + f) := by rw [hhdom]; exact ⟨hx₀M, hxf⟩
  have hhproper : Proper (δ + f) := ⟨⟨x₀, hx₀h⟩, hhbot⟩
  have hhcpc : ClosedProperConvexFn (δ + f) := hhpoly.closedProperConvexFn hhproper
  -- the relative-interior step
  obtain ⟨x₁, hx₁h, hx₁g⟩ :=
    relint_inter_relint_nonempty_of_subset_affineSpan
      (PolyhedralFn.convexFn hhpoly).convex_dom hg.convex.convex_dom
      (by rw [hhdom]; exact fun x hx => hx.1) hx₀h hxg
  -- the three exact splittings
  have hAg : IsExactSum B (δ + f) g := IsExactSum.of_relint_closed hhcpc hg hx₁h hx₁g
  have hδf : IsExactSum B δ f := IsExactSum.of_polyhedral_pair hδpoly hδproper hf hpf hx₀δ hxf
  have hx₀riδ : x₀ ∈ ri (dom δ) := by
    rw [hδdom, AffineSubspace.intrinsicInterior_coe]; exact hx₀M
  have hδg : IsExactSum B δ g := IsExactSum.of_relint_closed hδcpc hg hx₀riδ hxg
  -- `δ` is absorbed on both sides
  have hsumδg : δ + g = g := indicatorFn_add_eq_self hdomgM
  have hsum : δ + f + g = f + g := by
    rw [add_assoc]
    exact indicatorFn_add_eq_self
      (by rw [dom_add hpf.ne_bot hg.proper.ne_bot]; exact fun x hx => hdomgM hx.2)
  have hδne : ∀ y : F, conj B δ y ≠ ⊥ := fun y => conj_ne_bot hδproper.dom_nonempty y
  have hgne : ∀ y : F, conj B g y ≠ ⊥ := fun y => conj_ne_bot hg.proper.dom_nonempty y
  have hgconj : conj B g = infConv (conj B δ) (conj B g) := by
    have h0 := hδg.conj_add
    rwa [hsumδg] at h0
  refine ⟨hpf, hg.proper, fun y => ?_⟩
  obtain ⟨z₁, z₂, hz, hzle⟩ := hAg.exact_le y
  obtain ⟨u, v, huv, huvle⟩ := hδf.exact_le z₁
  have habs : conj B g (u + z₂) ≤ conj B δ u + conj B g z₂ := by
    have hle := infConv_le_add (f := conj B δ) (g := conj B g) hδne hgne (u + z₂) z₂
    rw [add_sub_cancel_right] at hle
    calc conj B g (u + z₂) = infConv (conj B δ) (conj B g) (u + z₂) := by rw [← hgconj]
      _ ≤ conj B δ u + conj B g z₂ := hle
  refine ⟨v, u + z₂, ?_, ?_⟩
  · rw [← hz, ← huv]; abel
  · calc conj B f v + conj B g (u + z₂)
        ≤ conj B f v + (conj B δ u + conj B g z₂) := add_le_add le_rfl habs
      _ = conj B δ u + conj B f v + conj B g z₂ := by
          rw [← add_assoc, add_comm (conj B f v)]
      _ ≤ conj B (δ + f) z₁ + conj B g z₂ := add_le_add huvle le_rfl
      _ ≤ conj B (δ + f + g) y := hzle
      _ = conj B (f + g) y := by rw [hsum]

/-- A proper polyhedral convex function and a *proper convex* function add exactly as soon as
`dom f` meets `ri (dom g)`. Neither closedness of `g` nor a relative interior point of `dom f` is
needed.

The reduction to `IsExactSum.of_polyhedral_closed` runs through the conjugate form
`conj_add_eq_conj_clFn_add_clFn`, whose two segment hypotheses are met on opposite grounds: `f` is
closed proper (only `x₀ ∈ dom f` needed) and `g` is proper convex (`x₀ ∈ ri (dom g)`). That
asymmetry is the asymmetry of the theorem itself. -/
theorem IsExactSum.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : Proper f) (hg : ConvexFn g) (hpg : Proper g)
    {x₀ : E} (hxf : x₀ ∈ dom f) (hxg : x₀ ∈ ri (dom g)) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hcl : clFn f = f := hfc.closed
  refine IsExactSum.of_clFn hpf hpg ?_
    (conj_add_eq_conj_clFn_add_clFn hfc.convex hpf hg hpg
      (hfc.tendstoClFnAlongSegment hxf) (hg.tendstoClFnAlongSegment hpg hxg))
  rw [hcl]
  exact IsExactSum.of_polyhedral_closed hf hpf
    ⟨convexFn_clFn hg, closedFn_clFn g, hg.proper_clFn hpg⟩ hxf
    (by rw [hg.relint_dom_clFn hpg]; exact hxg)

end Sum

/-! ### Exact addition of `m` summands -/

section FinsetSum

variable {ι : Type*} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s t u : Finset ι} {f : ι → E → EReal}

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A finite non-empty sum of proper polyhedral convex functions is polyhedral. -/
theorem polyhedralFn_finsetSum (hs : s.Nonempty) (hpoly : ∀ i ∈ s, PolyhedralFn (f i))
    (hbot : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) : PolyhedralFn (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons i t hi ih =>
    have hmt : ∀ j ∈ t, j ∈ Finset.cons i t hi := fun j hj => Finset.mem_cons_of_mem hj
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · rw [Finset.cons_empty, Finset.sum_singleton]
      exact hpoly i (by simp)
    rw [Finset.sum_cons]
    exact PolyhedralFn.add (hpoly i (by simp))
      (ih htne (fun j hj => hpoly j (hmt j hj)) (fun j hj => hbot j (hmt j hj)))
      (hbot i (by simp))
      (fun x => by
        rw [Finset.sum_apply]
        exact EReal.sum_ne_bot fun j hj => hbot j (hmt j hj) x)

private theorem isExactFinsetSum_of_polyhedral_pair_aux [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (f : ι → E → EReal) (x₀ : E) :
    ∀ t : Finset ι, t.Nonempty → (∀ i ∈ t, PolyhedralFn (f i)) → (∀ i ∈ t, Proper (f i)) →
      (∀ i ∈ t, x₀ ∈ dom (f i)) → IsExactFinsetSum B t f := by
  intro t
  induction t using Finset.cons_induction with
  | empty => intro hne; exact absurd hne (by simp)
  | cons i t hi ih =>
    intro _ hpoly hpf hx₀
    have hmt : ∀ j ∈ t, j ∈ Finset.cons i t hi := fun j hj => Finset.mem_cons_of_mem hj
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · rw [Finset.cons_empty]
      exact IsExactFinsetSum.singleton (hpf i (by simp))
    refine IsExactFinsetSum.cons hi ?_
      (ih htne (fun j hj => hpoly j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => hx₀ j (hmt j hj)))
    obtain ⟨-, hprop, hdom⟩ :=
      properConvexFn_finsetSum (fun j hj => (hpoly j (hmt j hj)).convexFn)
        (fun j hj => hpf j (hmt j hj)) (fun j hj => hx₀ j (hmt j hj))
    refine IsExactSum.of_polyhedral_pair (hpoly i (by simp)) (hpf i (by simp))
      (polyhedralFn_finsetSum htne (fun j hj => hpoly j (hmt j hj))
        (fun j hj x => (hpf j (hmt j hj)).ne_bot x)) hprop (hx₀ i (by simp)) ?_
    rw [hdom]
    exact Set.mem_iInter₂.2 fun j hj => hx₀ j (hmt j hj)

/-- **The all-polyhedral case, for `m` summands**: finitely many proper polyhedral convex
functions add exactly as soon as their effective domains have a point in common. -/
theorem IsExactFinsetSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hpoly : ∀ i ∈ s, PolyhedralFn (f i)) (hpf : ∀ i ∈ s, Proper (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ dom (f i)) : IsExactFinsetSum B s f :=
  isExactFinsetSum_of_polyhedral_pair_aux f x₀ s hs hpoly hpf hx₀

/-- The `m`-ary form: let `f₁, …, fₘ` be proper convex with `f₁, …, f_k` polyhedral, and suppose

`dom f₁ ∩ ⋯ ∩ dom f_k ∩ ri (dom f_{k+1}) ∩ ⋯ ∩ ri (dom fₘ) ≠ ∅`.

Then `f₁, …, fₘ` add exactly.

`t` is `{1, …, k}` and `u` is its complement; the splitting is spelled membership-wise rather than
as `s = t ∪ u` so that no `DecidableEq` instance enters the statement. `∑_{i ∈ t} fᵢ` is
polyhedral and adds exactly to `∑_{i ∈ u} fᵢ` by the binary case, while each block adds exactly on
its own — the polyhedral one by the all-polyhedral case, the other by the relative-interior
criterion. -/
theorem IsExactFinsetSum.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, Proper (f i)) {x₀ : E} (hxt : ∀ i ∈ t, x₀ ∈ dom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (dom (f i))) : IsExactFinsetSum B s f := by
  have hts : ∀ i ∈ t, i ∈ s := fun i hi => (hmem i).2 (Or.inl hi)
  have hus : ∀ i ∈ u, i ∈ s := fun i hi => (hmem i).2 (Or.inr hi)
  rcases Finset.eq_empty_or_nonempty t with rfl | htne
  · have hsu : s = u := Finset.ext fun i => by simpa using hmem i
    subst hsu
    exact IsExactFinsetSum.of_relint hs hconv hpf hxu
  rcases Finset.eq_empty_or_nonempty u with rfl | hune
  · have hst : s = t := Finset.ext fun i => by simpa using hmem i
    subst hst
    exact IsExactFinsetSum.of_polyhedral_pair hs hpoly hpf hxt
  obtain ⟨-, hpropt, hdomt⟩ :=
    properConvexFn_finsetSum (fun i hi => (hpoly i hi).convexFn) (fun i hi => hpf i (hts i hi)) hxt
  obtain ⟨hconvu, hpropu, -⟩ :=
    properConvexFn_finsetSum hconv (fun i hi => hpf i (hus i hi))
      (fun i hi => intrinsicInterior_subset (hxu i hi))
  refine IsExactFinsetSum.of_split hdisj hmem
    (IsExactFinsetSum.of_polyhedral_pair htne hpoly (fun i hi => hpf i (hts i hi)) hxt)
    (IsExactFinsetSum.of_relint hune hconv (fun i hi => hpf i (hus i hi)) hxu) ?_
  refine IsExactSum.of_polyhedral
    (polyhedralFn_finsetSum htne hpoly (fun i hi x => (hpf i (hts i hi)).ne_bot x)) hpropt
    hconvu hpropu ?_
    (mem_relint_dom_finsetSum hconv (fun i hi => hpf i (hus i hi)) hxu)
  rw [hdomt]
  exact Set.mem_iInter₂.2 hxt

end FinsetSum

/-! ### The polyhedral companion of the image rule -/

section PolyhedralImage

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f : E → EReal}

/-- An identity of epigraphs: for a polyhedral `f` the epigraph of the image `Af` really *is* the
image of `epi f` under `(x, μ) ↦ (Ax, μ)`.

In general `epi (Af)` is only the *epigraph closure* of that image, because an infimum need not be
attained. Here the image is polyhedral, hence closed, and a closed set with upward-closed vertical
sections is already an epigraph. Both conclusions — polyhedrality of `Af` and attainment of the
infimum — fall out of this one identity. -/
theorem epi_mapLin_of_polyhedralFn (hf : PolyhedralFn f) (A : E →ₗ[ℝ] G) :
    epi (mapLin A f) = A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f := by
  refine epi_mapLin (IsEpiLike.of_isClosed ?_ (Polyhedral.image hf _).isClosed)
  rintro y μ ν ⟨⟨x, ρ⟩, hx, hxy⟩ hμν
  have h1 : A x = y := congrArg Prod.fst hxy
  have h2 : ρ = μ := congrArg Prod.snd hxy
  refine ⟨(x, ν), mk_mem_epi.2 ?_, ?_⟩
  · exact le_trans (h2 ▸ mk_mem_epi.1 hx) (by exact_mod_cast hμν)
  · rw [LinearMap.prodMap_apply, h1]
    rfl

/-- The image of a polyhedral convex function under a linear transformation is polyhedral. By
`epi_mapLin_of_polyhedralFn`, `epi (Af)` *is* the image of `epi f`, and a linear image of a
polyhedral set is polyhedral. -/
theorem polyhedralFn_mapLin (hf : PolyhedralFn f) (A : E →ₗ[ℝ] G) :
    PolyhedralFn (mapLin A f) := by
  change Polyhedral (epi (mapLin A f))
  rw [epi_mapLin_of_polyhedralFn hf A]
  exact Polyhedral.image hf _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- A polyhedral convex function composed with a linear map is polyhedral. `epi (gA)` is `epi g`
pulled back along `(x, μ) ↦ (A x, μ)`, and a preimage of a polyhedral set under a linear map is
polyhedral (`Polyhedral.comap`).

This is much the cheaper direction: pulling back needs neither closedness nor attainment, so no
finite dimension is used on either side. -/
theorem polyhedralFn_compLin {g : G → EReal} (hg : PolyhedralFn g) (A : E →ₗ[ℝ] G) :
    PolyhedralFn (compLin g A) := by
  change Polyhedral (epi (compLin g A))
  rw [epi_compLin]
  exact Polyhedral.comap hg _

/-- **The attainment clause**: wherever `(Af)(y)` is finite the infimum defining it is attained,
some `x` in the fibre over `y` realising the value. By `epi_mapLin_of_polyhedralFn` the point
`(y, μ)` of `epi (Af)` is literally an image point. -/
theorem exists_mapLin_eq_of_polyhedralFn (hf : PolyhedralFn f) (A : E →ₗ[ℝ] G) {y : G} {μ : ℝ}
    (hy : mapLin A f y = (μ : EReal)) : ∃ x : E, A x = y ∧ f x = mapLin A f y := by
  have hmem : ((y, μ) : G × ℝ) ∈ epi (mapLin A f) := mk_mem_epi.2 (le_of_eq hy)
  rw [epi_mapLin_of_polyhedralFn hf A] at hmem
  obtain ⟨⟨x, ν⟩, hx, hxy⟩ := hmem
  have h1 : A x = y := congrArg Prod.fst hxy
  have h2 : ν = μ := congrArg Prod.snd hxy
  refine ⟨x, h1, le_antisymm ?_ (mapLin_le h1)⟩
  rw [hy]
  exact h2 ▸ mk_mem_epi.1 hx

end PolyhedralImage

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **The companion on the image side**: a proper *polyhedral* `g` pulls back exactly along `A` as
soon as the range of `A` meets `dom g` — no relative interior anywhere, exactly as on the sum side.

None of the sum theory is used. `g*` is polyhedral, so `A' g*` is polyhedral and therefore closed,
and the general image rule's *closure* formula has nothing left to close; the same fact attains the
infimum over the fibre. Properness of `g` enters twice and cheaply: it makes `g` closed, and
`A x₀ ∈ dom g` stops `(g A)*` from being `-∞`. -/
theorem IsExactImage.of_polyhedral [IsCompatiblePairing B'] [IsCompatiblePairing B.flip]
    (hA : IsAdjointPair B B' A A') (hg : PolyhedralFn g) (hp : Proper g)
    {x₀ : E} (hx₀ : A x₀ ∈ dom g) :
    IsExactImage B B' A A' hA g := by
  have hconjpoly : PolyhedralFn (conj B' g) := PolyhedralFn.conj hg
  have hmappoly : PolyhedralFn (mapLin A' (conj B' g)) := polyhedralFn_mapLin hconjpoly A'
  have hne : (dom (compLin g A)).Nonempty := ⟨x₀, by rwa [mem_dom, compLin_apply]⟩
  have hbot : ∀ y, conj B (compLin g A) y ≠ ⊥ := fun y => conj_ne_bot hne y
  have hmapbot : ∀ y, mapLin A' (conj B' g) y ≠ ⊥ := fun y hy =>
    hbot y (le_bot_iff.1 (hy ▸ conj_compLin_le_mapLin hA g y))
  have heq : conj B (compLin g A) = mapLin A' (conj B' g) := by
    rw [conj_compLin_eq_clFn_mapLin hA hg.convexFn (hg.closedFn hp.ne_bot)]
    exact hmappoly.closedFn hmapbot
  refine ⟨hp, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hmapbot y) hy
  obtain ⟨z, hz, hzeq⟩ := exists_mapLin_eq_of_polyhedralFn hconjpoly A' hμ
  exact ⟨z, hz, le_of_eq hzeq⟩

end Image

end ConvexAnalysis
