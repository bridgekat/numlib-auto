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
  as `dom f` meets `ri (dom g)` ([rockafellar1970convex] Theorem 20.1).
  `IsExactSum.of_polyhedral_closed` is the closed case, which carries the argument, and
  `relint_inter_relint_nonempty_of_subset_affineSpan` is the relative-interior step it turns on.
* `IsExactFinsetSum.of_polyhedral` — the same for `m` summands; `PolyhedralFn.finsetSum`, a finite
  sum of proper polyhedral functions being polyhedral, makes the polyhedral block one summand.
* `IsExactImage.of_polyhedral` — the same weakening on the *image* side: a proper polyhedral `g`
  pulls back exactly as soon as the range of `A` meets `dom g`. This is what gives the general
  image and subgradient rules their polyhedral clauses.

## Implementation notes

The pair case is the proof of `of_relint` with its closedness criterion replaced by polyhedrality:
both need `epi f* + epi g*` closed, and here that is free, a sum of polyhedral sets being
polyhedral and closed. `ClosedConvex` is a hypothesis on neither side, a proper polyhedral convex
function being automatically closed. The general case is the classical reduction, run on an
indicator: with `M = aff (dom g)` and `δ = δ(· | M)`, the function `δ + f` is polyhedral and
`M ∩ dom f` does meet `ri (dom g)`, so `of_relint` applies to `δ + f` and `g`; the leftover `δ*`
is then re-absorbed, since `δ + g = g` and `δ + (f + g) = f + g`.

## References

* [rockafellar1970convex] §20.
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
theorem PolyhedralFn.closedProperConvexFn (hf : PolyhedralFn f) (hpf : ProperConvex f) :
    ClosedProperConvexFn f :=
  ⟨hf.convexFn, hf.closedConvex hpf.ne_bot, hpf⟩

/-- **The all-polyhedral case**: two proper polyhedral convex functions add exactly as soon as
their effective domains meet, with no relative interior on either side. This is the case `k = m`,
to which the general form is reduced. -/
theorem IsExactSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : ProperConvex f) (hg : PolyhedralFn g) (hpg : ProperConvex g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ convexDom g) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hgc : ClosedProperConvexFn g := hg.closedProperConvexFn hpg
  have hup : ProperConvex (convexConj B f) := properConvex_convexConj hfc
  have hvp : ProperConvex (convexConj B g) := properConvex_convexConj hgc
  -- the sum of the two dual epigraphs is polyhedral, hence closed
  have hclosed : IsClosed (epi (convexConj B f) + epi (convexConj B g)) :=
    Polyhedral.isClosed (Polyhedral.add (PolyhedralFn.convexConj hf) (PolyhedralFn.convexConj hg))
  -- so that sum *is* the epigraph of the infimal convolute
  have hepiEq : epi (infConv (convexConj B f) (convexConj B g)) = epi (convexConj B f)
      + epi (convexConj B g) :=
    epi_infConv_of_polyhedralFn (PolyhedralFn.convexConj hf) (PolyhedralFn.convexConj hg)
  have hdomne : (convexDom (f + g)).Nonempty :=
    ⟨x₀, by
      rw [mem_convexDom, Pi.add_apply]
      exact EReal.add_lt_top (mem_convexDom.1 hxf).ne (mem_convexDom.1 hxg).ne⟩
  have hproper : ProperConvex (infConv (convexConj B f) (convexConj B g)) := by
    refine ⟨?_, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := hup.convexDom_nonempty
      obtain ⟨q, hq⟩ := hvp.convexDom_nonempty
      exact ⟨p + q, by rw [convexDom_infConv]; exact Set.add_mem_add hp hq⟩
    · have hle := convexConj_add_le_infConv B f g y
      rw [hy, le_bot_iff] at hle
      exact convexConj_ne_bot hdomne y hle
  have hclosedFn : ClosedConvex (infConv (convexConj B f) (convexConj B g)) :=
    (ClosedProperConvexFn.of_isClosed_epi
      (convexFn_infConv (convexFn_convexConj B f) (convexFn_convexConj B g))
      (by rw [hepiEq]; exact hclosed) hproper).closed
  have hconjadd : convexConj B (f + g) = infConv (convexConj B f) (convexConj B g) := by
    rw [convexConj_add_eq_convexCl_infConv hfc.convex hfc.closed hgc.convex hgc.closed]
    exact hclosedFn
  refine ⟨hpf, hpg, fun y => ?_⟩
  rw [hconjadd]
  rcases eq_top_or_lt_top (infConv (convexConj B f) (convexConj B g) y) with htop | htop
  · exact ⟨y, 0, add_zero y, by rw [htop]; exact le_top⟩
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hproper.ne_bot y) htop
  have hmem : ((y, μ) : F × ℝ) ∈ epi (convexConj B f) + epi (convexConj B g) := by
    rw [← hepiEq]; exact mk_mem_epi.2 hμ.le
  obtain ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ := hmem
  refine ⟨y₁, y₂, congrArg Prod.fst heq, ?_⟩
  have hab : a + b = μ := congrArg Prod.snd heq
  rw [hμ]
  calc convexConj B f y₁ + convexConj B g y₂ ≤ ((a : ℝ) : EReal) + ((b : ℝ) : EReal) :=
        add_le_add (mk_mem_epi.1 h₁) (mk_mem_epi.1 h₂)
    _ = ((μ : ℝ) : EReal) := by rw [← EReal.coe_add, hab]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- An indicator function is absorbed by any function whose effective domain it contains. This is
the algebraic device the reduction below runs on: with `M = aff (dom g)` both
`indicatorFn M + g` and `indicatorFn M + (f + g)` collapse. No properness is needed — off `C` the
sum is `⊤ + ⊤`. -/
theorem indicatorFn_add_eq_self {C : Set E} {k : E → EReal}
    (hsub : convexDom k ⊆ C) : indicatorFn C + k = k := by
  funext x
  by_cases hx : x ∈ C
  · rw [Pi.add_apply, indicatorFn_of_mem hx, zero_add]
  · have hxk : k x = ⊤ := by
      by_contra hcon
      exact hx (hsub (mem_convexDom.2 (lt_top_iff_ne_top.2 hcon)))
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
    (hf : PolyhedralFn f) (hpf : ProperConvex f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ ri (convexDom g)) : IsExactSum B f g := by
  classical
  have hx₀g : x₀ ∈ convexDom g := intrinsicInterior_subset hxg
  set MA : AffineSubspace ℝ E := affineSpan ℝ (convexDom g) with hMA
  have hx₀M : x₀ ∈ MA := subset_affineSpan ℝ (convexDom g) hx₀g
  have hdomgM : convexDom g ⊆ (MA : Set E) := subset_affineSpan ℝ (convexDom g)
  set δ : E → EReal := indicatorFn (MA : Set E) with hδdef
  have hδbot : ∀ x, δ x ≠ ⊥ := fun x => indicatorFn_ne_bot _ x
  have hδdom : convexDom δ = (MA : Set E) := convexDom_indicatorFn _
  have hδpoly : PolyhedralFn δ :=
    polyhedralFn_indicatorFn (polyhedral_coe_affineSubspace hx₀M)
  have hδproper : ProperConvex δ := ⟨⟨x₀, by rw [hδdom]; exact hx₀M⟩, hδbot⟩
  have hδcpc : ClosedProperConvexFn δ := hδpoly.closedProperConvexFn hδproper
  have hx₀δ : x₀ ∈ convexDom δ := by rw [hδdom]; exact hx₀M
  -- `h = δ + f` is polyhedral and proper, with `dom h = M ∩ dom f`
  have hhpoly : PolyhedralFn (δ + f) := PolyhedralFn.add hδpoly hf hδbot hpf.ne_bot
  have hhbot : ∀ x, (δ + f) x ≠ ⊥ := fun x =>
    EReal.add_ne_bot_iff.2 ⟨hδbot x, hpf.ne_bot x⟩
  have hhdom : convexDom (δ + f) = (MA : Set E) ∩ convexDom f := by
    rw [convexDom_add hδbot hpf.ne_bot, hδdom]
  have hx₀h : x₀ ∈ convexDom (δ + f) := by rw [hhdom]; exact ⟨hx₀M, hxf⟩
  have hhproper : ProperConvex (δ + f) := ⟨⟨x₀, hx₀h⟩, hhbot⟩
  have hhcpc : ClosedProperConvexFn (δ + f) := hhpoly.closedProperConvexFn hhproper
  -- the relative-interior step
  obtain ⟨x₁, hx₁h, hx₁g⟩ :=
    relint_inter_relint_nonempty_of_subset_affineSpan
      (PolyhedralFn.convexFn hhpoly).convex_convexDom hg.convex.convex_convexDom
      (by rw [hhdom]; exact fun x hx => hx.1) hx₀h hxg
  -- the three exact splittings
  have hAg : IsExactSum B (δ + f) g := IsExactSum.of_relint_closed hhcpc hg hx₁h hx₁g
  have hδf : IsExactSum B δ f := IsExactSum.of_polyhedral_pair hδpoly hδproper hf hpf hx₀δ hxf
  have hx₀riδ : x₀ ∈ ri (convexDom δ) := by
    rw [hδdom, AffineSubspace.intrinsicInterior_coe]; exact hx₀M
  have hδg : IsExactSum B δ g := IsExactSum.of_relint_closed hδcpc hg hx₀riδ hxg
  -- `δ` is absorbed on both sides
  have hsumδg : δ + g = g := indicatorFn_add_eq_self hdomgM
  have hsum : δ + f + g = f + g := by
    rw [add_assoc]
    exact indicatorFn_add_eq_self
      (by rw [convexDom_add hpf.ne_bot hg.proper.ne_bot]; exact fun x hx => hdomgM hx.2)
  have hδne : ∀ y : F, convexConj B δ y ≠ ⊥ :=
      fun y => convexConj_ne_bot hδproper.convexDom_nonempty y
  have hgne : ∀ y : F, convexConj B g y ≠ ⊥ :=
      fun y => convexConj_ne_bot hg.proper.convexDom_nonempty y
  have hgconj : convexConj B g = infConv (convexConj B δ) (convexConj B g) := by
    have h0 := hδg.convexConj_add
    rwa [hsumδg] at h0
  refine ⟨hpf, hg.proper, fun y => ?_⟩
  obtain ⟨z₁, z₂, hz, hzle⟩ := hAg.exact_le y
  obtain ⟨u, v, huv, huvle⟩ := hδf.exact_le z₁
  have habs : convexConj B g (u + z₂) ≤ convexConj B δ u + convexConj B g z₂ := by
    have hle := infConv_le_add (f := convexConj B δ) (g := convexConj B g) hδne hgne (u + z₂) z₂
    rw [add_sub_cancel_right] at hle
    calc convexConj B g (u + z₂) = infConv (convexConj B δ) (convexConj B g) (u + z₂) :=
        by rw [← hgconj]
      _ ≤ convexConj B δ u + convexConj B g z₂ := hle
  refine ⟨v, u + z₂, ?_, ?_⟩
  · rw [← hz, ← huv]; abel
  · calc convexConj B f v + convexConj B g (u + z₂)
        ≤ convexConj B f v + (convexConj B δ u + convexConj B g z₂) := add_le_add le_rfl habs
      _ = convexConj B δ u + convexConj B f v + convexConj B g z₂ := by
          rw [← add_assoc, add_comm (convexConj B f v)]
      _ ≤ convexConj B (δ + f) z₁ + convexConj B g z₂ := add_le_add huvle le_rfl
      _ ≤ convexConj B (δ + f + g) y := hzle
      _ = convexConj B (f + g) y := by rw [hsum]

/-- A proper polyhedral convex function and a *proper convex* function add exactly as soon as
`dom f` meets `ri (dom g)`. Neither closedness of `g` nor a relative interior point of `dom f` is
needed.

The reduction to `IsExactSum.of_polyhedral_closed` runs through the conjugate form
`convexConj_add_eq_convexConj_convexCl_add_convexCl`, whose two segment hypotheses are met on
opposite grounds: `f` is closed proper (only `x₀ ∈ dom f` needed) and `g` is proper convex
(`x₀ ∈ ri (dom g)`). That asymmetry is the asymmetry of the theorem itself. -/
theorem IsExactSum.of_polyhedral [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : PolyhedralFn f) (hpf : ProperConvex f) (hg : ConvexFn g) (hpg : ProperConvex g)
    {x₀ : E} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ ri (convexDom g)) : IsExactSum B f g := by
  have hfc : ClosedProperConvexFn f := hf.closedProperConvexFn hpf
  have hcl : convexCl f = f := hfc.closed
  refine IsExactSum.of_convexCl hpf hpg ?_
    (convexConj_add_eq_convexConj_convexCl_add_convexCl hfc.convex hpf hg hpg
      (hfc.tendstoConvexClAlongSegment hxf) (hg.tendstoConvexClAlongSegment hpg hxg))
  rw [hcl]
  exact IsExactSum.of_polyhedral_closed hf hpf
    ⟨convexFn_convexCl hg, closedConvex_convexCl g, hg.properConvex_convexCl hpg⟩ hxf
    (by rw [hg.relint_convexDom_convexCl hpg]; exact hxg)

end Sum

/-! ### Exact addition of `m` summands -/

section FinsetSum

variable {ι : Type*} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s t u : Finset ι} {f : ι → E → EReal}

private theorem isExactFinsetSum_of_polyhedral_pair_aux [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (f : ι → E → EReal) (x₀ : E) :
    ∀ t : Finset ι, t.Nonempty → (∀ i ∈ t, PolyhedralFn (f i)) → (∀ i ∈ t, ProperConvex (f i)) →
      (∀ i ∈ t, x₀ ∈ convexDom (f i)) → IsExactFinsetSum B t f := by
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
      (PolyhedralFn.finsetSum htne (fun j hj => hpoly j (hmt j hj))
        (fun j hj x => (hpf j (hmt j hj)).ne_bot x)) hprop (hx₀ i (by simp)) ?_
    rw [hdom]
    exact Set.mem_iInter₂.2 fun j hj => hx₀ j (hmt j hj)

/-- **The all-polyhedral case, for `m` summands**: finitely many proper polyhedral convex
functions add exactly as soon as their effective domains have a point in common. -/
theorem IsExactFinsetSum.of_polyhedral_pair [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hpoly : ∀ i ∈ s, PolyhedralFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (f i)) : IsExactFinsetSum B s f :=
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
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : E} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) : IsExactFinsetSum B s f := by
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
    (PolyhedralFn.finsetSum htne hpoly (fun i hi x => (hpf i (hts i hi)).ne_bot x)) hpropt
    hconvu hpropu ?_
    (mem_relint_convexDom_finsetSum hconv (fun i hi => hpf i (hus i hi)) hxu)
  rw [hdomt]
  exact Set.mem_iInter₂.2 hxt

end FinsetSum

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
    (hA : IsAdjointPair B B' A A') (hg : PolyhedralFn g) (hp : ProperConvex g)
    {x₀ : E} (hx₀ : A x₀ ∈ convexDom g) :
    IsExactImage B B' A A' hA g := by
  have hconjpoly : PolyhedralFn (convexConj B' g) := PolyhedralFn.convexConj hg
  have hmappoly : PolyhedralFn (mapLin A' (convexConj B' g)) := PolyhedralFn.mapLin hconjpoly A'
  have hne : (convexDom (compLin g A)).Nonempty := ⟨x₀, by rwa [mem_convexDom, compLin_apply]⟩
  have hbot : ∀ y, convexConj B (compLin g A) y ≠ ⊥ := fun y => convexConj_ne_bot hne y
  have hmapbot : ∀ y, mapLin A' (convexConj B' g) y ≠ ⊥ := fun y hy =>
    hbot y (le_bot_iff.1 (hy ▸ convexConj_compLin_le_mapLin hA g y))
  have heq : convexConj B (compLin g A) = mapLin A' (convexConj B' g) := by
    rw [convexConj_compLin_eq_convexCl_mapLin hA hg.convexFn (hg.closedConvex hp.ne_bot)]
    exact hmappoly.closedConvex hmapbot
  refine ⟨hp, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hmapbot y) hy
  obtain ⟨z, hz, hzeq⟩ := exists_mapLin_eq_of_polyhedralFn hconjpoly A' hμ
  exact ⟨z, hz, le_of_eq hzeq⟩

end Image

end ConvexAnalysis
