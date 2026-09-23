import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.RelativeInterior

/-!
# The relative-interior constraint qualification

`Duality/Exact.lean` names the *conclusions* `IsExactImage` and `IsExactSum` — that a conjugate
formula holds with the infimum attained. This file supplies the first sufficient condition for
each, the classical relative-interior hypothesis:

```
A ⁻¹' ri (dom g) ≠ ∅        and        ri (dom f) ∩ ri (dom g) ≠ ∅.
```

Both reduce to the same two ingredients: closedness of the dual object — a linear image, or a sum,
of closed convex sets — and the fact that a linear function which is `≤ 0` on a convex set and
attains that bound at a *relative interior* point is constant on the set.

## Main results

* `IsExactImage.of_relint` — a proper convex `g` pulls back exactly along a linear map whose range
  meets `ri (dom g)` ([rockafellar1970convex] Theorem 16.3). `IsExactImage.of_relint_closed` is the
  closed case, which carries the argument.
* `IsExactSum.of_relint` — two proper convex functions whose effective domains share a relative
  interior point add exactly ([rockafellar1970convex] Theorem 16.4); `IsExactSum.of_relint_closed`
  is again the closed case, and `IsExactFinsetSum.of_relint` the `m`-ary form.
* `TendstoConvexClAlongSegment` — "`cl f` is the limit of `f` along segments issuing from `x₀`", the
  single hypothesis shared by the two ways of obtaining it: `x₀ ∈ ri (dom f)` for a proper convex
  `f`, and `x₀ ∈ dom f` for a closed proper convex one.
* `convexConj_add_eq_convexConj_convexCl_add_convexCl`,
  `convexConj_compLin_eq_convexConj_compLin_convexCl` — passing to closures does not change the
  conjugate of a sum or of a composition, which is what removes closedness from the two
  constructors.
* `properConvex_convexConj_of_properConvex` — in finite dimensions a proper convex `f` already has
  `f*` proper, with no closedness hypothesis.

## Implementation notes

Closures are compared in the conjugate form `(f + g)* = (cl f + cl g)*` rather than as
`cl (f + g) = cl f + cl g` (which is `convexCl_add`, in `Recession/Closedness.lean`). The conjugate
form is weaker but cheaper: the identity of closures needs the segment limit for `f + g` as well,
hence a relative interior point of *both* domains, whereas the conjugate form makes do with a
point of `dom f` and one of `ri (dom g)`.

The two rules topologise opposite spaces. The image rule puts the image closedness theorem on `H`,
so `H` must be finite-dimensional, and `ri (dom g)` puts `G` there too; `F` only receives an image
and `E` is never topologised. The sum rule is the reverse: `ri (dom f)` needs only a normed `E`,
while the sum closedness theorem runs in `F × ℝ` and so `F` must be finite-dimensional.

## References

* [rockafellar1970convex] §9 and §16.
-/

open Pointwise

namespace ConvexAnalysis

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- The image closedness hypothesis for `g*` and the transpose `A'`, discharged from the
relative-interior condition: "`g*` recedes along `z`, and `A'` kills `z`" says that `⟨·, z⟩` is
`≤ 0` on `dom g` and vanishes at `A x₀ ∈ ri (dom g)`, which makes it constant there. -/
theorem mem_constancySpace_convexConj_of_relint [IsCompatiblePairing B']
    [IsCompatiblePairing B'.flip]
    (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (convexDom g)) {z : H}
    (hrec : recessionFn (convexConj B' g) z ≤ 0) (hz0 : A' z = 0) :
    z ∈ constancySpace (convexConj B' g) := by
  have hconjp : ProperConvex (convexConj B' g) := properConvex_convexConj hg
  rw [constancySpace_convexConj hg.proper hconjp]
  have hnonpos : ∀ x ∈ convexDom g, (B'.flip z) x ≤ 0 := by
    intro x hx
    rw [recessionFn_convexConj hg.proper hconjp, supportFn_le_zero_iff] at hrec
    exact hrec x hx
  have hvanish : (B'.flip z) (A x₀) = 0 := by
    rw [LinearMap.flip_apply, hA x₀ z, hz0, map_zero]
  exact eq_zero_of_nonpos_of_mem_relint hx₀ hnonpos hvanish

omit [FiniteDimensional ℝ G] in
/-- **A closed proper convex function pulls back exactly along a linear map whose range meets the
relative interior of its effective domain.** -/
theorem IsExactImage.of_relint_closed [IsCompatiblePairing B'] [IsCompatiblePairing B'.flip]
    [IsCompatiblePairing B.flip] (hA : IsAdjointPair B B' A A') (hg : ClosedProperConvexFn g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (convexDom g)) :
    IsExactImage B B' A A' hA g := by
  have hconjp : ProperConvex (convexConj B' g) := properConvex_convexConj hg
  have hconjcpc : ClosedProperConvexFn (convexConj B' g) :=
    ⟨convexFn_convexConj B' g, closedConvex_convexConj, hconjp⟩
  have hkey : ∀ z : H,
      recessionFn (convexConj B' g) z ≤ 0 → A' z = 0 → z ∈ constancySpace (convexConj B' g) :=
    fun z hrec hz0 => mem_constancySpace_convexConj_of_relint hA hg hx₀ hrec hz0
  obtain ⟨-, hcpc, -⟩ := closedProperConvexFn_mapLin hconjcpc A' hkey
  -- the image of the epigraph is already closed, so the closure in the identity is redundant
  have heq : convexConj B (compLin g A) = mapLin A' (convexConj B' g) := by
    rw [convexConj_compLin_eq_convexCl_mapLin hA hg.convex hg.closed]
    exact hcpc.closed
  refine ⟨hg.proper, fun y hy => ?_⟩
  rw [heq] at hy ⊢
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hcpc.proper.ne_bot y) hy
  obtain ⟨z, hzy, hz⟩ :=
    exists_mapLin_eq hconjcpc A' hkey hμ.le
  exact ⟨z, hzy, hμ ▸ hz⟩

end Image

/-! ### Sums -/

section Sum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [FiniteDimensional ℝ F] in
/-- A direction of recession of `epi f*` bounds the pairing on `dom f`: the recession function of
`f*` is the support function of `dom f`, read one point at a time. -/
theorem le_of_mk_mem_recessionCone_epi_convexConj [IsCompatiblePairing B]
    (hf : ClosedProperConvexFn f)
    {z : F} {ν : ℝ} (hp : ((z, ν) : F × ℝ) ∈ recessionCone (epi (convexConj B f)))
    {x : E} (hx : x ∈ convexDom f) : B x z ≤ ν := by
  have hle := recessionFn_le_coe_iff.2 hp
  rw [recessionFn_convexConj hf.proper (properConvex_convexConj hf), supportFn_le_coe_iff] at hle
  exact hle x hx

omit [FiniteDimensional ℝ F] in
/-- **The relative-interior step for sums.** If `(z, ν)` is a direction of recession of `epi f*`
whose bound `ν` is already attained at a relative interior point of `dom f`, then `(z, ν)` lies in
the lineality space: the recession direction reads as "`⟨·, z⟩ ≤ ν` on `dom f`", and a bound
attained at a relative interior point is attained across the whole domain. -/
theorem mk_mem_linealitySpace_epi_convexConj_of_relint [IsCompatiblePairing B]
    (hf : ClosedProperConvexFn f) {x₀ : E} (hx₀ : x₀ ∈ ri (convexDom f)) {z : F} {ν : ℝ}
    (hp : ((z, ν) : F × ℝ) ∈ recessionCone (epi (convexConj B f))) (hν : ν ≤ B x₀ z) :
    ((z, ν) : F × ℝ) ∈ linealitySpace (epi (convexConj B f)) := by
  have hx₀f : x₀ ∈ convexDom f := intrinsicInterior_subset hx₀
  have hmax : B x₀ z = ν :=
    le_antisymm (le_of_mk_mem_recessionCone_epi_convexConj hf hp hx₀f) hν
  have hconst : ∀ x ∈ convexDom f, (B.flip z) x = (B.flip z) x₀ :=
    eq_of_isMaxOn_of_mem_relint hx₀ fun x hx =>
      le_trans (le_of_mk_mem_recessionCone_epi_convexConj hf hp hx) hν
  refine mem_linealitySpace.2 ⟨hp, ?_⟩
  rw [Prod.neg_mk, ← recessionFn_le_coe_iff,
      recessionFn_convexConj hf.proper (properConvex_convexConj hf),
    supportFn_le_coe_iff]
  intro x hx
  have hx' : B x z = ν := by
    have hc := hconst x hx
    rw [LinearMap.flip_apply, LinearMap.flip_apply, hmax] at hc
    exact hc
  rw [map_neg, hx']

/-- **Two closed proper convex functions add exactly as soon as their effective domains have a
common relative interior point.**

The proof is the closedness of a sum of convex sets, applied to `epi f*` and `epi g*`: once their
sum is closed it is the epigraph of `f* □ g*`, and the splitting supplied at each of its points is
the attainment `IsExactSum.exact_le` asks for. -/
theorem IsExactSum.of_relint_closed [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    {x₀ : E} (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ ri (convexDom g)) :
    IsExactSum B f g := by
  have hx₀f : x₀ ∈ convexDom f := intrinsicInterior_subset hxf
  have hx₀g : x₀ ∈ convexDom g := intrinsicInterior_subset hxg
  have hup : ProperConvex (convexConj B f) := properConvex_convexConj hf
  have hvp : ProperConvex (convexConj B g) := properConvex_convexConj hg
  have hucpc : ClosedProperConvexFn (convexConj B f) :=
      ⟨convexFn_convexConj B f, closedConvex_convexConj, hup⟩
  have hvcpc : ClosedProperConvexFn (convexConj B g) :=
      ⟨convexFn_convexConj B g, closedConvex_convexConj, hvp⟩
  have hune : (epi (convexConj B f)).Nonempty := (epi_nonempty_iff _).2 hup.convexDom_nonempty
  have hvne : (epi (convexConj B g)).Nonempty := (epi_nonempty_iff _).2 hvp.convexDom_nonempty
  -- the closedness hypothesis, discharged from the relative-interior condition
  have hrec : ∀ p ∈ recessionCone (epi (convexConj B f)),
      ∀ q ∈ recessionCone (epi (convexConj B g)),
      p + q = 0 →
        p ∈ linealitySpace (epi (convexConj B f)) ∧ q ∈ linealitySpace (epi (convexConj B g)) := by
    rintro ⟨z, ν⟩ hp ⟨w, ρ⟩ hq hzero
    have hz : z + w = 0 := congrArg Prod.fst hzero
    have hνρ : ν + ρ = 0 := congrArg Prod.snd hzero
    have h₁ : B x₀ z ≤ ν := le_of_mk_mem_recessionCone_epi_convexConj hf hp hx₀f
    have h₂ : B x₀ w ≤ ρ := le_of_mk_mem_recessionCone_epi_convexConj hg hq hx₀g
    have hBzw : B x₀ z + B x₀ w = 0 := by rw [← map_add, hz, map_zero]
    exact ⟨mk_mem_linealitySpace_epi_convexConj_of_relint hf hxf hp (by linarith),
      mk_mem_linealitySpace_epi_convexConj_of_relint hg hxg hq (by linarith)⟩
  have hclosed : IsClosed (epi (convexConj B f) + epi (convexConj B g)) :=
    Convex.isClosed_add (convexFn_convexConj B f).convex_epi hucpc.isClosed_epi hune
      (convexFn_convexConj B g).convex_epi hvcpc.isClosed_epi hvne hrec
  -- a closed sum of epigraphs is an epigraph, namely that of the infimal convolution
  have hmono : ∀ (y : F) (μ ν : ℝ), (y, μ) ∈ epi (convexConj B f) + epi (convexConj B g) → μ ≤ ν →
      (y, ν) ∈ epi (convexConj B f) + epi (convexConj B g) := by
    rintro y μ ν ⟨⟨y₁, a⟩, h₁, ⟨y₂, b⟩, h₂, heq⟩ hμν
    have hy : y₁ + y₂ = y := congrArg Prod.fst heq
    have hab : a + b = μ := congrArg Prod.snd heq
    refine ⟨(y₁, a), h₁, (y₂, b + (ν - μ)), mk_mem_epi.2 ?_, ?_⟩
    · exact (mk_mem_epi.1 h₂).trans (by exact_mod_cast (by linarith : b ≤ b + (ν - μ)))
    · change ((y₁, a) : F × ℝ) + (y₂, b + (ν - μ)) = (y, ν)
      rw [Prod.mk_add_mk, hy, show a + (b + (ν - μ)) = ν by linarith]
  have hepiEq : epi (infConv (convexConj B f) (convexConj B g)) = epi (convexConj B f)
      + epi (convexConj B g) :=
    epi_infConv (IsEpiLike.of_isClosed hmono hclosed)
  -- properness of the infimal convolution, from properness of `(f + g)*`
  have hdomne : (convexDom (f + g)).Nonempty :=
    ⟨x₀, by
      rw [mem_convexDom, Pi.add_apply]
      exact EReal.add_lt_top (mem_convexDom.1 hx₀f).ne (mem_convexDom.1 hx₀g).ne⟩
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
    rw [convexConj_add_eq_convexCl_infConv hf.convex hf.closed hg.convex hg.closed]
    exact hclosedFn
  refine ⟨hf.proper, hg.proper, fun y => ?_⟩
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

end Sum

/-! ### Dropping closedness from the constraint qualifications -/

section Closure

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- `f` is **recovered along segments issuing from `x₀`**: at every `y` the value `(cl f) y` is the
limit of `f` along the half-open segment from `x₀` to `y`.

This holds for a proper convex `f` when `x₀ ∈ ri (dom f)`, and for a closed proper convex `f` when
`x₀ ∈ dom f`. It is the only property of `x₀` the closure-removal argument uses, so the two
constraint qualifications run through one and the same lemma. -/
def TendstoConvexClAlongSegment (f : E → EReal) (x₀ : E) : Prop :=
  ∀ y, Tendsto (fun a : ℝ => f ((1 - a) • x₀ + a • y)) (𝓝[<] (1 : ℝ)) (𝓝 (convexCl f y))

omit [FiniteDimensional ℝ F] in
/-- **In finite dimensions the conjugate of a proper convex function is proper**, with no
closedness hypothesis. It goes through the properness of `cl f`, which is where
finite-dimensionality enters: `f* = (cl f)*`, and `cl f` is closed proper convex. -/
theorem properConvex_convexConj_of_properConvex [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : ProperConvex f) :
    ProperConvex (convexConj B f) := by
  rw [← convexConj_convexCl]
  exact properConvex_convexConj
      ⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩

/-- **A proper convex function is recovered along segments issuing from any relative interior point
of its effective domain.** -/
theorem ConvexFn.tendstoConvexClAlongSegment (hf : ConvexFn f) (hp : ProperConvex f) {x₀ : E}
    (hx₀ : x₀ ∈ ri (convexDom f)) : TendstoConvexClAlongSegment f x₀ := by
  intro y
  rw [hf.convexCl_eq_lscHull hp]
  exact hf.tendsto_lscHull_along_segment_relint hx₀ y

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **A closed proper convex function is recovered along segments issuing from any point of its
effective domain** — no relative interior needed. -/
theorem ClosedProperConvexFn.tendstoConvexClAlongSegment (hf : ClosedProperConvexFn f) {x₀ : E}
    (hx₀ : x₀ ∈ convexDom f) : TendstoConvexClAlongSegment f x₀ := by
  intro y
  rw [show convexCl f = f from hf.closed]
  exact tendsto_along_segment_of_closed_proper hf hx₀ y

omit [FiniteDimensional ℝ F] in
/-- **Passing to closures does not change the conjugate of a sum**, in the form the constraint
qualifications consume: if two proper convex functions are both recovered along segments issuing
from one common point, then `f + g` and `cl f + cl g` have the same conjugate.

The stronger `cl (f + g) = cl f + cl g` needs the segment limit for `f + g` as well, hence a point
of `ri (dom f) ∩ ri (dom g)`. The conjugate form needs no such thing, since `f* = (cl f)*` holds
outright; that is what lets a caller make do with a point of `dom f` and one of `ri (dom g)`. -/
theorem convexConj_add_eq_convexConj_convexCl_add_convexCl (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g)
    (hpg : ProperConvex g) {x₀ : E} (hsf : TendstoConvexClAlongSegment f x₀)
    (hsg : TendstoConvexClAlongSegment g x₀) :
    convexConj B (f + g) = convexConj B (convexCl f + convexCl g) := by
  have hclf : ProperConvex (convexCl f) := hf.properConvex_convexCl hpf
  have hclg : ProperConvex (convexCl g) := hg.properConvex_convexCl hpg
  have hmono : convexCl f + convexCl g ≤ f + g :=
      fun x => add_le_add (convexCl_le f x) (convexCl_le g x)
  refine funext fun y => le_antisymm (convexConj_antitone B hmono y) ?_
  have key : ∀ c : ℝ, convexConj B (f + g) y ≤ (c : EReal) →
      convexConj B (convexCl f + convexCl g) y ≤ (c : EReal) := by
    intro c hc
    rw [convexConj_le_coe_iff] at hc ⊢
    intro x
    have hlin : ∀ a : ℝ, B ((1 - a) • x₀ + a • x) y = (1 - a) * B x₀ y + a * B x y := by
      intro a
      rw [map_add, map_smul, map_smul]
      simp
    have hL : Tendsto (fun a : ℝ => affineFn B y c ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 (affineFn B y c x)) := by
      simp only [affineFn_eq_coe, hlin]
      exact EReal.tendsto_coe.2
        ((tendsto_affine_nhdsLT_one (B x₀ y) (B x y)).sub tendsto_const_nhds)
    have hR : Tendsto (fun a : ℝ => (f + g) ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 ((convexCl f + convexCl g) x)) := by
      have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (convexCl f x, convexCl g x) :=
        EReal.continuousAt_add (Or.inr (hclg.ne_bot x)) (Or.inl (hclf.ne_bot x))
      exact hcont.tendsto.comp ((hsf x).prodMk_nhds (hsg x))
    exact le_of_tendsto_of_tendsto' hL hR fun a => hc _
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  exact absurd (key c h1.le) (not_le.2 h2)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Exactness passes from the closures to the functions themselves, as soon as the sum has not
changed its conjugate. `convexConj_add_eq_convexConj_convexCl_add_convexCl` is what supplies the
second hypothesis. -/
theorem IsExactSum.of_convexCl [IsContinuousPairing B] (hpf : ProperConvex f) (hpg : ProperConvex g)
    (h : IsExactSum B (convexCl f) (convexCl g))
    (hconj : convexConj B (f + g) = convexConj B (convexCl f + convexCl g)) : IsExactSum B f g := by
  refine ⟨hpf, hpg, fun y => ?_⟩
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  rw [convexConj_convexCl, convexConj_convexCl] at hle
  exact ⟨y₁, y₂, hy, by rw [hconj]; exact hle⟩

/-- **Two *proper convex* functions add exactly as soon as their effective domains have a relative
interior point in common.** Closedness is not needed;
`convexConj_add_eq_convexConj_convexCl_add_convexCl` and the invariance of `ri (dom f)` under
closure reduce it to `IsExactSum.of_relint_closed`. -/
theorem IsExactSum.of_relint [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConvexFn g) (hpg : ProperConvex g)
    {x₀ : E} (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ ri (convexDom g)) : IsExactSum B f g :=
  IsExactSum.of_convexCl hpf hpg
    (IsExactSum.of_relint_closed ⟨convexFn_convexCl hf, closedConvex_convexCl f,
        hf.properConvex_convexCl hpf⟩
      ⟨convexFn_convexCl hg, closedConvex_convexCl g, hg.properConvex_convexCl hpg⟩
      (by rw [hf.relint_convexDom_convexCl hpf]; exact hxf)
          (by rw [hg.relint_convexDom_convexCl hpg]; exact hxg))
    (convexConj_add_eq_convexConj_convexCl_add_convexCl hf hpf hg hpg
      (hf.tendstoConvexClAlongSegment hpf hxf) (hg.tendstoConvexClAlongSegment hpg hxg))

end Closure

/-! ### Dropping closedness on the image side -/

section ClosureImage

open Filter Topology

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [FiniteDimensional ℝ H] in
/-- **Passing to closures does not change the conjugate of a composition**: if `g` is recovered
along segments issuing from `A x₀`, then `g A` and `(cl g) A` have the same conjugate.

Cheaper than `convexConj_add_eq_convexConj_convexCl_add_convexCl`: one limit rather than two, so no
properness is needed, and `E` need not be topologised since the segment is pushed forward by `A`
before any limit is taken. The book's form here is `cl (g A) = (cl g) A` (`convexCl_compLin`), which
does need `E` finite-dimensional. -/
theorem convexConj_compLin_eq_convexConj_compLin_convexCl (A : E →ₗ[ℝ] G) {x₀ : E}
    (hs : TendstoConvexClAlongSegment g (A x₀)) :
    convexConj B (compLin g A) = convexConj B (compLin (convexCl g) A) := by
  have hmono : compLin (convexCl g) A ≤ compLin g A := fun x => convexCl_le g (A x)
  refine funext fun y => le_antisymm (convexConj_antitone B hmono y) ?_
  have key : ∀ c : ℝ, convexConj B (compLin g A) y ≤ (c : EReal) →
      convexConj B (compLin (convexCl g) A) y ≤ (c : EReal) := by
    intro c hc
    rw [convexConj_le_coe_iff] at hc ⊢
    intro x
    have hlin : ∀ a : ℝ, B ((1 - a) • x₀ + a • x) y = (1 - a) * B x₀ y + a * B x y := by
      intro a
      rw [map_add, map_smul, map_smul]
      simp
    have hL : Tendsto (fun a : ℝ => affineFn B y c ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 (affineFn B y c x)) := by
      simp only [affineFn_eq_coe, hlin]
      exact EReal.tendsto_coe.2
        ((tendsto_affine_nhdsLT_one (B x₀ y) (B x y)).sub tendsto_const_nhds)
    have hR : Tendsto (fun a : ℝ => compLin g A ((1 - a) • x₀ + a • x))
        (𝓝[<] (1 : ℝ)) (𝓝 (compLin (convexCl g) A x)) := by
      have hmap : ∀ a : ℝ, A ((1 - a) • x₀ + a • x) = (1 - a) • A x₀ + a • A x := fun a => by
        rw [map_add, map_smul, map_smul]
      simpa only [compLin_apply, hmap] using hs (A x)
    exact le_of_tendsto_of_tendsto' hL hR fun a => hc _
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  exact absurd (key c h1.le) (not_le.2 h2)

/-- **A *proper convex* `g` pulls back exactly along a linear map whose range meets `ri (dom g)`.**
Closedness is not needed; the reduction to `IsExactImage.of_relint_closed` is
`convexConj_compLin_eq_convexConj_compLin_convexCl` together with the fact that `cl g` has the same
relative interior of effective domain. -/
theorem IsExactImage.of_relint [IsCompatiblePairing B'] [IsCompatiblePairing B'.flip]
    [IsCompatiblePairing B.flip] (hA : IsAdjointPair B B' A A') (hg : ConvexFn g)
        (hp : ProperConvex g)
    {x₀ : E} (hx₀ : A x₀ ∈ ri (convexDom g)) :
    IsExactImage B B' A A' hA g := by
  have hcl := IsExactImage.of_relint_closed hA
    ⟨convexFn_convexCl hg, closedConvex_convexCl g, hg.properConvex_convexCl hp⟩
    (show A x₀ ∈ ri (convexDom (convexCl g)) by rw [hg.relint_convexDom_convexCl hp]; exact hx₀)
  have heq : convexConj B (compLin g A) = convexConj B (compLin (convexCl g) A) :=
    convexConj_compLin_eq_convexConj_compLin_convexCl A (hg.tendstoConvexClAlongSegment hp hx₀)
  refine ⟨hp, fun y hy => ?_⟩
  obtain ⟨z, hz, hle⟩ := hcl.exact_le y (by rw [← heq]; exact hy)
  exact ⟨z, hz, by rwa [convexConj_convexCl, ← heq] at hle⟩

end ClosureImage

/-! ### Finitely many summands -/

section FinsetSum

variable {ι : Type*} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The sum of a finite family of proper convex functions with a common domain point, packaged as
the three facts the binary constraint qualifications ask about it. -/
theorem properConvexFn_finsetSum (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (f i)) :
    ConvexFn (∑ i ∈ s, f i) ∧ ProperConvex (∑ i ∈ s, f i) ∧ convexDom (∑ i ∈ s, f i) = ⋂ i ∈ s,
        convexDom (f i) := by
  have hbot : ∀ i ∈ s, ∀ x, f i x ≠ ⊥ := fun i hi x => (hpf i hi).ne_bot x
  have hdom : convexDom (∑ i ∈ s, f i) = ⋂ i ∈ s, convexDom (f i) := convexDom_finsetSum hbot
  have hfun : (∑ i ∈ s, f i) = fun x => ∑ i ∈ s, f i x := by
    funext x
    rw [Finset.sum_apply]
  refine ⟨by rw [hfun]; exact ConvexFn.sum hf hbot, ⟨⟨x₀, ?_⟩, fun x => ?_⟩, hdom⟩
  · rw [hdom]
    exact Set.mem_iInter₂.2 hx₀
  · rw [Finset.sum_apply]
    exact EReal.sum_ne_bot fun i hi => hbot i hi x

omit [FiniteDimensional ℝ F] in
/-- **The relative interior of the effective domain of a sum**: a point lying in the relative
interior of every `dom fᵢ` lies in the relative interior of `dom (f₁ + ⋯ + fₘ)`. -/
theorem mem_relint_convexDom_finsetSum (hf : ∀ i ∈ s, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) : x₀ ∈ ri (convexDom (∑ i ∈ s, f i)) := by
  rw [convexDom_finsetSum fun i hi x => (hpf i hi).ne_bot x,
    Convex.relint_biInter_finset (fun i hi => (hf i hi).convex_convexDom) hx₀]
  exact Set.mem_iInter₂.2 hx₀

private theorem isExactFinsetSum_of_relint_aux [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (f : ι → E → EReal) (x₀ : E) : ∀ t : Finset ι, t.Nonempty → (∀ i ∈ t, ConvexFn (f i)) →
      (∀ i ∈ t, ProperConvex (f i)) → (∀ i ∈ t, x₀ ∈ ri (convexDom (f i)))
          → IsExactFinsetSum B t f := by
  intro t
  induction t using Finset.cons_induction with
  | empty => intro hne; exact absurd hne (by simp)
  | cons i t hi ih =>
    intro _ hf hpf hx₀
    have hmt : ∀ j ∈ t, j ∈ Finset.cons i t hi := fun j hj => Finset.mem_cons_of_mem hj
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · rw [Finset.cons_empty]
      exact IsExactFinsetSum.singleton (hpf i (by simp))
    refine IsExactFinsetSum.cons hi ?_
      (ih htne (fun j hj => hf j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => hx₀ j (hmt j hj)))
    obtain ⟨hconv, hprop, -⟩ :=
      properConvexFn_finsetSum (fun j hj => hf j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => intrinsicInterior_subset (hx₀ j (hmt j hj)))
    exact IsExactSum.of_relint (hf i (by simp)) (hpf i (by simp)) hconv hprop (hx₀ i (by simp))
      (mem_relint_convexDom_finsetSum (fun j hj => hf j (hmt j hj)) (fun j hj => hpf j (hmt j hj))
        (fun j hj => hx₀ j (hmt j hj)))

/-- **Finitely many proper convex functions add exactly as soon as the relative interiors of their
effective domains have a point in common.**

The induction is `IsExactFinsetSum.cons`; beyond the binary case it needs only that the effective
domain of a partial sum is `⋂ dom fᵢ` and that `x₀` lies in the relative interior of that
intersection (`mem_relint_convexDom_finsetSum`). -/
theorem IsExactFinsetSum.of_relint [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hs : s.Nonempty) (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : E}
    (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) : IsExactFinsetSum B s f :=
  isExactFinsetSum_of_relint_aux f x₀ s hs hf hpf hx₀

end FinsetSum

end ConvexAnalysis
