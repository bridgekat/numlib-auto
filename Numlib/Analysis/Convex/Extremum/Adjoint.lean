import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Extremum.Lagrangian

/-!
# Adjoint bifunctions and dual programs

The **adjoint** of a convex bifunction `F : U → X → EReal` is the concave bifunction

`(F* y)(v) = ⨅ (u, x) {F u x - ⟨x, y⟩ + ⟨u, v⟩}`,

and the concave program `(P*)` dual to `(P)` is "maximise `F* 0` over `V`". Everything here follows
from one computation: `F*` is the conjugate of the graph function of `F`, negated and read at the
reflected point `(-v, y)`. So `F*` is closed concave with no hypothesis on `F`, `F** = cl F`, and
the dual objective is the *concave* conjugate of `-inf F`. The same view shows that `cl F` is
computed slice by slice on `ri (dom F)`, and that closing a strongly consistent program changes
neither its value, its solutions, nor its Kuhn–Tucker vectors.

## Main definitions

* `convexAdjointBifun Bu Bx F`, `concaveAdjointBifun Bu Bx G` — the adjoint of a convex bifunction,
  and of a concave one (the same formula with a supremum).
* `lowerAdjointBifun Bu Bx F` — Rockafellar's `F⁎*`, the inverse of the adjoint, which is also the
  adjoint of the inverse (`convexAdjointBifun_flip_inverseBifun`,
  `lowerAdjointBifun_eq_concaveAdjointBifun`: the inverse commutes with the adjoint).
* `ClosedConvexBifun`, `ImageClosedBifun` — the graph function is closed, the slices `F u` are each
  closed; `convexClBifun F` is the closure of the graph function.

## Main results

* `convexAdjointBifun_eq_neg_convexConj_graphFn` — the computation above;
  `concaveFn_graphFn_convexAdjointBifun`, `closedConcave_graphFn_convexAdjointBifun`,
  `concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun`,
  `properConcave_graphFn_convexAdjointBifun_iff` — `F*` is closed concave, `F** = cl F`, and `F*` is
  proper exactly when `F` is ([rockafellar1970convex] Theorem 30.1);
  `convexBifun_lowerAdjointBifun`, `closedConvexBifun_lowerAdjointBifun`,
  `lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun`,
  `convexAdjointBifun_flip_lowerAdjointBifun` — the same in the `F⁎*` packaging.
* `convexAdjointBifun_zero_eq_concaveConj` — the dual objective as a concave conjugate;
  `convexAdjointBifun_zero_le` — weak duality.
* `mem_kuhnTucker_iff_convexAdjointBifun_zero_eq` — the Kuhn–Tucker vectors are the points where the
  dual objective attains the optimal value, with no normality needed.
* `convexClBifun_apply_eq_convexCl`, `infBifun_convexClBifun_eq` and the two `convexDomBifun`
  inclusions — the closure of a bifunction, slice by slice ([rockafellar1970convex] Theorem 29.4).

## Implementation notes

The sign flip is carried in the argument rather than in a reflected pairing: `⟨u, -v⟩ + ⟨x, y⟩` is
read as the pairing of `(u, x)` with `(-v, y)`, so `F*` is `convexConj` at a reflected point and
`convexConj`'s own lemmas apply verbatim. The two real terms are grouped inside one coercion, so no
`∞ - ∞` can arise, and the dual objective uses the *concave* conjugate, since `g* ≠ -(-g)*`. The
closedness of `F*` asks for `IsContinuousPairing (prodPairing Bu Bx).flip` rather than the
un-flipped class: `closedConvex_convexConj` needs continuity on the side the conjugate lives on, and
the un-flipped form would demand a topology on `U × X` that this development never supplies.

## References

* [rockafellar1970convex] §§29-30.
-/

namespace ConvexAnalysis

section Defs

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V} {y : Y}

/-- The **adjoint** of a convex bifunction: `(F* y)(v) = ⨅ (u, x) {F u x - ⟨x, y⟩ + ⟨u, v⟩}`, a
*concave* bifunction from `Y` to `V`. -/
noncomputable def convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal))

theorem convexAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (y : Y) (v : V) :
    convexAdjointBifun Bu Bx F y v = ⨅ p : U × X,
        (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal)) :=
  rfl

/-- The adjoint of a bifunction that is finite somewhere is nowhere `⊤`: the infimum defining it
is bounded above by the single term at `(u₀, x₀)`. -/
theorem convexAdjointBifun_ne_top {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤) (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (y : Y) (v : V) : convexAdjointBifun Bu Bx F y v ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.add_lt_top hF (EReal.coe_ne_top _)).ne (iInf_le _ (u₀, x₀))

/-- **The computation everything here rests on**: the adjoint is the conjugate of the graph
function, negated and evaluated at a reflected point. -/
theorem convexAdjointBifun_eq_neg_convexConj_graphFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    convexAdjointBifun Bu Bx F y v = -(convexConj (prodPairing Bu Bx) (graphFn F) (-v, y)) := by
  rw [convexAdjointBifun_apply, convexConj_apply, EReal.neg_iSup]
  refine iInf_congr fun p => ?_
  have hpair : (prodPairing Bu Bx p (-v, y) : ℝ) = -(Bu p.1 v - Bx p.2 y) := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair, EReal.neg_coe_sub]
  change graphFn F p + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal)
      = graphFn F p + -(-((Bu p.1 v - Bx p.2 y : ℝ) : EReal))
  rw [neg_neg]

end Defs

/-! ### The adjoint is a closed concave bifunction -/

section Closed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- The reflection `(y, v) ↦ (-v, y)` that turns the adjoint into a conjugate. -/
def adjointSwap (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y] :
    (Y × V) →ₗ[ℝ] (V × Y) :=
  LinearMap.prod (-LinearMap.snd ℝ Y V) (LinearMap.fst ℝ Y V)

@[simp] theorem adjointSwap_apply (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y]
    [Module ℝ Y] (q : Y × V) : adjointSwap V Y q = (-q.2, q.1) := rfl

/-- The graph function of the adjoint is minus a conjugate composed with a linear reflection. -/
theorem graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : graphFn (convexAdjointBifun Bu Bx F)
      = fun q => -(compLin (convexConj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) q) :=
  funext fun q => convexAdjointBifun_eq_neg_convexConj_graphFn Bu Bx F q.1 q.2

/-- The same with the sign moved across: `-F*` is a conjugate composed with a linear reflection.
Every closedness, convexity and properness statement about `F*` goes through this form. -/
theorem neg_graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : (fun q => -(graphFn (convexAdjointBifun Bu Bx F) q))
      = compLin (convexConj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
  funext q
  rw [graphFn_convexAdjointBifun, neg_neg]

/-- The adjoint of *any* bifunction is concave. No convexity, properness or closedness of `F` is
needed. -/
theorem concaveFn_graphFn_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveFn (graphFn (convexAdjointBifun Bu Bx F)) := by
  rw [concaveFn_iff_convexFn_neg, neg_graphFn_convexAdjointBifun]
  exact convexFn_compLin _ (convexFn_convexConj _ _)

/-- The same, packaged as a statement about bifunctions. -/
theorem concaveBifun_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveBifun (convexAdjointBifun Bu Bx F) :=
  concaveFn_graphFn_convexAdjointBifun Bu Bx F

/-- The same negated: `-F*` is a *convex* bifunction. This is the shape in which the concave
normality criteria consume the adjoint. -/
theorem convexBifun_neg_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun fun y v => -(convexAdjointBifun Bu Bx F y v) :=
  concaveFn_iff_convexFn_neg.1 (concaveFn_graphFn_convexAdjointBifun Bu Bx F)

/-- Each slice `F* y` of the adjoint is a concave function. -/
theorem concaveFn_convexAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) : ConcaveFn (convexAdjointBifun Bu Bx F y) :=
  concaveFn_iff_convexFn_neg.2 ((convexBifun_neg_convexAdjointBifun Bu Bx F).convexFn_apply y)

end Closed

section ClosedTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

omit [IsTopologicalAddGroup Y] [IsContinuousPairing (prodPairing Bu Bx).flip] in
theorem continuous_adjointSwap : Continuous (adjointSwap V Y) := by
  change Continuous fun q : Y × V => ((-q.2, q.1) : V × Y)
  exact (continuous_neg.comp continuous_snd).prodMk continuous_fst

/-- The adjoint of *any* bifunction is concave-closed. The conjugate is closed, and closedness
survives the linear reflection. -/
theorem closedConcave_graphFn_convexAdjointBifun :
    ClosedConcave (graphFn (convexAdjointBifun Bu Bx F)) := by
  rw [closedConcave_iff_closedConvex_neg, neg_graphFn_convexAdjointBifun]
  exact closedConvex_compLin closedConvex_convexConj continuous_adjointSwap

end ClosedTopology

/-! ### The closure of a bifunction -/

section BifunClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {F : Bifun U X}

/-- The **closure of a bifunction**: the bifunction whose graph function is the closure of that of
`F`. Two applications of the adjoint return exactly this. -/
noncomputable def convexClBifun (F : Bifun U X) : Bifun U X :=
    fun u x => convexCl (graphFn F) (u, x)

theorem convexClBifun_apply (F : Bifun U X) (u : U) (x : X) :
    convexClBifun F u x = convexCl (graphFn F) (u, x) := rfl

@[simp] theorem graphFn_convexClBifun (F : Bifun U X) : graphFn (convexClBifun F)
    = convexCl (graphFn F) := rfl

/-- A bifunction is **closed** when its graph function is. -/
def ClosedConvexBifun (F : Bifun U X) : Prop := ClosedConvex (graphFn F)

theorem closedConvexBifun_iff : ClosedConvexBifun F ↔ ClosedConvex (graphFn F) := Iff.rfl

theorem convexClBifun_le (F : Bifun U X) : convexClBifun F ≤ F :=
    fun u x => convexCl_le (graphFn F) (u, x)

theorem ClosedConvexBifun.convexClBifun_eq (hF : ClosedConvexBifun F) : convexClBifun F = F :=
  funext fun u => funext fun x => congrFun hF (u, x)

theorem closedConvexBifun_iff_convexClBifun_eq : ClosedConvexBifun F ↔ convexClBifun F = F := by
  refine ⟨fun hF => hF.convexClBifun_eq, fun hF => ?_⟩
  change convexCl (graphFn F) = graphFn F
  exact funext fun p => congrFun (congrFun hF p.1) p.2

end BifunClosure

section BifunClosureClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

theorem closedConvexBifun_convexClBifun (F : Bifun U X) : ClosedConvexBifun (convexClBifun F) :=
  closedConvex_convexCl (graphFn F)

/-- Exchanging the two arguments preserves closedness. -/
theorem closedConvexBifun_flipBifun {F : Bifun U X} (hF : ClosedConvexBifun F) :
    ClosedConvexBifun (flipBifun F) := by
  rcases closedConvex_iff.1 (closedConvexBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl (funext fun q => congrFun h (q.2, q.1)))
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_snd.prodMk continuous_fst), fun q => hne (q.2, q.1)⟩)

/-- **The inverse of a concave-closed bifunction is closed.** -/
theorem closedConvexBifun_inverseBifun {G : Bifun U X} (hG : ClosedConcave (graphFn G)) :
    ClosedConvexBifun (inverseBifun G) := by
  have h : ClosedConvexBifun fun u x => -(G u x) := closedConcave_iff_closedConvex_neg.1 hG
  exact closedConvexBifun_flipBifun h

end BifunClosureClosed

/-! ### The closure of a bifunction, slice by slice -/

section RelintClosure

open Filter Topology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- The effective domain of a bifunction is the projection of that of its graph function. Since `ri`
and `closure` commute with a linear image, the slice-by-slice closure is a fact about
`graph F`. -/
theorem convexDomBifun_eq_image_convexDom_graphFn (F : Bifun U X) :
    convexDomBifun F = LinearMap.fst ℝ U X '' convexDom (graphFn F) := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(u, x), mem_convexDom.2 (lt_of_le_of_ne le_top hx), rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, (mem_convexDom.1 hp).ne⟩

/-- **Relative interiors pass to slices**: if `(u, x)` is a relative interior point of a convex set
of pairs, then `x` is one of the slice through `u`. -/
theorem mem_relint_slice {S : Set (U × X)} (hS : Convex ℝ S) {u : U} {x : X}
    (hux : (u, x) ∈ ri S) : x ∈ ri {y | (u, y) ∈ S} := by
  have hT : Convex ℝ {y | (u, y) ∈ S} := by
    intro a ha b hb s t hs ht hst
    have h := hS ha hb hs ht hst
    have hu : s • ((u, a) : U × X) + t • (u, b) = (u, s • a + t • b) := by
      rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hst, one_smul]
    rwa [hu] at h
  have hxT : ((u, x) : U × X) ∈ S := intrinsicInterior_subset hux
  refine (Convex.mem_relint_iff_prolong hT ⟨x, hxT⟩).2 fun y hy => ?_
  obtain ⟨μ, hμ, hmem⟩ := (Convex.mem_relint_iff_prolong hS ⟨(u, y), hy⟩).1 hux (u, y) hy
  refine ⟨μ, hμ, ?_⟩
  have hu : (1 - μ) • ((u, y) : U × X) + μ • (u, x) = (u, (1 - μ) • y + μ • x) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel, one_smul]
  rwa [hu] at hmem

/-- At a relative interior point of `dom F` the closure of a convex bifunction is computed slice by
slice, `(cl F) u = cl (F u)`. A relative interior point of `dom (graph F)` is placed over `u` with
`x` in `ri (dom (F u))`, and both closures are then the same limit along a segment inside the
slice. -/
theorem convexClBifun_apply_eq_convexCl (hF : ConvexBifun F) {u : U}
    (hu : u ∈ ri (convexDomBifun F)) :
    convexClBifun F u = convexCl (F u) := by
  have hconv : Convex ℝ (convexDom (graphFn F)) := ConvexFn.convex_convexDom hF
  have himg : u ∈ LinearMap.fst ℝ U X '' ri (convexDom (graphFn F)) := by
    rw [← Convex.relint_image hconv, ← convexDomBifun_eq_image_convexDom_graphFn]
    exact hu
  obtain ⟨⟨u', x⟩, hp, hpu⟩ := himg
  simp only [LinearMap.fst_apply] at hpu
  subst hpu
  have hslice : x ∈ ri (convexDom (F u')) := mem_relint_slice hconv hp
  have hxdom : x ∈ convexDom (F u') := intrinsicInterior_subset hslice
  by_cases hpr : ProperConvex (graphFn F)
  · have hFu : ProperConvex (F u') := ⟨⟨x, hxdom⟩, fun y => hpr.ne_bot (u', y)⟩
    funext y
    have h1 : Tendsto (fun a : ℝ => graphFn F ((1 - a) • ((u', x) : U × X) + a • (u', y)))
        (𝓝[<] (1 : ℝ)) (𝓝 (convexCl (graphFn F) (u', y))) :=
      ConvexFn.tendsto_convexCl_along_segment_relint hF hpr hp (u', y)
    have heq : (fun a : ℝ => graphFn F ((1 - a) • ((u', x) : U × X) + a • (u', y)))
        = fun a : ℝ => F u' ((1 - a) • x + a • y) := by
      funext a
      have hu : (1 - a) • ((u', x) : U × X) + a • (u', y) = (u', (1 - a) • x + a • y) := by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel, one_smul]
      rw [hu]
      rfl
    rw [heq] at h1
    exact tendsto_nhds_unique h1
      (ConvexFn.tendsto_convexCl_along_segment_relint (hF.convexFn_apply u') hFu hslice y)
  · have hbot : graphFn F (u', x) = ⊥ := ConvexFn.eq_bot_of_mem_relint_convexDom hF hpr hp
    have hb1 : lscHull (graphFn F) (u', x) = ⊥ :=
      le_bot_iff.1 (hbot ▸ lscHull_le (graphFn F) (u', x))
    have hb2 : lscHull (F u') x = ⊥ := le_bot_iff.1 (hbot ▸ lscHull_le (F u') x)
    rw [convexCl_of_exists_eq_bot ⟨x, hb2⟩]
    funext y
    rw [convexClBifun_apply, convexCl_of_exists_eq_bot ⟨(u', x), hb1⟩]

/-- At a relative interior point of `dom F` the program `(cl F) u` has the same optimal value as
`F u`. A convex function and its closure have the same infimum; the content is the slice formula,
which makes `(cl F) u` a closure at all. -/
theorem infBifun_convexClBifun_eq (hF : ConvexBifun F) {u : U} (hu : u ∈ ri (convexDomBifun F)) :
    infBifun (convexClBifun F) u = infBifun F u := by
  rw [infBifun_apply, infBifun_apply, convexClBifun_apply_eq_convexCl hF hu]
  exact iInf_convexCl_eq_iInf (F u)

/-- Closing a proper convex bifunction can only enlarge its effective domain. -/
theorem convexDomBifun_subset_convexDomBifun_convexClBifun (hF : ConvexBifun F)
    (hp : ProperConvex (graphFn F)) :
    convexDomBifun F ⊆ convexDomBifun (convexClBifun F) := by
  rw [convexDomBifun_eq_image_convexDom_graphFn F,
      convexDomBifun_eq_image_convexDom_graphFn (convexClBifun F), graphFn_convexClBifun]
  refine Set.image_mono ?_
  rw [ConvexFn.convexCl_eq_lscHull hF hp]
  exact convexDom_subset_convexDom_lscHull _

/-- Closing a proper convex bifunction cannot enlarge its effective domain beyond the closure of
that domain. -/
theorem convexDomBifun_convexClBifun_subset_closure (hF : ConvexBifun F)
    (hp : ProperConvex (graphFn F)) :
    convexDomBifun (convexClBifun F) ⊆ closure (convexDomBifun F) := by
  rw [convexDomBifun_eq_image_convexDom_graphFn F,
      convexDomBifun_eq_image_convexDom_graphFn (convexClBifun F), graphFn_convexClBifun]
  refine subset_trans (Set.image_mono ?_) (image_closure_subset_closure_image continuous_fst)
  rw [ConvexFn.convexCl_eq_lscHull hF hp]
  exact convexDom_lscHull_subset_closure_convexDom _

end RelintClosure

section ImageClosed

variable {U X : Type*} [TopologicalSpace X] {F : Bifun U X}

/-- A bifunction is **image-closed** when each `F u` is a closed function. This is all the
correspondence with concave-convex functions sees of `F`. -/
def ImageClosedBifun (F : Bifun U X) : Prop := ∀ u, ClosedConvex (F u)

theorem imageClosedBifun_iff : ImageClosedBifun F ↔ ∀ u, ClosedConvex (F u) := Iff.rfl

end ImageClosed

section ImageClosedSlice

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- A closed bifunction is image-closed: a slice of a closed function is closed. The converse
fails — image-closedness says nothing about the joint behaviour in `(u, x)`. -/
theorem ClosedConvexBifun.imageClosedBifun (hF : ClosedConvexBifun F) : ImageClosedBifun F := by
  intro u
  rcases closedConvex_iff.1 (closedConvexBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedConvex_iff.2 (Or.inl (funext fun x => congrFun h (u, x)))
  · exact closedConvex_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_const.prodMk continuous_id), fun x => hne (u, x)⟩)

end ImageClosedSlice

section BifunClosureConvex

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [TopologicalSpace X] [AddCommGroup X]
  [Module ℝ X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] {F : Bifun U X}

theorem ConvexBifun.convexClBifun (hF : ConvexBifun F) :
    ConvexBifun (ConvexAnalysis.convexClBifun F) :=
  convexFn_convexCl hF

end BifunClosureConvex

section AdjointClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {F : Bifun U X}

/-- **The adjoint sees only the closure**: `(cl F)* = F*`, which is `convexConj_convexCl` on the
graph function. -/
theorem convexAdjointBifun_convexClBifun : convexAdjointBifun Bu Bx (convexClBifun F)
    = convexAdjointBifun Bu Bx F := by
  funext y v
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, convexAdjointBifun_eq_neg_convexConj_graphFn,
      graphFn_convexClBifun,
    convexConj_convexCl]

end AdjointClosure

section NegAdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

/-- Negated: `-F*` is a closed bifunction, with no hypothesis on `F`. -/
theorem closedConvexBifun_neg_convexAdjointBifun :
    ClosedConvexBifun fun y v => -(convexAdjointBifun Bu Bx F y v) :=
  closedConcave_iff_closedConvex_neg.1 closedConcave_graphFn_convexAdjointBifun

end NegAdjointClosed

section NegAdjointClosedSlice

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- Each slice of the negated adjoint is a closed convex function: the adjoint of a bifunction is
closed, read slice by slice. -/
theorem closedConvex_neg_convexAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] (F : Bifun U X) (y : Y) :
    ClosedConvex fun v => -(convexAdjointBifun Bu Bx F y v) := by
  have := isContinuousPairing_prodPairing_flip Bu Bx
  have h : ClosedConvexBifun fun y v => -(convexAdjointBifun Bu Bx F y v) :=
      closedConvexBifun_neg_convexAdjointBifun
  exact h.imageClosedBifun y

end NegAdjointClosedSlice

/-! ### The second adjoint: `F** = cl F` -/

section ConcaveAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **adjoint of a concave bifunction**: the formula of `convexAdjointBifun` with the infimum
replaced by a supremum. A concave `G` from `Y` to `V` has an adjoint from `U` to `X`. -/
noncomputable def concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) : Bifun U X :=
  fun u x => ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal))

theorem concaveAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx G u x
      = ⨆ q : Y × V, (G q.1 q.2 + ((Bx x q.1 - Bu u q.2 : ℝ) : EReal)) := rfl

/-- The reflection is onto: `(y, v) ↦ (-v, y)` hits `(v, y)` at `(y, -v)`. -/
theorem surjective_adjointSwap : Function.Surjective (adjointSwap V Y) :=
  fun w => ⟨(w.2, -w.1), by rw [adjointSwap_apply, neg_neg]⟩

/-- **The algebraic core of the biconjugation**: the concave adjoint of `F*` is the *biconjugate*
of the graph function of `F`, the two reflections cancelling by reindexing. -/
theorem concaveAdjointBifun_convexAdjointBifun_eq_convexBiconj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) u x
      = convexBiconj (prodPairing Bu Bx) (graphFn F) (u, x) := by
  rw [concaveAdjointBifun_apply, convexBiconj_apply,
    ← (surjective_adjointSwap (V := V) (Y := Y)).iSup_comp
      (fun w : V × Y => ((prodPairing Bu Bx (u, x) w : ℝ) : EReal)
        - convexConj (prodPairing Bu Bx) (graphFn F) w)]
  refine iSup_congr fun q => ?_
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, adjointSwap_apply]
  have hpair : (prodPairing Bu Bx (u, x) (-q.2, q.1) : ℝ) = Bx x q.1 - Bu u q.2 := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair]
  exact add_comm _ _

end ConcaveAdjoint

/-! ### The adjoint of the inverse, `F⁎*` -/

section LowerAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {F : Bifun U X}

/-- Rockafellar's `F⁎*`: the adjoint of the inverse of `F`, a *convex* bifunction from `V` to `Y`.

It is the inverse of the adjoint, `(F⁎* v)(y) = -(F* y)(v)`, which is how it is defined here; that
this is also the (concave) adjoint of the inverse is `lowerAdjointBifun_eq_concaveAdjointBifun`.
Working through `F⁎*` keeps the closed-case algebra of bifunctions between *convex* bifunctions and
avoids a `concaveClBifun`. -/
noncomputable def lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun V Y := fun v y => -(convexAdjointBifun Bu Bx F y v)

@[simp] theorem lowerAdjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y = -(convexAdjointBifun Bu Bx F y v) := rfl

/-- `F⁎*` is the inverse of the adjoint, by definition. -/
theorem lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    lowerAdjointBifun Bu Bx F = inverseBifun (convexAdjointBifun Bu Bx F) := rfl

/-- **The inverse commutes with the adjoint, concave orientation**: for a concave bifunction `G`
from `Y` to `V`, the convex adjoint of `G_*` at the flipped pairings is the inverse of the concave
adjoint of `G`, `(G_*)^* = (G^*)_*`. No hypothesis on `G` is needed — both sides are the same
iterated extremum, and the proof is one exchange of bound variables. -/
theorem convexAdjointBifun_flip_inverseBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) :
    convexAdjointBifun Bu.flip Bx.flip (inverseBifun G)
      = inverseBifun (concaveAdjointBifun Bu Bx G) := by
  funext x u
  have hpt : ∀ (v : V) (y : Y),
      inverseBifun G v y + ((Bu u v - Bx x y : ℝ) : EReal)
        = -(G y v + ((Bx x y - Bu u v : ℝ) : EReal)) := by
    intro v y
    have hneg : -(G y v + ((Bx x y - Bu u v : ℝ) : EReal))
        = -(G y v) + -(((Bx x y - Bu u v : ℝ) : EReal)) :=
      EReal.neg_add (.inr (EReal.coe_ne_top _))
        (.inr (EReal.coe_ne_bot _))
    have hr : (Bu u v - Bx x y : ℝ) = -(Bx x y - Bu u v) := by ring
    rw [hneg, inverseBifun_apply, hr, EReal.coe_neg]
  rw [inverseBifun_apply, concaveAdjointBifun_apply, EReal.neg_iSup, iInf_prod,
    convexAdjointBifun_apply, iInf_prod, iInf_comm]
  exact iInf_congr fun y => iInf_congr fun v => hpt v y

/-- **The inverse commutes with the adjoint, convex orientation**: `F⁎*`, defined as the inverse of
`F*`, is also the concave adjoint of the inverse `F⁎`, for the flipped pairings. This is
`convexAdjointBifun_flip_inverseBifun` read at `G = F⁎`. -/
theorem lowerAdjointBifun_eq_concaveAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) :
    lowerAdjointBifun Bu Bx F = concaveAdjointBifun Bu.flip Bx.flip (inverseBifun F) := by
  have h := convexAdjointBifun_flip_inverseBifun Bu.flip Bx.flip (inverseBifun F)
  simp only [LinearMap.flip_flip, inverseBifun_inverseBifun] at h
  rw [lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun, h, inverseBifun_inverseBifun]

/-- `F⁎*` is a convex bifunction, with no hypothesis on `F`: it is the inverse of the concave
`F*`. -/
theorem convexBifun_lowerAdjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun (lowerAdjointBifun Bu Bx F) :=
  convexBifun_inverseBifun (concaveBifun_convexAdjointBifun Bu Bx F)

/-- `F⁎*` never takes the value `-∞` when `F` is finite somewhere. -/
theorem lowerAdjointBifun_ne_bot {u₀ : U} {x₀ : X} (hF : F u₀ x₀ ≠ ⊤)
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) (y : Y) :
    lowerAdjointBifun Bu Bx F v y ≠ ⊥ := by
  rw [lowerAdjointBifun_apply]
  simpa using convexAdjointBifun_ne_top hF Bu Bx y v

end LowerAdjoint

section LowerAdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

/-- **`F⁎*` is a closed convex bifunction, with no hypothesis on `F` at all.** The adjoint `F*` is
concave-closed for any `F`, and `F⁎*` is its inverse. This is what makes a bifunction exhibited as
some `H⁎*` closed. -/
theorem closedConvexBifun_lowerAdjointBifun : ClosedConvexBifun (lowerAdjointBifun Bu Bx F) :=
  closedConvexBifun_inverseBifun closedConcave_graphFn_convexAdjointBifun

end LowerAdjointClosed

section SecondAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X}

/-- **The second adjoint is the closure**: `F** = cl F`. The two adjoints compose to the
biconjugate of the graph function, and Fenchel–Moreau turns that into its closure. Compatibility of
the product pairing follows from compatibility of `Bu` and `Bx`. -/
theorem concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun (hF : ConvexBifun F) :
    concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) = convexClBifun F := by
  funext u x
  rw [concaveAdjointBifun_convexAdjointBifun_eq_convexBiconj, convexClBifun_apply]
  exact congrFun (convexBiconj_eq_convexCl (B := prodPairing Bu Bx) hF) (u, x)

/-- Fixed-point form: `F** = F` for a closed convex bifunction. -/
theorem concaveAdjointBifun_convexAdjointBifun_eq_self (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    concaveAdjointBifun Bu Bx (convexAdjointBifun Bu Bx F) = F := by
  rw [concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF, hcl.convexClBifun_eq]

/-- **`F⁎*⁎* = cl F`**, the biadjoint identity in the `F⁎*` packaging: the inverse commutes with the
adjoint, and the inverse is involutory, so this is `F** = cl F`. -/
theorem lowerAdjointBifun_lowerAdjointBifun_eq_convexClBifun (hF : ConvexBifun F) :
    lowerAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = convexClBifun F := by
  rw [lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun,
    lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun, convexAdjointBifun_flip_inverseBifun,
    inverseBifun_inverseBifun, concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF]

/-- **The biadjoint identity `(F⁎*)^* = F⁎`** for a closed convex bifunction: the adjoint of `F⁎*`
at the flipped pairings is the inverse of `F`. It is `convexAdjointBifun_flip_inverseBifun` followed
by involutivity of the adjoint on closed convex bifunctions. -/
theorem convexAdjointBifun_flip_lowerAdjointBifun (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    convexAdjointBifun Bu.flip Bx.flip (lowerAdjointBifun Bu Bx F) = inverseBifun F := by
  rw [lowerAdjointBifun_eq_inverseBifun_convexAdjointBifun, convexAdjointBifun_flip_inverseBifun,
    concaveAdjointBifun_convexAdjointBifun_eq_self hF hcl]

/-- The adjoint of a *closed proper* convex bifunction is finite somewhere. This is properness of
a conjugate, read through `convexAdjointBifun_eq_neg_convexConj_graphFn`: `F*` is somewhere `> -∞`
exactly when `(graph F)*` is somewhere `< +∞`. -/
theorem exists_convexAdjointBifun_ne_bot (hF : ClosedProperConvexFn (graphFn F)) :
    ∃ (y : Y) (v : V), convexAdjointBifun Bu Bx F y v ≠ ⊥ := by
  obtain ⟨q, hq⟩ := (properConvex_convexConj (B := prodPairing Bu Bx) hF).convexDom_nonempty
  refine ⟨q.2, -q.1, ?_⟩
  rw [convexAdjointBifun_eq_neg_convexConj_graphFn, neg_neg]
  simpa using hq.ne

/-- **The properness clause in full**: for a closed convex `F`, the adjoint `F*` is a proper
*concave* bifunction exactly when `F` is proper. This is properness of a conjugate read through the
onto reflection `(y, v) ↦ (-v, y)`; as there, closedness is used only for the direction "`F` proper
⇒ `F*` proper". -/
theorem properConcave_graphFn_convexAdjointBifun_iff (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) :
    ProperConcave (graphFn (convexAdjointBifun Bu Bx F)) ↔ ProperConvex (graphFn F) := by
  rw [properConcave_iff_properConvex_neg, neg_graphFn_convexAdjointBifun,
    properConvex_compLin_of_surjective surjective_adjointSwap,
    properConvex_convexConj_iff (B := prodPairing Bu Bx) hF hcl]

end SecondAdjoint

section LowerAdjointProper

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {F : Bifun U X}

/-- `F⁎*` is somewhere `< ⊤`, for a closed proper convex `F`: that is properness of `F*`
(`exists_convexAdjointBifun_ne_bot`) read through the inverse. -/
theorem exists_lowerAdjointBifun_ne_top (hF : ClosedProperConvexFn (graphFn F))
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] : ∃ (v : V) (y : Y), lowerAdjointBifun Bu Bx F v y ≠ ⊤ := by
  obtain ⟨y, v, hyv⟩ := exists_convexAdjointBifun_ne_bot (Bu := Bu) (Bx := Bx) (F := F) hF
  exact ⟨v, y, by rw [lowerAdjointBifun_apply]; simpa using hyv⟩

end LowerAdjointProper

/-! ### The dual objective -/

section Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- The dual objective, unfolded: `(F* 0)(v) = ⨅ u (⟨u, v⟩ + inf F u)`. -/
theorem convexAdjointBifun_zero_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) :
    convexAdjointBifun Bu Bx F 0 v = ⨅ u, (((Bu u v : ℝ) : EReal) + infBifun F u) := by
  rw [convexAdjointBifun_apply, iInf_prod]
  refine iInf_congr fun u => ?_
  have hzero : ∀ x : X, (Bu u v - Bx x 0 : ℝ) = Bu u v := fun x => by
    rw [map_zero, sub_zero]
  simp only [hzero]
  rw [infBifun_apply, add_comm, EReal.iInf_add_coe]

/-- The dual objective is the *concave* conjugate of the concave function `-inf F`. -/
theorem convexAdjointBifun_zero_eq_concaveConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) :
    convexAdjointBifun Bu Bx F 0 = concaveConj Bu (fun u => -(infBifun F u)) := by
  funext v
  rw [convexAdjointBifun_zero_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- **Weak duality**: every value of the dual objective is at most the optimal value of `(P)`,
with no hypothesis at all. -/
theorem convexAdjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (v : V) : convexAdjointBifun Bu Bx F 0 v ≤ infBifun F 0 := by
  rw [convexAdjointBifun_zero_apply]
  exact iInf_add_infBifun_le Bu F v

/-- The half that holds without normality: the Kuhn–Tucker vectors of `(P)` are the points at
which the dual objective attains the optimal value of `(P)`. -/
theorem mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    v ∈ KuhnTucker Bu F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      convexAdjointBifun Bu Bx F 0 v = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, convexAdjointBifun_zero_apply]

/-- Weak duality in the form normality uses: the supremum of the dual objective never exceeds the
optimal value of `(P)`. -/
theorem iSup_convexAdjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : (⨆ v, convexAdjointBifun Bu Bx F 0 v) ≤ infBifun F 0 :=
  iSup_le (convexAdjointBifun_zero_le Bu Bx F)

end Dual

/-! ### Closing a strongly consistent program changes nothing -/

section ClosureInvariance

open Filter Topology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

/-- **Domain clause**: closing a proper convex bifunction leaves the relative interior of its
effective domain alone. `dom (cl F)` is sandwiched between `dom F` and `cl (dom F)`, and such a
sandwich has the same relative interior. -/
theorem relint_convexDomBifun_convexClBifun (hF : ConvexBifun F) (hp : ProperConvex (graphFn F)) :
    ri (convexDomBifun (convexClBifun F)) = ri (convexDomBifun F) := by
  have hconv : Convex ℝ (convexDomBifun F) := convex_convexDomBifun hF
  have hconvcl : Convex ℝ (convexDomBifun (convexClBifun F)) :=
      convex_convexDomBifun (ConvexBifun.convexClBifun hF)
  refine (Convex.closure_eq_iff_relint_eq hconvcl hconv).1 ?_
  exact Convex.closure_eq_of_relint_subset_of_subset_closure hconv
    (intrinsicInterior_subset.trans (convexDomBifun_subset_convexDomBifun_convexClBifun hF hp))
    (convexDomBifun_convexClBifun_subset_closure hF hp)

/-- `(cl P)` is strongly consistent whenever `(P)` is. -/
theorem stronglyConsistent_convexClBifun (hF : ConvexBifun F) (hp : ProperConvex (graphFn F))
    (hs : StronglyConsistent F) : StronglyConsistent (convexClBifun F) := by
  rw [StronglyConsistent, relint_convexDomBifun_convexClBifun hF hp]
  exact hs

/-- The objective of `(cl P)` is the closure of that of `(P)`: the slice formula at the origin. -/
theorem convexClBifun_zero_eq_convexCl (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    convexClBifun F 0 = convexCl (F 0) :=
  convexClBifun_apply_eq_convexCl hF hs

/-- `(P)` and `(cl P)` have the same optimal value. -/
theorem infBifun_convexClBifun_zero_eq (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    infBifun (convexClBifun F) 0 = infBifun F 0 :=
  infBifun_convexClBifun_eq hF hs

/-- Every optimal solution to `(P)` is one to `(cl P)`. The inclusion is strict in general —
closing can create new minimisers. -/
theorem argmin_subset_argmin_convexClBifun (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    argmin (F 0) ⊆ argmin (convexClBifun F 0) := by
  rw [convexClBifun_zero_eq_convexCl hF hs]
  intro x hx
  rw [mem_argmin_iff_le_iInf] at hx ⊢
  rw [iInf_convexCl_eq_iInf]
  exact le_trans (convexCl_le _ x) hx

/-- The perturbation functions of `(P)` and `(cl P)` agree on a neighbourhood of the origin.

The slice formula supplies agreement only on `ri (dom F)`, a *relative* neighbourhood; the two are
reconciled by the points outside `aff (dom F)`, where both perturbation functions are `+∞`. Since
`ri (dom F)` is relatively open and `dom (cl F) ⊆ cl (dom F) ⊆ aff (dom F)`, a small enough ball
around the origin meets no other kind of point. -/
theorem eventually_infBifun_convexClBifun_eq (hF : ConvexBifun F) (hp : ProperConvex (graphFn F))
    (hs : StronglyConsistent F) :
    ∀ᶠ u in 𝓝 (0 : U), infBifun (convexClBifun F) u = infBifun F u := by
  have hconv : Convex ℝ (convexDomBifun F) := convex_convexDomBifun hF
  have h0 : (0 : U) ∈ ri (ri (convexDomBifun F)) := by
    rw [Convex.relint_relint hconv]
    exact hs
  obtain ⟨-, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 h0
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε, hε, fun {u} hu => ?_⟩
  by_cases haff : u ∈ affineSpan ℝ (convexDomBifun F)
  · refine infBifun_convexClBifun_eq hF (hball u ?_ hu)
    rwa [Convex.affineSpan_relint hconv]
  · have hcl : u ∉ convexDomBifun (convexClBifun F) := fun hmem =>
      haff (closure_subset_affineSpan _ (convexDomBifun_convexClBifun_subset_closure hF hp hmem))
    have hF0 : u ∉ convexDomBifun F := fun hmem => haff (subset_affineSpan ℝ _ hmem)
    rw [infBifun_eq_top_of_notMem_convexDomBifun hcl, infBifun_eq_top_of_notMem_convexDomBifun hF0]

end ClosureInvariance

section ClosureKuhnTucker

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {F : Bifun U X}

/-- `(P)` and `(cl P)` have the same Kuhn–Tucker vectors. Such a vector is a point where the dual
objective attains the optimal value, the adjoint does not see the closure, and strong consistency
equates the two optimal values. -/
theorem kuhnTucker_convexClBifun_eq {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx] (hF : ConvexBifun F)
    (hs : StronglyConsistent F) : KuhnTucker Bu (convexClBifun F) = KuhnTucker Bu F := by
  have hval : infBifun (convexClBifun F) 0 = infBifun F 0 := infBifun_convexClBifun_eq hF hs
  ext v
  rw [mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx),
    mem_kuhnTucker_iff_convexAdjointBifun_zero_eq (Bx := Bx),
        convexAdjointBifun_convexClBifun, hval]

end ClosureKuhnTucker

end ConvexAnalysis
