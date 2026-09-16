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

* `adjointBifun Bu Bx F`, `concaveAdjointBifun Bu Bx G` — the adjoint of a convex bifunction, and
  of a concave one (the same formula with a supremum).
* `ConcaveBifun`, `ClosedBifun`, `ImageClosedBifun` — the graph function is concave, it is closed,
  the slices `F u` are each closed; `clBifun F` is the closure of the graph function.

## Main results

* `adjointBifun_eq_neg_conj_graphFn` — the computation above; `concaveFn_graphFn_adjointBifun`,
  `closedConcaveFn_graphFn_adjointBifun`, `concaveAdjointBifun_adjointBifun_eq_clBifun`,
  `properConcave_graphFn_adjointBifun_iff` — `F*` is closed concave, `F** = cl F`, and `F*` is
  proper exactly when `F` is ([rockafellar1970convex] Theorem 30.1).
* `adjointBifun_zero_eq_concaveConj` — the dual objective as a concave conjugate;
  `adjointBifun_zero_le` — weak duality.
* `mem_kuhnTucker_iff_adjointBifun_zero_eq` — the Kuhn–Tucker vectors are the points where the dual
  objective attains the optimal value, with no normality needed.
* `clBifun_apply_eq_clFn`, `infBifun_clBifun_eq` and the two `domBifun` inclusions — the closure of
  a bifunction, slice by slice ([rockafellar1970convex] Theorem 29.4).

## Implementation notes

The sign flip is carried in the argument rather than in a reflected pairing: `⟨u, -v⟩ + ⟨x, y⟩` is
read as the pairing of `(u, x)` with `(-v, y)`, so `F*` is `conj` at a reflected point and `conj`'s
own lemmas apply verbatim. The two real terms are grouped inside one coercion, so no `∞ - ∞` can
arise, and the dual objective uses the *concave* conjugate, since `g* ≠ -(-g)*`. The closedness of
`F*` asks for `IsContinuousPairing (prodPairing Bu Bx).flip` rather than the un-flipped class:
`closedFn_conj` needs continuity on the side the conjugate lives on, and the un-flipped form would
demand a topology on `U × X` that this development never supplies.

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
noncomputable def adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : Bifun Y V :=
  fun y v => ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal))

theorem adjointBifun_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (y : Y) (v : V) :
    adjointBifun Bu Bx F y v = ⨅ p : U × X, (F p.1 p.2 + ((Bu p.1 v - Bx p.2 y : ℝ) : EReal)) :=
  rfl

/-- **The computation everything here rests on**: the adjoint is the conjugate of the graph
function, negated and evaluated at a reflected point. -/
theorem adjointBifun_eq_neg_conj_graphFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    adjointBifun Bu Bx F y v = -(conj (prodPairing Bu Bx) (graphFn F) (-v, y)) := by
  rw [adjointBifun_apply, conj_apply, EReal.neg_iSup]
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

/-- A bifunction is **concave** when its graph function is. -/
def ConcaveBifun (G : Bifun U X) : Prop := ConcaveFn (graphFn G)

theorem concaveBifun_iff {G : Bifun U X} : ConcaveBifun G ↔ ConcaveFn (graphFn G) := Iff.rfl

/-- The reflection `(y, v) ↦ (-v, y)` that turns the adjoint into a conjugate. -/
def adjointSwap (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y] :
    (Y × V) →ₗ[ℝ] (V × Y) :=
  LinearMap.prod (-LinearMap.snd ℝ Y V) (LinearMap.fst ℝ Y V)

@[simp] theorem adjointSwap_apply (V Y : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup Y]
    [Module ℝ Y] (q : Y × V) : adjointSwap V Y q = (-q.2, q.1) := rfl

/-- The graph function of the adjoint is minus a conjugate composed with a linear reflection. -/
theorem graphFn_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : graphFn (adjointBifun Bu Bx F)
      = fun q => -(compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) q) :=
  funext fun q => adjointBifun_eq_neg_conj_graphFn Bu Bx F q.1 q.2

/-- The adjoint of *any* bifunction is concave. No convexity, properness or closedness of `F` is
needed. -/
theorem concaveFn_graphFn_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveFn (graphFn (adjointBifun Bu Bx F)) := by
  rw [concaveFn_iff_convexFn_neg]
  have h : (fun q => -(graphFn (adjointBifun Bu Bx F) q))
      = compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_adjointBifun, neg_neg]
  rw [h]
  exact convexFn_compLin _ (convexFn_conj _ _)

/-- The same, packaged as a statement about bifunctions. -/
theorem concaveBifun_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConcaveBifun (adjointBifun Bu Bx F) :=
  concaveFn_graphFn_adjointBifun Bu Bx F

/-- The same negated: `-F*` is a *convex* bifunction. This is the shape in which the concave
normality criteria consume the adjoint. -/
theorem convexBifun_neg_adjointBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : ConvexBifun fun y v => -(adjointBifun Bu Bx F y v) :=
  concaveFn_iff_convexFn_neg.1 (concaveFn_graphFn_adjointBifun Bu Bx F)

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
theorem closedConcaveFn_graphFn_adjointBifun :
    ClosedConcaveFn (graphFn (adjointBifun Bu Bx F)) := by
  rw [closedConcaveFn_iff]
  have h : (fun q => -(graphFn (adjointBifun Bu Bx F) q))
      = compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_adjointBifun, neg_neg]
  rw [h]
  exact closedFn_compLin closedFn_conj continuous_adjointSwap

end ClosedTopology

/-! ### The closure of a bifunction -/

section BifunClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {F : Bifun U X}

/-- The **closure of a bifunction**: the bifunction whose graph function is the closure of that of
`F`. Two applications of the adjoint return exactly this. -/
noncomputable def clBifun (F : Bifun U X) : Bifun U X := fun u x => clFn (graphFn F) (u, x)

theorem clBifun_apply (F : Bifun U X) (u : U) (x : X) :
    clBifun F u x = clFn (graphFn F) (u, x) := rfl

@[simp] theorem graphFn_clBifun (F : Bifun U X) : graphFn (clBifun F) = clFn (graphFn F) := rfl

/-- A bifunction is **closed** when its graph function is. -/
def ClosedBifun (F : Bifun U X) : Prop := ClosedFn (graphFn F)

theorem closedBifun_iff : ClosedBifun F ↔ ClosedFn (graphFn F) := Iff.rfl

theorem clBifun_le (F : Bifun U X) : clBifun F ≤ F := fun u x => clFn_le (graphFn F) (u, x)

theorem ClosedBifun.clBifun_eq (hF : ClosedBifun F) : clBifun F = F :=
  funext fun u => funext fun x => congrFun hF (u, x)

theorem closedBifun_iff_clBifun_eq : ClosedBifun F ↔ clBifun F = F := by
  refine ⟨fun hF => hF.clBifun_eq, fun hF => ?_⟩
  change clFn (graphFn F) = graphFn F
  exact funext fun p => congrFun (congrFun hF p.1) p.2

end BifunClosure

section BifunClosureClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

theorem closedBifun_clBifun (F : Bifun U X) : ClosedBifun (clBifun F) :=
  closedFn_clFn (graphFn F)

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
theorem domBifun_eq_image_dom_graphFn (F : Bifun U X) :
    domBifun F = LinearMap.fst ℝ U X '' dom (graphFn F) := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(u, x), mem_dom.2 (lt_of_le_of_ne le_top hx), rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, (mem_dom.1 hp).ne⟩

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
theorem clBifun_apply_eq_clFn (hF : ConvexBifun F) {u : U} (hu : u ∈ ri (domBifun F)) :
    clBifun F u = clFn (F u) := by
  have hconv : Convex ℝ (dom (graphFn F)) := ConvexFn.convex_dom hF
  have himg : u ∈ LinearMap.fst ℝ U X '' ri (dom (graphFn F)) := by
    rw [← Convex.relint_image hconv, ← domBifun_eq_image_dom_graphFn]
    exact hu
  obtain ⟨⟨u', x⟩, hp, hpu⟩ := himg
  simp only [LinearMap.fst_apply] at hpu
  subst hpu
  have hslice : x ∈ ri (dom (F u')) := mem_relint_slice hconv hp
  have hxdom : x ∈ dom (F u') := intrinsicInterior_subset hslice
  by_cases hpr : Proper (graphFn F)
  · have hFu : Proper (F u') := ⟨⟨x, hxdom⟩, fun y => hpr.ne_bot (u', y)⟩
    funext y
    have h1 : Tendsto (fun a : ℝ => graphFn F ((1 - a) • ((u', x) : U × X) + a • (u', y)))
        (𝓝[<] (1 : ℝ)) (𝓝 (clFn (graphFn F) (u', y))) :=
      ConvexFn.tendsto_clFn_along_segment_relint hF hpr hp (u', y)
    have heq : (fun a : ℝ => graphFn F ((1 - a) • ((u', x) : U × X) + a • (u', y)))
        = fun a : ℝ => F u' ((1 - a) • x + a • y) := by
      funext a
      have hu : (1 - a) • ((u', x) : U × X) + a • (u', y) = (u', (1 - a) • x + a • y) := by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, sub_add_cancel, one_smul]
      rw [hu]
      rfl
    rw [heq] at h1
    exact tendsto_nhds_unique h1
      (ConvexFn.tendsto_clFn_along_segment_relint (hF.convexFn_apply u') hFu hslice y)
  · have hbot : graphFn F (u', x) = ⊥ := ConvexFn.eq_bot_of_mem_relint_dom hF hpr hp
    have hb1 : lscHull (graphFn F) (u', x) = ⊥ :=
      le_bot_iff.1 (hbot ▸ lscHull_le (graphFn F) (u', x))
    have hb2 : lscHull (F u') x = ⊥ := le_bot_iff.1 (hbot ▸ lscHull_le (F u') x)
    rw [clFn_of_exists_eq_bot ⟨x, hb2⟩]
    funext y
    rw [clBifun_apply, clFn_of_exists_eq_bot ⟨(u', x), hb1⟩]

/-- At a relative interior point of `dom F` the program `(cl F) u` has the same optimal value as
`F u`. A convex function and its closure have the same infimum; the content is the slice formula,
which makes `(cl F) u` a closure at all. -/
theorem infBifun_clBifun_eq (hF : ConvexBifun F) {u : U} (hu : u ∈ ri (domBifun F)) :
    infBifun (clBifun F) u = infBifun F u := by
  rw [infBifun_apply, infBifun_apply, clBifun_apply_eq_clFn hF hu]
  exact iInf_clFn_eq_iInf (F u)

/-- Closing a proper convex bifunction can only enlarge its effective domain. -/
theorem domBifun_subset_domBifun_clBifun (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    domBifun F ⊆ domBifun (clBifun F) := by
  rw [domBifun_eq_image_dom_graphFn F, domBifun_eq_image_dom_graphFn (clBifun F), graphFn_clBifun]
  refine Set.image_mono ?_
  rw [ConvexFn.clFn_eq_lscHull hF hp]
  exact dom_subset_dom_lscHull _

/-- Closing a proper convex bifunction cannot enlarge its effective domain beyond the closure of
that domain. -/
theorem domBifun_clBifun_subset_closure (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    domBifun (clBifun F) ⊆ closure (domBifun F) := by
  rw [domBifun_eq_image_dom_graphFn F, domBifun_eq_image_dom_graphFn (clBifun F), graphFn_clBifun]
  refine subset_trans (Set.image_mono ?_) (image_closure_subset_closure_image continuous_fst)
  rw [ConvexFn.clFn_eq_lscHull hF hp]
  exact dom_lscHull_subset_closure_dom _

end RelintClosure

section ImageClosed

variable {U X : Type*} [TopologicalSpace X] {F : Bifun U X}

/-- A bifunction is **image-closed** when each `F u` is a closed function. This is all the
correspondence with concave-convex functions sees of `F`. -/
def ImageClosedBifun (F : Bifun U X) : Prop := ∀ u, ClosedFn (F u)

theorem imageClosedBifun_iff : ImageClosedBifun F ↔ ∀ u, ClosedFn (F u) := Iff.rfl

end ImageClosed

section ImageClosedSlice

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {F : Bifun U X}

/-- A closed bifunction is image-closed: a slice of a closed function is closed. The converse
fails — image-closedness says nothing about the joint behaviour in `(u, x)`. -/
theorem ClosedBifun.imageClosedBifun (hF : ClosedBifun F) : ImageClosedBifun F := by
  intro u
  rcases closedFn_iff.1 (closedBifun_iff.1 hF) with h | ⟨hlsc, hne⟩
  · exact closedFn_iff.2 (Or.inl (funext fun x => congrFun h (u, x)))
  · exact closedFn_iff.2 (Or.inr ⟨lowerSemicontinuous_comp hlsc
      (continuous_const.prodMk continuous_id), fun x => hne (u, x)⟩)

end ImageClosedSlice

section BifunClosureConvex

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [TopologicalSpace X] [AddCommGroup X]
  [Module ℝ X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] {F : Bifun U X}

theorem ConvexBifun.clBifun (hF : ConvexBifun F) : ConvexBifun (ConvexAnalysis.clBifun F) :=
  convexFn_clFn hF

end BifunClosureConvex

section AdjointClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing Bx] {F : Bifun U X}

/-- **The adjoint sees only the closure**: `(cl F)* = F*`, which is `conj_clFn` on the graph
function. -/
theorem adjointBifun_clBifun : adjointBifun Bu Bx (clBifun F) = adjointBifun Bu Bx F := by
  funext y v
  rw [adjointBifun_eq_neg_conj_graphFn, adjointBifun_eq_neg_conj_graphFn, graphFn_clBifun,
    conj_clFn]

end AdjointClosure

section NegAdjointClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsContinuousPairing (prodPairing Bu Bx).flip] {F : Bifun U X}

/-- Negated: `-F*` is a closed bifunction, with no hypothesis on `F`. -/
theorem closedBifun_neg_adjointBifun :
    ClosedBifun fun y v => -(adjointBifun Bu Bx F y v) :=
  closedConcaveFn_iff.1 closedConcaveFn_graphFn_adjointBifun

end NegAdjointClosed

/-! ### The second adjoint: `F** = cl F` -/

section ConcaveAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **adjoint of a concave bifunction**: the formula of `adjointBifun` with the infimum replaced
by a supremum. A concave `G` from `Y` to `V` has an adjoint from `U` to `X`. -/
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
theorem concaveAdjointBifun_adjointBifun_eq_biconj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (u : U) (x : X) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) u x
      = biconj (prodPairing Bu Bx) (graphFn F) (u, x) := by
  rw [concaveAdjointBifun_apply, biconj_apply,
    ← (surjective_adjointSwap (V := V) (Y := Y)).iSup_comp
      (fun w : V × Y => ((prodPairing Bu Bx (u, x) w : ℝ) : EReal)
        - conj (prodPairing Bu Bx) (graphFn F) w)]
  refine iSup_congr fun q => ?_
  rw [adjointBifun_eq_neg_conj_graphFn, adjointSwap_apply]
  have hpair : (prodPairing Bu Bx (u, x) (-q.2, q.1) : ℝ) = Bx x q.1 - Bu u q.2 := by
    rw [prodPairing_apply, map_neg]
    ring
  rw [hpair]
  exact add_comm _ _

end ConcaveAdjoint

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
theorem concaveAdjointBifun_adjointBifun_eq_clBifun (hF : ConvexBifun F) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) = clBifun F := by
  funext u x
  rw [concaveAdjointBifun_adjointBifun_eq_biconj, clBifun_apply]
  exact congrFun (biconj_eq_clFn (B := prodPairing Bu Bx) hF) (u, x)

/-- Fixed-point form: `F** = F` for a closed convex bifunction. -/
theorem concaveAdjointBifun_adjointBifun_eq_self (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) = F := by
  rw [concaveAdjointBifun_adjointBifun_eq_clBifun hF, hcl.clBifun_eq]

/-- The adjoint of a *closed proper* convex bifunction is finite somewhere. This is properness of
a conjugate, read through `adjointBifun_eq_neg_conj_graphFn`: `F*` is somewhere `> -∞` exactly when
`(graph F)*` is somewhere `< +∞`. -/
theorem exists_adjointBifun_ne_bot (hF : ClosedProperConvexFn (graphFn F)) :
    ∃ (y : Y) (v : V), adjointBifun Bu Bx F y v ≠ ⊥ := by
  obtain ⟨q, hq⟩ := (proper_conj (B := prodPairing Bu Bx) hF).dom_nonempty
  refine ⟨q.2, -q.1, ?_⟩
  rw [adjointBifun_eq_neg_conj_graphFn, neg_neg]
  simpa using hq.ne

/-- **The properness clause in full**: for a closed convex `F`, the adjoint `F*` is a proper
*concave* bifunction exactly when `F` is proper. This is properness of a conjugate read through the
onto reflection `(y, v) ↦ (-v, y)`; as there, closedness is used only for the direction "`F` proper
⇒ `F*` proper". -/
theorem properConcave_graphFn_adjointBifun_iff (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ProperConcave (graphFn (adjointBifun Bu Bx F)) ↔ Proper (graphFn F) := by
  have hg : (fun q : Y × V => -(graphFn (adjointBifun Bu Bx F) q))
      = compLin (conj (prodPairing Bu Bx) (graphFn F)) (adjointSwap V Y) := by
    funext q
    rw [graphFn_adjointBifun, neg_neg]
  rw [properConcave_iff_proper_neg, hg, proper_compLin_of_surjective surjective_adjointSwap,
    proper_conj_iff (B := prodPairing Bu Bx) hF hcl]

end SecondAdjoint

/-! ### The dual objective -/

section Dual

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- The dual objective, unfolded: `(F* 0)(v) = ⨅ u (⟨u, v⟩ + inf F u)`. -/
theorem adjointBifun_zero_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (v : V) :
    adjointBifun Bu Bx F 0 v = ⨅ u, (((Bu u v : ℝ) : EReal) + infBifun F u) := by
  rw [adjointBifun_apply, iInf_prod]
  refine iInf_congr fun u => ?_
  have hzero : ∀ x : X, (Bu u v - Bx x 0 : ℝ) = Bu u v := fun x => by
    rw [map_zero, sub_zero]
  simp only [hzero]
  rw [infBifun_apply, add_comm, EReal.iInf_add_coe]

/-- The dual objective is the *concave* conjugate of the concave function `-inf F`. -/
theorem adjointBifun_zero_eq_concaveConj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) :
    adjointBifun Bu Bx F 0 = concaveConj Bu (fun u => -(infBifun F u)) := by
  funext v
  rw [adjointBifun_zero_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- **Weak duality**: every value of the dual objective is at most the optimal value of `(P)`,
with no hypothesis at all. -/
theorem adjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X)
    (v : V) : adjointBifun Bu Bx F 0 v ≤ infBifun F 0 := by
  rw [adjointBifun_zero_apply]
  exact iInf_add_infBifun_le Bu F v

/-- The half that holds without normality: the Kuhn–Tucker vectors of `(P)` are the points at
which the dual objective attains the optimal value of `(P)`. -/
theorem mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    v ∈ KuhnTucker Bu F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      adjointBifun Bu Bx F 0 v = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, adjointBifun_zero_apply]

/-- Weak duality in the form normality uses: the supremum of the dual objective never exceeds the
optimal value of `(P)`. -/
theorem iSup_adjointBifun_zero_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) : (⨆ v, adjointBifun Bu Bx F 0 v) ≤ infBifun F 0 :=
  iSup_le (adjointBifun_zero_le Bu Bx F)

end Dual

/-! ### Closing a strongly consistent program changes nothing -/

section ClosureInvariance

open Filter Topology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

/-- **Domain clause**: closing a proper convex bifunction leaves the relative interior of its
effective domain alone. `dom (cl F)` is sandwiched between `dom F` and `cl (dom F)`, and such a
sandwich has the same relative interior. -/
theorem relint_domBifun_clBifun (hF : ConvexBifun F) (hp : Proper (graphFn F)) :
    ri (domBifun (clBifun F)) = ri (domBifun F) := by
  have hconv : Convex ℝ (domBifun F) := convex_domBifun hF
  have hconvcl : Convex ℝ (domBifun (clBifun F)) := convex_domBifun (ConvexBifun.clBifun hF)
  refine (Convex.closure_eq_iff_relint_eq hconvcl hconv).1 ?_
  exact Convex.closure_eq_of_relint_subset_of_subset_closure hconv
    (intrinsicInterior_subset.trans (domBifun_subset_domBifun_clBifun hF hp))
    (domBifun_clBifun_subset_closure hF hp)

/-- `(cl P)` is strongly consistent whenever `(P)` is. -/
theorem stronglyConsistent_clBifun (hF : ConvexBifun F) (hp : Proper (graphFn F))
    (hs : StronglyConsistent F) : StronglyConsistent (clBifun F) := by
  rw [StronglyConsistent, relint_domBifun_clBifun hF hp]
  exact hs

/-- The objective of `(cl P)` is the closure of that of `(P)`: the slice formula at the origin. -/
theorem clBifun_zero_eq_clFn (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    clBifun F 0 = clFn (F 0) :=
  clBifun_apply_eq_clFn hF hs

/-- `(P)` and `(cl P)` have the same optimal value. -/
theorem infBifun_clBifun_zero_eq (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    infBifun (clBifun F) 0 = infBifun F 0 :=
  infBifun_clBifun_eq hF hs

/-- Every optimal solution to `(P)` is one to `(cl P)`. The inclusion is strict in general —
closing can create new minimisers. -/
theorem argmin_subset_argmin_clBifun (hF : ConvexBifun F) (hs : StronglyConsistent F) :
    argmin (F 0) ⊆ argmin (clBifun F 0) := by
  rw [clBifun_zero_eq_clFn hF hs]
  intro x hx
  rw [mem_argmin_iff_le_iInf] at hx ⊢
  rw [iInf_clFn_eq_iInf]
  exact le_trans (clFn_le _ x) hx

/-- The perturbation functions of `(P)` and `(cl P)` agree on a neighbourhood of the origin.

The slice formula supplies agreement only on `ri (dom F)`, a *relative* neighbourhood; the two are
reconciled by the points outside `aff (dom F)`, where both perturbation functions are `+∞`. Since
`ri (dom F)` is relatively open and `dom (cl F) ⊆ cl (dom F) ⊆ aff (dom F)`, a small enough ball
around the origin meets no other kind of point. -/
theorem eventually_infBifun_clBifun_eq (hF : ConvexBifun F) (hp : Proper (graphFn F))
    (hs : StronglyConsistent F) :
    ∀ᶠ u in 𝓝 (0 : U), infBifun (clBifun F) u = infBifun F u := by
  have hconv : Convex ℝ (domBifun F) := convex_domBifun hF
  have h0 : (0 : U) ∈ ri (ri (domBifun F)) := by
    rw [Convex.relint_relint hconv]
    exact hs
  obtain ⟨-, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 h0
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε, hε, fun {u} hu => ?_⟩
  by_cases haff : u ∈ affineSpan ℝ (domBifun F)
  · refine infBifun_clBifun_eq hF (hball u ?_ hu)
    rwa [Convex.affineSpan_relint hconv]
  · have hcl : u ∉ domBifun (clBifun F) := fun hmem =>
      haff (closure_subset_affineSpan _ (domBifun_clBifun_subset_closure hF hp hmem))
    have hF0 : u ∉ domBifun F := fun hmem => haff (subset_affineSpan ℝ _ hmem)
    rw [infBifun_eq_top_of_notMem_domBifun hcl, infBifun_eq_top_of_notMem_domBifun hF0]

end ClosureInvariance

section ClosureKuhnTucker

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsContinuousPairing Bu] {F : Bifun U X}

/-- `(P)` and `(cl P)` have the same Kuhn–Tucker vectors. Such a vector is a point where the dual
objective attains the optimal value, the adjoint does not see the closure, and strong consistency
equates the two optimal values. -/
theorem kuhnTucker_clBifun_eq {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx] (hF : ConvexBifun F)
    (hs : StronglyConsistent F) : KuhnTucker Bu (clBifun F) = KuhnTucker Bu F := by
  have hval : infBifun (clBifun F) 0 = infBifun F 0 := infBifun_clBifun_eq hF hs
  ext v
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx),
    mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx), adjointBifun_clBifun, hval]

end ClosureKuhnTucker

end ConvexAnalysis
