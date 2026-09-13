import Numlib.Analysis.Convex.Optimization.Adjoint
import Numlib.Analysis.Convex.Optimization.Minimum

/-!
# Normality of a dual pair of convex programs

A convex program `(P)` is **normal** when its perturbation function is closed at the origin,

`(cl (inf F))(0) = (inf F)(0)`,

and this one condition turns out to be equivalent to the absence of a duality gap and to normality
of the dual `(P*)`. Ten sufficient conditions for it are collected below, and under normality the
Kuhn–Tucker vectors of `(P)` are precisely the optimal solutions of `(P*)`. Everything rests on
Fenchel–Moreau at the origin, `(cl f)(0) = ⨆ y, ⨅ x, (⟨x, y⟩ + f x)`: with `f = inf F` the inner
infimum is the dual objective `(F* 0)(y)`, so `(cl (inf F))(0) = sup F* 0`.

## Main definitions

* `Normal F` — normality of the convex program associated with `F`.
* `supBifun G`, `domConcaveBifun G`, `ConcaveConsistent G`, `ConcaveStronglyConsistent G`,
  `ConcaveNormal G`, `ConcaveKuhnTucker` — the concave counterparts of `infBifun`, `domBifun`,
  `Consistent`, `StronglyConsistent`, `Normal` and `KuhnTucker`, each the convex notion at `-G`.

## Main results

* `clFn_infBifun_zero_eq_iSup_adjointBifun`, `clConcave_supBifun_adjointBifun_zero_eq` — each
  optimal value is the other program's perturbation function closed at the origin;
  `iSup_adjointBifun_eq_bot_iff` and companions — inconsistency of one program as unboundedness of
  the other; `liminf_infBifun_eq_iSup_adjointBifun` — the same values as a `liminf`.
* `normal_iff_iSup_adjointBifun_eq`, `concaveNormal_adjointBifun_iff`,
  `normal_iff_concaveNormal_adjointBifun` — normality, absence of a duality gap and normality of
  the dual are one condition (Theorem 30.3 in [^1]).
* `StronglyConsistent.normal`, `normal_of_concaveStronglyConsistent_adjointBifun`,
  `normal_of_kuhnTucker_nonempty`, `normal_of_exists_setOf_le` and companions — ten sufficient
  conditions for normality (Theorem 30.4 in [^1], clauses (a)–(j)).
* `mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup`, `kuhnTucker_eq_setOf_isMax` — the Kuhn–Tucker
  vectors are exactly the dual optimal solutions (Theorem 30.5 in [^1]), with
  `mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin` for the dual assertion;
  `exists_infBifun_eq_of_concaveStronglyConsistent` — attainment of the primal infimum.

## Implementation notes

The first formula for `(cl (inf F))(0)` needs only convexity of `F`, not closedness: it is
Fenchel–Moreau for `inf F`, and the adjoint does not distinguish `F` from `cl F`. So normality and
the absence of a duality gap agree for every convex bifunction, and only normality of the dual
needs `ClosedBifun F`. A Kuhn–Tucker vector is made to imply normality through weak duality rather
than through subgradients, so needs no finite dimension.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §30.
-/

open Filter Topology

namespace ConvexAnalysis

/-! ### The closure of a convex function at the origin -/

section ClosureAtZero

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- `EReal.neg_coe_sub` with the difference read as a sum. -/
private theorem neg_coe_sub_eq {c : ℝ} {w : EReal} :
    -(((c : ℝ) : EReal) - w) = w + ((-c : ℝ) : EReal) := by
  rw [EReal.neg_coe_sub]
  rfl

/-- **Fenchel–Moreau at the origin.** For a convex `f`, the closure at `0` is the supremum over the
dual variable of the infimum of `x ↦ ⟨x, y⟩ + f x`. Everything below rests on this computation. -/
theorem clFn_zero_eq_iSup_iInf (hf : ConvexFn f) :
    clFn f 0 = ⨆ y : F, ⨅ x : E, (((B x y : ℝ) : EReal) + f x) := by
  have hsurj : Function.Surjective (fun y : F => -y) := fun y => ⟨-y, neg_neg y⟩
  have hterm : ∀ y : F, ((B (0 : E) y : ℝ) : EReal) - conj B f y
      = ⨅ x : E, (((B x (-y) : ℝ) : EReal) + f x) := by
    intro y
    rw [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero, zero_sub, conj_apply,
      EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    have hb : (B x (-y) : ℝ) = -(B x y) := by rw [map_neg]
    rw [neg_coe_sub_eq, hb, add_comm]
  rw [← biconj_eq_clFn (B := B) hf, biconj_apply, iSup_congr hterm]
  exact hsurj.iSup_comp fun y : F => ⨅ x : E, (((B x y : ℝ) : EReal) + f x)

end ClosureAtZero

/-! ### Normality -/

section Normal

variable {U X : Type*} [AddCommGroup U] [TopologicalSpace U] {F : Bifun U X}

/-- A convex program is **normal** when its perturbation function is closed at the origin,
`(cl (inf F))(0) = (inf F)(0)`. When `0 ∈ cl (dom F)` this is lower semicontinuity of
`u ↦ inf F u` at `u = 0`. -/
def Normal (F : Bifun U X) : Prop := clFn (infBifun F) 0 = infBifun F 0

theorem normal_iff : Normal F ↔ clFn (infBifun F) 0 = infBifun F 0 := Iff.rfl

end Normal

/-! ### The concave counterparts of the convex vocabulary -/

section ConcaveVocabulary

variable {V Y : Type*} {G : Bifun Y V}

/-- The optimal value of the concave program `G y`, as a function of the perturbation `y`: the
mirror of `infBifun`. Rockafellar writes `sup G`. -/
noncomputable def supBifun (G : Bifun Y V) : Y → EReal := fun y => ⨆ v, G y v

theorem supBifun_apply (G : Bifun Y V) (y : Y) : supBifun G y = ⨆ v, G y v := rfl

/-- The mirror of `domBifun`: the perturbations for which the concave program is consistent. -/
def domConcaveBifun (G : Bifun Y V) : Set Y := {y | ∃ v, G y v ≠ ⊥}

theorem mem_domConcaveBifun {y : Y} : y ∈ domConcaveBifun G ↔ ∃ v, G y v ≠ ⊥ := Iff.rfl

/-- Negating a concave bifunction turns its `sup` into the `inf` of the negation. -/
theorem neg_supBifun (G : Bifun Y V) :
    (fun y => -(supBifun G y)) = infBifun fun y v => -(G y v) := by
  funext y
  rw [supBifun_apply, EReal.neg_iSup, infBifun_apply]

/-- **The effective domain of `-G` is the concave effective domain of `G`**: `-(G y v) ≠ ⊤` and
`G y v ≠ ⊥` are the same condition. This turns every consistency hypothesis about a concave program
into the corresponding hypothesis about the convex program `-G`. -/
theorem domBifun_neg (G : Bifun Y V) : domBifun (fun y v => -(G y v)) = domConcaveBifun G := by
  ext y
  simp only [mem_domBifun, mem_domConcaveBifun, ne_eq, _root_.EReal.neg_eq_top_iff]

/-- The mirror of `dom_infBifun`. -/
theorem domConcave_supBifun (G : Bifun Y V) : domConcave (supBifun G) = domConcaveBifun G := by
  ext y
  simp only [mem_domConcave, supBifun_apply, mem_domConcaveBifun, bot_lt_iff_ne_bot, ne_eq,
    iSup_eq_bot, not_forall]

end ConcaveVocabulary

section ConcaveConsistency

variable {V Y : Type*} [AddCommGroup Y] {G : Bifun Y V}

/-- The mirror of `Consistent`: the unperturbed concave program has a point where it is not
`-∞`. -/
def ConcaveConsistent (G : Bifun Y V) : Prop := (0 : Y) ∈ domConcaveBifun G

theorem concaveConsistent_iff : ConcaveConsistent G ↔ ∃ v, G 0 v ≠ ⊥ := Iff.rfl

end ConcaveConsistency

section ConcaveNormality

variable {V Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] {G : Bifun Y V}

/-- The mirror of `Normal` for a concave program: `(cl (sup G))(0) = (sup G)(0)`, the closure taken
in the concave sense. -/
def ConcaveNormal (G : Bifun Y V) : Prop := clConcave (supBifun G) 0 = supBifun G 0

theorem concaveNormal_iff : ConcaveNormal G ↔ clConcave (supBifun G) 0 = supBifun G 0 := Iff.rfl

/-- Concave normality of `G` is ordinary normality of `-G`. This is what makes each concave
sufficient condition free: it is the corresponding convex one read at `-F*`, pairings flipped. -/
theorem concaveNormal_iff_normal_neg : ConcaveNormal G ↔ Normal fun y v => -(G y v) := by
  have hval : ∀ y, infBifun (fun y' v => -(G y' v)) y = -(supBifun G y) :=
    fun y => (congrFun (neg_supBifun G) y).symm
  have hcl : clFn (infBifun fun y' v => -(G y' v)) 0 = -(clConcave (supBifun G) 0) := by
    rw [clConcave_apply, neg_neg, neg_supBifun]
  rw [concaveNormal_iff, normal_iff, hcl, hval 0, neg_inj]

end ConcaveNormality

section ConcaveStrongConsistency

variable {V Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {G : Bifun Y V}

/-- The mirror of `StronglyConsistent`. -/
def ConcaveStronglyConsistent (G : Bifun Y V) : Prop := (0 : Y) ∈ ri (domConcaveBifun G)

theorem ConcaveStronglyConsistent.concaveConsistent (h : ConcaveStronglyConsistent G) :
    ConcaveConsistent G :=
  intrinsicInterior_subset h

/-- Strong consistency of the concave program `G` is strong consistency of `-G`; this is what lets
the concave consistency statements be read off the convex ones. -/
theorem concaveStronglyConsistent_iff_stronglyConsistent_neg :
    ConcaveStronglyConsistent G ↔ StronglyConsistent fun y v => -(G y v) := by
  rw [ConcaveStronglyConsistent, StronglyConsistent, domBifun_neg]

end ConcaveStrongConsistency

/-! ### Concavity of the dual perturbation function -/

section ConcaveFnSup

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Y] [Module ℝ Y]
  {G : Bifun Y V}

/-- The mirror of `convexFn_infBifun`: the optimal value of a concave program is a concave function
of the perturbation. -/
theorem concaveFn_supBifun (hG : ConcaveBifun G) : ConcaveFn (supBifun G) :=
  concaveFn_iff_convexFn_neg.2 (by
    rw [neg_supBifun]
    exact convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG))

end ConcaveFnSup

/-! ### The two optimal values -/

section OptimalValues

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

/-- **The optimal value of the dual program**: `(cl (inf F))(0) = sup F* 0`. Closedness of `F` is
not needed — the formula is Fenchel–Moreau for `inf F`, and `F*` does not see the closure. -/
theorem clFn_infBifun_zero_eq_iSup_adjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    clFn (infBifun F) 0 = ⨆ v : V, adjointBifun Bu Bx F 0 v := by
  rw [clFn_zero_eq_iSup_iInf (B := Bu) (convexFn_infBifun hF)]
  exact iSup_congr fun v => (adjointBifun_zero_apply Bu Bx F v).symm

/-- Normality is exactly the absence of a duality gap: `sup F* 0 = inf F 0`. -/
theorem normal_iff_iSup_adjointBifun_eq (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    Normal F ↔ (⨆ v : V, adjointBifun Bu Bx F 0 v) = infBifun F 0 := by
  rw [normal_iff, clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bu) Bx hF]

end OptimalValues

section ConcaveOptimalValues

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx.flip]
  {G : Bifun Y V}

/-- Negating a sum whose second summand is finite. -/
private theorem neg_neg_add_coe {a : EReal} {c : ℝ} :
    -(-a + (c : EReal)) = a + ((-c : ℝ) : EReal) := by
  rw [_root_.EReal.neg_add (.inr (_root_.EReal.coe_ne_top _)) (.inr (_root_.EReal.coe_ne_bot _)),
    neg_neg, sub_eq_add_neg, ← _root_.EReal.coe_neg]

/-- The dual of `clFn_infBifun_zero_eq_iSup_adjointBifun`: the concave closure of the dual
perturbation function at the origin is the optimal value of the doubly-adjoint program. -/
theorem clConcave_supBifun_zero_eq_infBifun_concaveAdjointBifun (hG : ConcaveBifun G) :
    clConcave (supBifun G) 0 = infBifun (concaveAdjointBifun Bu Bx G) 0 := by
  have hsurj : Function.Surjective (fun x : X => -x) := fun x => ⟨-x, neg_neg x⟩
  have hneg : ConvexBifun fun y v => -(G y v) := concaveFn_iff_convexFn_neg.1 hG
  have hpt : ∀ x : X, -(adjointBifun Bx.flip Bu.flip (fun y v => -(G y v)) 0 x)
      = concaveAdjointBifun Bu Bx G 0 (-x) := by
    intro x
    rw [adjointBifun_apply, EReal.neg_iInf, concaveAdjointBifun_apply]
    refine iSup_congr fun q => ?_
    have h1 : (Bx.flip q.1 x - Bu.flip q.2 (0 : U) : ℝ) = Bx x q.1 := by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, map_zero, LinearMap.zero_apply, sub_zero]
    have h2 : (Bx (-x) q.1 - Bu (0 : U) q.2 : ℝ) = -(Bx x q.1) := by
      rw [map_zero, LinearMap.zero_apply, sub_zero, map_neg, LinearMap.neg_apply]
    rw [h1, h2, neg_neg_add_coe]
  rw [clConcave_apply, neg_supBifun,
    clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bx.flip) Bu.flip hneg, EReal.neg_iSup,
    iInf_congr hpt]
  exact hsurj.iInf_comp fun x : X => concaveAdjointBifun Bu Bx G 0 x

end ConcaveOptimalValues

/-! ### Normality of `(P)`, of `(P*)`, and the absence of a duality gap -/

section DualityGap

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **The optimal value of the primal program**: `(cl (sup F*))(0) = inf F 0` for a closed convex
bifunction. Closedness is what turns `F**` back into `F`. -/
theorem clConcave_supBifun_adjointBifun_zero_eq (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    clConcave (supBifun (adjointBifun Bu Bx F)) 0 = infBifun F 0 := by
  rw [clConcave_supBifun_zero_eq_infBifun_concaveAdjointBifun (Bu := Bu) (Bx := Bx)
      (concaveBifun_adjointBifun Bu Bx F),
    concaveAdjointBifun_adjointBifun_eq_clBifun hF, hcl.clBifun_eq]

/-- The dual program is normal exactly when there is no duality gap. -/
theorem concaveNormal_adjointBifun_iff (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ConcaveNormal (adjointBifun Bu Bx F)
      ↔ (⨆ v : V, adjointBifun Bu Bx F 0 v) = infBifun F 0 := by
  rw [concaveNormal_iff, clConcave_supBifun_adjointBifun_zero_eq hF hcl]
  exact eq_comm

/-- A closed convex program is normal exactly when its dual program is. -/
theorem normal_iff_concaveNormal_adjointBifun (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Normal F ↔ ConcaveNormal (adjointBifun Bu Bx F) :=
  (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).trans
    (concaveNormal_adjointBifun_iff hF hcl).symm

end DualityGap

/-! ### Sufficient conditions for normality -/

section KuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {v : V}

/-- If a Kuhn–Tucker vector exists then normality holds. Such a vector is a point at which the dual
objective reaches `inf F 0`, and weak duality says it can never exceed it. (Finiteness of the
optimal value is already part of `KuhnTucker`.) -/
theorem normal_of_kuhnTucker_nonempty (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (h : (KuhnTucker Bu F).Nonempty) : Normal F := by
  obtain ⟨w, hw⟩ := h
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx)] at hw
  rw [normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF]
  refine le_antisymm (iSup_adjointBifun_zero_le Bu Bx F) ?_
  rw [← hw.2.2]
  exact le_iSup (fun z : V => adjointBifun Bu Bx F 0 z) w

/-- Under normality, and with the optimal value finite, the Kuhn–Tucker vectors of `(P)` are
exactly the optimal solutions of `(P*)`. -/
theorem mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (hn : Normal F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker Bu F
      ↔ adjointBifun Bu Bx F 0 v = ⨆ w : V, adjointBifun Bu Bx F 0 w := by
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx),
    (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).1 hn]
  exact ⟨fun h => h.2.2, fun h => ⟨ht, hb, h⟩⟩

/-- The same as an equation between sets: the Kuhn–Tucker set is the set of dual maximisers. -/
theorem kuhnTucker_eq_setOf_isMax (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) (hn : Normal F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker Bu F
      = {v : V | adjointBifun Bu Bx F 0 v = ⨆ w : V, adjointBifun Bu Bx F 0 w} :=
  Set.ext fun _ => mem_kuhnTucker_iff_adjointBifun_zero_eq_iSup Bx hF hn ht hb

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [IsCompatiblePairing Bu] in
/-- A Kuhn–Tucker vector is a dual optimal solution, with common optimal value `inf F 0`. This half
needs no normality hypothesis — the vector's existence supplies it. -/
theorem isGreatest_adjointBifun_zero_of_mem_kuhnTucker (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hv : v ∈ KuhnTucker Bu F) :
    IsGreatest (Set.range (adjointBifun Bu Bx F 0)) (infBifun F 0) := by
  rw [mem_kuhnTucker_iff_adjointBifun_zero_eq (Bx := Bx)] at hv
  exact ⟨⟨v, hv.2.2⟩, by rintro _ ⟨w, rfl⟩; exact adjointBifun_zero_le Bu Bx F w⟩

end KuhnTucker

section StrongConsistency

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup X] [Module ℝ X] {F : Bifun U X}

/-- A strongly consistent convex program is normal: a convex function agrees with its closure
throughout the relative interior of its effective domain, which here contains the origin. -/
theorem StronglyConsistent.normal (hs : StronglyConsistent F) (hF : ConvexBifun F) : Normal F := by
  have hri : (0 : U) ∈ ri (dom (infBifun F)) := by rwa [dom_infBifun]
  exact (convexFn_infBifun hF).clFn_eq_of_mem_relint_dom hri

/-- A strictly consistent convex program is normal. -/
theorem StrictlyConsistent.normal (hs : StrictlyConsistent F) (hF : ConvexBifun F) : Normal F :=
  hs.stronglyConsistent.normal hF

end StrongConsistency

/-! ### Strong consistency of the dual program -/

section

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] {G : Bifun Y V}

/-- The concave mirror: a strongly consistent concave program is normal. -/
theorem ConcaveStronglyConsistent.concaveNormal (hs : ConcaveStronglyConsistent G)
    (hG : ConcaveBifun G) : ConcaveNormal G := by
  have hri : (0 : Y) ∈ ri (dom fun z => -(supBifun G z)) := by
    rw [← domConcave_eq_dom_neg, domConcave_supBifun]
    exact hs
  rw [ConcaveNormal, clConcave_apply,
    (concaveFn_supBifun hG).convexFn_neg.clFn_eq_of_mem_relint_dom hri, neg_neg]

end

section DualStrongConsistency

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- If the *dual* program is strongly consistent then normality holds for the pair. -/
theorem normal_of_concaveStronglyConsistent_adjointBifun (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hs : ConcaveStronglyConsistent (adjointBifun Bu Bx F)) : Normal F :=
  (normal_iff_concaveNormal_adjointBifun hF hcl).2
    (hs.concaveNormal (concaveBifun_adjointBifun Bu Bx F))

end DualStrongConsistency

/-! ### Bounded level sets and bounded sets of optimal solutions -/

section Shift

variable {U V X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {y : Y}

/-- `F` with a linear function of `x` subtracted off; its optimal value at `u` is `-(F u)*(y)`, so
the dual-value formula applied to it computes the whole `y`-slice `sup (F* y)` of the adjoint. -/
noncomputable def shiftBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) : Bifun U X :=
  fun u x => F u x - ((Bx x y : ℝ) : EReal)

@[simp] theorem shiftBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U)
    (x : X) : shiftBifun Bx F y u x = F u x - ((Bx x y : ℝ) : EReal) := rfl

/-- The optimal value of the shifted program is the conjugate of the slice, negated. -/
theorem infBifun_shiftBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (F : Bifun U X) (y : Y) (u : U) :
    infBifun (shiftBifun Bx F y) u = -(conj Bx (F u) y) := by
  rw [infBifun_apply, conj_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [shiftBifun_apply, _root_.EReal.neg_sub (Or.inl (_root_.EReal.coe_ne_bot ((Bx x) y)))
    (Or.inl (_root_.EReal.coe_ne_top ((Bx x) y))), sub_eq_add_neg]
  exact add_comm _ _

end Shift

section ShiftConvex

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {F : Bifun U X} {y : Y}

/-- Subtracting a linear function of `x` keeps a convex bifunction convex. -/
theorem convexBifun_shiftBifun (hF : ConvexBifun F) (y : Y) :
    ConvexBifun (shiftBifun Bx F y) := by
  have hl : ∀ (p q : U × X) (a b : ℝ), a + b = 1 →
      (fun r : U × X => -(Bx r.2 y)) (a • p + b • q)
        = a * (fun r : U × X => -(Bx r.2 y)) p + b * (fun r : U × X => -(Bx r.2 y)) q := by
    intro p q a b _
    simp only [Prod.snd_add, Prod.smul_snd, map_add, map_smul, smul_eq_mul,
      LinearMap.add_apply, LinearMap.smul_apply]
    ring
  have h := convexFn_add_coe (f := graphFn F) (l := fun r : U × X => -(Bx r.2 y)) hF hl
  have heq : (fun p : U × X => graphFn F p + ((-(Bx p.2 y) : ℝ) : EReal))
      = graphFn (shiftBifun Bx F y) := by
    funext p
    simp only [graphFn, shiftBifun, _root_.EReal.coe_neg, sub_eq_add_neg]
  refine convexBifun_iff.2 ?_
  rw [← heq]
  exact h

/-- Shifting by `y` and reading the adjoint at the origin is the adjoint at `y`. -/
theorem adjointBifun_shiftBifun_zero (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (F : Bifun U X) (y : Y) (v : V) :
    adjointBifun Bu Bx (shiftBifun Bx F y) 0 v = adjointBifun Bu Bx F y v := by
  have key : ∀ (z : EReal) (b c : ℝ),
      (z - (c : EReal)) + (b : EReal) = z + ((b - c : ℝ) : EReal) := by
    intro z b c
    rw [_root_.EReal.coe_sub, sub_eq_add_neg z, sub_eq_add_neg ((b : ℝ) : EReal), add_assoc,
      add_comm (-(((c : ℝ) : EReal))) (((b : ℝ) : EReal))]
  simp only [adjointBifun_apply, shiftBifun_apply, map_zero, sub_zero, key]

end ShiftConvex

section BoundedLevelSets

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X} {y : Y}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] in
/-- **The dual objective at an arbitrary `y`**: the supremum defining it is the closure, at the
origin, of the optimal value of the shifted program. -/
theorem supBifun_adjointBifun (hF : ConvexBifun F) (y : Y) :
    supBifun (adjointBifun Bu Bx F) y = clFn (infBifun (shiftBifun Bx F y)) 0 := by
  rw [supBifun_apply,
    clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bu) Bx (convexBifun_shiftBifun hF y)]
  exact (iSup_congr fun v => adjointBifun_shiftBifun_zero Bu Bx F y v).symm

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [IsCompatiblePairing Bx]
  [IsCompatiblePairing Bx.flip] in
/-- If the perturbed objective `F u - ⟨·, y⟩` is bounded below for *every* perturbation `u`, then
`y` belongs to the effective domain of the dual program.

`domConcaveBifun F*` asks for `sup (F* y) ≠ -∞`, which is `cl (inf (F - ⟨·, y⟩)) 0 ≠ -∞`, strictly
stronger than the `inf (F - ⟨·, y⟩) 0 ≠ -∞` that `y ∈ dom ((F 0)*)` says. What bridges them is that
a proper convex function has a proper closure. This is the one statement here needing
`FiniteDimensional ℝ U`. -/
theorem mem_domConcaveBifun_adjointBifun (hF : ConvexBifun F) (hc : Consistent F)
    (h : ∀ u : U, conj Bx (F u) y ≠ ⊤) :
    y ∈ domConcaveBifun (adjointBifun Bu Bx F) := by
  obtain ⟨x₀, hx₀⟩ := hc
  have hprop : Proper (infBifun (shiftBifun Bx F y)) := by
    refine ⟨⟨0, mem_dom.2 ?_⟩, fun u => ?_⟩
    · have hle : infBifun (shiftBifun Bx F y) 0 ≤ shiftBifun Bx F y 0 x₀ := iInf_le _ x₀
      refine lt_of_le_of_lt hle ?_
      rw [shiftBifun_apply, sub_eq_add_neg]
      exact _root_.EReal.add_lt_top hx₀
        (by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact _root_.EReal.coe_ne_bot _)
    · rw [infBifun_shiftBifun, Ne, _root_.EReal.neg_eq_bot_iff]
      exact h u
  have hcl := (convexFn_infBifun (convexBifun_shiftBifun (Bx := Bx) hF y)).proper_clFn hprop
  have hne : supBifun (adjointBifun Bu Bx F) y ≠ ⊥ := by
    rw [supBifun_adjointBifun hF y]
    exact hcl.ne_bot 0
  rw [mem_domConcaveBifun]
  by_contra hcon
  push Not at hcon
  exact hne (by rw [supBifun_apply, iSup_eq_bot.2 hcon])

include Bu Bx in
/-- If some level set `{x | (F 0)(x) ≤ α}` is non-empty and bounded, then normality holds for `(P)`
and `(P*)`.

A bounded level set gives `0 ∈ int (dom ((F 0)*))`, but strict consistency of `(P*)` is
`0 ∈ int (domConcaveBifun F*)`, an intersection over *all* perturbations `u` of the sets
`dom ((F u)*)`, and openness of an intersection is not automatic. What makes it open is that all
slices of a closed convex bifunction have the same recession function, so every
`int (dom ((F u)*))` is described by the same inequality and they are all equal. No properness is
assumed: an improper closed convex bifunction has `inf F 0 = -∞`, where normality is trivial. -/
theorem normal_of_exists_setOf_le (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : ∃ α : ℝ, {x : X | F 0 x ≤ (α : EReal)}.Nonempty ∧
      Bornology.IsBounded {x : X | F 0 x ≤ (α : EReal)}) :
    Normal F := by
  obtain ⟨α, ⟨x₀, hx₀⟩, hbd⟩ := h
  have hx₀top : F 0 x₀ ≠ ⊤ := (lt_of_le_of_lt hx₀ (_root_.EReal.coe_lt_top α)).ne
  have hcons : Consistent F := ⟨x₀, hx₀top⟩
  have hlsc : LowerSemicontinuous (graphFn F) := ClosedFn.lowerSemicontinuous hcl
  have hcont : ∀ u : U, Continuous fun x : X => (u, x) := fun u =>
    continuous_const.prodMk continuous_id
  by_cases hbot : ∃ p : U × X, graphFn F p = ⊥
  · have hb : F 0 x₀ = ⊥ :=
      (ConvexFn.eq_bot_or_eq_top hF hlsc hbot (0, x₀)).resolve_right hx₀top
    have hval : infBifun F 0 = ⊥ := by
      refine le_bot_iff.1 ?_
      rw [infBifun_apply, ← hb]
      exact iInf_le _ x₀
    have hle : clFn (infBifun F) 0 ≤ ⊥ := by rw [← hval]; exact clFn_le _ 0
    rw [normal_iff, le_bot_iff.1 hle, hval]
  push Not at hbot
  have hslice : ∀ u : U, u ∈ domBifun F → ClosedProperConvexFn (F u) := by
    intro u hu
    obtain ⟨x₁, hx₁⟩ := hu
    refine ⟨hF.convexFn_apply u, ?_, ⟨⟨x₁, mem_dom.2 (lt_top_iff_ne_top.2 hx₁)⟩,
      fun x => hbot (u, x)⟩⟩
    refine (closedFn_iff_lowerSemicontinuous fun x => hbot (u, x)).2 fun x r hr => ?_
    exact ((hcont u).tendsto x).eventually (hlsc (u, x) r hr)
  have hepi : IsClosed (epi (graphFn F)) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  have h0int : (0 : Y) ∈ interior (dom (conj Bx (F 0))) := by
    have h0 := hslice 0 hcons
    exact (exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (B := Bx)
      h0.convex h0.closed h0.proper).1 ⟨α, ⟨x₀, hx₀⟩, hbd⟩
  have hsub : interior (dom (conj Bx (F 0))) ⊆ domConcaveBifun (adjointBifun Bu Bx F) := by
    intro z hz
    refine mem_domConcaveBifun_adjointBifun hF hcons fun u => ?_
    by_cases hu : u ∈ domBifun F
    · have hrec : recessionFn (F 0) = recessionFn (F u) :=
        recessionFn_slice_eq hF hepi hcons hu
      have hzu : z ∈ interior (dom (conj Bx (F u))) := by
        rw [mem_interior_dom_conj_iff (hslice u hu) z, ← hrec]
        exact (mem_interior_dom_conj_iff (hslice 0 hcons) z).1 hz
      exact (mem_dom.1 (interior_subset hzu)).ne
    · have htop : ∀ x : X, F u x = ⊤ := fun x => by
        by_contra hcon
        exact hu ⟨x, hcon⟩
      have hinf : infBifun (shiftBifun Bx F z) u = ⊤ := by
        rw [infBifun_apply]
        refine le_antisymm le_top (le_iInf fun x => ?_)
        rw [shiftBifun_apply, htop x, _root_.EReal.top_sub_coe]
      rw [infBifun_shiftBifun] at hinf
      rw [_root_.EReal.neg_eq_top_iff.1 hinf]
      exact bot_ne_top
  exact normal_of_concaveStronglyConsistent_adjointBifun hF hcl
    (interior_subset_intrinsicInterior (interior_maximal hsub isOpen_interior h0int))

include Bu Bx in
/-- If the optimal solutions to `(P)` form a non-empty bounded set — in particular if there is
exactly one — then normality holds. With `F 0` proper this is the level-set criterion, since
`argmin (F 0)` is then a level set at the minimum value. Properness is not removable: for
`F 0 ≡ ⊤` over a zero-dimensional `X` the optimal solutions are non-empty and bounded while no
level set is. -/
theorem normal_of_argmin_nonempty_and_isBounded (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hp : Proper (F 0)) (hne : (argmin (F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmin (F 0))) :
    Normal F := by
  have hc : ClosedFn (F 0) := by
    refine (closedFn_iff_lowerSemicontinuous hp.ne_bot).2 fun x r hr => ?_
    exact ((continuous_const.prodMk continuous_id).tendsto x).eventually
      (ClosedFn.lowerSemicontinuous hcl (0, x) r hr)
  exact normal_of_exists_setOf_le (Bu := Bu) (Bx := Bx) hF hcl
    ((argmin_nonempty_and_isBounded_iff_exists_setOf_le (B := Bx) (hF.convexFn_apply 0) hc hp).1
      ⟨hne, hbd⟩)

end BoundedLevelSets

/-! ### Bounded level sets of the dual objective -/

section DualBoundedLevelSets

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] [IsCompatiblePairing Bu.flip]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
  {F : Bifun U X}

/-- If some superlevel set `{v | α ≤ (F* 0)(v)}` of the dual objective is non-empty and bounded,
then normality holds for `(P)` and `(P*)`.

This is the level-set criterion read for the *convex* program associated with `-F*`, which is
convex and closed with no hypothesis on `F`: its objective is `-(F* 0)` and its sublevel set at
`-α` is the superlevel set of `F* 0` at `α`. Normality of that program is concave normality of
`F*`, hence normality of `(P)`. Going this way needs no concave mirror of the level-set and
recession machinery on `V`. -/
theorem normal_of_exists_setOf_ge_adjointBifun (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : ∃ α : ℝ, {v : V | (α : EReal) ≤ adjointBifun Bu Bx F 0 v}.Nonempty ∧
      Bornology.IsBounded {v : V | (α : EReal) ≤ adjointBifun Bu Bx F 0 v}) :
    Normal F := by
  have hpair : IsContinuousPairing (prodPairing Bu Bx).flip :=
    isContinuousPairing_prodPairing_flip Bu Bx
  obtain ⟨α, hne, hbd⟩ := h
  have hset : {v : V | -(adjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal)}
      = {v : V | (α : EReal) ≤ adjointBifun Bu Bx F 0 v} := by
    ext v
    have hiff : (-(adjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal))
        ↔ ((α : EReal) ≤ adjointBifun Bu Bx F 0 v) := by
      rw [_root_.EReal.neg_le, _root_.EReal.coe_neg, neg_neg]
    exact hiff
  have hne' : {v : V | -(adjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal)}.Nonempty := by
    rw [hset]; exact hne
  have hbd' : Bornology.IsBounded {v : V | -(adjointBifun Bu Bx F 0 v) ≤ ((-α : ℝ) : EReal)} := by
    rw [hset]; exact hbd
  have hnormal : Normal fun y v => -(adjointBifun Bu Bx F y v) :=
    normal_of_exists_setOf_le (Bu := Bx.flip) (Bx := Bu.flip)
      (convexBifun_neg_adjointBifun Bu Bx F) closedBifun_neg_adjointBifun ⟨-α, hne', hbd'⟩
  exact (normal_iff_concaveNormal_adjointBifun hF hcl).2 (concaveNormal_iff_normal_neg.2 hnormal)

/-- If the optimal solutions to `(P*)` form a non-empty bounded set — in particular if there is
exactly one — then normality holds. The bounded-`argmin` criterion read for the convex program
associated with `-F*`; properness of the objective is not removable there either. -/
theorem normal_of_argmax_adjointBifun_nonempty_and_isBounded (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hp : Proper fun v => -(adjointBifun Bu Bx F 0 v))
    (hne : (argmax (adjointBifun Bu Bx F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmax (adjointBifun Bu Bx F 0))) :
    Normal F := by
  have hpair : IsContinuousPairing (prodPairing Bu Bx).flip :=
    isContinuousPairing_prodPairing_flip Bu Bx
  have harg : argmin (fun v : V => -(adjointBifun Bu Bx F 0 v))
      = argmax (adjointBifun Bu Bx F 0) := (argmax_eq_argmin_neg _).symm
  have hne' : (argmin fun v : V => -(adjointBifun Bu Bx F 0 v)).Nonempty := by
    rw [harg]; exact hne
  have hbd' : Bornology.IsBounded (argmin fun v : V => -(adjointBifun Bu Bx F 0 v)) := by
    rw [harg]; exact hbd
  have hnormal : Normal fun y v => -(adjointBifun Bu Bx F y v) :=
    normal_of_argmin_nonempty_and_isBounded (Bu := Bx.flip) (Bx := Bu.flip)
      (convexBifun_neg_adjointBifun Bu Bx F) closedBifun_neg_adjointBifun hp hne' hbd'
  exact (normal_iff_concaveNormal_adjointBifun hF hcl).2 (concaveNormal_iff_normal_neg.2 hnormal)

end DualBoundedLevelSets

/-! ### Consistency of the two programs -/

section ConjTop

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup G] [Module ℝ G] {B : E →ₗ[ℝ] G →ₗ[ℝ] ℝ} [IsCompatiblePairing B]
  {f : E → EReal}

/-- **A dichotomy for conjugates**: the conjugate of a convex function is identically `⊤` exactly
when the function takes the value `⊥` somewhere. One direction is free; the other uses that a
proper convex function has a proper closure, whose conjugate is proper, and `(cl f)* = f*`. -/
theorem forall_conj_eq_top_iff (hf : ConvexFn f) :
    (∀ y : G, conj B f y = ⊤) ↔ ∃ x : E, f x = ⊥ := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    by_cases hd : ∃ x : E, f x ≠ ⊤
    · obtain ⟨x₀, hx₀⟩ := hd
      have hp : Proper f := ⟨⟨x₀, mem_dom.2 (lt_of_le_of_ne le_top hx₀)⟩, hcon⟩
      have hpc : Proper (conj B (clFn f)) :=
        proper_conj ⟨convexFn_clFn hf, closedFn_clFn f, hf.proper_clFn hp⟩
      rw [conj_clFn] at hpc
      obtain ⟨y, hy⟩ := hpc.dom_nonempty
      exact absurd (h y) (mem_dom.1 hy).ne
    · push Not at hd
      have hbot : conj B f 0 = ⊥ := conj_eq_bot_iff.2 hd
      rw [h 0] at hbot
      exact absurd hbot (by simp)
  · rintro ⟨x, hx⟩ y
    refine top_le_iff.1 ?_
    rw [conj_apply]
    refine le_trans (le_of_eq ?_) (le_iSup (fun z : E => ((B z y : ℝ) : EReal) - f z) x)
    rw [hx]
    simp

end ConjTop

section DualConsistency

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

/-- Negating a sum whose first summand is finite. -/
private theorem neg_coe_add {c : ℝ} {w : EReal} :
    -(((c : ℝ) : EReal) + w) = ((-c : ℝ) : EReal) - w := by
  rw [_root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _)) (.inl (_root_.EReal.coe_ne_top _)),
    ← _root_.EReal.coe_neg]

omit [FiniteDimensional ℝ U] [IsCompatiblePairing Bu] in
/-- The dual objective, negated, is the conjugate of the perturbation function at the reflected
point: `-(F* 0)(v) = (inf F)*(-v)`. -/
theorem neg_adjointBifun_zero_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) :
    -(adjointBifun Bu Bx F 0 v) = conj Bu (infBifun F) (-v) := by
  rw [adjointBifun_zero_apply, EReal.neg_iInf, conj_apply]
  refine iSup_congr fun u => ?_
  rw [neg_coe_add, map_neg]

omit [FiniteDimensional ℝ U] [IsCompatiblePairing Bu] in
/-- The dual objective is `-∞` at `v` exactly when the conjugate of the perturbation function is
`+∞` at `-v`. -/
theorem adjointBifun_zero_eq_bot_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (v : V) :
    adjointBifun Bu Bx F 0 v = ⊥ ↔ conj Bu (infBifun F) (-v) = ⊤ := by
  rw [← neg_adjointBifun_zero_apply (Bu := Bu) Bx (F := F) v, _root_.EReal.neg_eq_top_iff]

/-- **Inconsistency of the dual**: `(P*)` is inconsistent exactly when some perturbation of `(P)`
is unbounded below. Closedness of `F` is not needed, because `F*` never sees the difference
between `F` and `cl F`. -/
theorem not_concaveConsistent_adjointBifun_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ¬ ConcaveConsistent (adjointBifun Bu Bx F) ↔ ∃ u, infBifun F u = ⊥ := by
  rw [← forall_conj_eq_top_iff (B := Bu) (convexFn_infBifun hF), concaveConsistent_iff]
  push Not
  constructor
  · intro h y
    have hy := (adjointBifun_zero_eq_bot_iff (Bu := Bu) Bx (F := F) (-y)).1 (h (-y))
    rwa [neg_neg] at hy
  · intro h v
    exact (adjointBifun_zero_eq_bot_iff (Bu := Bu) Bx (F := F) v).2 (h (-v))

/-- The positive form: `(P*)` is consistent exactly when no perturbation of `(P)` is unbounded
below. -/
theorem concaveConsistent_adjointBifun_iff (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F) :
    ConcaveConsistent (adjointBifun Bu Bx F) ↔ ∀ u, infBifun F u ≠ ⊥ := by
  rw [← not_iff_not, not_concaveConsistent_adjointBifun_iff Bx hF]
  push Not
  rfl

end DualConsistency

/-! ### The objective of the doubly-adjoint program

Three algebraic facts about `G* 0` for a concave `G`. They carried the whole instance context of
the consistency section with an `omit` list per declaration; none of them uses any of it, so they
sit in their own section at the weakest layer instead. -/

section ConcaveAdjointZero

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {G : Bifun Y V}

/-- The mirror of `adjointBifun_zero_apply`: the objective of the program associated with the
concave adjoint is `(G* 0)(x) = ⨆ y (⟨x, y⟩ + sup G y)`. -/
theorem concaveAdjointBifun_zero_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) (x : X) :
    concaveAdjointBifun Bu Bx G 0 x = ⨆ y, (((Bx x y : ℝ) : EReal) + supBifun G y) := by
  rw [concaveAdjointBifun_apply, iSup_prod]
  refine iSup_congr fun y => ?_
  have hzero : ∀ v : V, (Bx x y - Bu (0 : U) v : ℝ) = Bx x y := fun v => by
    rw [map_zero, LinearMap.zero_apply, sub_zero]
  simp only [hzero]
  rw [supBifun_apply, add_comm, EReal.iSup_add_coe]

/-- The doubly-adjoint objective is the conjugate of `-sup G`: `(-sup G)* = G* 0`. -/
theorem concaveAdjointBifun_zero_eq_conj (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (G : Bifun Y V) :
    concaveAdjointBifun Bu Bx G 0 = conj Bx.flip (fun y => -(supBifun G y)) := by
  funext x
  rw [concaveAdjointBifun_zero_apply, conj_apply]
  exact iSup_congr fun y => by rw [LinearMap.flip_apply, sub_eq_add_neg, neg_neg]

/-- `-sup G` is convex when `G` is a concave bifunction: it is `inf (-G)`. -/
theorem convexFn_neg_supBifun (hG : ConcaveBifun G) : ConvexFn (fun y => -(supBifun G y)) := by
  rw [neg_supBifun]
  exact convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG)

end ConcaveAdjointZero

section PrimalConsistency

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Inconsistency of the primal**: `(P)` is inconsistent exactly when some perturbation of `(P*)`
is unbounded above. Unlike the dual half this does need `F` closed: it is that half read for the
dual pair, and `F** = F` identifies the objective of `(P)`. -/
theorem not_consistent_iff_exists_supBifun_eq_top (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    ¬ Consistent F ↔ ∃ y, supBifun (adjointBifun Bu Bx F) y = ⊤ := by
  have hg : ConvexFn (fun y => -(supBifun (adjointBifun Bu Bx F) y)) :=
    convexFn_neg_supBifun (concaveBifun_adjointBifun Bu Bx F)
  have hF0 : ∀ x : X,
      F 0 x = conj Bx.flip (fun y => -(supBifun (adjointBifun Bu Bx F) y)) x := by
    intro x
    rw [← concaveAdjointBifun_zero_eq_conj Bu Bx (adjointBifun Bu Bx F),
      concaveAdjointBifun_adjointBifun_eq_self hF hcl]
  rw [consistent_iff]
  push Not
  simp only [hF0]
  rw [forall_conj_eq_top_iff (B := Bx.flip) hg]
  exact exists_congr fun y => _root_.EReal.neg_eq_bot_iff

/-- The positive form: `(P)` is consistent exactly when no perturbation of `(P*)` is unbounded
above. -/
theorem consistent_iff_forall_supBifun_ne_top (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    Consistent F ↔ ∀ y, supBifun (adjointBifun Bu Bx F) y ≠ ⊤ := by
  rw [← not_iff_not, not_consistent_iff_exists_supBifun_eq_top (Bu := Bu) (Bx := Bx) hF hcl]
  push Not
  rfl

end PrimalConsistency

/-! ### Kuhn–Tucker vectors of the dual program -/

section ConcaveKuhnTucker

variable {V X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {B : Y →ₗ[ℝ] X →ₗ[ℝ] ℝ} {G : Bifun Y V} {x : X}

/-- **Kuhn–Tucker vectors for a concave program**, the mirror of `KuhnTucker`: the `x` for which
`⨆ y (⟨y, x⟩ + sup G y)` is finite and equal to the optimal value `sup G 0`. -/
def ConcaveKuhnTucker (B : Y →ₗ[ℝ] X →ₗ[ℝ] ℝ) (G : Bifun Y V) : Set X :=
  {x | supBifun G 0 ≠ ⊤ ∧ supBifun G 0 ≠ ⊥ ∧
    (⨆ y, (((B y x : ℝ) : EReal) + supBifun G y)) = supBifun G 0}

/-- The concave mirror is the reflection of the convex notion: `x` is a Kuhn–Tucker vector of the
concave program `G` exactly when `-x` is one of the convex program `-G`. -/
theorem mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker :
    x ∈ ConcaveKuhnTucker B G ↔ -x ∈ KuhnTucker B (fun y v => -(G y v)) := by
  have hinf : ∀ y : Y, infBifun (fun y' v => -(G y' v)) y = -(supBifun G y) := fun y =>
    (congrFun (neg_supBifun G) y).symm
  have hkey : (⨅ y : Y, (((B y (-x) : ℝ) : EReal) + infBifun (fun y' v => -(G y' v)) y))
      = -(⨆ y : Y, (((B y x : ℝ) : EReal) + supBifun G y)) := by
    rw [EReal.neg_iSup]
    refine iInf_congr fun y => ?_
    have hb : ((B y (-x) : ℝ) : EReal) = -(((B y x : ℝ)) : EReal) := by
      rw [← _root_.EReal.coe_neg, map_neg]
    rw [hinf y, hb, _root_.EReal.neg_add (.inl (_root_.EReal.coe_ne_bot _))
      (.inl (_root_.EReal.coe_ne_top _))]
    rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hinf 0, ne_eq, _root_.EReal.neg_eq_top_iff]
      exact h2
    · rw [hinf 0, ne_eq, _root_.EReal.neg_eq_bot_iff]
      exact h1
    · rw [hkey, hinf 0, h3]
  · rintro ⟨h1, h2, h3⟩
    rw [hinf 0, ne_eq, _root_.EReal.neg_eq_top_iff] at h1
    rw [hinf 0, ne_eq, _root_.EReal.neg_eq_bot_iff] at h2
    rw [hkey, hinf 0] at h3
    exact ⟨h2, h1, neg_inj.1 h3⟩

end ConcaveKuhnTucker

section ConcaveKuhnTuckerNormal

variable {V X Y : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] {B : Y →ₗ[ℝ] X →ₗ[ℝ] ℝ}
  [IsCompatiblePairing B] {G : Bifun Y V}

/-- The concave mirror: a concave program possessing a Kuhn–Tucker vector is normal. Such a vector
is a supergradient of `sup G` at the origin, and a convex function agrees with its closure wherever
it is subdifferentiable. -/
theorem concaveNormal_of_concaveKuhnTucker_nonempty (hG : ConcaveBifun G)
    (h : (ConcaveKuhnTucker B G).Nonempty) : ConcaveNormal G := by
  obtain ⟨x, hx⟩ := h
  rw [mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker] at hx
  have ht := hx.1
  have hb := hx.2.1
  have hsub : -(-x) ∈ subgradient B (infBifun fun y v => -(G y v)) 0 :=
    (mem_kuhnTucker_iff_neg_mem_subgradient ht hb).1 hx
  rw [neg_neg] at hsub
  have hclosed : clFn (infBifun fun y v => -(G y v)) 0 = infBifun (fun y v => -(G y v)) 0 :=
    clFn_eq_of_mem_subgradient (B := B) (convexFn_infBifun (concaveFn_iff_convexFn_neg.1 hG)) hsub
  have hinf0 : infBifun (fun y v => -(G y v)) 0 = -(supBifun G 0) :=
    (congrFun (neg_supBifun G) 0).symm
  rw [concaveNormal_iff, clConcave_apply, neg_supBifun, hclosed, hinf0, neg_neg]

end ConcaveKuhnTuckerNormal

section DualKuhnTucker

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- If the *dual* program has a Kuhn–Tucker vector (its optimal value being finite, which is part
of `ConcaveKuhnTucker`), then normality holds for the pair. -/
theorem normal_of_concaveKuhnTucker_adjointBifun_nonempty (hF : ConvexBifun F)
    (hcl : ClosedBifun F)
    (h : (ConcaveKuhnTucker Bx.flip (adjointBifun Bu Bx F)).Nonempty) : Normal F :=
  (normal_iff_concaveNormal_adjointBifun hF hcl).2
    (concaveNormal_of_concaveKuhnTucker_nonempty (concaveBifun_adjointBifun Bu Bx F) h)

end DualKuhnTucker

/-! ### Polyhedral programs -/

section Polyhedral

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {F : Bifun U X}

/-- A polyhedral convex program that is merely *consistent* is normal: `inf F` is then polyhedral,
and a polyhedral convex function agrees with its closure throughout its effective domain, which
consistency places the origin in. -/
theorem PolyhedralBifun.normal (hF : PolyhedralBifun F) (hc : Consistent F) : Normal F := by
  have hdom : (0 : U) ∈ dom (infBifun F) := by
    rw [dom_infBifun]
    exact hc
  exact PolyhedralFn.clFn_eq_of_mem_dom hF.polyhedralFn_infBifun hdom

end Polyhedral

section ConcavePolyhedral

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] {G : Bifun Y V}

/-- A concave bifunction is **polyhedral** when its negative is: the mirror of
`PolyhedralBifun`. -/
def ConcavePolyhedralBifun (G : Bifun Y V) : Prop := PolyhedralBifun fun y v => -(G y v)

/-- The concave mirror: a consistent polyhedral concave program is normal. -/
theorem ConcavePolyhedralBifun.concaveNormal (hG : ConcavePolyhedralBifun G)
    (hc : ConcaveConsistent G) : ConcaveNormal G := by
  have hne : supBifun G 0 ≠ ⊥ := by
    have h0 : (0 : Y) ∈ domConcave (supBifun G) := by
      rw [domConcave_supBifun]
      exact hc
    exact (mem_domConcave.1 h0).ne'
  have hdom : (0 : Y) ∈ dom fun z => -(supBifun G z) := mem_dom.2 (by
    rw [lt_top_iff_ne_top, ne_eq, _root_.EReal.neg_eq_top_iff]
    exact hne)
  have hpoly : PolyhedralFn fun z : Y => -(supBifun G z) := by
    rw [neg_supBifun]
    exact PolyhedralBifun.polyhedralFn_infBifun hG
  rw [concaveNormal_iff, clConcave_apply, PolyhedralFn.clFn_eq_of_mem_dom hpoly hdom]
  exact neg_neg _

end ConcavePolyhedral

section DualPolyhedral

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- If the *dual* program is polyhedral and consistent then normality holds for the pair. -/
theorem normal_of_concavePolyhedral_adjointBifun (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hG : ConcavePolyhedralBifun (adjointBifun Bu Bx F))
    (hc : ConcaveConsistent (adjointBifun Bu Bx F)) : Normal F :=
  (normal_iff_concaveNormal_adjointBifun hF hcl).2
    (ConcavePolyhedralBifun.concaveNormal hG hc)

end DualPolyhedral

/-! ### The two optimal values as a `liminf` and a `limsup` -/

section ClConcaveLimsup

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {g : E → EReal}

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The mirror of `liminf_nhds_le`: a function is at most its own `limsup` along the neighbourhood
filter. -/
theorem le_limsup_nhds (g : E → EReal) (x : E) : g x ≤ Filter.limsup g (𝓝 x) := by
  have h := liminf_nhds_le (-g) x
  rw [_root_.EReal.liminf_neg, Pi.neg_apply] at h
  exact _root_.EReal.neg_le_neg_iff.1 h

/-- The concave mirror of `clFn_eq_liminf_or`: for concave `g` the concave closure at `x` is the
`limsup` of `g` at `x`, except when the left side is `+∞` and the right `-∞`. -/
theorem clConcave_eq_limsup_or (hg : ConcaveFn g) (x : E) :
    clConcave g x = Filter.limsup g (𝓝 x)
      ∨ (clConcave g x = ⊤ ∧ Filter.limsup g (𝓝 x) = ⊥) := by
  have hkey : Filter.liminf (fun z => -(g z)) (𝓝 x) = -(Filter.limsup g (𝓝 x)) :=
    _root_.EReal.liminf_neg
  rcases clFn_eq_liminf_or (concaveFn_iff_convexFn_neg.1 hg) x with heq | ⟨hbot, htop⟩
  · exact Or.inl (by rw [clConcave_apply, heq, hkey, neg_neg])
  · refine Or.inr ⟨by rw [clConcave_apply, hbot, _root_.EReal.neg_bot], ?_⟩
    rw [hkey] at htop
    exact _root_.EReal.neg_eq_top_iff.1 htop

end ClConcaveLimsup

section Liminf

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X}

/-- Unless *both* programs are inconsistent, `liminf_{u → 0} (inf F u) = sup F* 0`. The exception
is unavoidable: `cl (inf F)` and `liminf (inf F)` can differ only when the first is `-∞`, i.e. the
dual is inconsistent, and the second is `+∞`, which forces `inf F 0 = +∞`. -/
theorem liminf_infBifun_eq_iSup_adjointBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hF : ConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (adjointBifun Bu Bx F)) :
    Filter.liminf (infBifun F) (𝓝 (0 : U)) = ⨆ v : V, adjointBifun Bu Bx F 0 v := by
  rcases clFn_eq_liminf_or (convexFn_infBifun hF) (0 : U) with heq | ⟨hbot, htop⟩
  · rw [← heq, clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bu) Bx hF]
  · exfalso
    have hsup : (⨆ v : V, adjointBifun Bu Bx F 0 v) = ⊥ := by
      rw [← clFn_infBifun_zero_eq_iSup_adjointBifun (Bu := Bu) Bx hF]
      exact hbot
    have hinf : infBifun F 0 = ⊤ := by
      have hle := liminf_nhds_le (infBifun F) (0 : U)
      rw [htop] at hle
      exact top_le_iff.1 hle
    rw [infBifun_apply] at hinf
    rcases h with hc | hc
    · obtain ⟨x, hx⟩ := hc
      exact hx (iInf_eq_top.1 hinf x)
    · obtain ⟨v, hv⟩ := hc
      exact hv (iSup_eq_bot.1 hsup v)

end Liminf

section Limsup

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- Dually: unless both programs are inconsistent, `limsup_{y → 0} (sup F* y) = inf F 0`. -/
theorem limsup_supBifun_adjointBifun_eq (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (h : Consistent F ∨ ConcaveConsistent (adjointBifun Bu Bx F)) :
    Filter.limsup (supBifun (adjointBifun Bu Bx F)) (𝓝 (0 : Y)) = infBifun F 0 := by
  rcases clConcave_eq_limsup_or (concaveFn_supBifun (concaveBifun_adjointBifun Bu Bx F))
    (0 : Y) with heq | ⟨htop, hbot⟩
  · rw [← heq, clConcave_supBifun_adjointBifun_zero_eq hF hcl]
  · exfalso
    have hinf : infBifun F 0 = ⊤ := by
      rw [← clConcave_supBifun_adjointBifun_zero_eq (Bu := Bu) (Bx := Bx) hF hcl]
      exact htop
    have hsup : supBifun (adjointBifun Bu Bx F) 0 = ⊥ :=
      le_bot_iff.1 (hbot ▸ le_limsup_nhds (supBifun (adjointBifun Bu Bx F)) (0 : Y))
    rw [infBifun_apply] at hinf
    rw [supBifun_apply] at hsup
    rcases h with hc | hc
    · obtain ⟨x, hx⟩ := hc
      exact hx (iInf_eq_top.1 hinf x)
    · obtain ⟨v, hv⟩ := hc
      exact hv (iSup_eq_bot.1 hsup v)

end Limsup

/-! ### The dual assertion, and attainment of the primal infimum

The dual counterpart of "the Kuhn–Tucker vectors are the dual optimal solutions" comes last because
it needs both the concave Kuhn–Tucker vocabulary and the second-adjoint computation
`concaveAdjointBifun_zero_apply` introduced for the consistency criteria. -/

section ConcaveKuhnTuckerAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **The concave mirror of `mem_kuhnTucker_iff_adjointBifun_zero_eq`**: `x` is a Kuhn–Tucker vector
of the concave program `G` exactly when `sup G 0` is finite and the objective of the doubly-adjoint
program attains it at `x`. Note that `ConcaveKuhnTucker` pairs with `Bx.flip` where the adjoint
pairs with `Bx`. -/
theorem mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (G : Bifun Y V) (x : X) :
    x ∈ ConcaveKuhnTucker Bx.flip G
      ↔ supBifun G 0 ≠ ⊤ ∧ supBifun G 0 ≠ ⊥
        ∧ concaveAdjointBifun Bu Bx G 0 x = supBifun G 0 := by
  have h : concaveAdjointBifun Bu Bx G 0 x
      = ⨆ y, (((Bx.flip y x : ℝ) : EReal) + supBifun G y) := by
    rw [concaveAdjointBifun_zero_apply]
    exact iSup_congr fun y => by rw [LinearMap.flip_apply]
  rw [h]
  exact Iff.rfl

end ConcaveKuhnTuckerAdjoint

section DualAssertion

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {F : Bifun U X} {x : X}

/-- **The dual assertion**: under normality, `x` is a Kuhn–Tucker vector for `(P*)` exactly when it
is an optimal solution to `(P)`. The defining supremum of a concave Kuhn–Tucker vector is the
objective of the doubly-adjoint program, and `F** = F` turns that into `(F 0)(x)`; normality
identifies the two optimal values. -/
theorem mem_concaveKuhnTucker_adjointBifun_iff_mem_argmin (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hn : Normal F) (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    x ∈ ConcaveKuhnTucker Bx.flip (adjointBifun Bu Bx F) ↔ x ∈ argmin (F 0) := by
  have hval : supBifun (adjointBifun Bu Bx F) 0 = infBifun F 0 := by
    rw [supBifun_apply]
    exact (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).1 hn
  have hself : concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) 0 = F 0 :=
    congrFun (concaveAdjointBifun_adjointBifun_eq_self hF hcl) 0
  rw [mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq Bu Bx, hself, hval,
    mem_argmin_iff_eq_iInf, ← infBifun_apply]
  exact ⟨fun h => h.2.2, fun h => ⟨ht, hb, h⟩⟩

end DualAssertion

section Attainment

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip] {F : Bifun U X}

/-- **Attainment of the primal infimum**: if `(P)` is consistent and `(P*)` is strongly consistent,
the infimum of `(P)` is attained.

The route is through the convex program associated with `-F*`: that is a convex bifunction with no
hypothesis on `F`, strong consistency of `(P*)` is strong consistency of it, and its perturbation
function `-sup F*` is proper because the optimal values are finite. Strong consistency then
produces a Kuhn–Tucker vector for `-F*`, which the dual assertion above turns into a minimiser of
`F 0`. -/
theorem exists_infBifun_eq_of_concaveStronglyConsistent (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hc : Consistent F) (hbot : infBifun F 0 ≠ ⊥)
    (hs : ConcaveStronglyConsistent (adjointBifun Bu Bx F)) : ∃ x, F 0 x = infBifun F 0 := by
  have hnorm : Normal F := normal_of_concaveStronglyConsistent_adjointBifun hF hcl hs
  have hgap : supBifun (adjointBifun Bu Bx F) 0 = infBifun F 0 := by
    rw [supBifun_apply]
    exact (normal_iff_iSup_adjointBifun_eq (Bu := Bu) Bx hF).1 hnorm
  have htop : ∀ y, supBifun (adjointBifun Bu Bx F) y ≠ ⊤ :=
    (consistent_iff_forall_supBifun_ne_top (Bu := Bu) (Bx := Bx) hF hcl).1 hc
  have hinfneg : ∀ y, infBifun (fun y' v => -(adjointBifun Bu Bx F y' v)) y
      = -(supBifun (adjointBifun Bu Bx F) y) :=
    fun y => (congrFun (neg_supBifun (adjointBifun Bu Bx F)) y).symm
  have ht : infBifun (fun y' v => -(adjointBifun Bu Bx F y' v)) 0 ≠ ⊤ := by
    rw [hinfneg 0, hgap, ne_eq, _root_.EReal.neg_eq_top_iff]
    exact hbot
  have hp : Proper (infBifun fun y' v => -(adjointBifun Bu Bx F y' v)) := by
    refine ⟨⟨0, lt_top_iff_ne_top.2 ht⟩, fun y => ?_⟩
    rw [hinfneg y, ne_eq, _root_.EReal.neg_eq_bot_iff]
    exact htop y
  obtain ⟨w, hw⟩ := kuhnTucker_nonempty_of_stronglyConsistent (B := Bx.flip)
    (convexBifun_neg_adjointBifun Bu Bx F) hp
    (concaveStronglyConsistent_iff_stronglyConsistent_neg.1 hs) ht
  have hkt : -w ∈ ConcaveKuhnTucker Bx.flip (adjointBifun Bu Bx F) := by
    rw [mem_concaveKuhnTucker_iff_neg_mem_kuhnTucker, neg_neg]
    exact hw
  obtain ⟨-, -, heq⟩ :=
    (mem_concaveKuhnTucker_iff_concaveAdjointBifun_zero_eq Bu Bx _ (-w)).1 hkt
  have hself : concaveAdjointBifun Bu Bx (adjointBifun Bu Bx F) 0 = F 0 :=
    congrFun (concaveAdjointBifun_adjointBifun_eq_self hF hcl) 0
  exact ⟨-w, by rw [← hgap, ← heq, hself]⟩

end Attainment

end ConvexAnalysis
