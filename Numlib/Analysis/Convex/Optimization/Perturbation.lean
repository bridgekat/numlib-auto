import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Optimization.Minimum
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Subgradient.Existence
import Numlib.Analysis.Convex.Subgradient.Gradient

/-!
# Convex bifunctions and generalized convex programs

A *bifunction* `F : U → X → EReal` is a family of minimisation problems indexed by a perturbation
parameter `u`. The **generalized convex program** `(P)` associated with `F` is "minimise `F 0` over
`X`, with the perturbations `F u` on offer"; its **perturbation function** is
`inf F : u ↦ ⨅ x, F u x`, and its **Kuhn–Tucker vectors** are the prices at which no perturbation
is worth buying.

Everything rests on one identification: `inf F` is a partial minimisation of the graph function,
hence convex, and `v` is a Kuhn–Tucker vector exactly when `-v ∈ ∂(inf F)(0)`. The Kuhn–Tucker set
is a reflected subdifferential, so the whole subgradient theory transfers wholesale: existence
under strong consistency, compactness under strict consistency, the directional-derivative
formulas, the polyhedral case.

## Main definitions

* `Bifun U X` — a bifunction; `graphFn F` is the same data on `U × X`, `ConvexBifun F` and
  `PolyhedralBifun F` are convexity and polyhedrality of it.
* `infBifun F`, `domBifun F` — the perturbation function and the effective domain `{u | F u ≢ ⊤}`.
* `KuhnTucker B F` — the `v` for which `⨅ u (⟨u, v⟩ + inf F u)` is finite and equal to `inf F 0`.
* `Consistent`, `StronglyConsistent`, `StrictlyConsistent` — `0 ∈ dom F`, `0 ∈ ri (dom F)`,
  `0 ∈ int (dom F)`.

## Main results

* `convexFn_infBifun`, `dom_infBifun`, `mem_kuhnTucker_iff_neg_mem_subgradient` — `inf F` is
  convex with effective domain `dom F`, and `∂(inf F)(0)` is the reflected Kuhn–Tucker set
  (Theorem 29.1 in [^1]).
* `kuhnTucker_eq_neg_subgradient`, `convex_kuhnTucker`, `isClosed_kuhnTucker`,
  `supportFn_kuhnTucker` — the Kuhn–Tucker set is closed convex with a computable support function;
  `kuhnTucker_eq_empty_iff` — when it is empty; `kuhnTucker_eq_singleton_of_hasGradientAtFn` — when
  it is one vector; `kuhnTucker_nonempty_of_stronglyConsistent`, `dirDeriv_infBifun_eq` — existence
  and the directional-derivative formula.
* `isCompact_kuhnTucker_of_strictlyConsistent`, `continuousOn_infBifun_interior` — what strict
  consistency buys; `infBifun_eq_bot_of_mem_relint` — an improper `inf F` is `-∞` on `ri (dom F)`.
* `PolyhedralBifun.polyhedralFn_infBifun`, `kuhnTucker_nonempty_of_polyhedralBifun`,
  `argmin_nonempty_of_polyhedralBifun` and companions — the polyhedral case (Theorem 29.2 in [^1]).

## Implementation notes

`KuhnTucker` is the book's own definition, not the subdifferential characterisation: the inequality
form `inf F 0 ≤ ⟨u, v⟩ + inf F u` is a consequence, and defining `KuhnTucker` by it would have made
that characterisation an `Iff.rfl`. The boundedness clause under strict consistency is
finite-dimensional in `V`: pairing-boundedness is all a general dual pair supports, and a norm
bound needs a coordinate estimate against a finite basis.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §29.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Bifunctions and the perturbation function -/

section Defs

variable {U X : Type*}

/-- A **bifunction** from `U` to `X`: a family of `EReal`-valued functions on `X` indexed by a
perturbation parameter in `U`. The program `(P)` is identified with `F` itself. -/
abbrev Bifun (U X : Type*) := U → X → EReal

/-- The **graph function** of a bifunction: the same data as a function on `U × X`. Every convexity
statement about `F` is one about `graphFn F`. -/
def graphFn (F : Bifun U X) : U × X → EReal := fun p => F p.1 p.2

@[simp] theorem graphFn_apply (F : Bifun U X) (u : U) (x : X) : graphFn F (u, x) = F u x := rfl

/-- **The inverse `F_*` of a bifunction**: `(F_* x) u = -(F u)(x)`. Unlike `flipBifun` it also
changes the sign, so it carries convex bifunctions to concave ones and back; it is involutory, and
composition of bifunctions is built on it. The sign flip is what makes
`(Ff)(x) = ⨅ (f - F_* x)` agree with `⨅ u, f u + (F u)(x)`. -/
noncomputable def inverseBifun (F : Bifun U X) : Bifun X U := fun x u => -(F u x)

@[simp] theorem inverseBifun_apply (F : Bifun U X) (x : X) (u : U) :
    inverseBifun F x u = -(F u x) := rfl

/-- **The inverse operation is involutory**: `(F_*)_* = F`. -/
@[simp] theorem inverseBifun_inverseBifun (F : Bifun U X) :
    inverseBifun (inverseBifun F) = F :=
  funext fun u => funext fun x => neg_neg (F u x)

theorem graphFn_inverseBifun (F : Bifun U X) (q : X × U) :
    graphFn (inverseBifun F) q = -(graphFn F (q.2, q.1)) := rfl

/-- The **perturbation function** `inf F`; its value at `0` is the optimal value of `(P)`. -/
noncomputable def infBifun (F : Bifun U X) : U → EReal := fun u => ⨅ x, F u x

theorem infBifun_apply (F : Bifun U X) (u : U) : infBifun F u = ⨅ x, F u x := rfl

/-- The **effective domain** of a bifunction: the perturbations for which `F u` is not identically
`⊤`. -/
def domBifun (F : Bifun U X) : Set U := {u | ∃ x, F u x ≠ ⊤}

@[simp] theorem mem_domBifun {F : Bifun U X} {u : U} :
    u ∈ domBifun F ↔ ∃ x, F u x ≠ ⊤ := Iff.rfl

/-- The effective domain of the perturbation function is the effective domain of `F`. -/
theorem dom_infBifun (F : Bifun U X) : dom (infBifun F) = domBifun F := by
  ext u
  constructor
  · intro h
    by_contra hcon
    have hall : ∀ x, F u x = ⊤ := fun x => by
      by_contra hx
      exact hcon ⟨x, hx⟩
    have htop : (⨅ x, F u x) = ⊤ := le_antisymm le_top (le_iInf fun x => (hall x).ge)
    rw [mem_dom, infBifun_apply, htop] at h
    exact absurd h (lt_irrefl ⊤)
  · rintro ⟨x, hx⟩
    exact mem_dom.2 (lt_of_le_of_lt (iInf_le _ x) (lt_top_iff_ne_top.2 hx))

end Defs

/-! ### Convexity -/

section Convex

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- A bifunction is **convex** when its graph function is a convex function on `U × X`. -/
def ConvexBifun (F : Bifun U X) : Prop := ConvexFn (graphFn F)

theorem convexBifun_iff : ConvexBifun F ↔ ConvexFn (graphFn F) := Iff.rfl

/-- The perturbation function of a convex bifunction is convex: a partial minimisation of the
jointly convex graph function along the projection `(u, x) ↦ u`. -/
theorem convexFn_infBifun (hF : ConvexBifun F) : ConvexFn (infBifun F) :=
  convexFn_iInf_right hF

/-- Each image `F u` of a convex bifunction is a convex function: a slice of a jointly convex
function, since `a * u + b * u = u` when `a + b = 1`. -/
theorem ConvexBifun.convexFn_apply (hF : ConvexBifun F) (u : U) : ConvexFn (F u) := by
  refine convexFn_of_epi_combo fun x y mu nu hx hy a b ha hb hab => ?_
  have h := hF.epi_combo (x := (u, x)) (y := (u, y)) hx hy ha hb hab
  have hu : a • (u, x) + b • (u, y) = (u, a • x + b • y) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hu] at h

/-- The effective domain of a convex bifunction is convex — it is `dom (inf F)`. -/
theorem convex_domBifun (hF : ConvexBifun F) : Convex ℝ (domBifun F) := by
  rw [← dom_infBifun]
  exact ConvexFn.convex_dom (convexFn_infBifun hF)

end Convex

/-! ### Consistency -/

section Consistency

variable {U X : Type*} [AddCommGroup U] {F : Bifun U X}

/-- `(P)` is **consistent** when it has a feasible solution, i.e. when its optimal value is
`< ⊤`. -/
def Consistent (F : Bifun U X) : Prop := (0 : U) ∈ domBifun F

theorem consistent_iff : Consistent F ↔ ∃ x, F 0 x ≠ ⊤ := Iff.rfl

end Consistency

section ConsistencyTopology

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {F : Bifun U X}

/-- `(P)` is **strongly consistent** when `0` is a *relative interior* point of `dom F`: the
qualification behind the existence of Kuhn–Tucker vectors. -/
def StronglyConsistent (F : Bifun U X) : Prop := (0 : U) ∈ ri (domBifun F)

/-- `(P)` is **strictly consistent** when `0` is an interior point of `dom F`. -/
def StrictlyConsistent (F : Bifun U X) : Prop := (0 : U) ∈ interior (domBifun F)

theorem StrictlyConsistent.stronglyConsistent (h : StrictlyConsistent F) :
    StronglyConsistent F :=
  interior_subset_intrinsicInterior h

theorem StronglyConsistent.consistent (h : StronglyConsistent F) : Consistent F :=
  intrinsicInterior_subset h

end ConsistencyTopology

/-! ### Kuhn–Tucker vectors -/

section KuhnTucker

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V}

/-- **Kuhn–Tucker vectors** for the program associated with `F`: the prices `v` at which
`⨅ u (⟨u, v⟩ + inf F u)` is finite and equal to the optimal value `inf F 0`. -/
def KuhnTucker (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : Set V :=
  {v | infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) = infBifun F 0}

/-- Evaluating at `u = 0`: the infimum defining a Kuhn–Tucker vector never exceeds `inf F 0`. -/
theorem iInf_add_infBifun_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ u, (((B u v : ℝ) : EReal) + infBifun F u)) ≤ infBifun F 0 := by
  refine le_trans (iInf_le _ 0) (le_of_eq ?_)
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_add]

/-- A Kuhn–Tucker vector is a price at which every perturbation costs at least what it saves. -/
theorem mem_kuhnTucker_iff_forall_le :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      ∀ u, infBifun F 0 ≤ ((B u v : ℝ) : EReal) + infBifun F u := by
  constructor
  · rintro ⟨ht, hb, heq⟩
    refine ⟨ht, hb, fun u => ?_⟩
    rw [← heq]
    exact iInf_le _ u
  · rintro ⟨ht, hb, hall⟩
    exact ⟨ht, hb, le_antisymm (iInf_add_infBifun_le B F v) (le_iInf hall)⟩

/-- Moving a real constant across an `EReal` inequality. -/
private theorem coe_add_neg_le_iff {c p : ℝ} {w : EReal} :
    (c : EReal) + ((-p : ℝ) : EReal) ≤ w ↔ (c : EReal) ≤ (p : EReal) + w := by
  induction w with
  | bot => simp
  | coe q =>
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith
  | top => simp

/-- When the optimal value is finite, the Kuhn–Tucker vectors are exactly the `v` with
`-v ∈ ∂(inf F)(0)`. The subgradient inequality at `0` in the direction `-v` says precisely that no
perturbation is worth buying at the price `v`. -/
theorem mem_kuhnTucker_iff_neg_mem_subgradient (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    v ∈ KuhnTucker B F ↔ -v ∈ subgradient B (infBifun F) 0 := by
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hiff : ∀ u : U, (infBifun F 0 ≤ ((B u v : ℝ) : EReal) + infBifun F u)
      ↔ (infBifun F 0 + ((B (u - 0) (-v) : ℝ) : EReal) ≤ infBifun F u) := by
    intro u
    rw [sub_zero, map_neg, hc]
    exact coe_add_neg_le_iff.symm
  rw [mem_kuhnTucker_iff_forall_le, mem_subgradient]
  exact ⟨fun h u => (hiff u).1 (h.2.2 u), fun h => ⟨ht, hb, fun u => (hiff u).2 (h u)⟩⟩

/-- The same as an equation between sets: the Kuhn–Tucker set is the reflected subdifferential of
the perturbation function at the origin. -/
theorem kuhnTucker_eq_neg_subgradient (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker B F = -(subgradient B (infBifun F) 0) := by
  ext v
  rw [Set.mem_neg]
  exact mem_kuhnTucker_iff_neg_mem_subgradient ht hb

/-- The Kuhn–Tucker vectors form a convex set. -/
theorem convex_kuhnTucker (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) :
    Convex ℝ (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subgradient ht hb]
  exact (convex_subgradient B (infBifun F) 0).neg

end KuhnTucker

/-! ### Closedness and existence -/

section Topology

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- The Kuhn–Tucker vectors form a closed set. -/
theorem isClosed_kuhnTucker [IsContinuousPairing B.flip] (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : IsClosed (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subgradient ht hb]
  exact (isClosed_subgradient (B := B) (infBifun F) 0).neg

end Topology

section Existence

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- A strongly consistent convex program whose perturbation function is proper has a Kuhn–Tucker
vector: `inf F` is subdifferentiable at the origin, a relative-interior point of its domain. -/
theorem kuhnTucker_nonempty_of_stronglyConsistent [IsCompatiblePairing B] (hF : ConvexBifun F)
    (hp : Proper (infBifun F)) (hs : StronglyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    (KuhnTucker B F).Nonempty := by
  have hri : (0 : U) ∈ ri (dom (infBifun F)) := by rwa [dom_infBifun]
  obtain ⟨y, hy⟩ :=
    subgradient_nonempty_of_mem_relint_dom (B := B) (convexFn_infBifun hF) hp hri
  refine ⟨-y, ?_⟩
  rw [mem_kuhnTucker_iff_neg_mem_subgradient ht (hp.ne_bot 0), neg_neg]
  exact hy

end Existence

/-! ### The directional derivative of the perturbation function -/

section DirDeriv

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- The support function of a reflected set is the support function read at the reflected
point. -/
theorem supportFn_neg_set (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (s : Set U) (v : V) :
    supportFn B (-s) v = supportFn B s (-v) := by
  rw [supportFn_apply, supportFn_apply]
  refine le_antisymm (iSup₂_le fun u hu => ?_) (iSup₂_le fun u hu => ?_)
  · have hmem : -u ∈ s := hu
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun w (_ : w ∈ s) => ((B w (-v) : ℝ) : EReal)) (-u) hmem)
    simp
  · have hmem : -u ∈ -s := by
      rw [Set.mem_neg, neg_neg]
      exact hu
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun w (_ : w ∈ -s) => ((B w v : ℝ) : EReal)) (-u) hmem)
    simp

omit [AddCommGroup X] [Module ℝ X] in
/-- `(inf F)'(0; ·)` is positively homogeneous, for every bifunction. -/
theorem posHomogeneous_dirDeriv_infBifun (F : Bifun U X) :
    PosHomogeneous (dirDeriv (infBifun F) 0) :=
  posHomogeneous_dirDeriv _ _

/-- `(inf F)'(0; ·)` is convex in the direction when `inf F 0` is finite. -/
theorem convexFn_dirDeriv_infBifun (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : ConvexFn (dirDeriv (infBifun F) 0) :=
  convexFn_dirDeriv (convexFn_infBifun hF) ht hb

end DirDeriv

section DirDerivSupport

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace U] [IsTopologicalAddGroup U]
  [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {F : Bifun U X}

/-- The support function of the Kuhn–Tucker set is the closure of `u ↦ (inf F)'(0; -u)`: the
support function of a subdifferential, composed with the reflection. -/
theorem supportFn_kuhnTucker (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (u : U) :
    supportFn B.flip (KuhnTucker B F) u = clFn (dirDeriv (infBifun F) 0) (-u) := by
  rw [kuhnTucker_eq_neg_subgradient ht hb, supportFn_neg_set,
    clFn_dirDeriv (B := B) (convexFn_infBifun hF) ht hb]

end DirDerivSupport

/-! ### The improper and the empty case -/

section Improper

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [AddCommGroup V]
  [Module ℝ V] [AddCommGroup X] [Module ℝ X] in
/-- Off `dom F` the optimal value is `+∞`. -/
theorem infBifun_eq_top_of_notMem_domBifun {u : U} (hu : u ∉ domBifun F) : infBifun F u = ⊤ := by
  by_contra h
  exact hu (by rw [← dom_infBifun]; exact mem_dom.2 (lt_of_le_of_ne le_top h))

omit [FiniteDimensional ℝ U] [AddCommGroup V] [Module ℝ V] in
/-- If some perturbation drives the optimal value to `-∞`, so does every perturbation in
`ri (dom F)`: an improper convex function is `-∞` throughout the relative interior of its
domain. -/
theorem infBifun_eq_bot_of_mem_relint (hF : ConvexBifun F) (h : ∃ u, infBifun F u = ⊥) {u : U}
    (hu : u ∈ ri (domBifun F)) : infBifun F u = ⊥ := by
  obtain ⟨u₀, hu₀⟩ := h
  have hp : ¬ Proper (infBifun F) := fun hp => hp.ne_bot u₀ hu₀
  refine ConvexFn.eq_bot_of_mem_relint_dom (convexFn_infBifun hF) hp ?_
  rwa [dom_infBifun]

end Improper

section KuhnTuckerEmpty

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {F : Bifun U X}

/-- A convex program with a finite optimal value has no Kuhn–Tucker vector exactly when some
direction of perturbation makes the two-sided directional derivative `-∞`,
`(inf F)'(0; u) = -(inf F)'(0; -u) = -∞`. Forwards: an empty subdifferential makes
`cl (inf F)'(0; ·)` the constant `-∞`, and the closure of a proper convex function is proper. -/
theorem kuhnTucker_eq_empty_iff (hF : ConvexBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker B F = ∅ ↔
      ∃ u : U, dirDeriv (infBifun F) 0 u = ⊥ ∧ dirDeriv (infBifun F) 0 (-u) = ⊤ := by
  have hconv := convexFn_infBifun hF
  constructor
  · intro hempty
    have h1 : -(subgradient B (infBifun F) 0) = ∅ := by
      rw [← kuhnTucker_eq_neg_subgradient ht hb]
      exact hempty
    have hsub : subgradient B (infBifun F) 0 = ∅ := by
      rw [← neg_neg (subgradient B (infBifun F) 0), h1]
      simp
    have hcl : clFn (dirDeriv (infBifun F) 0) = fun _ => (⊥ : EReal) := by
      rw [clFn_dirDeriv (B := B) hconv ht hb, hsub, supportFn_empty]
    have hnp : ¬ Proper (dirDeriv (infBifun F) 0) := by
      intro hp
      have hpc := ConvexFn.proper_clFn (convexFn_dirDeriv hconv ht hb) hp
      rw [hcl] at hpc
      exact hpc.ne_bot 0 rfl
    have hdom : (dom (dirDeriv (infBifun F) 0)).Nonempty :=
      ⟨0, mem_dom.2 (by rw [dirDeriv_zero ht hb]; exact EReal.zero_lt_top)⟩
    have hy : ∃ u, dirDeriv (infBifun F) 0 u = ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hnp ⟨hdom, hcon⟩
    obtain ⟨u, hub⟩ := hy
    refine ⟨u, hub, ?_⟩
    have hle := neg_dirDeriv_neg_le hconv ht hb u
    rw [hub, le_bot_iff, EReal.neg_eq_bot_iff] at hle
    exact hle
  · rintro ⟨u, hu, -⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro v hv
    rw [mem_kuhnTucker_iff_neg_mem_subgradient ht hb,
      mem_subgradient_iff_le_dirDeriv ht hb] at hv
    have hcontra := hv u
    rw [hu, le_bot_iff] at hcontra
    exact absurd hcontra (EReal.coe_ne_bot _)

end KuhnTuckerEmpty

/-! ### What consistency and differentiability buy -/

section Consistency

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup X] [Module ℝ X] {F : Bifun U X}

omit [FiniteDimensional ℝ U] in
/-- A strongly consistent convex program whose optimal value is `> -∞` has a proper perturbation
function: an improper `inf F` would be `-∞` throughout `ri (dom F)`. -/
theorem proper_infBifun_of_stronglyConsistent (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hb : infBifun F 0 ≠ ⊥) : Proper (infBifun F) := by
  refine ⟨⟨0, ?_⟩, fun u => ?_⟩
  · rw [dom_infBifun]
    exact StronglyConsistent.consistent hs
  · exact fun hcon => hb (infBifun_eq_bot_of_mem_relint hF ⟨u, hcon⟩ hs)

/-- Under strict consistency the optimal value is finite and continuous on `int (dom F)`, a
neighbourhood of the origin. -/
theorem continuousOn_infBifun_interior (hF : ConvexBifun F) (hp : Proper (infBifun F)) :
    ContinuousOn (infBifun F) (interior (domBifun F)) := by
  have hsub : interior (domBifun F) ⊆ ri (dom (infBifun F)) := by
    rw [dom_infBifun]
    exact interior_subset_intrinsicInterior
  exact ContinuousOn.mono ((convexFn_infBifun hF).continuousOn_relint_dom hp) hsub

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [AddCommGroup X]
  [Module ℝ X] in
/-- The optimal value is finite at every point of `dom F`. -/
theorem infBifun_ne_top_of_mem_domBifun {u : U} (hu : u ∈ domBifun F) : infBifun F u ≠ ⊤ := by
  rw [← dom_infBifun] at hu
  exact (mem_dom.1 hu).ne

end Consistency

section DirDerivFormula

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {F : Bifun U X}

/-- **The derivative formula**: for a strongly consistent program with a proper perturbation
function, `(inf F)'(0; u) = δ*(-u | U*)`, the support function of the Kuhn–Tucker set read at the
reflected direction. -/
theorem dirDeriv_infBifun_eq (hF : ConvexBifun F) (hp : Proper (infBifun F))
    (hs : StronglyConsistent F) (u : U) :
    dirDeriv (infBifun F) 0 u = supportFn B.flip (KuhnTucker B F) (-u) := by
  have hri : (0 : U) ∈ ri (dom (infBifun F)) := by rwa [dom_infBifun]
  have ht : infBifun F 0 ≠ ⊤ := (mem_dom.1 (intrinsicInterior_subset hri)).ne
  rw [kuhnTucker_eq_neg_subgradient ht (hp.ne_bot 0), supportFn_neg_set, neg_neg,
    dirDeriv_eq_supportFn_of_mem_relint_dom (B := B) (convexFn_infBifun hF) hp hri]

/-- Under *strict* consistency the Kuhn–Tucker set is bounded in the pairing sense: every
`⟨u, ·⟩` is bounded above on it. -/
theorem bddAbove_kuhnTucker_of_strictlyConsistent (hF : ConvexBifun F) (hp : Proper (infBifun F))
    (hs : StrictlyConsistent F) (u : U) :
    ∃ c : ℝ, ∀ v ∈ KuhnTucker B F, B u v ≤ c := by
  have hint : (0 : U) ∈ interior (dom (infBifun F)) := by rwa [dom_infBifun]
  have hri : (0 : U) ∈ ri (dom (infBifun F)) := interior_subset_intrinsicInterior hint
  have ht : infBifun F 0 ≠ ⊤ := (mem_dom.1 (intrinsicInterior_subset hri)).ne
  obtain ⟨c, hc⟩ :=
    (bddAbove_subgradient_iff_mem_interior_dom (B := B) (convexFn_infBifun hF) hp hri).2 hint (-u)
  refine ⟨c, fun v hv => ?_⟩
  rw [kuhnTucker_eq_neg_subgradient ht (hp.ne_bot 0), Set.mem_neg] at hv
  have hb := hc (-v) hv
  simpa using hb

end DirDerivFormula

section KuhnTuckerCompact

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup X] [Module ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {F : Bifun U X}

/-- Under *strict* consistency the Kuhn–Tucker set is bounded in the norm. The upgrade from
pairing-boundedness is finite-dimensional. -/
theorem isBounded_kuhnTucker_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : Proper (infBifun F)) (hs : StrictlyConsistent F) :
    Bornology.IsBounded (KuhnTucker B F) := by
  rw [isBounded_iff_forall_bddAbove (B := B.flip)]
  intro u
  simpa using bddAbove_kuhnTucker_of_strictlyConsistent (B := B) hF hp hs u

/-- Under *strict* consistency the Kuhn–Tucker set is compact — closed and bounded, hence compact
by Heine–Borel. With nonemptiness and convexity this is the book's "non-empty closed bounded convex
set". -/
theorem isCompact_kuhnTucker_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : Proper (infBifun F)) (hs : StrictlyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    IsCompact (KuhnTucker B F) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_kuhnTucker ht (hp.ne_bot 0))
    (isBounded_kuhnTucker_of_strictlyConsistent hF hp hs)

omit [FiniteDimensional ℝ V] [IsCompatiblePairing B.flip] in
/-- A strictly consistent program is strongly consistent, so it has a Kuhn–Tucker vector. -/
theorem kuhnTucker_nonempty_of_strictlyConsistent (hF : ConvexBifun F)
    (hp : Proper (infBifun F)) (hs : StrictlyConsistent F) (ht : infBifun F 0 ≠ ⊤) :
    (KuhnTucker B F).Nonempty :=
  kuhnTucker_nonempty_of_stronglyConsistent (B := B) hF hp hs.stronglyConsistent ht

end KuhnTuckerCompact

section KuhnTuckerUnique

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

omit [AddCommGroup X] [Module ℝ X] in
/-- **Algebraic form**: if `(inf F)'(0; ·)` is the linear function `⟨·, -v₀⟩` then `v₀` is the
unique Kuhn–Tucker vector. -/
theorem kuhnTucker_eq_singleton_of_dirDeriv_eq (hsep : Function.Injective B.flip)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) {v₀ : V}
    (h : ∀ u : U, dirDeriv (infBifun F) 0 u = ((B u (-v₀) : ℝ) : EReal)) :
    KuhnTucker B F = {v₀} := by
  rw [kuhnTucker_eq_neg_subgradient ht hb,
    subgradient_eq_singleton_of_dirDeriv_eq hsep ht hb h]
  simp

end KuhnTuckerUnique

section KuhnTuckerGradient

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [AddCommGroup X] [Module ℝ X]
  {F : Bifun U X}

/-- **Fréchet form**: where the perturbation function is differentiable, the program has exactly
one Kuhn–Tucker vector, namely `-∇(inf F)(0)`. -/
theorem kuhnTucker_eq_singleton_of_hasGradientAtFn (hF : ConvexBifun F)
    {f' : StrongDual ℝ U} (h : HasGradientAtFn (infBifun F) f' 0) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) :
    KuhnTucker (topDualPairing ℝ U).flip F = {-f'} := by
  rw [kuhnTucker_eq_neg_subgradient ht hb, HasGradientAtFn.subgradient_eq (convexFn_infBifun hF) h]
  simp

end KuhnTuckerGradient

/-! ### Polyhedral convex programs -/

section PolyhedralImage

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f : E → EReal}

/-- A polyhedral convex function agrees with its closure throughout its effective domain: if proper
it *is* closed, and otherwise both are `-∞` there. -/
theorem PolyhedralFn.clFn_eq_of_mem_dom (hf : PolyhedralFn f) {x : E} (hx : x ∈ dom f) :
    clFn f x = f x := by
  by_cases hp : Proper f
  · exact congrFun (hf.closedFn hp.ne_bot) x
  · have hbot : f x = ⊥ :=
      ConvexFn.eq_bot_of_mem_closure_dom hf.convexFn hf.lowerSemicontinuous hp (subset_closure hx)
    have hl : lscHull f x = ⊥ := le_bot_iff.1 (hbot ▸ lscHull_le f x)
    rw [clFn_of_exists_eq_bot ⟨x, hl⟩, hbot]

end PolyhedralImage

section PolyhedralBifun

variable {U V X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X}

/-- A convex bifunction is **polyhedral** when its graph function is; the associated program is then
a *polyhedral convex program*. -/
def PolyhedralBifun (F : Bifun U X) : Prop := PolyhedralFn (graphFn F)

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
theorem polyhedralBifun_iff : PolyhedralBifun F ↔ PolyhedralFn (graphFn F) := Iff.rfl

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
theorem PolyhedralBifun.convexBifun (hF : PolyhedralBifun F) : ConvexBifun F :=
  PolyhedralFn.convexFn hF

omit [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ X] in
/-- Every image `F u` of a polyhedral convex bifunction — the objective `F 0` in particular — is a
polyhedral convex function. -/
theorem PolyhedralBifun.polyhedralFn_apply (hF : PolyhedralBifun F) (u : U) :
    PolyhedralFn (F u) := by
  have hpre : epi (F u)
      = (fun p : X × ℝ => ((LinearMap.inr ℝ U X).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) p
          + ((u, (0 : X)), (0 : ℝ))) ⁻¹' epi (graphFn F) := by
    ext p
    simp [graphFn]
  change Polyhedral (epi (F u))
  rw [hpre]
  exact Polyhedral.comap_affine hF _ _

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The perturbation function of a polyhedral convex program is polyhedral: a partial minimisation
of a polyhedral function along the projection `(u, x) ↦ u`. -/
theorem PolyhedralBifun.polyhedralFn_infBifun (hF : PolyhedralBifun F) :
    PolyhedralFn (infBifun F) := by
  have h : infBifun F = mapLin (LinearMap.fst ℝ U X) (graphFn F) := by
    funext u
    rw [mapLin_fst_apply, infBifun_apply]
    rfl
  rw [h]
  exact polyhedralFn_mapLin hF _

omit [FiniteDimensional ℝ V] in
/-- A polyhedral convex program with a finite optimal value has a Kuhn–Tucker vector: a polyhedral
convex function is subdifferentiable throughout its effective domain. -/
theorem kuhnTucker_nonempty_of_polyhedralBifun [IsCompatiblePairing B] (hF : PolyhedralBifun F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) : (KuhnTucker B F).Nonempty := by
  obtain ⟨y, hy⟩ :=
    subgradient_nonempty_of_polyhedralFn (B := B) hF.polyhedralFn_infBifun ht hb
  exact ⟨-y, by rw [mem_kuhnTucker_iff_neg_mem_subgradient ht hb, neg_neg]; exact hy⟩

/-- The Kuhn–Tucker vectors of a polyhedral convex program with a finite optimal value form a
polyhedral convex set. -/
theorem polyhedral_kuhnTucker_of_polyhedralBifun (hF : PolyhedralBifun F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) : Polyhedral (KuhnTucker B F) := by
  rw [kuhnTucker_eq_neg_subgradient ht hb]
  exact Polyhedral.neg
    (polyhedral_subgradient_of_polyhedralFn (B := B) hF.polyhedralFn_infBifun ht hb)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ U] in
/-- A polyhedral convex program whose optimal value is not `-∞` has an **optimal solution**. The
book assumes the optimal value finite; only `inf F 0 ≠ -∞` is used here, an optimal value of `+∞`
meaning every point is optimal. Finiteness is what the polyhedrality of the minimum set below
needs. -/
theorem argmin_nonempty_of_polyhedralBifun (hF : PolyhedralBifun F) (hb : infBifun F 0 ≠ ⊥) :
    (argmin (F 0)).Nonempty := by
  refine argmin_nonempty_of_polyhedralFn (hF.polyhedralFn_apply 0) ?_
  have h : (⨅ x, F 0 x) = infBifun F 0 := (infBifun_apply F 0).symm
  rw [h]
  exact lt_of_le_of_ne bot_le (Ne.symm hb)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ U] in
/-- The optimal solutions of a polyhedral convex program with a finite optimal value form a
polyhedral convex set — a sublevel set of `F 0` at the optimal value. -/
theorem polyhedral_argmin_of_polyhedralBifun (hF : PolyhedralBifun F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) : Polyhedral (argmin (F 0)) := by
  obtain ⟨x, hx⟩ := argmin_nonempty_of_polyhedralBifun hF hb
  have hval : F 0 x = infBifun F 0 := by
    rw [infBifun_apply]
    exact le_antisymm (le_iInf hx) (iInf_le _ x)
  have hb' : F 0 x ≠ ⊥ := by rw [hval]; exact hb
  have ht' : F 0 x < ⊤ := by rw [hval]; exact lt_top_iff_ne_top.2 ht
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb' ht'
  rw [argmin_eq_setOf_le hx hμ]
  exact (hF.polyhedralFn_apply 0).polyhedral_sublevel μ

end PolyhedralBifun

end ConvexAnalysis
