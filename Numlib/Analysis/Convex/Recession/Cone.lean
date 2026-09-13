import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Normed.Affine.AsymptoticCone
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Recession cones and lineality spaces

The *recession cone* `0⁺C` of a set `C` collects the directions in which `C` recedes: the `y` such
that every half-line `{x + a • y | a ≥ 0}` issuing from a point of `C` stays inside `C`. The
*lineality space* is the largest subspace it contains, `0⁺C ∩ (-0⁺C)`, the directions in which `C`
is linear. Most of the theory is algebraic; closedness of `0⁺C` and the limit descriptions need
only a real topological vector space, and finite dimensionality enters only for boundedness.

## Main definitions

* `recessionCone C`, `recessionPointedCone C` — `0⁺C`, bare and as a `PointedCone ℝ E`.
* `linealitySpace C`, `linealitySubmodule C`, `lineality C` — the lineality space, bare, as a
  `Submodule ℝ E`, and its dimension.

## Main results

* `recessionCone_eq_add_subset` — for convex `C`, `0⁺C = {y | C + y ⊆ C}`. That `0⁺C` is a convex
  cone containing the origin needs no hypothesis (`recessionPointedCone`).
* `recessionCone_setOf_forall_le` — the recession cone of a system of weak linear inequalities is
  the homogeneous system; `recessionCone_coe_affineSubspace` does the same for affine sets.
* `eq_add_inter_of_isCompl` — the decomposition `C = L + (C ∩ L')` for a complement `L'` of `L`.
* `isClosed_recessionCone` — `0⁺C` is closed as soon as `C` is; no convexity, no nonemptiness.
* `mem_recessionCone_iff_exists_tendsto` — for nonempty closed convex `C`, `0⁺C` is the set of
  limits of sequences `lᵢ • xᵢ` with `xᵢ ∈ C` and `lᵢ ↓ 0` ([rockafellar1970convex] Theorem 8.2).
* `mem_recessionCone_of_exists_ray` — one half-line in the direction `y` inside a closed convex
  `C` forces all of them ([rockafellar1970convex] Theorem 8.3); `recessionCone_iInter` and
  `recessionCone_preimage` carry that to intersections and preimages, and `recessionCone_prod`,
  `recessionCone_pi` say that a nonempty product recedes coordinatewise.
* `isBounded_iff_recessionCone_eq_zero` — a nonempty closed convex set is bounded exactly when it
  recedes in no direction, and `isBounded_inter_of_direction_eq` moves that along parallel slices.
* `iInter_recessionCone_eq_zero_iff_exists_isBounded` — the recession hypothesis of Helly's
  theorem: for closed convex sets with the finite-intersection property, "no common direction of
  recession" holds exactly when some finite subfamily is bounded.

## Implementation notes

Mathlib's `asymptoticCone ℝ C` is not `0⁺C`: it is always closed and is empty for `C = ∅`, and
what it computes is `0⁺(cl C)` (`recessionCone_closure_eq_asymptoticCone`; the two agree for
nonempty closed convex sets). `0⁺C` itself is algebraic, and is used where there is no topology.

## References

* [rockafellar1970convex] §8 and §21.
-/

open Bornology Filter Pointwise Set Topology

namespace ConvexAnalysis

/-! ### The definitions and their algebraic structure -/

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {x y z : E} {a : ℝ}

/-- The recession cone `0⁺C`: the directions in which `C` recedes.

`y ∈ 0⁺C` when every half-line `{x + a • y | a ≥ 0}` issuing from a point `x` of `C` is contained
in `C`. The classical definition excludes `y = 0`, which has no direction; including it is what
makes `0⁺C` a cone. -/
def recessionCone (C : Set E) : Set E := {y | ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C}

/-- Membership in the recession cone, unfolded. -/
theorem mem_recessionCone : y ∈ recessionCone C ↔ ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C :=
  Iff.rfl

/-- The defining property of a direction of recession. -/
theorem add_smul_mem_of_mem_recessionCone (hy : y ∈ recessionCone C) (hx : x ∈ C) (ha : 0 ≤ a) :
    x + a • y ∈ C := hy x hx a ha

/-- A direction of recession may be added to any point of `C`. -/
theorem add_mem_of_mem_recessionCone (hy : y ∈ recessionCone C) (hx : x ∈ C) : x + y ∈ C := by
  simpa using hy x hx 1 zero_le_one

@[simp]
theorem zero_mem_recessionCone (C : Set E) : (0 : E) ∈ recessionCone C := fun x hx _ _ => by
  simpa using hx

theorem smul_mem_recessionCone (ha : 0 ≤ a) (hy : y ∈ recessionCone C) :
    a • y ∈ recessionCone C := fun x hx b hb => by
  rw [smul_smul]
  exact hy x hx (b * a) (mul_nonneg hb ha)

theorem add_mem_recessionCone (hy : y ∈ recessionCone C) (hz : z ∈ recessionCone C) :
    y + z ∈ recessionCone C := fun x hx a ha => by
  rw [smul_add, ← add_assoc]
  exact hz _ (hy x hx a ha) a ha

/-- **`0⁺C` is a convex cone containing the origin**, bundled as a Mathlib `PointedCone`. No
hypothesis on `C` is needed; convexity enters only in `recessionCone_eq_add_subset`, the
description of `0⁺C` by a single step. -/
def recessionPointedCone (C : Set E) : PointedCone ℝ E where
  carrier := recessionCone C
  zero_mem' := zero_mem_recessionCone C
  add_mem' := add_mem_recessionCone
  smul_mem' c _ hy := smul_mem_recessionCone c.2 hy

@[simp]
theorem coe_recessionPointedCone (C : Set E) :
    (recessionPointedCone C : Set E) = recessionCone C := rfl

@[simp]
theorem mem_recessionPointedCone : y ∈ recessionPointedCone C ↔ y ∈ recessionCone C := Iff.rfl

theorem convex_recessionCone (C : Set E) : Convex ℝ (recessionCone C) :=
  ((recessionPointedCone C : ConvexCone ℝ E)).convex

/-- Every direction recedes from the empty set, vacuously. -/
@[simp]
theorem recessionCone_empty : recessionCone (∅ : Set E) = univ := by
  ext y; simp [recessionCone]

@[simp]
theorem recessionCone_univ : recessionCone (univ : Set E) = univ := by
  ext y; simp [recessionCone]

@[simp]
theorem recessionCone_singleton (x : E) : recessionCone ({x} : Set E) = {0} := by
  ext y
  refine ⟨fun hy => ?_, ?_⟩
  · have h : x + (1 : ℝ) • y ∈ ({x} : Set E) := hy x rfl 1 zero_le_one
    rw [one_smul] at h
    simpa using h
  · rintro rfl
    exact zero_mem_recessionCone _

/-- The recession cone as an intersection of preimages of `C`. This is what makes it closed
whenever `C` is; see `isClosed_recessionCone`. For `a > 0` the `a`-th preimage is
`a⁻¹ • (C - x)`, which is the form Rockafellar's argument uses. -/
theorem recessionCone_eq_iInter (C : Set E) :
    recessionCone C = ⋂ x ∈ C, ⋂ a ∈ Ici (0 : ℝ), (fun y => x + a • y) ⁻¹' C := by
  ext y; simp [recessionCone]

/-- Directions of recession of every member of a family recede from the intersection. The reverse
inclusion needs closedness and convexity; it is `recessionCone_iInter`. -/
theorem iInter_recessionCone_subset {ι : Sort*} (C : ι → Set E) :
    ⋂ i, recessionCone (C i) ⊆ recessionCone (⋂ i, C i) := by
  intro y hy x hx a ha
  exact mem_iInter.2 fun i => (mem_iInter.1 hy i) x (mem_iInter.1 hx i) a ha

theorem inter_recessionCone_subset (C D : Set E) :
    recessionCone C ∩ recessionCone D ⊆ recessionCone (C ∩ D) := by
  rintro y ⟨hyC, hyD⟩ x ⟨hxC, hxD⟩ a ha
  exact ⟨hyC x hxC a ha, hyD x hxD a ha⟩

/-- For a convex set it is enough to test the recession condition at `a = 1`. -/
theorem mem_recessionCone_iff_forall_add_mem (hC : Convex ℝ C) :
    y ∈ recessionCone C ↔ ∀ x ∈ C, x + y ∈ C := by
  refine ⟨fun hy x hx => add_mem_of_mem_recessionCone hy hx, fun hy x hx a ha => ?_⟩
  have key : ∀ n : ℕ, x + (n : ℝ) • y ∈ C := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have h := hy _ ih
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_smul, one_smul, ← add_assoc]
      exact h
  obtain ⟨n, hn⟩ := exists_nat_ge a
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hx
  · have hn0 : (0 : ℝ) < n := ha'.trans_le hn
    have hle : a / (n : ℝ) ≤ 1 := (div_le_one hn0).2 hn
    have h := hC hx (key n) (by linarith : (0 : ℝ) ≤ 1 - a / (n : ℝ))
      (by positivity : (0 : ℝ) ≤ a / (n : ℝ)) (by ring)
    have hcancel : a / (n : ℝ) * (n : ℝ) = a := div_mul_cancel₀ a hn0.ne'
    rwa [smul_add, smul_smul, hcancel, ← add_assoc, ← add_smul,
      show 1 - a / (n : ℝ) + a / (n : ℝ) = 1 by ring, one_smul] at h

omit [Module ℝ E] in
/-- The condition `C + y ⊆ C`, spelled out. -/
theorem add_singleton_subset_iff_forall (C : Set E) (y : E) :
    C + {y} ⊆ C ↔ ∀ x ∈ C, x + y ∈ C := by
  rw [Set.add_singleton, Set.image_subset_iff]
  exact ⟨fun h x hx => h hx, fun h _ hx => h _ hx⟩

/-- The recession cone of a convex set is the set of `y` with `C + y ⊆ C`. -/
theorem recessionCone_eq_add_subset (hC : Convex ℝ C) :
    recessionCone C = {y | C + {y} ⊆ C} := by
  ext y
  rw [mem_recessionCone_iff_forall_add_mem hC]
  exact (add_singleton_subset_iff_forall C y).symm

theorem recessionCone_neg (C : Set E) : recessionCone (-C) = -recessionCone C := by
  ext v
  simp only [Set.mem_neg, mem_recessionCone]
  constructor
  · intro h x hx a ha
    have hmem : -(-x) ∈ C := by rw [neg_neg]; exact hx
    have hstep := h (-x) hmem a ha
    have heq : -(-x + a • v) = x + a • (-v) := by module
    rwa [heq] at hstep
  · intro h x hx a ha
    have hstep := h (-x) hx a ha
    have heq : -x + a • (-v) = -(x + a • v) := by module
    rwa [heq] at hstep

/-- The lineality space of `C`: the directions in which `C` is linear. -/
def linealitySpace (C : Set E) : Set E := recessionCone C ∩ (-recessionCone C)

theorem mem_linealitySpace :
    y ∈ linealitySpace C ↔ y ∈ recessionCone C ∧ -y ∈ recessionCone C := by
  simp [linealitySpace]

@[simp] theorem zero_mem_linealitySpace (C : Set E) : (0 : E) ∈ linealitySpace C :=
  mem_linealitySpace.2 ⟨zero_mem_recessionCone C, by
    rw [neg_zero]; exact zero_mem_recessionCone C⟩

theorem linealitySpace_subset_recessionCone (C : Set E) :
    linealitySpace C ⊆ recessionCone C := inter_subset_left

/-- The lineality space is a subspace, bundled as a `Submodule ℝ E`. It is Mathlib's
`PointedCone.lineal` of `recessionPointedCone`. -/
noncomputable def linealitySubmodule (C : Set E) : Submodule ℝ E :=
  (recessionPointedCone C).lineal

@[simp]
theorem coe_linealitySubmodule (C : Set E) :
    (linealitySubmodule C : Set E) = linealitySpace C := by
  ext y; simp [linealitySubmodule, linealitySpace]

@[simp]
theorem mem_linealitySubmodule : y ∈ linealitySubmodule C ↔ y ∈ linealitySpace C := by
  rw [← SetLike.mem_coe, coe_linealitySubmodule]

theorem convex_linealitySpace (C : Set E) : Convex ℝ (linealitySpace C) := by
  simpa using (linealitySubmodule C).convex

/-- The lineality space is the largest subspace inside `0⁺C`. -/
theorem linealitySubmodule_isGreatest (C : Set E) :
    IsGreatest {L : Submodule ℝ E | (L : Set E) ⊆ recessionCone C} (linealitySubmodule C) := by
  constructor
  · have hsub : ((linealitySubmodule C : Submodule ℝ E) : Set E) ⊆ recessionCone C := by
      rw [coe_linealitySubmodule]
      exact linealitySpace_subset_recessionCone C
    exact hsub
  · intro L hL y hy
    exact mem_linealitySubmodule.2 (mem_linealitySpace.2 ⟨hL hy, hL (L.neg_mem hy)⟩)

/-- The lineality space of a convex set consists of the `y` with `C + y = C`, in contrast with
`C + y ⊆ C` for the recession cone. -/
theorem linealitySpace_eq_add_eq (hC : Convex ℝ C) :
    linealitySpace C = {y | C + {y} = C} := by
  ext y
  rw [mem_linealitySpace, mem_recessionCone_iff_forall_add_mem hC,
    mem_recessionCone_iff_forall_add_mem hC]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine Set.Subset.antisymm ((add_singleton_subset_iff_forall C y).2 h₁) fun x hx => ?_
    exact ⟨x + -y, h₂ x hx, y, rfl, by change x + -y + y = x; abel⟩
  · intro h
    have hsub : C + {y} ⊆ C := h.le
    refine ⟨(add_singleton_subset_iff_forall C y).1 hsub, fun x hx => ?_⟩
    obtain ⟨w, hw, v, hv, hwv⟩ := h.ge hx
    have hwv' : w + v = x := hwv
    rw [Set.mem_singleton_iff] at hv
    have hxw : x + -y = w := by rw [← hwv', hv]; abel
    exact hxw ▸ hw

/-- **The direct-sum decomposition**, for an arbitrary subspace `N` of the lineality space: if `M`
is a complement of `N`, then `C = N + (C ∩ M)`. Only `N ⊆ lin C` is used, and that extra room is
what the closed-image theorem needs, where the relevant subspace is `lin C ∩ ker A`. -/
theorem eq_add_inter_of_isCompl_of_le {N M : Submodule ℝ E}
    (hN : (N : Set E) ⊆ linealitySpace C) (h : IsCompl N M) :
    C = (N : Set E) + (C ∩ (M : Set E)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · have hmem : x ∈ N ⊔ M := by rw [h.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hmem
    have hpneg : -p ∈ recessionCone C := (mem_linealitySpace.1 (hN hp)).2
    have hqC : q ∈ C := by
      have hstep := add_mem_of_mem_recessionCone hpneg hx
      simpa [add_comm, add_assoc] using hstep
    exact Set.add_mem_add hp ⟨hqC, hq⟩
  · rintro _ ⟨p, hp, q, ⟨hqC, -⟩, rfl⟩
    have hpC : p ∈ recessionCone C := (mem_linealitySpace.1 (hN hp)).1
    simpa [add_comm] using add_mem_of_mem_recessionCone hpC hqC

/-- **The direct-sum decomposition**: if `L'` is any complement of the lineality space `L` of `C`,
then `C = L + (C ∩ L')`. The classical statement takes `L' = Lᗮ` in an inner-product space; that
is the special case. -/
theorem eq_add_inter_of_isCompl {L : Submodule ℝ E} (h : IsCompl (linealitySubmodule C) L) :
    C = (linealitySubmodule C : Set E) + (C ∩ (L : Set E)) :=
  eq_add_inter_of_isCompl_of_le (coe_linealitySubmodule C).subset h

/-- Convexity is preserved by the change of variables `z ↦ x + c • z`. -/
theorem convex_preimage_affine_smul (hC : Convex ℝ C) (x : E) (c : ℝ) :
    Convex ℝ {z | x + c • z ∈ C} := by
  intro z₁ h₁ z₂ h₂ a b ha hb hab
  have hxab : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have heq : x + c • (a • z₁ + b • z₂) = a • (x + c • z₁) + b • (x + c • z₂) := by
    conv_lhs => rw [← hxab]
    simp only [smul_add, smul_smul]
    rw [mul_comm c a, mul_comm c b]
    abel
  change x + c • (a • z₁ + b • z₂) ∈ C
  rw [heq]
  exact hC h₁ h₂ ha hb hab

/-- **The recession cone is invariant under `z ↦ x + c • z` for `c > 0`.** Directions of recession
do not see translations, and positive rescaling permutes the rays of a cone. This is the change of
variables that turns "`C` recedes in the direction `v`" into a *decreasing* family of sets. -/
theorem recessionCone_preimage_affine {c : ℝ} (hc : 0 < c) (x : E) (C : Set E) :
    recessionCone {z | x + c • z ∈ C} = recessionCone C := by
  ext w
  simp only [mem_recessionCone, Set.mem_ofPred_eq]
  constructor
  · intro hw u hu b hb
    have hz : x + c • (c⁻¹ • (u - x)) ∈ C := by
      rw [smul_inv_smul₀ hc.ne']
      simpa using hu
    have hstep := hw _ hz (b / c) (by positivity)
    have heq : x + c • (c⁻¹ • (u - x) + (b / c) • w) = u + b • w := by
      rw [smul_add, smul_inv_smul₀ hc.ne', smul_smul, mul_div_cancel₀ _ hc.ne']
      abel
    rwa [heq] at hstep
  · intro hw z hz a ha
    have hstep := hw _ hz (c * a) (by positivity)
    have heq : x + c • (z + a • w) = x + c • z + (c * a) • w := by
      rw [smul_add, smul_smul]
      abel
    rwa [heq]


/-- The *lineality of `C`*: the dimension of its lineality space. -/
noncomputable def lineality (C : Set E) : ℕ := Module.finrank ℝ (linealitySubmodule C)

end Defs

/-! ### Affine sets and systems of weak linear inequalities -/

section Examples

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A subspace is its own recession cone. -/
@[simp] theorem recessionCone_coe_submodule (M : Submodule ℝ E) :
    recessionCone (M : Set E) = M := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · simpa using hy 0 M.zero_mem 1 zero_le_one
  · exact M.add_mem hz (M.smul_mem a hy)

/-- **A pointed convex cone is its own recession cone.** This is what makes the sum rule for
cones a special case of the sum rule for sets: for cones the recession hypothesis is a hypothesis
about the cones themselves. -/
@[simp] theorem recessionCone_coe_pointedCone (K : PointedCone ℝ E) :
    recessionCone (K : Set E) = K := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · simpa using hy 0 K.zero_mem 1 zero_le_one
  · exact K.add_mem hz (K.smul_mem ha hy)

/-- The recession cone of a nonempty affine set is the subspace parallel to it. -/
theorem recessionCone_coe_affineSubspace {s : AffineSubspace ℝ E} (hs : (s : Set E).Nonempty) :
    recessionCone (s : Set E) = s.direction := by
  obtain ⟨x, hx⟩ := hs
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy z hz a ha => ?_)
  · have h : x + (1 : ℝ) • y ∈ s := hy x hx 1 zero_le_one
    rw [one_smul] at h
    simpa using AffineSubspace.vsub_mem_direction h hx
  · have h : a • y ∈ s.direction := s.direction.smul_mem a hy
    simpa [vadd_eq_add, add_comm] using AffineSubspace.vadd_mem_of_mem_direction h hz

/-- The lineality space of a nonempty affine set is the subspace parallel to it. -/
theorem linealitySpace_coe_affineSubspace {s : AffineSubspace ℝ E} (hs : (s : Set E).Nonempty) :
    linealitySpace (s : Set E) = s.direction := by
  ext y
  rw [mem_linealitySpace, recessionCone_coe_affineSubspace hs]
  exact ⟨fun h => h.1, fun h => ⟨h, s.direction.neg_mem h⟩⟩

/-- The recession cone of the solution set of a system of weak linear inequalities is the solution
set of the corresponding homogeneous system. -/
theorem recessionCone_setOf_forall_le {ι : Type*} (b : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (h : {x : E | ∀ i, β i ≤ b i x}.Nonempty) :
    recessionCone {x : E | ∀ i, β i ≤ b i x} = {y : E | ∀ i, 0 ≤ b i y} := by
  refine Set.Subset.antisymm (fun y hy i => ?_) (fun y hy x hx a ha i => ?_)
  · by_contra hb
    obtain ⟨x, hx⟩ := h
    have hxi : ∀ j, β j ≤ b j x := hx
    have hd : 0 < -(b i y) := by linarith [not_le.1 hb]
    have hnum : (0 : ℝ) ≤ b i x - β i + 1 := by linarith [hxi i]
    have ha : (0 : ℝ) ≤ (b i x - β i + 1) / (-(b i y)) := div_nonneg hnum hd.le
    have hstep : ∀ j, β j ≤ b j (x + ((b i x - β i + 1) / (-(b i y))) • y) := hy x hx _ ha
    have hval := hstep i
    rw [map_add, map_smul, smul_eq_mul] at hval
    have hcancel : (b i x - β i + 1) / (-(b i y)) * (-(b i y)) = b i x - β i + 1 :=
      div_mul_cancel₀ _ hd.ne'
    have hneg : (b i x - β i + 1) / (-(b i y)) * (-(b i y))
        = -((b i x - β i + 1) / (-(b i y)) * b i y) := by ring
    linarith
  · have hxi : ∀ j, β j ≤ b j x := hx
    have hyi : ∀ j, (0 : ℝ) ≤ b j y := hy
    change β i ≤ b i (x + a • y)
    rw [map_add, map_smul, smul_eq_mul]
    have : (0 : ℝ) ≤ a * b i y := mul_nonneg ha (hyi i)
    linarith [hxi i]

/-- The lineality space of the solution set of a system of weak linear inequalities is given by
the corresponding system of equations. -/
theorem linealitySpace_setOf_forall_le {ι : Type*} (b : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (h : {x : E | ∀ i, β i ≤ b i x}.Nonempty) :
    linealitySpace {x : E | ∀ i, β i ≤ b i x} = {y : E | ∀ i, b i y = 0} := by
  ext y
  rw [mem_linealitySpace, recessionCone_setOf_forall_le b β h]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    have h₁' : ∀ j, (0 : ℝ) ≤ b j y := h₁
    have h₂' : ∀ j, (0 : ℝ) ≤ b j (-y) := h₂
    have := h₂' i
    rw [map_neg] at this
    linarith [h₁' i]
  · intro hy
    have hy' : ∀ j, b j y = 0 := hy
    exact ⟨fun i => (hy' i).ge, fun i => by rw [map_neg, hy' i]; simp⟩

end Examples

/-! ### Products, and preimages under a linear map -/

section Prod

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {C : Set E} {D : Set F}

theorem prod_recessionCone_subset (C : Set E) (D : Set F) :
    recessionCone C ×ˢ recessionCone D ⊆ recessionCone (C ×ˢ D) := by
  rintro ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩ ⟨x₁, x₂⟩ hx a ha
  exact ⟨hy₁ x₁ hx.1 a ha, hy₂ x₂ hx.2 a ha⟩

/-- **The recession cone of a product is the product of the recession cones.** Both factors must be
nonempty: `0⁺(C ×ˢ ∅) = 0⁺ ∅ = univ`, which is not `0⁺C ×ˢ univ` unless `0⁺C` is everything. -/
theorem recessionCone_prod (hC : C.Nonempty) (hD : D.Nonempty) :
    recessionCone (C ×ˢ D) = recessionCone C ×ˢ recessionCone D := by
  refine Set.Subset.antisymm (fun y hy => ⟨fun x hx a ha => ?_, fun x hx a ha => ?_⟩)
    (prod_recessionCone_subset C D)
  · obtain ⟨w, hw⟩ := hD
    exact (hy (x, w) ⟨hx, hw⟩ a ha).1
  · obtain ⟨w, hw⟩ := hC
    exact (hy (w, x) ⟨hw, hx⟩ a ha).2

/-- **The lineality space of a product is the product of the lineality spaces.** -/
theorem linealitySpace_prod (hC : C.Nonempty) (hD : D.Nonempty) :
    linealitySpace (C ×ˢ D) = linealitySpace C ×ˢ linealitySpace D := by
  ext ⟨y₁, y₂⟩
  simp only [mem_linealitySpace, recessionCone_prod hC hD, Set.mem_prod, Prod.neg_mk]
  tauto

end Prod

section Pi

variable {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
  {s : Set ι} {C : ∀ i, Set (E i)}

/-- A family of recession directions is a recession direction of the product set. Unconditional,
and the `Set.pi` form of `prod_recessionCone_subset`. -/
theorem pi_recessionCone_subset (s : Set ι) (C : ∀ i, Set (E i)) :
    s.pi (fun i => recessionCone (C i)) ⊆ recessionCone (s.pi C) := by
  intro y hy x hx a ha i hi
  exact hy i hi (x i) (hx i hi) a ha

/-- **The recession cone of a product set is the product of the recession cones.** The `Set.pi`
form of `recessionCone_prod`; the nonemptiness hypothesis is there for the same reason, that
testing one coordinate needs a witness in all the others. -/
theorem recessionCone_pi (hC : (s.pi C).Nonempty) :
    recessionCone (s.pi C) = s.pi (fun i => recessionCone (C i)) := by
  classical
  refine Set.Subset.antisymm (fun y hy => ?_) (pi_recessionCone_subset s C)
  intro i hi x hx a ha
  obtain ⟨w, hw⟩ := hC
  have hupd : Function.update w i x ∈ s.pi C := by
    intro j hj
    rcases eq_or_ne j i with rfl | hji
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hji]
      exact hw j hj
  have hmem := hy (Function.update w i x) hupd a ha i hi
  rwa [Pi.add_apply, Pi.smul_apply, Function.update_self] at hmem

/-- **The lineality space of a product set is the product of the lineality spaces.** -/
theorem linealitySpace_pi (hC : (s.pi C).Nonempty) :
    linealitySpace (s.pi C) = s.pi (fun i => linealitySpace (C i)) := by
  ext y
  simp only [mem_linealitySpace, recessionCone_pi hC, Set.mem_pi, Pi.neg_apply, forall_and]

end Pi

section PreimageDefs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- One inclusion of the preimage rule, valid with no hypothesis at all. -/
theorem preimage_recessionCone_subset (A : E →ₗ[ℝ] F) (D : Set F) :
    A ⁻¹' recessionCone D ⊆ recessionCone (A ⁻¹' D) := by
  intro y hy x hx a ha
  have h : A x + a • A y ∈ D := hy (A x) hx a ha
  simpa [map_add, map_smul] using h

end PreimageDefs

/-! ### Closedness, limits, and one-half-line criteria -/

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {C D : Set E} {y : E}

/-- The sequence `(n+1)⁻¹` tends to `0`. Mathlib states this as `1 / (n + 1)`. -/
theorem tendsto_inv_nat_add_one_atTop_nhds_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- **The closure of a pointed convex cone is its own recession cone.** `PointedCone.closure`
supplies the cone structure on `cl K`; `recessionCone_coe_pointedCone` then applies verbatim. -/
theorem recessionCone_closure_coe_pointedCone (K : PointedCone ℝ E) :
    recessionCone (closure (K : Set E)) = closure (K : Set E) := by
  rw [← PointedCone.coe_closure]
  exact recessionCone_coe_pointedCone K.closure

/-- The recession cone of a closed set is closed. No convexity, no nonemptiness and no local
compactness are needed: by `recessionCone_eq_iInter`, `0⁺C` is an intersection of preimages of `C`
under the continuous maps `y ↦ x + a • y`. -/
theorem isClosed_recessionCone (hC : IsClosed C) : IsClosed (recessionCone C) := by
  rw [recessionCone_eq_iInter]
  exact isClosed_biInter fun x _ => isClosed_biInter fun a _ => hC.preimage (by fun_prop)

omit [ContinuousSMul ℝ E] in
/-- Directions of recession survive taking the closure. The reverse inclusion is false: for
`C = {(s, t) | s > 0, t > 0} ∪ {0}` in `ℝ²`, `0⁺(cl C)` is the closed quadrant while `0⁺C` is `C`
itself. -/
theorem recessionCone_subset_recessionCone_closure (C : Set E) :
    recessionCone C ⊆ recessionCone (closure C) := by
  intro y hy x hx a ha
  have hcont : Continuous fun z : E => z + a • y := by fun_prop
  have himg : (fun z : E => z + a • y) '' closure C ⊆ closure ((fun z : E => z + a • y) '' C) :=
    image_closure_subset_closure_image hcont
  refine closure_mono (fun z hz => ?_) (himg ⟨x, hx, rfl⟩)
  obtain ⟨w, hw, rfl⟩ := hz
  exact hy w hw a ha

/-- The sequence `(n+1)⁻¹ • (x + (n+1) • y)` converges to `y`: the witness for the easy half of
the sequential description, and what makes one half-line enough. -/
theorem tendsto_inv_smul_ray (x y : E) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x + ((n : ℝ) + 1) • y)) atTop (𝓝 y) := by
  have hfun : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (x + ((n : ℝ) + 1) • y))
      = fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x + y := by
    funext n
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) := tendsto_const_nhds
  have hsum := (tendsto_inv_nat_add_one_atTop_nhds_zero.smul_const x).add hconst
  rw [hfun]
  simpa using hsum

/-- **The hard half of the sequential description**: a limit of `lᵢ • xᵢ` with `xᵢ ∈ C` and
`lᵢ ↓ 0` is a direction of recession of a closed convex `C`. Finite-dimensionality is not needed:
`(1 - a lᵢ) • x + (a lᵢ) • xᵢ` lies in `C` once `a lᵢ ≤ 1`, and converges to `x + a • y`. -/
theorem mem_recessionCone_of_tendsto (hC : Convex ℝ C) (hC' : IsClosed C) {l : ℕ → ℝ} {u : ℕ → E}
    (hu : ∀ n, u n ∈ C) (hl : ∀ n, 0 < l n) (hl0 : Tendsto l atTop (𝓝 0))
    (hly : Tendsto (fun n => l n • u n) atTop (𝓝 y)) : y ∈ recessionCone C := by
  intro x hx a ha
  have hal : Tendsto (fun n => a * l n) atTop (𝓝 0) := by simpa using hl0.const_mul a
  have hev : ∀ᶠ n in atTop, a * l n ≤ 1 :=
    (hal.eventually_lt_const one_pos).mono fun n hn => hn.le
  have hmem : ∀ᶠ n in atTop, (1 - a * l n) • x + (a * l n) • u n ∈ C := by
    filter_upwards [hev] with n hn
    exact hC hx (hu n) (by linarith) (mul_nonneg ha (hl n).le) (by ring)
  have h1 : Tendsto (fun n => (1 - a * l n) • x) atTop (𝓝 x) := by
    have hone : Tendsto (fun n => 1 - a * l n) atTop (𝓝 1) := by simpa using hal.const_sub 1
    simpa using hone.smul_const x
  have h2 : Tendsto (fun n => (a * l n) • u n) atTop (𝓝 (a • y)) := by
    simpa [mul_smul] using hly.const_smul a
  exact hC'.mem_of_tendsto (h1.add h2) hmem

/-- **The easy half**: every direction of recession of a nonempty set is a limit of `lᵢ • xᵢ`
with `xᵢ ∈ C` and `lᵢ ↓ 0`. -/
theorem exists_tendsto_of_mem_recessionCone (hne : C.Nonempty) (hy : y ∈ recessionCone C) :
    ∃ (l : ℕ → ℝ) (u : ℕ → E), (∀ n, u n ∈ C) ∧ (∀ n, 0 < l n) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • u n) atTop (𝓝 y) := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨fun n => ((n : ℝ) + 1)⁻¹, fun n => x + ((n : ℝ) + 1) • y,
    fun n => hy x hx _ (by positivity), fun n => by positivity,
    tendsto_inv_nat_add_one_atTop_nhds_zero, tendsto_inv_smul_ray x y⟩

/-- For a nonempty closed convex set, `0⁺C` is exactly the set of limits of sequences `lᵢ • xᵢ`
with `xᵢ ∈ C` and `lᵢ ↓ 0`. -/
theorem mem_recessionCone_iff_exists_tendsto (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) :
    y ∈ recessionCone C ↔ ∃ (l : ℕ → ℝ) (u : ℕ → E), (∀ n, u n ∈ C) ∧ (∀ n, 0 < l n) ∧
      Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • u n) atTop (𝓝 y) :=
  ⟨exists_tendsto_of_mem_recessionCone hne, fun ⟨_, _, hu, hl, hl0, hly⟩ =>
    mem_recessionCone_of_tendsto hC hC' hu hl hl0 hly⟩

/-- **One half-line is enough**: if a closed convex set `C` contains even one half-line in the
direction `y`, it contains every half-line in that direction issuing from a point of `C`. -/
theorem mem_recessionCone_of_exists_ray (hC : Convex ℝ C) (hC' : IsClosed C)
    (h : ∃ x, ∀ a : ℝ, 0 ≤ a → x + a • y ∈ C) : y ∈ recessionCone C := by
  obtain ⟨x, hx⟩ := h
  exact mem_recessionCone_of_tendsto hC hC' (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹)
    (fun n => hx ((n : ℝ) + 1) (by positivity)) (fun n => by positivity)
    tendsto_inv_nat_add_one_atTop_nhds_zero (tendsto_inv_smul_ray x y)

/-- For a closed convex set containing the origin, `0⁺C = ⋂_{ε > 0} ε • C`. -/
theorem recessionCone_eq_iInter_smul (hC : Convex ℝ C) (hC' : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone C = ⋂ ε ∈ Ioi (0 : ℝ), ε • C := by
  refine Set.Subset.antisymm (fun y hy => mem_iInter₂.2 fun ε hε => ?_) (fun y hy => ?_)
  · have hε' : (0 : ℝ) < ε := hε
    have hmem : ε⁻¹ • y ∈ C := by simpa using hy 0 h0 ε⁻¹ (by positivity)
    simpa [smul_inv_smul₀ hε'.ne'] using Set.smul_mem_smul_set (a := ε) hmem
  · have hu : ∀ n : ℕ, ((n : ℝ) + 1) • y ∈ C := by
      intro n
      have hne : (((n : ℝ) + 1)⁻¹ : ℝ) ≠ 0 := by positivity
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      have hmem : y ∈ ((n : ℝ) + 1)⁻¹ • C := mem_iInter₂.1 hy ((n : ℝ) + 1)⁻¹ hpos
      simpa using (Set.mem_smul_set_iff_inv_smul_mem₀ hne C y).1 hmem
    refine mem_recessionCone_of_tendsto hC hC' (l := fun n : ℕ => ((n : ℝ) + 1)⁻¹) hu
      (fun n => by positivity) tendsto_inv_nat_add_one_atTop_nhds_zero ?_
    have hconst : (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • (((n : ℝ) + 1) • y)) = fun _ : ℕ => y := by
      funext n
      rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [hconst]
    exact tendsto_const_nhds

/-- The recession cone of an intersection of closed convex sets with a common point is the
intersection of the recession cones. -/
theorem recessionCone_iInter {ι : Sort*} {C : ι → Set E} (hconv : ∀ i, Convex ℝ (C i))
    (hclosed : ∀ i, IsClosed (C i)) (hne : (⋂ i, C i).Nonempty) :
    recessionCone (⋂ i, C i) = ⋂ i, recessionCone (C i) := by
  refine Set.Subset.antisymm (fun y hy => mem_iInter.2 fun i => ?_)
    (iInter_recessionCone_subset C)
  obtain ⟨x, hx⟩ := hne
  exact mem_recessionCone_of_exists_ray (hconv i) (hclosed i)
    ⟨x, fun a ha => mem_iInter.1 (hy x hx a ha) i⟩

/-- The same over a *sub*family: the recession cone of `⋂ i ∈ s, C i` is
`⋂ i ∈ s, 0⁺Cᵢ`. Stated with a bare predicate rather than a `Set` or a `Finset`, so that it applies
to either spelling of the bounded intersection. -/
theorem recessionCone_iInter₂ {ι : Sort*} {p : ι → Prop} {C : ∀ i, p i → Set E}
    (hconv : ∀ i h, Convex ℝ (C i h)) (hclosed : ∀ i h, IsClosed (C i h))
    (hne : (⋂ i, ⋂ h, C i h).Nonempty) :
    recessionCone (⋂ i, ⋂ h, C i h) = ⋂ i, ⋂ h, recessionCone (C i h) := by
  obtain ⟨x, hx⟩ := hne
  rw [recessionCone_iInter (fun i => convex_iInter (hconv i))
    (fun i => isClosed_iInter (hclosed i)) ⟨x, hx⟩]
  exact iInter_congr fun i =>
    recessionCone_iInter (hconv i) (hclosed i) ⟨x, mem_iInter.1 hx i⟩

/-- The binary form: `0⁺(C ∩ D) = 0⁺C ∩ 0⁺D` for closed convex sets that meet. -/
theorem recessionCone_inter (hC : Convex ℝ C) (hC' : IsClosed C) (hD : Convex ℝ D)
    (hD' : IsClosed D) (hne : (C ∩ D).Nonempty) :
    recessionCone (C ∩ D) = recessionCone C ∩ recessionCone D := by
  obtain ⟨x, hxC, hxD⟩ := hne
  refine Set.Subset.antisymm (fun y hy => ⟨?_, ?_⟩) (inter_recessionCone_subset C D)
  · exact mem_recessionCone_of_exists_ray hC hC' ⟨x, fun a ha => (hy x ⟨hxC, hxD⟩ a ha).1⟩
  · exact mem_recessionCone_of_exists_ray hD hD' ⟨x, fun a ha => (hy x ⟨hxC, hxD⟩ a ha).2⟩

/-- A convex set with nonempty interior has the same directions of recession as its interior and
as its closure. The classical statement uses the relative interior in place of `interior`. -/
theorem recessionCone_interior_eq_recessionCone_closure (hC : Convex ℝ C)
    (hne : (interior C).Nonempty) :
    recessionCone (interior C) = recessionCone (closure C) := by
  refine Set.Subset.antisymm ?_ (fun y hy x hx a ha => ?_)
  · rw [← hC.closure_interior_eq_closure_of_nonempty_interior hne]
    exact recessionCone_subset_recessionCone_closure _
  · have h2 : x + (2 * a) • y ∈ closure C :=
      hy x (subset_closure (interior_subset hx)) (2 * a) (by linarith)
    have hcombo := hC.combo_interior_closure_mem_interior hx h2 (a := (1 : ℝ) / 2)
      (b := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
    have hcoef : (1 : ℝ) / 2 * (2 * a) = a := by ring
    have heq : ((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • (x + (2 * a) • y) = x + a • y := by
      rw [smul_add, smul_smul, hcoef, ← add_assoc, ← add_smul]
      norm_num
    rwa [heq] at hcombo

/-! #### The bridge to Mathlib's `asymptoticCone` -/

/-- Every direction of recession of a nonempty set lies in Mathlib's `asymptoticCone`. -/
theorem recessionCone_subset_asymptoticCone (hne : C.Nonempty) :
    recessionCone C ⊆ asymptoticCone ℝ C := by
  obtain ⟨x, hx⟩ := hne
  intro y hy
  rw [mem_asymptoticCone_iff]
  refine (((tendsto_id (x := atTop (α := ℝ))).atTop_smul_const_tendsto_asymptoticNhds
    y).asymptoticNhds_vadd_const x).frequently (Filter.Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
  simpa [vadd_eq_add, add_comm] using hy x hx c hc

/-- For a closed convex set, Mathlib's `asymptoticCone` is contained in the recession cone. -/
theorem asymptoticCone_subset_recessionCone (hC : Convex ℝ C) (hC' : IsClosed C) :
    asymptoticCone ℝ C ⊆ recessionCone C := fun y hy x hx a ha => by
  simpa [vadd_eq_add, add_comm] using
    hC.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hC' ha hy hx

/-- For a nonempty closed convex set, `0⁺C` is Mathlib's `asymptoticCone ℝ C`. -/
theorem recessionCone_eq_asymptoticCone (hC : Convex ℝ C) (hC' : IsClosed C) (hne : C.Nonempty) :
    recessionCone C = asymptoticCone ℝ C :=
  Set.Subset.antisymm (recessionCone_subset_asymptoticCone hne)
    (asymptoticCone_subset_recessionCone hC hC')

/-- In general Mathlib's `asymptoticCone ℝ C` is the recession cone of the *closure* of `C` — the
"asymptotic cone" of the older literature. -/
theorem recessionCone_closure_eq_asymptoticCone (hC : Convex ℝ C) (hne : C.Nonempty) :
    recessionCone (closure C) = asymptoticCone ℝ C := by
  rw [recessionCone_eq_asymptoticCone hC.closure isClosed_closure hne.closure,
    asymptoticCone_closure]

end Topological

/-! ### Preimages under a linear map -/

section Preimage

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {D : Set F}

/-- `0⁺(A⁻¹ D) = A⁻¹ (0⁺D)` for a closed convex `D` with nonempty preimage. Continuity of `A` is
*not* needed — one half-line is enough inside `D`, not inside `A ⁻¹' D` — so the domain `E`
carries no topology. -/
theorem recessionCone_preimage (A : E →ₗ[ℝ] F) (hD : Convex ℝ D) (hD' : IsClosed D)
    (hne : (A ⁻¹' D).Nonempty) :
    recessionCone (A ⁻¹' D) = A ⁻¹' recessionCone D := by
  obtain ⟨x, hx⟩ := hne
  refine Set.Subset.antisymm (fun y hy => ?_) (preimage_recessionCone_subset A D)
  refine mem_recessionCone_of_exists_ray hD hD' ⟨A x, fun a ha => ?_⟩
  simpa [map_add, map_smul] using hy x hx a ha

end Preimage

/-! ### Bounded sets and balls -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- **A nonempty bounded set recedes in no direction.** Neither closedness, nor convexity, nor
finite-dimensionality is needed. -/
theorem recessionCone_eq_zero_of_isBounded (hne : C.Nonempty) (h : IsBounded C) :
    recessionCone C = {0} := by
  refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨R, hR⟩ := h.exists_norm_le
  by_contra hy0
  have hyne : y ≠ 0 := by simpa using hy0
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hyne
  have hR0 : 0 ≤ R := (norm_nonneg x).trans (hR x hx)
  set a : ℝ := (R + ‖x‖ + 1) / ‖y‖ with hadef
  have ha : 0 ≤ a := by positivity
  have hmem : ‖x + a • y‖ ≤ R := hR _ (hy x hx a ha)
  have hsplit : ‖a • y‖ ≤ ‖x + a • y‖ + ‖x‖ := by
    have hrw : ‖a • y‖ = ‖x + a • y - x‖ := by congr 1; abel
    rw [hrw]
    exact norm_sub_le (x + a • y) x
  have hnorm : ‖a • y‖ = R + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, hadef, div_mul_cancel₀ _ hy'.ne']
  rw [hnorm] at hsplit
  linarith

/-- The recession cone of a closed ball is trivial. -/
theorem recessionCone_closedBall (x : E) {ε : ℝ} (hε : 0 ≤ ε) :
    recessionCone (Metric.closedBall x ε) = {0} :=
  recessionCone_eq_zero_of_isBounded ⟨x, Metric.mem_closedBall_self hε⟩ Metric.isBounded_closedBall

variable {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- The recession cone of `A ⁻¹' (closedBall x ε)` is the kernel of `A`. This is the computation
the closed-image theorem runs on, and it needs no topology on the domain. -/
theorem recessionCone_preimage_closedBall (A : G →ₗ[ℝ] E) (x : E) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : (A ⁻¹' Metric.closedBall x ε).Nonempty) :
    recessionCone (A ⁻¹' Metric.closedBall x ε) = LinearMap.ker A := by
  rw [recessionCone_preimage A (convex_closedBall x ε) Metric.isClosed_closedBall hne,
    recessionCone_closedBall x hε]
  ext y
  simp [LinearMap.mem_ker]

end Normed

/-! ### Boundedness -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E}

/-- **A nonempty closed convex set is bounded exactly when it recedes in no direction.** This is
the one place in this file where finite-dimensionality is used, and it enters through Mathlib's
`isBounded_iff_asymptoticCone_subset_singleton`. -/
theorem isBounded_iff_recessionCone_eq_zero (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) : IsBounded C ↔ recessionCone C = {0} := by
  rw [recessionCone_eq_asymptoticCone hC hC' hne, isBounded_iff_asymptoticCone_subset_singleton]
  refine ⟨fun h => Set.Subset.antisymm h ?_, fun h => h.subset⟩
  simpa using zero_mem_asymptoticCone.2 hne

/-- Contrapositive form: an unbounded closed convex set recedes in some nonzero direction. -/
theorem exists_ne_zero_mem_recessionCone_of_not_isBounded (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) (hub : ¬ IsBounded C) : ∃ y ∈ recessionCone C, y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hub ((isBounded_iff_recessionCone_eq_zero hC hC' hne).2 ?_)
  refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
  simpa using hcon y hy

/-- A nonempty closed convex set is compact exactly when it recedes in no direction. -/
theorem isCompact_iff_recessionCone_eq_zero (hC : Convex ℝ C) (hC' : IsClosed C)
    (hne : C.Nonempty) : IsCompact C ↔ recessionCone C = {0} := by
  rw [← isBounded_iff_recessionCone_eq_zero hC hC' hne]
  exact ⟨fun h => h.isBounded, fun h => Metric.isCompact_of_isClosed_isBounded hC' h⟩

/-- If `M ∩ C` is nonempty and bounded for a closed convex `C` and an affine set `M`, then
`N ∩ C` is bounded for every affine set `N` parallel to `M`. -/
theorem isBounded_inter_of_direction_eq (hC : Convex ℝ C) (hC' : IsClosed C)
    {M N : AffineSubspace ℝ E} (hMN : M.direction = N.direction)
    (hM : ((M : Set E) ∩ C).Nonempty) (hb : IsBounded ((M : Set E) ∩ C)) :
    IsBounded ((N : Set E) ∩ C) := by
  rcases Set.eq_empty_or_nonempty ((N : Set E) ∩ C) with h | hN
  · simp [h]
  have hMne : (M : Set E).Nonempty := hM.mono inter_subset_left
  have hNne : (N : Set E).Nonempty := hN.mono inter_subset_left
  have hMcl : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  have hNcl : IsClosed (N : Set E) := N.closed_of_finiteDimensional
  have key : recessionCone ((N : Set E) ∩ C) = recessionCone ((M : Set E) ∩ C) := by
    rw [recessionCone_inter N.convex hNcl hC hC' hN, recessionCone_inter M.convex hMcl hC hC' hM,
      recessionCone_coe_affineSubspace hNne, recessionCone_coe_affineSubspace hMne, hMN]
  rw [isBounded_iff_recessionCone_eq_zero (N.convex.inter hC) (hNcl.inter hC') hN, key]
  exact (isBounded_iff_recessionCone_eq_zero (M.convex.inter hC) (hMcl.inter hC') hM).1 hb

/-- A family of closed sets whose recession cones meet only at the origin has a **finite**
subfamily whose recession cones already meet only at the origin. Convexity is not used: `0⁺C` is a
closed cone, so the unit sphere is covered by the complements of finitely many of them. -/
theorem exists_finset_iInter₂_recessionCone_eq_zero {ι : Type*} {C : ι → Set E}
    (hcl : ∀ i, IsClosed (C i)) (h : ⋂ i, recessionCone (C i) = {0}) :
    ∃ S : Finset ι, ⋂ i ∈ S, recessionCone (C i) = {0} := by
  have hempty : Metric.sphere (0 : E) 1 ∩ ⋂ i, recessionCone (C i) = ∅ := by
    rw [h]
    ext y
    simp +contextual
  obtain ⟨S, hS⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subfamily_closed
    (fun i => recessionCone (C i)) (fun i => isClosed_recessionCone (hcl i))
    (Set.disjoint_iff_inter_eq_empty.2 hempty)
  rw [Set.disjoint_iff_inter_eq_empty] at hS
  refine ⟨S, Set.Subset.antisymm (fun y hy => ?_) (by simp)⟩
  by_contra hy0
  have hyne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 (by simpa using hy0)
  have hmem : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 ∩ ⋂ i ∈ S, recessionCone (C i) := by
    refine ⟨?_, mem_iInter₂.2 fun i hi =>
      smul_mem_recessionCone (by positivity) (mem_iInter₂.1 hy i hi)⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (by simpa using hyne)]
  rw [hS] at hmem
  exact hmem

/-- **The recession hypothesis of Helly's theorem**: for a family of closed convex sets *every
finite subfamily of which has a common point*, having no common direction of recession holds **if
and only if** some finite subfamily has a bounded intersection. Neither direction needs the
recession cone of the *whole* intersection: `⇒` applies the boundedness criterion to a finite
subfamily produced by compactness of the unit sphere, and `⇐` reads it backwards through the
recession cone of an intersection. -/
theorem iInter_recessionCone_eq_zero_iff_exists_isBounded {ι : Type*} {C : ι → Set E}
    (hconv : ∀ i, Convex ℝ (C i)) (hcl : ∀ i, IsClosed (C i))
    (hne : ∀ S : Finset ι, (⋂ i ∈ S, C i).Nonempty) :
    ⋂ i, recessionCone (C i) = {0} ↔ ∃ S : Finset ι, IsBounded (⋂ i ∈ S, C i) := by
  have hrec : ∀ S : Finset ι,
      recessionCone (⋂ i ∈ S, C i) = ⋂ i ∈ S, recessionCone (C i) := fun S =>
    recessionCone_iInter₂ (C := fun i (_ : i ∈ S) => C i) (fun i _ => hconv i)
      (fun i _ => hcl i) (hne S)
  have hbdd : ∀ S : Finset ι,
      IsBounded (⋂ i ∈ S, C i) ↔ ⋂ i ∈ S, recessionCone (C i) = {0} := fun S => by
    rw [isBounded_iff_recessionCone_eq_zero (convex_iInter₂ fun i _ => hconv i)
      (isClosed_iInter fun i => isClosed_iInter fun _ => hcl i) (hne S), hrec S]
  constructor
  · intro h
    obtain ⟨S, hS⟩ := exists_finset_iInter₂_recessionCone_eq_zero hcl h
    exact ⟨S, (hbdd S).2 hS⟩
  · rintro ⟨S, hS⟩
    refine Set.Subset.antisymm (fun y hy => ?_) (by simp)
    rw [← (hbdd S).1 hS]
    exact mem_iInter₂.2 fun i _ => mem_iInter.1 hy i

end FiniteDimensional

end ConvexAnalysis
