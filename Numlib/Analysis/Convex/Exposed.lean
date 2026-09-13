import Numlib.Analysis.Convex.Representation

/-!
# Exposed directions and the exposed representation of a closed convex set

An **exposed face** of a convex set `C` is the set on which some continuous linear functional
attains its maximum over `C`; an **exposed point** is a one-point exposed face, and an **exposed
direction** is the direction of an exposed face that is a closed half-line. Every exposed face is a
face, so exposed points are extreme points and exposed directions are extreme directions, but not
conversely.

The theorem proved here is that a closed convex set containing no lines is recovered from its
exposed points and exposed directions alone, up to closure: `C = cl (conv (exp C ∪ expdir C))`.
`Representation.lean` gives the same recovery from the *extreme* points and directions with no
closure at all; the closure is the price of passing to the smaller, exposed, data, and it cannot be
dropped, because the exposed points of a closed convex set need not be closed. The dual
representation — a closed convex set with nonempty interior is the intersection of the closed
half-spaces *tangent* to it — is in `Tangent.lean`.

## Main definitions

* `IsExposedDirection C y` — the direction of `y` is an *exposed direction* of `C`: some closed
  half-line in the direction of `y` is an exposed face of `C`. `exposedDirections C` is the set of
  vectors generating such directions, the analogue for `exposedPoints` of `IsExtremeDirection`.

## Main results

* `exists_forall_sub_le_mul_sub` — the multiplier for one linear equation: if `g ≤ γ` on the slice
  `C ∩ {f = β}`, and `f` takes values on both sides of `β` on `C`, then `g - γ ≤ c * (f - β)` on
  all of `C` for some `c`.
* `closure_convexHullPD_exposedPoints_exposedDirections` — the exposed representation of a
  line-free closed convex set.
* `closure_coneHull_exposedDirections`, `closure_coneHull_of_forall_exposedDirection` — the cone
  case: a line-free closed convex cone is the closure of the cone its exposed directions
  generate.
* `isExposed_recessionCone` — the recession cone of an exposed face is an exposed face of the
  recession cone, given that it is contained in it; the exposed analogue of `isFace_recessionCone`.
  `exposedDirections_subset_exposedDirections_recessionCone` is the consequence for closed `C`,
  and `isExposedDirection_recessionCone` its topology-free form.

## Implementation notes

The classical proof extends a codimension-two affine set to a supporting
hyperplane, which is really a multiplier: `exists_forall_sub_le_mul_sub` produces it by a
one-dimensional argument valid in every dimension. The final case split is then bounded/unbounded
rather than by the shape of a one-dimensional face — the bounded case is Minkowski's theorem in
every dimension, and only the unbounded case uses `dim C' ≤ 1`.

## References

* [rockafellar1970convex] §18.
-/

open Set Bornology

namespace ConvexAnalysis

/-! ### Exposed directions -/

section Directions

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {C : Set E} {y : E}

/-- `y` generates an **exposed direction** of `C`: `y ≠ 0` and some closed half-line in the
direction of `y` is an exposed face of `C`. Rockafellar's exposed direction — an "exposed point at
infinity" — is the direction itself; representing it by a generating vector avoids a quotient, at
the cost of `exposedDirections C` being closed under multiplication by positive scalars. -/
def IsExposedDirection (C : Set E) (y : E) : Prop :=
  y ≠ 0 ∧ ∃ x, IsExposed ℝ C (halfLine x y)

/-- The set of vectors that generate exposed directions of `C`. -/
def exposedDirections (C : Set E) : Set E := {y | IsExposedDirection C y}

/-- Membership in `exposedDirections`, unfolded. -/
theorem mem_exposedDirections : y ∈ exposedDirections C ↔ IsExposedDirection C y := Iff.rfl

/-- **An exposed direction is an extreme direction.** The half-line that the exposed face happens
to be is a face of `C`, since it is convex and exposed sets are extreme. -/
theorem IsExposedDirection.isExtremeDirection (h : IsExposedDirection C y) :
    IsExtremeDirection C y := by
  obtain ⟨hy, x, hx⟩ := h
  exact ⟨hy, x, ⟨IsExposed.isExtreme hx, convex_halfLine x y⟩⟩

/-- **Exposed directions are extreme directions.** -/
theorem exposedDirections_subset_extremeDirections (C : Set E) :
    exposedDirections C ⊆ extremeDirections C :=
  fun _ hy => IsExposedDirection.isExtremeDirection hy

/-- Exposed directions do not change under positive rescaling of the generator. -/
theorem IsExposedDirection.smul (h : IsExposedDirection C y) {a : ℝ} (ha : 0 < a) :
    IsExposedDirection C (a • y) :=
  ⟨smul_ne_zero ha.ne' h.1, by
    obtain ⟨x, hx⟩ := h.2
    exact ⟨x, by rwa [halfLine_smul x y ha]⟩⟩

/-- The half-line in an exposed direction lies in `C`. -/
theorem IsExposedDirection.halfLine_subset (h : IsExposedDirection C y) :
    ∃ x, halfLine x y ⊆ C := by
  obtain ⟨-, x, hx⟩ := h
  exact ⟨x, IsExposed.subset hx⟩

/-- **The recession cone of an exposed face is an exposed face of the recession cone**, exposed by
the same functional. The hypothesis `0⁺C' ⊆ 0⁺C` supplies the monotonicity the recession cone does
not have; the mechanism is that a functional maximised over `C` is non-positive on `0⁺C` and
vanishes exactly on the directions in which the face itself recedes. -/
theorem isExposed_recessionCone {C' : Set E} (h : IsExposed ℝ C C')
    (hrec : recessionCone C' ⊆ recessionCone C) :
    IsExposed ℝ (recessionCone C) (recessionCone C') := by
  rcases C'.eq_empty_or_nonempty with rfl | hne
  · rw [recessionCone_empty] at hrec ⊢
    rw [univ_subset_iff.1 hrec]
  · intro _
    obtain ⟨l, hl⟩ := h hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hx₀' : x₀ ∈ C ∧ ∀ w ∈ C, l w ≤ l x₀ := by
      have h' := hx₀
      rw [hl, mem_sep_iff] at h'
      exact h'
    -- a functional maximised over `C` is non-positive on every direction of recession
    have hnonpos : ∀ v ∈ recessionCone C, l v ≤ 0 := by
      intro v hv
      have hle := hx₀'.2 _ (add_mem_of_mem_recessionCone hv hx₀'.1)
      rw [map_add] at hle
      linarith
    refine ⟨l, subset_antisymm (fun u hu => ?_) (fun u hu => ?_)⟩
    · have huC : u ∈ recessionCone C := hrec hu
      have hu0 : l u = 0 := by
        have hmem := add_mem_of_mem_recessionCone hu hx₀
        rw [hl, mem_sep_iff] at hmem
        have hle := hmem.2 x₀ hx₀'.1
        rw [map_add] at hle
        have := hnonpos u huC
        linarith
      refine mem_sep_iff.2 ⟨huC, fun v hv => ?_⟩
      rw [hu0]
      exact hnonpos v hv
    · rw [mem_sep_iff] at hu
      have hu0 : l u = 0 := by
        have hle := hu.2 0 (zero_mem_recessionCone C)
        rw [map_zero] at hle
        have := hnonpos u hu.1
        linarith
      intro w hw t ht
      rw [hl, mem_sep_iff] at hw
      rw [hl]
      refine mem_sep_iff.2 ⟨add_smul_mem_of_mem_recessionCone hu.1 hw.1 ht, fun q hq => ?_⟩
      rw [map_add, map_smul, smul_eq_mul, hu0, mul_zero, add_zero]
      exact hw.2 q hq

/-- **An exposed direction in which `C` recedes is an exposed direction of `0⁺C`**: the exposed
analogue of `isExtremeDirection_recessionCone`, and proved the same way. -/
theorem isExposedDirection_recessionCone (h : IsExposedDirection C y)
    (hy : y ∈ recessionCone C) : IsExposedDirection (recessionCone C) y := by
  obtain ⟨hy0, x, hexp⟩ := h
  have hrec : recessionCone (halfLine x y) ⊆ recessionCone C := by
    rw [recessionCone_halfLine_eq_halfLine_zero]
    rintro z ⟨a, ha, rfl⟩
    simpa using smul_mem_recessionCone ha hy
  have hfin := isExposed_recessionCone hexp hrec
  rw [recessionCone_halfLine_eq_halfLine_zero] at hfin
  exact ⟨hy0, 0, hfin⟩

end Directions

/-! ### Exposed directions of the recession cone -/

section DirectionsTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {C : Set E}

/-- **Every exposed direction of a closed convex set is an exposed direction of its recession
cone.** Closedness enters only in knowing that the direction of a half-line exposed face recedes
in `C`. -/
theorem exposedDirections_subset_exposedDirections_recessionCone (hC : Convex ℝ C)
    (hCcl : IsClosed C) : exposedDirections C ⊆ exposedDirections (recessionCone C) :=
  fun _ hy =>
    isExposedDirection_recessionCone hy
      ((exposedDirections_subset_extremeDirections C).trans
        (extremeDirections_subset_recessionCone hC hCcl) hy)

end DirectionsTopology

/-! ### A multiplier for one linear equation -/

section Multiplier

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- **A linear function dominated on a slice is dominated up to a multiple of the slicing
function.** If `g ≤ γ` wherever `f = β` on a convex set `C`, and `f` takes values strictly below
and strictly above `β` on `C`, then `g - γ ≤ c * (f - β)` on all of `C` for some scalar `c`.
Geometrically, the image of `C` under `z ↦ (f z - β, g z - γ)` misses the open upward vertical ray,
so it lies below a line through the origin, and `c` is that line's slope. This replaces the
"extend an `(n-2)`-dimensional affine set to a supporting hyperplane" step of the classical
proof, and needs no dimension hypothesis. -/
theorem exists_forall_sub_le_mul_sub (hC : Convex ℝ C) (f g : E →ₗ[ℝ] ℝ) {β γ : ℝ}
    (hslice : ∀ z ∈ C, f z = β → g z ≤ γ)
    (hlo : ∃ z ∈ C, f z < β) (hhi : ∃ z ∈ C, β < f z) :
    ∃ c : ℝ, ∀ z ∈ C, g z - γ ≤ c * (f z - β) := by
  -- the quotients over the far side of the hyperplane are bounded by those over the near side
  have hcross : ∀ y ∈ C, f y < β → ∀ z ∈ C, β < f z →
      (g z - γ) / (f z - β) ≤ (g y - γ) / (f y - β) := by
    intro y hy hfy z hz hfz
    obtain ⟨a, ha, hfy2⟩ : ∃ a : ℝ, 0 < a ∧ f y - β = -a :=
      ⟨β - f y, by linarith, by ring⟩
    obtain ⟨b, hb, hfz2⟩ : ∃ b : ℝ, 0 < b ∧ f z - β = b :=
      ⟨f z - β, by linarith, rfl⟩
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hab : 0 < a + b := by linarith
    have hab0 : a + b ≠ 0 := ne_of_gt hab
    have hw : (b / (a + b)) • y + (a / (a + b)) • z ∈ C :=
      hC hy hz (by positivity) (by positivity) (by field_simp; ring)
    have hfval : f ((b / (a + b)) • y + (a / (a + b)) • z) = β := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have hfy' : f y = β - a := by linarith
      have hfz' : f z = β + b := by linarith
      rw [hfy', hfz']
      field_simp
      ring
    have hgval := hslice _ hw hfval
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hgval
    have hkey : b * (g y - γ) + a * (g z - γ) ≤ 0 := by
      have h := mul_le_mul_of_nonneg_left hgval hab.le
      have hexp : (a + b) * (b / (a + b) * g y + a / (a + b) * g z) = b * g y + a * g z := by
        field_simp
      rw [hexp] at h
      nlinarith [h]
    rw [hfy2, hfz2]
    have hres : (g y - γ) / -a - (g z - γ) / b
        = -(b * (g y - γ) + a * (g z - γ)) / (a * b) := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ -(b * (g y - γ) + a * (g z - γ)) / (a * b) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  obtain ⟨y₀, hy₀, hfy₀⟩ := hlo
  set A : Set ℝ := {r | ∃ z ∈ C, β < f z ∧ r = (g z - γ) / (f z - β)} with hA
  have hAne : A.Nonempty := by
    obtain ⟨z, hz, hfz⟩ := hhi
    exact ⟨_, z, hz, hfz, rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨(g y₀ - γ) / (f y₀ - β), ?_⟩
    rintro r ⟨z, hz, hfz, rfl⟩
    exact hcross y₀ hy₀ hfy₀ z hz hfz
  refine ⟨sSup A, fun z hz => ?_⟩
  rcases lt_trichotomy (f z) β with hlt | heq | hgt
  · have hub : sSup A ≤ (g z - γ) / (f z - β) := by
      refine csSup_le hAne ?_
      rintro r ⟨w, hw, hfw, rfl⟩
      exact hcross z hz hlt w hw hfw
    rw [le_div_iff_of_neg (by linarith : f z - β < 0)] at hub
    exact hub
  · rw [heq, sub_self, mul_zero, sub_nonpos]
    exact hslice z hz heq
  · have hmem : (g z - γ) / (f z - β) ∈ A := ⟨z, hz, hgt, rfl⟩
    have hle := le_csSup hAbdd hmem
    rwa [div_le_iff₀ (by linarith : (0 : ℝ) < f z - β)] at hle

end Multiplier

/-! ### The exposed representation of a line-free closed convex set -/

section Representation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **A closed convex set containing no lines is the closure of the convex hull of its exposed
points and exposed directions.** Unlike the extreme-point representation the closure cannot be
dropped — the exposed points of a closed convex set need not be closed, and Straszewicz's theorem
only places the extreme points in their closure.

Sketch: if the exposed hull `C₀` were not all of `C`, separate a point of `C \ C₀` from `C₀` by
`H = {f = β}`. The slice `C ∩ H` is a nonempty closed convex set containing no lines, so it has an
exposed point `x`, and `exists_forall_sub_le_mul_sub` turns its
exposing functional into one maximised over `C` at `x`. Its exposed face `C'` meets `H` only at
`x`, which forces `x ∈ ri C'` and `dim C' ≤ 1`; a bounded `C'` is then the hull of its extreme
points, an unbounded one a half-line whose direction is exposed, and either way `x ∈ C₀`. -/
theorem closure_convexHullPD_exposedPoints_exposedDirections
    (hC : Convex ℝ C) (hCcl : IsClosed C) (hnl : ContainsNoLine C) :
    closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) = C := by
  have hDrec : exposedDirections C ⊆ recessionCone C :=
    (exposedDirections_subset_extremeDirections C).trans
      (extremeDirections_subset_recessionCone hC hCcl)
  have hsub : convexHullPD (C.exposedPoints ℝ) (exposedDirections C) ⊆ C :=
    convexHullPD_min hC exposedPoints_subset hDrec
  have hC₀C : closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) ⊆ C :=
    closure_minimal hsub hCcl
  refine subset_antisymm hC₀C ?_
  by_contra hcon
  obtain ⟨x₀, hx₀C, hx₀⟩ := not_subset.1 hcon
  have hextcl : C.extremePoints ℝ ⊆
      closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) :=
    (extremePoints_subset_closure_exposedPoints hC hCcl).trans
      (closure_mono (subset_convexHullPD _ _))
  have hC₀ne : (closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C))).Nonempty := by
    obtain ⟨e, he⟩ := extremePoints_nonempty_of_containsNoLine hC hCcl hnl ⟨x₀, hx₀C⟩
    exact ⟨e, hextcl he⟩
  have hC₀conv : Convex ℝ (closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C))) :=
    (convex_convexHullPD _ _).closure
  obtain ⟨f, β, hfC₀, hfx₀⟩ :=
    geometric_hahn_banach_closed_point hC₀conv isClosed_closure hx₀
  -- the hyperplane `f = β` meets `C`
  obtain ⟨z, hzC₀⟩ := hC₀ne
  have hzC : z ∈ C := hC₀C hzC₀
  have hfz : f z < β := hfC₀ z hzC₀
  have hden : (0 : ℝ) < f x₀ - f z := by linarith
  have ht0 : (0 : ℝ) ≤ (β - f z) / (f x₀ - f z) := div_nonneg (by linarith) hden.le
  have ht1 : (β - f z) / (f x₀ - f z) ≤ 1 := by rw [div_le_one hden]; linarith
  have hwC : (1 - (β - f z) / (f x₀ - f z)) • z + ((β - f z) / (f x₀ - f z)) • x₀ ∈ C :=
    hC hzC hx₀C (by linarith) ht0 (by ring)
  have hfw : f ((1 - (β - f z) / (f x₀ - f z)) • z + ((β - f z) / (f x₀ - f z)) • x₀) = β := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  -- an exposed point of the slice
  have hKconv : Convex ℝ (C ∩ {y : E | f y = β}) :=
    hC.inter (convex_hyperplane (f : E →ₗ[ℝ] ℝ).isLinear β)
  have hKcl : IsClosed (C ∩ {y : E | f y = β}) :=
    hCcl.inter (isClosed_eq f.continuous continuous_const)
  have hKne : (C ∩ {y : E | f y = β}).Nonempty := ⟨_, hwC, hfw⟩
  have hKnl : ContainsNoLine (C ∩ {y : E | f y = β}) := hnl.mono inter_subset_left
  have hexpne : ((C ∩ {y : E | f y = β}).exposedPoints ℝ).Nonempty := by
    obtain ⟨e, he⟩ := extremePoints_nonempty_of_containsNoLine hKconv hKcl hKnl hKne
    rw [← closure_nonempty_iff]
    exact ⟨e, extremePoints_subset_closure_exposedPoints hKconv hKcl he⟩
  obtain ⟨x, ⟨hxC, hxf⟩, g, hg⟩ := hexpne
  have hxf' : f x = β := hxf
  -- the multiplier: `g - c • f` is maximised over `C` at `x`
  obtain ⟨c, hc⟩ := exists_forall_sub_le_mul_sub (γ := g x) (β := β) hC
    (f : E →ₗ[ℝ] ℝ) (g : E →ₗ[ℝ] ℝ)
    (fun y hy hfy => (hg y ⟨hy, hfy⟩).1) ⟨z, hzC, hfz⟩ ⟨x₀, hx₀C, hfx₀⟩
  simp only [ContinuousLinearMap.coe_coe] at hc
  have hhle : ∀ y ∈ C, (g - c • f) y ≤ (g - c • f) x := by
    intro y hy
    have h := hc y hy
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [hxf']
    linarith
  -- the exposed face it cuts out
  have hC'exp : IsExposed ℝ C (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) := by
    refine fun _ => ⟨g - c • f, ?_⟩
    ext y
    constructor
    · rintro ⟨hyC, hy⟩
      exact ⟨hyC, fun v hv => by rw [show (g - c • f) y = (g - c • f) x from hy]; exact hhle v hv⟩
    · rintro ⟨hyC, hy⟩
      exact ⟨hyC, le_antisymm (hhle y hyC) (hy x hxC)⟩
  have hC'face : IsFace C (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) :=
    IsExposed.isFace hC'exp hC
  have hC'conv : Convex ℝ (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) := hC'face.convex
  have hC'cl : IsClosed (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) :=
    hC'face.isClosed hC hCcl
  have hxC' : x ∈ C ∩ {y : E | (g - c • f) y = (g - c • f) x} := ⟨hxC, rfl⟩
  -- the face meets the hyperplane only at `x`
  have hC'H : ∀ y ∈ C ∩ {y : E | (g - c • f) y = (g - c • f) x}, f y = β → y = x := by
    rintro y ⟨hyC, hy⟩ hfy
    have hy' : (g - c • f) y = (g - c • f) x := hy
    simp only [sub_apply, smul_apply, smul_eq_mul] at hy'
    rw [hfy, hxf'] at hy'
    exact (hg y ⟨hyC, hfy⟩).2 (le_of_eq (by linarith))
  have hxC₀ : x ∉ closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) := by
    intro hm
    have := hfC₀ x hm
    rw [hxf'] at this
    exact lt_irrefl β this
  have hxnotext : x ∉ (C ∩ {y : E | (g - c • f) y = (g - c • f) x}).extremePoints ℝ := fun hm =>
    hxC₀ (hextcl (hC'face.toIsExtreme.extremePoints_subset_extremePoints hm))
  -- `f` takes values on both sides of `β` on the face
  have hlo' : ∃ y ∈ C ∩ {y : E | (g - c • f) y = (g - c • f) x}, f y < β := by
    by_contra hcon2
    push Not at hcon2
    refine hxnotext (exposedPoints_subset_extremePoints ⟨hxC', -f, fun y hy => ?_⟩)
    have h1 : β ≤ f y := hcon2 y hy
    refine ⟨by simp only [neg_apply, hxf']; linarith, fun hle => ?_⟩
    simp only [neg_apply, hxf', neg_le_neg_iff] at hle
    exact hC'H y hy (le_antisymm hle h1)
  have hhi' : ∃ y ∈ C ∩ {y : E | (g - c • f) y = (g - c • f) x}, β < f y := by
    by_contra hcon2
    push Not at hcon2
    refine hxnotext (exposedPoints_subset_extremePoints ⟨hxC', f, fun y hy => ?_⟩)
    have h1 : f y ≤ β := hcon2 y hy
    refine ⟨by rw [hxf']; exact h1, fun hle => ?_⟩
    rw [hxf'] at hle
    exact hC'H y hy (le_antisymm h1 hle)
  -- hence `x` is a relative interior point of the face
  have hxri : x ∈ ri (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) := by
    obtain ⟨y₁, hy₁, hf₁⟩ := hlo'
    obtain ⟨y₂, hy₂, hf₂⟩ := hhi'
    have himg : Convex ℝ ((f : E →ₗ[ℝ] ℝ) '' (C ∩ {y : E | (g - c • f) y = (g - c • f) x})) :=
      Convex.linear_image hC'conv _
    have hIcc : Icc (f y₁) (f y₂) ⊆
        (f : E →ₗ[ℝ] ℝ) '' (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) :=
      himg.ordConnected.out ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
    have hβri : β ∈ ri ((f : E →ₗ[ℝ] ℝ) '' (C ∩ {y : E | (g - c • f) y = (g - c • f) x})) :=
      interior_subset_intrinsicInterior
        (mem_interior.2 ⟨Ioo (f y₁) (f y₂), Ioo_subset_Icc_self.trans hIcc, isOpen_Ioo,
          ⟨hf₁, hf₂⟩⟩)
    rw [Convex.relint_image hC'conv (f : E →ₗ[ℝ] ℝ)] at hβri
    obtain ⟨v, hv, hfv⟩ := hβri
    have hvx : v = x := hC'H v (intrinsicInterior_subset hv) hfv
    rwa [hvx] at hv
  -- and the face is at most one-dimensional
  have hdim : Module.finrank ℝ
      (vectorSpan ℝ (C ∩ {y : E | (g - c • f) y = (g - c • f) x})) ≤ 1 := by
    obtain ⟨hxA, ε, hε, hball⟩ := mem_intrinsicInterior_iff.1 hxri
    have hinj : Function.Injective
        ((f : E →ₗ[ℝ] ℝ).comp
          (vectorSpan ℝ (C ∩ {y : E | (g - c • f) y = (g - c • f) x})).subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨v, hvmem⟩ hv0
      have hfv0 : f v = 0 := hv0
      have hnorm : (0 : ℝ) < ‖v‖ + 1 := by positivity
      set δ : ℝ := ε / (2 * (‖v‖ + 1)) with hδ
      have hδpos : 0 < δ := by positivity
      have hspan : x + δ • v ∈ affineSpan ℝ (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) := by
        have hmem : δ • v ∈
            (affineSpan ℝ (C ∩ {y : E | (g - c • f) y = (g - c • f) x})).direction := by
          rw [direction_affineSpan]
          exact Submodule.smul_mem _ δ hvmem
        have h := AffineSubspace.vadd_mem_of_mem_direction hmem hxA
        rwa [vadd_eq_add, add_comm] at h
      have hdist : dist (x + δ • v) x < ε := by
        rw [dist_eq_norm, show x + δ • v - x = δ • v by module, norm_smul, Real.norm_eq_abs,
          abs_of_pos hδpos, hδ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
      have hin := hball _ hspan hdist
      have hfval : f (x + δ • v) = β := by
        rw [map_add, map_smul, smul_eq_mul, hfv0, hxf', mul_zero, add_zero]
      have heqx := hC'H _ hin hfval
      have hzero : δ • v = 0 := by
        have : x + δ • v - x = x - x := by rw [heqx]
        simpa using this
      have hv : v = 0 := by
        rcases smul_eq_zero.1 hzero with h | h
        · exact absurd h hδpos.ne'
        · exact h
      exact Subtype.ext hv
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using hle
  -- conclude, according to whether the face is bounded
  by_cases hb : IsBounded (C ∩ {y : E | (g - c • f) y = (g - c • f) x})
  · have hcomp : IsCompact (C ∩ {y : E | (g - c • f) y = (g - c • f) x}) :=
      Metric.isCompact_of_isClosed_isBounded hC'cl hb
    refine hxC₀ ?_
    have hsubC₀ : C ∩ {y : E | (g - c • f) y = (g - c • f) x} ⊆
        closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C)) := by
      rw [← convexHull_extremePoints hcomp hC'conv]
      exact convexHull_min
        (fun p hp => hextcl (hC'face.toIsExtreme.extremePoints_subset_extremePoints hp)) hC₀conv
    exact hsubC₀ hxC'
  · obtain ⟨a, y, hy0, hC'eq⟩ :=
      exists_eq_halfLine hC'conv hC'cl ⟨x, hxC'⟩ (hnl.mono hC'face.subset) hdim hb
    have hyD : y ∈ exposedDirections C := ⟨hy0, a, hC'eq ▸ hC'exp⟩
    have haext : a ∈ (C ∩ {y : E | (g - c • f) y = (g - c • f) x}).extremePoints ℝ := by
      rw [hC'eq]
      exact mem_extremePoints_halfLine a y hy0
    have haC₀ := hextcl (hC'face.toIsExtreme.extremePoints_subset_extremePoints haext)
    have hyrec : y ∈ recessionCone
        (closure (convexHullPD (C.exposedPoints ℝ) (exposedDirections C))) :=
      recessionCone_subset_recessionCone_closure _
        (subset_recessionCone_convexHullPD _ _ hyD)
    refine hxC₀ ?_
    have hxmem : x ∈ halfLine a y := hC'eq ▸ hxC'
    obtain ⟨s, hs, rfl⟩ := hxmem
    exact add_smul_mem_of_mem_recessionCone hyrec haC₀ hs

/-! ### The cone case -/

/-- **A closed convex cone containing no lines is the closure of the cone generated by its exposed
directions.** The usual statement assumes the cone contains more than the origin; that is
unnecessary, since the zero cone has no exposed directions and
`PointedCone.hull ℝ ∅ = {0}`. -/
theorem closure_coneHull_exposedDirections (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hne : C.Nonempty) (hcone : ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → a • x ∈ C)
    (hnl : ContainsNoLine C) :
    closure (PointedCone.hull ℝ (exposedDirections C) : Set E) = C := by
  have h := closure_convexHullPD_exposedPoints_exposedDirections hC hCcl hnl
  have hsub : C.exposedPoints ℝ ⊆ ({0} : Set E) := by
    rw [← extremePoints_eq_singleton_zero hne hcone hnl]
    exact exposedPoints_subset_extremePoints
  rcases (C.exposedPoints ℝ).eq_empty_or_nonempty with hem | ⟨p, hp⟩
  · rw [hem, convexHullPD_empty_left, closure_empty] at h
    exact absurd hne (by rw [← h]; exact not_nonempty_empty)
  · have hzero : (0 : E) ∈ C.exposedPoints ℝ := by
      rwa [show p = 0 from hsub hp] at hp
    rw [subset_antisymm hsub (singleton_subset_iff.2 hzero), convexHullPD_zero_singleton] at h
    exact h

/-- **The generating form**: any set of vectors of a line-free closed convex cone that generates
all of its exposed rays generates the cone, up to closure. -/
theorem closure_coneHull_of_forall_exposedDirection {T : Set E} (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hne : C.Nonempty) (hcone : ∀ x ∈ C, ∀ a : ℝ, 0 ≤ a → a • x ∈ C)
    (hnl : ContainsNoLine C) (hTC : T ⊆ C)
    (hgen : ∀ y ∈ exposedDirections C, ∃ x ∈ T, ∃ a : ℝ, 0 < a ∧ y = a • x) :
    closure (PointedCone.hull ℝ T : Set E) = C := by
  refine subset_antisymm
    (closure_minimal (coeHull_subset_of_forall_smul_mem hC hne hcone hTC) hCcl) ?_
  rw [← closure_coneHull_exposedDirections hC hCcl hne hcone hnl]
  refine closure_mono ?_
  have hle : PointedCone.hull ℝ (exposedDirections C) ≤ PointedCone.hull ℝ T := by
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨u, huT, a, ha, rfl⟩ := hgen y hy
    exact Submodule.smul_mem _ (⟨a, ha.le⟩ : {r : ℝ // 0 ≤ r}) (PointedCone.subset_hull huT)
  exact hle

end Representation

end ConvexAnalysis

