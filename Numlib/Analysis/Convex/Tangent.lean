import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Exposed

/-!
# Tangent half-spaces of a convex set

A hyperplane is **tangent** to a closed convex set `C` at a point `y` when it is the *unique*
supporting hyperplane to `C` at `y`, and a **tangent half-space** is a supporting half-space whose
boundary hyperplane is tangent. The theorem proved here is that a closed convex set with nonempty
interior is the intersection of its tangent closed half-spaces — a sharpening of the statement
that a closed convex set is the intersection of *all* the closed half-spaces containing it.

The interior hypothesis is not removable as stated: a closed convex set with empty interior lies in
a proper affine subspace and has no tangent hyperplane anywhere, since every supporting hyperplane
at a point can be tilted around that subspace. The right general statement intersects the tangent
half-spaces *within the affine hull* and adds the affine hull itself.

Tangency is dual to exposedness: after translating so that `0 ∈ int C`, the tangent half-spaces of
`C` correspond exactly to the exposed points of the polar `C°`, and this correspondence carries
the proof.

## Main definitions

* `IsSupportingAt C f y` — `y ∈ C` and the linear functional `f` attains its maximum over `C` at
  `y`, so `{z | f z ≤ f y}` is a supporting half-space and `{z | f z = f y}` a supporting
  hyperplane.
* `IsTangentAt C f y` — that supporting hyperplane is the only one at `y`: every nonzero
  functional supported at `y` is a *positive* multiple of `f`.

## Main results

* `eq_iInter_tangent_halfSpaces` — a closed convex set with nonempty interior is the intersection
  of the closed half-spaces tangent to it.
* `exists_isTangentAt_lt_of_zero_mem_interior` — the separating form: a point outside such a set
  is cut off by a tangent half-space.

## Implementation notes

The proof stays in the polar picture rather than homogenising. After translating so that
`0 ∈ int C`, the polar `C°` is compact; Minkowski's theorem writes it as the hull of its extreme
points, Straszewicz's theorem puts those in the closure of its exposed points, and the exposed
points of `C°` are exactly the normals of the tangent half-spaces to `C`. So a point outside `C` is
already excluded by the half-space of some *exposed* point of `C°`. Identifying an exposing
functional on `E*` with a point of `E`, which produces the point of contact, uses reflexivity
(`Module.evalEquiv`, packaged as `exists_forall_apply_eq`) — a step invisible in `ℝⁿ`.

## References

* [rockafellar1970convex] §18.
-/

open Set Bornology

namespace ConvexAnalysis

/-! ### Supporting and tangent hyperplanes -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
  {f : StrongDual ℝ E} {y x₁ : E}

/-- `f` **supports** `C` at `y`: the point `y` belongs to `C` and maximises `f` over `C`, so that
`{z | f z ≤ f y}` is a supporting half-space and `{z | f z = f y}` a supporting hyperplane. -/
def IsSupportingAt (C : Set E) (f : StrongDual ℝ E) (y : E) : Prop :=
  y ∈ C ∧ ∀ z ∈ C, f z ≤ f y

/-- The hyperplane `{z | f z = f y}` is **tangent** to `C` at `y`: it supports `C` at `y`, and it is
the only supporting hyperplane there. Uniqueness is stated up to a *positive* multiple of the
functional — a hyperplane determines its functional up to a nonzero scalar, and the supporting
inequality fixes the sign. -/
def IsTangentAt (C : Set E) (f : StrongDual ℝ E) (y : E) : Prop :=
  f ≠ 0 ∧ IsSupportingAt C f y ∧
    ∀ g : StrongDual ℝ E, g ≠ 0 → (∀ z ∈ C, g z ≤ g y) → ∃ a : ℝ, 0 < a ∧ g = a • f

/-- A tangent half-space contains `C`. -/
theorem IsTangentAt.subset_halfSpace (h : IsTangentAt C f y) : C ⊆ {z : E | f z ≤ f y} :=
  fun z hz => h.2.1.2 z hz


/-- Tangency is invariant under translation: `{z | z + x₁ ∈ C}` is `C` shifted by `-x₁`. -/
theorem IsTangentAt.shift (h : IsTangentAt {z : E | z + x₁ ∈ C} f y) :
    IsTangentAt C f (y + x₁) := by
  obtain ⟨hf0, ⟨hyC, hymax⟩, huniq⟩ := h
  refine ⟨hf0, ⟨hyC, fun z hz => ?_⟩, fun g hg0 hgmax => ?_⟩
  · have hz' : z - x₁ ∈ {z : E | z + x₁ ∈ C} := by simpa using hz
    have hle := hymax _ hz'
    rw [map_sub] at hle
    rw [map_add]
    linarith
  · refine huniq g hg0 fun u hu => ?_
    have hu' : u + x₁ ∈ C := hu
    have hle := hgmax _ hu'
    rw [map_add, map_add] at hle
    linarith

end Defs

/-! ### A convex set is the intersection of its tangent half-spaces -/

section Tangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- A vector rescaled to a prescribed norm lies in the corresponding ball. This is the only metric
input to the compactness of the polar and to the nondegeneracy of a supporting functional. -/
private theorem smul_div_norm_mem_closedBall {x : E} (hx : x ≠ 0) {r s : ℝ} (hr : 0 < r)
    (hs : |s| = r) : (s / ‖x‖) • x ∈ Metric.closedBall (0 : E) r := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hcancel : r / ‖x‖ * ‖x‖ = r := by field_simp
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_pos hxn, hs, hcancel]

variable [FiniteDimensional ℝ E]

/-- For a closed convex set with the origin in its interior, every point outside is cut off by a
*tangent* half-space. The normal of that half-space is an exposed point of
the polar `C°`, which is compact because `0 ∈ int C`. -/
theorem exists_isTangentAt_lt_of_zero_mem_interior (hC : Convex ℝ C) (hCcl : IsClosed C)
    (h0 : (0 : E) ∈ interior C) {x₀ : E} (hx₀ : x₀ ∉ C) :
    ∃ (f : StrongDual ℝ E) (y : E), IsTangentAt C f y ∧ f y < f x₀ := by
  have h0C : (0 : E) ∈ C := interior_subset h0
  obtain ⟨r, hr, hball⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : E) r ⊆ C := by
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
    exact ⟨ε / 2, by linarith,
      fun z hz => interior_subset (hsub (Metric.closedBall_subset_ball (by linarith) hz))⟩
  have hr0 : r ≠ 0 := ne_of_gt hr
  -- the polar set of `C`
  have hPmem : ∀ y : StrongDual ℝ E,
      y ∈ polarSet ((topDualPairing ℝ E).flip) C ↔ ∀ x ∈ C, y x ≤ 1 := fun _ => Iff.rfl
  have hPconv : Convex ℝ (polarSet ((topDualPairing ℝ E).flip) C) := by
    intro u hu v hv a b ha hb hab x hx
    have h1 := (hPmem u).1 hu x hx
    have h2 := (hPmem v).1 hv x hx
    have hval : (a • u + b • v) x = a * u x + b * v x := by simp
    change (a • u + b • v) x ≤ 1
    rw [hval]
    nlinarith
  have hPcl : IsClosed (polarSet ((topDualPairing ℝ E).flip) C) := by
    have h : polarSet ((topDualPairing ℝ E).flip) C
        = ⋂ x ∈ C, {y : StrongDual ℝ E | y x ≤ 1} := by ext y; simp [polarSet]
    rw [h]
    exact isClosed_biInter fun x _ =>
      isClosed_le (ContinuousLinearMap.apply ℝ ℝ x).continuous continuous_const
  have hPbdd : IsBounded (polarSet ((topDualPairing ℝ E).flip) C) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨r⁻¹, fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_pos.2 hr).le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hxn0 : ‖x‖ ≠ 0 := ne_of_gt hxn
    have h1 := (hPmem y).1 hy _ (hball (smul_div_norm_mem_closedBall hx hr (abs_of_pos hr)))
    have h2 := (hPmem y).1 hy _
      (hball (smul_div_norm_mem_closedBall hx hr (by rw [abs_neg, abs_of_pos hr])))
    rw [map_smul, smul_eq_mul] at h1 h2
    have hc : (0 : ℝ) < ‖x‖ / r := by positivity
    have hA := mul_le_mul_of_nonneg_left h1 hc.le
    have hB := mul_le_mul_of_nonneg_left h2 hc.le
    have e1 : ‖x‖ / r * (r / ‖x‖ * y x) = y x := by field_simp
    have e2 : ‖x‖ / r * (-r / ‖x‖ * y x) = -y x := by field_simp
    have e3 : ‖x‖ / r * 1 = r⁻¹ * ‖x‖ := by rw [mul_one, div_eq_inv_mul]
    rw [e1, e3] at hA
    rw [e2, e3] at hB
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, hA⟩
  have hPcomp : IsCompact (polarSet ((topDualPairing ℝ E).flip) C) :=
    Metric.isCompact_of_isClosed_isBounded hPcl hPbdd
  -- the bipolar theorem
  have hbip : ∀ x : E, (∀ y ∈ polarSet ((topDualPairing ℝ E).flip) C, y x ≤ 1) → x ∈ C := by
    intro x hx
    rw [← polarSet_polarSet (B := (topDualPairing ℝ E).flip) hC hCcl h0C]
    exact fun y hy => hx y hy
  -- some exposed point of the polar already excludes `x₀`
  have hexists : ∃ y ∈ (polarSet ((topDualPairing ℝ E).flip) C).exposedPoints ℝ, 1 < y x₀ := by
    by_contra hcon
    push Not at hcon
    refine hx₀ (hbip x₀ fun y hy => ?_)
    have hclos : closure ((polarSet ((topDualPairing ℝ E).flip) C).exposedPoints ℝ)
        ⊆ {w : StrongDual ℝ E | w x₀ ≤ 1} :=
      closure_minimal (fun w hw => hcon w hw)
        (isClosed_le (ContinuousLinearMap.apply ℝ ℝ x₀).continuous continuous_const)
    have hhull : convexHull ℝ
        (closure ((polarSet ((topDualPairing ℝ E).flip) C).exposedPoints ℝ))
        ⊆ {w : StrongDual ℝ E | w x₀ ≤ 1} :=
      convexHull_min hclos (convex_halfSpace_le
        (f := fun w : StrongDual ℝ E => w x₀) ⟨fun u v => rfl, fun a u => rfl⟩ 1)
    have hmink : convexHull ℝ ((polarSet ((topDualPairing ℝ E).flip) C).extremePoints ℝ)
        = polarSet ((topDualPairing ℝ E).flip) C := convexHull_extremePoints hPcomp hPconv
    have hy' : y ∈ convexHull ℝ ((polarSet ((topDualPairing ℝ E).flip) C).extremePoints ℝ) := by
      rw [hmink]; exact hy
    exact hhull (convexHull_mono
      (extremePoints_subset_closure_exposedPoints hPconv hPcl) hy')
  obtain ⟨ystar, ⟨hyP, Λ, hΛ⟩, hylt⟩ := hexists
  -- the exposing functional is evaluation at a point of `E`
  obtain ⟨p, hp⟩ := exists_forall_apply_eq Λ
  have hexp : ∀ g ∈ polarSet ((topDualPairing ℝ E).flip) C, g p ≤ ystar p ∧
      (ystar p ≤ g p → g = ystar) := by
    intro g hg
    obtain ⟨h1, h2⟩ := hΛ g hg
    rw [hp, hp] at h1 h2
    exact ⟨h1, h2⟩
  have hzeroP : (0 : StrongDual ℝ E) ∈ polarSet ((topDualPairing ℝ E).flip) C :=
    fun x _ => by simp
  have hy0 : ystar ≠ 0 := by
    intro h
    rw [h] at hylt
    simp only [zero_apply] at hylt
    linarith
  have hlam : 0 < ystar p := by
    rcases lt_or_eq_of_le (hexp 0 hzeroP).1 with h | h
    · simpa using h
    · exact absurd ((hexp 0 hzeroP).2 (le_of_eq h.symm)).symm hy0
  -- the point of contact
  have hqval : ∀ g : StrongDual ℝ E, g ((ystar p)⁻¹ • p) = (ystar p)⁻¹ * g p := by
    intro g; rw [map_smul, smul_eq_mul]
  have hystarq : ystar ((ystar p)⁻¹ • p) = 1 := by
    rw [hqval, inv_mul_cancel₀ (ne_of_gt hlam)]
  have hqC : (ystar p)⁻¹ • p ∈ C := by
    refine hbip _ fun g hg => ?_
    rw [hqval, inv_mul_le_iff₀ hlam, mul_one]
    exact (hexp g hg).1
  refine ⟨ystar, (ystar p)⁻¹ • p,
    ⟨hy0, ⟨hqC, fun z hz => by rw [hystarq]; exact (hPmem ystar).1 hyP z hz⟩,
      fun g hg0 hgmax => ?_⟩, by rw [hystarq]; exact hylt⟩
  -- uniqueness of the supporting hyperplane at the point of contact
  have hμnn : 0 ≤ g ((ystar p)⁻¹ • p) := by simpa using hgmax 0 h0C
  have hμpos : 0 < g ((ystar p)⁻¹ • p) := by
    rcases lt_or_eq_of_le hμnn with h | h
    · exact h
    exfalso
    refine hg0 (ContinuousLinearMap.ext fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 := hgmax _ (hball (smul_div_norm_mem_closedBall hx hr (abs_of_pos hr)))
    have h2 := hgmax _
      (hball (smul_div_norm_mem_closedBall hx hr (by rw [abs_neg, abs_of_pos hr])))
    rw [map_smul, smul_eq_mul, ← h] at h1
    rw [map_smul, smul_eq_mul, ← h] at h2
    have hpos : 0 < r / ‖x‖ := by positivity
    simp only [zero_apply]
    have he : (-r / ‖x‖) * g x = -((r / ‖x‖) * g x) := by ring
    rw [he] at h2
    have hz : (r / ‖x‖) * g x = 0 := le_antisymm h1 (by linarith)
    exact (mul_eq_zero.1 hz).resolve_left (ne_of_gt hpos)
  refine ⟨g ((ystar p)⁻¹ • p), hμpos, ?_⟩
  have hmem : (g ((ystar p)⁻¹ • p))⁻¹ • g ∈ polarSet ((topDualPairing ℝ E).flip) C := by
    intro z hz
    change ((g ((ystar p)⁻¹ • p))⁻¹ • g) z ≤ 1
    rw [smul_apply, smul_eq_mul, inv_mul_le_iff₀ hμpos, mul_one]
    exact hgmax z hz
  have hqg : ((g ((ystar p)⁻¹ • p))⁻¹ • g) ((ystar p)⁻¹ • p) = 1 := by
    rw [smul_apply, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt hμpos)]
  have hqg2 : (ystar p)⁻¹ * (((g ((ystar p)⁻¹ • p))⁻¹ • g) p) = 1 := by
    rw [← hqval]; exact hqg
  have hval : ((g ((ystar p)⁻¹ • p))⁻¹ • g) p = ystar p := by
    have hrw : ((g ((ystar p)⁻¹ • p))⁻¹ • g) p
        = ystar p * ((ystar p)⁻¹ * (((g ((ystar p)⁻¹ • p))⁻¹ • g) p)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlam), one_mul]
    rw [hqg2, mul_one] at hrw
    exact hrw
  have heq : (g ((ystar p)⁻¹ • p))⁻¹ • g = ystar := (hexp _ hmem).2 (le_of_eq hval.symm)
  have hgeq : g = g ((ystar p)⁻¹ • p) • ((g ((ystar p)⁻¹ • p))⁻¹ • g) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hμpos), one_smul]
  exact hgeq.trans (by rw [heq])

/-- **A closed convex set with nonempty interior is the intersection of the closed half-spaces
tangent to it.** ("`n`-dimensional in `ℝⁿ`" is `(interior C).Nonempty`.) This sharpens
`isClosed_convex_eq_iInter_halfspaces`, which intersects *all* the closed half-spaces containing
`C`. -/
theorem eq_iInter_tangent_halfSpaces (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hint : (interior C).Nonempty) :
    ⋂ (f : StrongDual ℝ E) (y : E) (_ : IsTangentAt C f y), {z : E | f z ≤ f y} = C := by
  refine subset_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · by_contra hxC
    obtain ⟨x₁, hx₁⟩ := hint
    have hC₁conv : Convex ℝ {z : E | z + x₁ ∈ C} := by
      intro u hu v hv a b ha hb hab
      have hx2 : a • (u + x₁) + b • (v + x₁) = a • u + b • v + (a + b) • x₁ := by module
      rw [hab, one_smul] at hx2
      change a • u + b • v + x₁ ∈ C
      rw [← hx2]
      exact hC hu hv ha hb hab
    have hC₁cl : IsClosed {z : E | z + x₁ ∈ C} := hCcl.preimage (by fun_prop)
    have h0₁ : (0 : E) ∈ interior {z : E | z + x₁ ∈ C} := by
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 isOpen_interior x₁ hx₁
      have hballsub : Metric.ball (0 : E) ε ⊆ {z : E | z + x₁ ∈ C} := by
        intro z hz
        have hz' : z + x₁ ∈ Metric.ball x₁ ε := by
          rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
          simpa using hz
        change z + x₁ ∈ C
        exact interior_subset (hsub hz')
      exact interior_maximal hballsub Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hx₀₁ : x - x₁ ∉ {z : E | z + x₁ ∈ C} := fun hmem => hxC (by simpa using hmem)
    obtain ⟨f, w, htan, hlt⟩ :=
      exists_isTangentAt_lt_of_zero_mem_interior hC₁conv hC₁cl h0₁ hx₀₁
    have hle : f x ≤ f (w + x₁) := by
      simp only [mem_iInter] at hx
      exact hx f (w + x₁) (IsTangentAt.shift htan)
    rw [map_sub] at hlt
    rw [map_add] at hle
    linarith
  · simp only [mem_iInter]
    exact fun f y hty => IsTangentAt.subset_halfSpace hty hx

end Tangent

end ConvexAnalysis
