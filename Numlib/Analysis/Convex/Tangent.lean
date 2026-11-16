/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Exposed

/-!
# Tangent half-spaces of a convex set

Let $C$ be a closed convex set in a finite-dimensional real normed space $E$. A hyperplane is
**tangent** to $C$ at a point $y$ if it is the only supporting hyperplane to $C$ at $y$, and a
**tangent half-space** is a supporting closed half-space whose boundary hyperplane is tangent. This
module proves that a closed convex set with nonempty interior is the intersection of its tangent
closed half-spaces, following §18 of [rockafellar1970convex]. This sharpens the fact that a closed
convex set is the intersection of all the closed half-spaces that contain it.

The interior hypothesis cannot be removed from this statement. A closed convex set with empty
interior lies in a proper affine subspace and has no tangent hyperplane at any point, because every
supporting hyperplane at a point can be tilted around that subspace. The correct general statement
intersects the tangent half-spaces within the affine hull and adds the affine hull itself. Tangency
is dual to exposedness: if $0 \in \operatorname{int} C$, the tangent half-spaces of $C$ correspond
exactly to the exposed points of the polar set $C^\circ$, and this correspondence gives the proof.

## Main definitions

* `ConvexAnalysis.IsSupportingAt`: $y \in C$ and the continuous linear functional $f$ attains its
  maximum over $C$ at $y$, so $\{z : f(z) \le f(y)\}$ is a supporting half-space and
  $\{z : f(z) = f(y)\}$ is a supporting hyperplane.
* `ConvexAnalysis.IsTangentAt`: $f \neq 0$ supports $C$ at $y$, and every nonzero functional that
  supports $C$ at $y$ is a positive multiple of $f$.

## Main results

* `ConvexAnalysis.exists_isTangentAt_lt_of_zero_mem_interior`: if $0 \in \operatorname{int} C$,
  every point outside $C$ is separated from $C$ by a tangent half-space.
* `ConvexAnalysis.eq_iInter_tangent_halfSpaces`: a closed convex set with nonempty interior is the
  intersection of its tangent closed half-spaces.

## Proof outline

The proof works with the polar set and does not pass to a cone. After a translation,
$0 \in \operatorname{int} C$, and then the polar $C^\circ$ is compact. By Minkowski's theorem,
$C^\circ$ is the convex hull of its extreme points. By Straszewicz's theorem, these are in the
closure of the exposed points of $C^\circ$. The exposed points of $C^\circ$ are exactly the normals
of the tangent half-spaces of $C$. So a point outside $C$ is already excluded by the half-space of
some exposed point of $C^\circ$.

## Implementation notes

* An exposing functional on the dual $E^*$ is identified with a point of $E$, which is the point of
  contact. This uses the reflexivity of $E$ (`Module.evalEquiv`, packaged as
  `ConvexAnalysis.exists_forall_apply_eq`), a step that is not visible in $\mathbb{R}^n$.
-/

open Set Bornology

namespace ConvexAnalysis

/-! ### Supporting and tangent hyperplanes -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
  {f : StrongDual ℝ E} {y x₁ : E}

/-- Let $E$ be a real normed space, let $C \subseteq E$, let $f$ be a continuous linear functional
on $E$ and let $y \in E$. The functional $f$ **supports** $C$ at $y$ if $y \in C$ and
$f(z) \le f(y)$ for all $z \in C$. Then $\{z : f(z) \le f(y)\}$ is a supporting half-space and
$\{z : f(z) = f(y)\}$ is a supporting hyperplane to $C$ at $y$. -/
def IsSupportingAt (C : Set E) (f : StrongDual ℝ E) (y : E) : Prop :=
  y ∈ C ∧ ∀ z ∈ C, f z ≤ f y

/-- Let $E$ be a real normed space, let $C \subseteq E$, let $f$ be a continuous linear functional
on $E$ and let $y \in E$. The hyperplane $\{z : f(z) = f(y)\}$ is **tangent** to $C$ at $y$ if
$f \neq 0$, $f$ supports $C$ at $y$, and every nonzero continuous linear functional $g$ with
$g(z) \le g(y)$ for all $z \in C$ is $g = a f$ for some $a > 0$.

So the tangent hyperplane is the only supporting hyperplane at $y$. Uniqueness is stated up to a
positive multiple of the functional, because a hyperplane determines its functional up to a
nonzero factor and the supporting inequality fixes the sign. -/
def IsTangentAt (C : Set E) (f : StrongDual ℝ E) (y : E) : Prop :=
  f ≠ 0 ∧ IsSupportingAt C f y ∧
    ∀ g : StrongDual ℝ E, g ≠ 0 → (∀ z ∈ C, g z ≤ g y) → ∃ a : ℝ, 0 < a ∧ g = a • f

/-- If $\{z : f(z) = f(y)\}$ is tangent to $C$ at $y$, then $C \subseteq \{z : f(z) \le f(y)\}$. -/
theorem IsTangentAt.subset_halfSpace (h : IsTangentAt C f y) : C ⊆ {z : E | f z ≤ f y} :=
  fun z hz => h.2.1.2 z hz


/-- If $f$ is tangent at $y$ to the translated set $C - x_1 = \{z : z + x_1 \in C\}$, then $f$ is
tangent to $C$ at $y + x_1$. -/
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

/-- If $x \neq 0$, $r > 0$ and $|s| = r$, then $(s / \|x\|) x$ lies in the closed ball of radius $r$
about $0$. -/
private theorem smul_div_norm_mem_closedBall {x : E} (hx : x ≠ 0) {r s : ℝ} (hr : 0 < r)
    (hs : |s| = r) : (s / ‖x‖) • x ∈ Metric.closedBall (0 : E) r := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hcancel : r / ‖x‖ * ‖x‖ = r := by field_simp
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_pos hxn, hs, hcancel]

variable [FiniteDimensional ℝ E]

/-- Let $E$ be a finite-dimensional real normed space and let $C \subseteq E$ be a closed convex set
with $0 \in \operatorname{int} C$. Then for every $x_0 \notin C$ there are a continuous linear
functional $f$ and a point $y$ such that $\{z : f(z) = f(y)\}$ is tangent to $C$ at $y$ and
$$f(y) < f(x_0).$$
So every point outside $C$ is separated from $C$ by a tangent half-space.

The normal $f$ of this half-space is an exposed point of the polar set $C^\circ$, which is
compact because $0 \in \operatorname{int} C$. -/
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

/-- Let $E$ be a finite-dimensional real normed space and let $C \subseteq E$ be a closed convex set
with nonempty interior. Then $C$ is the intersection of its tangent closed half-spaces:
$$C = \bigcap \{ \{z : f(z) \le f(y)\} : \{z : f(z) = f(y)\} \text{ is tangent to } C \text{ at
  } y \}.$$

The intersection is over all pairs $(f, y)$ of a continuous linear functional and a point with
`ConvexAnalysis.IsTangentAt C f y`. In $\mathbb{R}^n$, the hypothesis that $C$ is
$n$-dimensional is the hypothesis `(interior C).Nonempty`. This sharpens Mathlib's
`RCLike.iInter_halfSpaces_eq'`, which intersects all the closed half-spaces that contain $C$. -/
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
